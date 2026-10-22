import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import SOptLib.Glue.Algebra
import SOptLib.Glue.Martingale
import SOptLib.Model.ConditionalExpectation
import SOptLib.Model.Filtration
import SOptLib.Model.Iterates
import SOptLib.Model.Objective
import SOptLib.Layer0.Objective
import SOptLib.Layer1.Telescope
import Algorithms.Unverified.TimeVaryingPushPull.Part001

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
open scoped Topology

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

/- Active-source specialization of Lemma 4.2's row-Dobrushin route.  This
theorem is intentionally proved directly from the generic row-minorized
consecutive-product API, rather than through the retained legacy push helper or
through the bundled `PeriodicProductContraction` conclusion. -/
theorem pushLiftProduct_consensusError_frobenius_rate_from_rowMinorized_source
    (t j : ℕ) (X : State Node E) :
    stateFrobeniusNorm (Node := Node) (E := E)
        (consensusError (Node := Node) (E := E)
          (leftMul (Node := Node) (E := E) (setup.pushLiftProduct t j) X)) ≤
      setup.rowContractionConstant * setup.contractionRate ^ j *
        stateFrobeniusNorm (Node := Node) (E := E)
          (consensusError (Node := Node) (E := E) X) := by
  have hdelta_pos : 0 < setup.contractionDelta := setup.contractionDelta_pos
  have hdelta_lt : setup.contractionDelta < 1 := setup.contractionDelta_lt_one
  have hwindow_pos : 0 < contractionWindow (Node := Node) := by
    simp [contractionWindow]
  have hrate_nonneg : 0 ≤ setup.contractionRate := setup.contractionRate_nonneg
  have hrate_window :
      setup.contractionRate ^ contractionWindow (Node := Node) =
        setup.contractionDelta := by
    rw [contractionRate]
    exact Real.rpow_inv_natCast_pow hdelta_pos.le (Nat.ne_of_gt hwindow_pos)
  rw [setup.pushLiftProduct_eq_consecutiveProduct]
  simpa [rowContractionConstant] using
    (rowConsecutiveProduct_consensusError_frobenius_rate_of_blockMinorization
      (Node := Node) (E := E) setup.R
      (setup.minPositiveWeight ^ contractionWindow (Node := Node))
      setup.contractionDelta setup.contractionRate
      (contractionWindow (Node := Node)) hwindow_pos hdelta_pos hdelta_lt
      hrate_nonneg hrate_window
      (le_max_right (1 / 2)
        (1 - (nodeCount (Node := Node) : ℝ) *
          setup.minPositiveWeight ^ contractionWindow (Node := Node)))
      setup.R_rowStochastic
      (by
        intro s i k
        rw [← setup.pushLiftProduct_eq_consecutiveProduct]
        exact setup.pushLiftProduct_window_entry_lowerBound s i k)
      t j X)

theorem pullLiftProduct_extend_source (j t : ℕ) (hjt : j < t) :
    setup.pullLiftProduct (j + 1) (t - j) =
      matrixMul (Node := Node) (setup.C t)
        (setup.pullLiftProduct (j + 1) (t - 1 - j)) := by
  have hlen : t - j = (t - 1 - j) + 1 := by omega
  rw [hlen, pullLiftProduct]
  congr 2
  omega

/- Every Perron residual `S_t X` has zero column sum. -/
theorem perronResidual_sum_zero_source (t : ℕ) (X : State Node E) :
    ∑ i : Node, setup.perronResidual t X i = 0 := by
  classical
  unfold perronResidual
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
  have hv : ∑ i : Node, setup.perronRight t i = 1 := by
    simpa [rowSum] using setup.perronRight_sum t
  rw [hv, one_smul, sub_self]

/- Appendix B expansion of (6.4). -/
theorem meanJointCoordinate_unroll_source
    (noise : NoisePath Node E) (t : ℕ) :
    setup.meanJointCoordinate noise t =
      leftMul (Node := Node) (E := E) (setup.pullLiftProduct 0 t)
          (setup.meanJointCoordinate noise 0) +
        ∑ j ∈ Finset.range t,
          leftMul (Node := Node) (E := E)
            (setup.pullLiftProduct (j + 1) (t - 1 - j))
            (leftMul (Node := Node) (E := E)
              (setup.perronResidualMatrix (j + 1))
              (setup.gradientTable (setup.primalState noise (j + 1)) -
                setup.gradientTable (setup.primalState noise j))) := by
  classical
  induction t with
  | zero =>
      simp [pullLiftProduct, leftMul_identity]
  | succ t ih =>
      rw [setup.meanJointCoordinate_succ noise t, ih, leftMul_add_state,
        leftMul_finset_sum_state, Finset.sum_range_succ]
      have hinitial :
          leftMul (Node := Node) (E := E) (setup.C t)
              (leftMul (Node := Node) (E := E) (setup.pullLiftProduct 0 t)
                (setup.meanJointCoordinate noise 0)) =
            leftMul (Node := Node) (E := E) (setup.pullLiftProduct 0 (t + 1))
              (setup.meanJointCoordinate noise 0) := by
        rw [← leftMul_matrixMul]
        simp only [pullLiftProduct, Nat.zero_add]
      have hterms :
          (∑ j ∈ Finset.range t,
              leftMul (Node := Node) (E := E) (setup.C t)
                (leftMul (Node := Node) (E := E)
                  (setup.pullLiftProduct (j + 1) (t - 1 - j))
                  (leftMul (Node := Node) (E := E)
                    (setup.perronResidualMatrix (j + 1))
                    (setup.gradientTable (setup.primalState noise (j + 1)) -
                      setup.gradientTable (setup.primalState noise j))))) =
            ∑ j ∈ Finset.range t,
              leftMul (Node := Node) (E := E)
                (setup.pullLiftProduct (j + 1) (t - j))
                (leftMul (Node := Node) (E := E)
                  (setup.perronResidualMatrix (j + 1))
                  (setup.gradientTable (setup.primalState noise (j + 1)) -
                    setup.gradientTable (setup.primalState noise j))) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [← leftMul_matrixMul,
          ← setup.pullLiftProduct_extend_source j t (Finset.mem_range.mp hj)]
      rw [hinitial, hterms]
      have hsum_succ :
          (∑ j ∈ Finset.range t,
              leftMul (Node := Node) (E := E)
                (setup.pullLiftProduct (j + 1) (t - j))
                (leftMul (Node := Node) (E := E)
                  (setup.perronResidualMatrix (j + 1))
                  (setup.gradientTable (setup.primalState noise (j + 1)) -
                    setup.gradientTable (setup.primalState noise j)))) =
            ∑ j ∈ Finset.range t,
              leftMul (Node := Node) (E := E)
                (setup.pullLiftProduct (j + 1) ((t + 1) - 1 - j))
                (leftMul (Node := Node) (E := E)
                  (setup.perronResidualMatrix (j + 1))
                  (setup.gradientTable (setup.primalState noise (j + 1)) -
                    setup.gradientTable (setup.primalState noise j))) := by
        apply Finset.sum_congr rfl
        intro j hj
        congr 3
      rw [hsum_succ]
      simp only [show t + 1 - 1 - t = 0 by omega, pullLiftProduct,
        leftMul_identity, Nat.zero_add]
      abel

/- Appendix B expansion of the noise-driven tracker recursion (5.10). -/
theorem noiseTrackerError_unroll_source
    (noise : NoisePath Node E) (t : ℕ) :
    setup.noiseTrackerError noise t =
      ∑ j ∈ Finset.range t,
        leftMul (Node := Node) (E := E)
          (setup.pullLiftProduct (j + 1) (t - 1 - j))
          (leftMul (Node := Node) (E := E)
            (matrixSub (Node := Node) (setup.C j)
              (identityMatrix (Node := Node))) (noise j)) := by
  classical
  induction t with
  | zero =>
      simp [noiseTrackerError, SOptLib.recursiveIterateProcess]
  | succ t ih =>
      change
        leftMul (Node := Node) (E := E) (setup.C t)
            (setup.noiseTrackerError noise t) +
          leftMul (Node := Node) (E := E)
            (matrixSub (Node := Node) (setup.C t)
              (identityMatrix (Node := Node))) (noise t) = _
      rw [ih, leftMul_finset_sum_state, Finset.sum_range_succ]
      have hterms :
          (∑ j ∈ Finset.range t,
              leftMul (Node := Node) (E := E) (setup.C t)
                (leftMul (Node := Node) (E := E)
                  (setup.pullLiftProduct (j + 1) (t - 1 - j))
                  (leftMul (Node := Node) (E := E)
                    (matrixSub (Node := Node) (setup.C j)
                      (identityMatrix (Node := Node))) (noise j)))) =
            ∑ j ∈ Finset.range t,
              leftMul (Node := Node) (E := E)
                (setup.pullLiftProduct (j + 1) (t - j))
                (leftMul (Node := Node) (E := E)
                  (matrixSub (Node := Node) (setup.C j)
                    (identityMatrix (Node := Node))) (noise j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [← leftMul_matrixMul,
          ← setup.pullLiftProduct_extend_source j t (Finset.mem_range.mp hj)]
      rw [hterms]
      have hsum_succ :
          (∑ j ∈ Finset.range t,
              leftMul (Node := Node) (E := E)
                (setup.pullLiftProduct (j + 1) (t - j))
                (leftMul (Node := Node) (E := E)
                  (matrixSub (Node := Node) (setup.C j)
                    (identityMatrix (Node := Node))) (noise j))) =
            ∑ j ∈ Finset.range t,
              leftMul (Node := Node) (E := E)
                (setup.pullLiftProduct (j + 1) ((t + 1) - 1 - j))
                (leftMul (Node := Node) (E := E)
                  (matrixSub (Node := Node) (setup.C j)
                    (identityMatrix (Node := Node))) (noise j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        congr 3
      rw [hsum_succ]
      simp only [show t + 1 - 1 - t = 0 by omega, pullLiftProduct,
        leftMul_identity]

/-- The exact source expansion preceding (6.6):
`J_t^epsilon = epsilon_t + sum_{j<t} C_{t-1:j+1}(C_j-I)epsilon_j`. -/
theorem noiseJointCoordinate_unroll
    (noise : NoisePath Node E) (t : ℕ) :
    setup.noiseJointCoordinate noise t =
      noise t +
        ∑ j ∈ Finset.range t,
          leftMul (Node := Node) (E := E)
            (setup.pullLiftProduct (j + 1) (t - 1 - j))
            (leftMul (Node := Node) (E := E)
              (matrixSub (Node := Node) (setup.C j)
                (identityMatrix (Node := Node))) (noise j)) := by
  rw [noiseJointCoordinate, setup.noiseTrackerError_unroll_source]

theorem gradientTable_difference_stateFrobenius_le
    (X Y : State Node E) :
    stateFrobeniusNorm (Node := Node) (E := E)
        (setup.gradientTable X - setup.gradientTable Y) ≤
      setup.L * stateFrobeniusNorm (Node := Node) (E := E) (X - Y) := by
  have hsq := setup.gradientTable_difference_frobeniusSq_le X Y
  have hsq' :
      stateFrobeniusNorm (Node := Node) (E := E)
          (setup.gradientTable X - setup.gradientTable Y) ^ 2 ≤
        (setup.L * stateFrobeniusNorm (Node := Node) (E := E) (X - Y)) ^ 2 := by
    rw [stateFrobeniusNorm_sq, mul_pow,
      stateFrobeniusNorm_sq]
    exact hsq
  exact (sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg setup.L_pos.le (Real.sqrt_nonneg _))).mp hsq'

theorem perronResidualNormMax_nonneg_source :
    0 ≤ setup.perronResidualNormMax := by
  let r : Fin setup.period := ⟨0, setup.period_pos⟩
  have hnorm : 0 ≤ matrixEuclideanOperatorNorm (Node := Node)
      (setup.perronResidualMatrix r.1) :=
    (matrixEuclideanOperatorNorm_spec (Node := Node) _).1
  exact hnorm.trans (by
    simpa [perronResidualNormMax] using
      (setup.le_periodMax
        (fun q : Fin setup.period =>
          matrixEuclideanOperatorNorm (Node := Node)
            (setup.perronResidualMatrix q.1)) r))

/- Norm form of the Appendix B convolution for the mean joint coordinate. -/
theorem meanJointCoordinate_norm_convolution_source
    (noise : NoisePath Node E) (t : ℕ) :
    stateFrobeniusNorm (Node := Node) (E := E)
        (setup.meanJointCoordinate noise t) ≤
      setup.columnContractionConstant * setup.contractionRate ^ t *
          stateFrobeniusNorm (Node := Node) (E := E)
            (setup.meanJointCoordinate noise 0) +
        ∑ j ∈ Finset.range t,
          setup.columnContractionConstant * setup.contractionRate ^ (t - 1 - j) *
            (setup.perronResidualNormMax * setup.L *
              stateFrobeniusNorm (Node := Node) (E := E)
                (setup.primalState noise (j + 1) - setup.primalState noise j)) := by
  rw [setup.meanJointCoordinate_unroll_source noise t]
  calc
    _ ≤ stateFrobeniusNorm (Node := Node) (E := E)
          (leftMul (Node := Node) (E := E) (setup.pullLiftProduct 0 t)
            (setup.meanJointCoordinate noise 0)) +
        stateFrobeniusNorm (Node := Node) (E := E)
          (∑ j ∈ Finset.range t,
            leftMul (Node := Node) (E := E)
              (setup.pullLiftProduct (j + 1) (t - 1 - j))
              (leftMul (Node := Node) (E := E)
                (setup.perronResidualMatrix (j + 1))
                (setup.gradientTable (setup.primalState noise (j + 1)) -
                  setup.gradientTable (setup.primalState noise j)))) :=
      stateFrobeniusNorm_add_le _ _
    _ ≤ stateFrobeniusNorm (Node := Node) (E := E)
          (leftMul (Node := Node) (E := E) (setup.pullLiftProduct 0 t)
            (setup.meanJointCoordinate noise 0)) +
        ∑ j ∈ Finset.range t,
          stateFrobeniusNorm (Node := Node) (E := E)
            (leftMul (Node := Node) (E := E)
              (setup.pullLiftProduct (j + 1) (t - 1 - j))
              (leftMul (Node := Node) (E := E)
                (setup.perronResidualMatrix (j + 1))
                (setup.gradientTable (setup.primalState noise (j + 1)) -
                  setup.gradientTable (setup.primalState noise j)))) :=
      add_le_add le_rfl (stateFrobeniusNorm_finset_sum_le _ _)
    _ ≤ setup.columnContractionConstant * setup.contractionRate ^ t *
          stateFrobeniusNorm (Node := Node) (E := E)
            (setup.meanJointCoordinate noise 0) +
        ∑ j ∈ Finset.range t,
          setup.columnContractionConstant * setup.contractionRate ^ (t - 1 - j) *
            (setup.perronResidualNormMax * setup.L *
              stateFrobeniusNorm (Node := Node) (E := E)
                (setup.primalState noise (j + 1) - setup.primalState noise j)) := by
      apply add_le_add
      · exact setup.pullLiftProduct_frobenius_rate
          setup.contractionDelta_pos setup.contractionDelta_lt_one 0 t
          ⟨setup.meanJointCoordinate noise 0,
            setup.meanJointCoordinate_zeroSum noise 0⟩
      · apply Finset.sum_le_sum
        intro j _hj
        let dZ := setup.gradientTable (setup.primalState noise (j + 1)) -
          setup.gradientTable (setup.primalState noise j)
        let W : ZeroSumState Node E :=
          ⟨leftMul (Node := Node) (E := E)
              (setup.perronResidualMatrix (j + 1)) dZ,
            by
              rw [setup.leftMul_perronResidualMatrix]
              exact setup.perronResidual_sum_zero_source (j + 1) dZ⟩
        have hprop := setup.pullLiftProduct_frobenius_rate
          setup.contractionDelta_pos setup.contractionDelta_lt_one
          (j + 1) (t - 1 - j) W
        have hres := setup.perronResidual_stateFrobenius_action (j + 1) dZ
        have hgrad := setup.gradientTable_difference_stateFrobenius_le
          (setup.primalState noise (j + 1)) (setup.primalState noise j)
        have hcoeff :
            0 ≤ setup.columnContractionConstant *
              setup.contractionRate ^ (t - 1 - j) := by
          exact mul_nonneg
            (div_nonneg (Real.sqrt_nonneg _) setup.contractionDelta_pos.le)
            (pow_nonneg setup.contractionRate_nonneg _)
        have hresidual :
            stateFrobeniusNorm (Node := Node) (E := E) W.1 ≤
              setup.perronResidualNormMax * setup.L *
                stateFrobeniusNorm (Node := Node) (E := E)
                  (setup.primalState noise (j + 1) - setup.primalState noise j) := by
          calc
            _ ≤ setup.perronResidualNormMax *
                stateFrobeniusNorm (Node := Node) (E := E) dZ := hres
            _ ≤ setup.perronResidualNormMax *
                (setup.L * stateFrobeniusNorm (Node := Node) (E := E)
                  (setup.primalState noise (j + 1) - setup.primalState noise j)) :=
              mul_le_mul_of_nonneg_left hgrad
                setup.perronResidualNormMax_nonneg_source
            _ = _ := by ring
        exact hprop.trans (mul_le_mul_of_nonneg_left hresidual hcoeff)

/-- Equation (6.5), before expectation: the mean joint-coordinate energy is
bounded pathwise by the initial heterogeneity and primal displacement energy.
This is the deterministic estimate that the paper subsequently integrates. -/
theorem meanJointCoordinate_pathwise_energy_bound
    (noise : NoisePath Node E) (N : ℕ) :
    Finset.sum (Finset.range (N + 1)) (fun t =>
        frobeniusNormSq (Node := Node) (E := E)
          (setup.meanJointCoordinate noise t)) ≤
      setup.thetaInitialConstant * setup.initialGradientHeterogeneity ^ 2 +
        setup.thetaDisplacementConstant * setup.L ^ 2 *
          Finset.sum (Finset.range N) (fun t =>
            frobeniusNormSq (Node := Node) (E := E)
              (setup.primalState noise (t + 1) - setup.primalState noise t)) := by
  have hM : 0 ≤ setup.columnContractionConstant := by
    rw [columnContractionConstant]
    exact div_nonneg (Real.sqrt_nonneg _) setup.contractionDelta_pos.le
  have hr0 : 0 < setup.contractionRate := by
    rw [contractionRate]
    exact Real.rpow_pos_of_pos setup.contractionDelta_pos _
  have hr1 : setup.contractionRate < 1 := setup.contractionRate_lt_one
  have hconv := SquareSummableGeometricConvolution
    (u := fun t => stateFrobeniusNorm (Node := Node) (E := E)
      (setup.meanJointCoordinate noise t))
    (z := fun t => setup.perronResidualNormMax * setup.L *
      stateFrobeniusNorm (Node := Node) (E := E)
        (setup.primalState noise (t + 1) - setup.primalState noise t))
    (M := setup.columnContractionConstant) (r := setup.contractionRate)
    (fun _ => Real.sqrt_nonneg _)
    (fun _ => mul_nonneg
      (mul_nonneg setup.perronResidualNormMax_nonneg_source setup.L_pos.le)
      (Real.sqrt_nonneg _))
    hM hr0 hr1
    (fun t => setup.meanJointCoordinate_norm_convolution_source noise t) N
  have hzero :
      stateFrobeniusNorm (Node := Node) (E := E)
          (setup.meanJointCoordinate noise 0) =
        setup.initialGradientHeterogeneity := by
    rw [setup.meanJointCoordinate_zero]
    rfl
  calc
    Finset.sum (Finset.range (N + 1)) (fun t =>
        frobeniusNormSq (Node := Node) (E := E)
          (setup.meanJointCoordinate noise t)) =
      Finset.sum (Finset.range (N + 1)) (fun t =>
        stateFrobeniusNorm (Node := Node) (E := E)
          (setup.meanJointCoordinate noise t) ^ 2) := by
        apply Finset.sum_congr rfl
        intro t _
        exact (stateFrobeniusNorm_sq _).symm
    _ ≤ (2 * setup.columnContractionConstant ^ 2 /
          (1 - setup.contractionRate ^ 2)) *
          stateFrobeniusNorm (Node := Node) (E := E)
            (setup.meanJointCoordinate noise 0) ^ 2 +
        (2 * setup.columnContractionConstant ^ 2 /
          (1 - setup.contractionRate) ^ 2) *
          Finset.sum (Finset.range N) (fun j =>
            (setup.perronResidualNormMax * setup.L *
              stateFrobeniusNorm (Node := Node) (E := E)
                (setup.primalState noise (j + 1) - setup.primalState noise j)) ^ 2) :=
      hconv
    _ = setup.thetaInitialConstant * setup.initialGradientHeterogeneity ^ 2 +
        setup.thetaDisplacementConstant * setup.L ^ 2 *
          Finset.sum (Finset.range N) (fun t =>
            frobeniusNormSq (Node := Node) (E := E)
              (setup.primalState noise (t + 1) - setup.primalState noise t)) := by
      rw [hzero, thetaInitialConstant, thetaDisplacementConstant,
        Finset.mul_sum]
      apply congrArg₂ (· + ·) rfl
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      rw [show
        (setup.perronResidualNormMax * setup.L *
          stateFrobeniusNorm (Node := Node) (E := E)
            (setup.primalState noise (t + 1) - setup.primalState noise t)) ^ 2 =
          setup.perronResidualNormMax ^ 2 * setup.L ^ 2 *
            frobeniusNormSq (Node := Node) (E := E)
              (setup.primalState noise (t + 1) - setup.primalState noise t) by
        rw [mul_pow, mul_pow, stateFrobeniusNorm_sq]
        ]
      ring

/- Coordinatewise `L²` regularity of the deterministic joint coordinate.  It
is derived from the generated primal process and component smoothness, rather
than added to the oracle contract. -/
theorem meanJointCoordinate_coordinate_memLp
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) :
    ∀ t : ℕ, ∀ i : Node,
      MemLp (fun ω => setup.meanJointCoordinate (oracle.noise ω) t i) 2 μ := by
  classical
  let K : NNReal := ⟨setup.L, setup.L_pos.le⟩
  have hgradient_lipschitz (i : Node) :
      LipschitzWith K (setup.componentGradient i) := by
    rw [lipschitzWith_iff_norm_sub_le]
    intro x y
    simpa [K, componentGradient] using
      setup.componentGradient_lipschitz_bound i x y
  have hgradient (t : ℕ) (i : Node) :
      MemLp (fun ω => setup.gradientTable
        (setup.primalState (oracle.noise ω) t) i) 2 μ := by
    have hprimal :=
      (setup.generated_pushpull_coordinate_memLp μ oracle horacle t).1 i
    simpa [gradientTable] using
      memLp_two_comp_lipschitz (setup.componentGradient i) K
        (hgradient_lipschitz i) hprimal
  intro t
  induction t with
  | zero =>
      intro i
      have hconst : MemLp
          (fun _ : Ω =>
            setup.perronResidual 0 (setup.gradientTable setup.initialPrimal) i)
          2 μ := memLp_const _
      refine MemLp.ae_eq ?_ hconst
      exact Filter.Eventually.of_forall fun ω =>
        (congrFun (setup.meanJointCoordinate_zero (oracle.noise ω)) i).symm
  | succ t ih =>
      intro i
      have hpropagated : MemLp
          (fun ω => ∑ j : Node,
            setup.C t i j • setup.meanJointCoordinate (oracle.noise ω) t j)
          2 μ := by
        apply memLp_finset_sum Finset.univ
        intro j _hj
        exact (ih j).const_smul (setup.C t i j)
      have hforcing : MemLp
          (fun ω => ∑ j : Node,
            setup.perronResidualMatrix (t + 1) i j •
              (setup.gradientTable
                  (setup.primalState (oracle.noise ω) (t + 1)) j -
                setup.gradientTable
                  (setup.primalState (oracle.noise ω) t) j))
          2 μ := by
        apply memLp_finset_sum Finset.univ
        intro j _hj
        exact ((hgradient (t + 1) j).sub (hgradient t j)).const_smul
          (setup.perronResidualMatrix (t + 1) i j)
      have hsum := hpropagated.add hforcing
      refine MemLp.ae_eq ?_ hsum
      exact Filter.Eventually.of_forall fun ω => by
        simpa only [leftMul_apply, Pi.add_apply] using
          (congrFun (setup.meanJointCoordinate_succ (oracle.noise ω) t) i).symm

/-- Expected form of source equation (6.5).  The deterministic convolution
core is `meanJointCoordinate_pathwise_energy_bound`; the remaining proof is
the finite-horizon Bochner-integral interchange against the generated run. -/
theorem meanJointCoordinate_energy_bound
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) (N : ℕ) :
    Finset.sum (Finset.range (N + 1)) (fun t =>
        ∫ ω, frobeniusNormSq (Node := Node) (E := E)
          (setup.meanJointCoordinate (oracle.noise ω) t) ∂μ) ≤
      setup.thetaInitialConstant * setup.initialGradientHeterogeneity ^ 2 +
        setup.thetaDisplacementConstant * setup.L ^ 2 *
          setup.displacementEnergy μ oracle N := by
  classical
  have htheta_int : ∀ t ∈ Finset.range (N + 1),
      Integrable (fun ω => frobeniusNormSq (Node := Node) (E := E)
        (setup.meanJointCoordinate (oracle.noise ω) t)) μ := by
    intro t _ht
    unfold frobeniusNormSq
    apply integrable_finset_sum Finset.univ
    intro i _hi
    have hmem := setup.meanJointCoordinate_coordinate_memLp μ oracle horacle t i
    exact (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).1 hmem
  have hdisp_int : ∀ t ∈ Finset.range N,
      Integrable (fun ω => frobeniusNormSq (Node := Node) (E := E)
        (setup.primalState (oracle.noise ω) (t + 1) -
          setup.primalState (oracle.noise ω) t)) μ := by
    intro t _ht
    have hnext := setup.generated_pushpull_coordinate_memLp
      μ oracle horacle (t + 1)
    have hcur := setup.generated_pushpull_coordinate_memLp μ oracle horacle t
    unfold frobeniusNormSq
    apply integrable_finset_sum Finset.univ
    intro i _hi
    have hmem := (hnext.1 i).sub (hcur.1 i)
    simpa only [Pi.sub_apply] using
      (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).1 hmem
  have hleft_sum_int : Integrable
      (fun ω => Finset.sum (Finset.range (N + 1)) (fun t =>
        frobeniusNormSq (Node := Node) (E := E)
          (setup.meanJointCoordinate (oracle.noise ω) t))) μ :=
    integrable_finset_sum _ htheta_int
  have hdisp_sum_int : Integrable
      (fun ω => Finset.sum (Finset.range N) (fun t =>
        frobeniusNormSq (Node := Node) (E := E)
          (setup.primalState (oracle.noise ω) (t + 1) -
            setup.primalState (oracle.noise ω) t))) μ :=
    integrable_finset_sum _ hdisp_int
  have hright_int : Integrable
      (fun ω => setup.thetaInitialConstant * setup.initialGradientHeterogeneity ^ 2 +
        (setup.thetaDisplacementConstant * setup.L ^ 2) *
          Finset.sum (Finset.range N) (fun t =>
            frobeniusNormSq (Node := Node) (E := E)
              (setup.primalState (oracle.noise ω) (t + 1) -
                setup.primalState (oracle.noise ω) t))) μ :=
    (integrable_const _).add
      (hdisp_sum_int.const_mul (setup.thetaDisplacementConstant * setup.L ^ 2))
  have hmono :
      (∫ ω, Finset.sum (Finset.range (N + 1)) (fun t =>
          frobeniusNormSq (Node := Node) (E := E)
            (setup.meanJointCoordinate (oracle.noise ω) t)) ∂μ) ≤
        ∫ ω, setup.thetaInitialConstant * setup.initialGradientHeterogeneity ^ 2 +
          (setup.thetaDisplacementConstant * setup.L ^ 2) *
            Finset.sum (Finset.range N) (fun t =>
              frobeniusNormSq (Node := Node) (E := E)
                (setup.primalState (oracle.noise ω) (t + 1) -
                  setup.primalState (oracle.noise ω) t)) ∂μ := by
    apply MeasureTheory.integral_mono_ae hleft_sum_int hright_int
    exact Filter.Eventually.of_forall fun ω =>
      setup.meanJointCoordinate_pathwise_energy_bound (oracle.noise ω) N
  unfold displacementEnergy
  calc
    Finset.sum (Finset.range (N + 1)) (fun t =>
        ∫ ω, frobeniusNormSq (Node := Node) (E := E)
          (setup.meanJointCoordinate (oracle.noise ω) t) ∂μ) =
      ∫ ω, Finset.sum (Finset.range (N + 1)) (fun t =>
        frobeniusNormSq (Node := Node) (E := E)
          (setup.meanJointCoordinate (oracle.noise ω) t)) ∂μ := by
        rw [MeasureTheory.integral_finset_sum]
        exact htheta_int
    _ ≤ ∫ ω, setup.thetaInitialConstant * setup.initialGradientHeterogeneity ^ 2 +
        (setup.thetaDisplacementConstant * setup.L ^ 2) *
          Finset.sum (Finset.range N) (fun t =>
            frobeniusNormSq (Node := Node) (E := E)
              (setup.primalState (oracle.noise ω) (t + 1) -
                setup.primalState (oracle.noise ω) t)) ∂μ := hmono
    _ = setup.thetaInitialConstant * setup.initialGradientHeterogeneity ^ 2 +
        (setup.thetaDisplacementConstant * setup.L ^ 2) *
          Finset.sum (Finset.range N) (fun t =>
            ∫ ω, frobeniusNormSq (Node := Node) (E := E)
              (setup.primalState (oracle.noise ω) (t + 1) -
                setup.primalState (oracle.noise ω) t) ∂μ) := by
      rw [MeasureTheory.integral_add, MeasureTheory.integral_const,
        MeasureTheory.integral_const_mul,
        MeasureTheory.integral_finset_sum]
      · simp
      · exact hdisp_int
      · exact integrable_const _
      · exact hdisp_sum_int.const_mul _
    _ = setup.thetaInitialConstant * setup.initialGradientHeterogeneity ^ 2 +
        setup.thetaDisplacementConstant * setup.L ^ 2 *
          Finset.sum (Finset.range N) (fun t =>
            ∫ ω, frobeniusNormSq (Node := Node) (E := E)
              (setup.primalState (oracle.noise ω) (t + 1) -
                setup.primalState (oracle.noise ω) t) ∂μ) := by ring

/- Source equation (6.17), before expectation.  It separates the aggregate
local-gradient table into the gradient at the arithmetic average and the node
disagreement. -/
theorem gradientTable_sum_sq_le_average_consensus
    (noise : NoisePath Node E) (t : ℕ) :
    ‖∑ i : Node, setup.gradientTable (setup.primalState noise t) i‖ ^ 2 ≤
      2 * (nodeCount (Node := Node) : ℝ) ^ 2 *
          ‖setup.averageGradient (setup.averageIterate noise t)‖ ^ 2 +
        2 * (nodeCount (Node := Node) : ℝ) * setup.L ^ 2 *
          frobeniusNormSq (Node := Node) (E := E)
            (setup.consensusState noise t) := by
  classical
  let n : ℝ := nodeCount (Node := Node)
  let avg := setup.averageIterate noise t
  let dev : Node → E := fun i =>
    setup.componentGradient i (setup.primalState noise t i) -
      setup.componentGradient i avg
  have hn_pos : 0 < n := by
    dsimp [n, nodeCount]
    exact_mod_cast Fintype.card_pos
  have hsplit :
      (∑ i : Node, setup.gradientTable (setup.primalState noise t) i) =
        (∑ i : Node, dev i) +
          ∑ i : Node, setup.componentGradient i avg := by
    simp only [gradientTable, dev]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    abel
  have hmean :
      (∑ i : Node, setup.componentGradient i avg) =
        n • setup.averageGradient avg := by
    have havg := setup.averageGradient_eq_componentGradient_average avg
    dsimp [n]
    rw [havg, smul_smul,
      mul_inv_cancel₀ (nodeCount_real_ne_zero (Node := Node)), one_smul]
  have hdev_sum :
      ‖∑ i : Node, dev i‖ ^ 2 ≤
        n * ∑ i : Node, ‖dev i‖ ^ 2 := by
    have hnorm : ‖∑ i : Node, dev i‖ ≤ ∑ i : Node, ‖dev i‖ := by
      simpa using norm_sum_le (s := (Finset.univ : Finset Node)) (f := dev)
    have hsq :
        (∑ i : Node, ‖dev i‖) ^ 2 ≤
          n * ∑ i : Node, ‖dev i‖ ^ 2 := by
      simpa [n, nodeCount] using
        (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset Node))
          (f := fun i => ‖dev i‖))
    nlinarith [norm_nonneg (∑ i : Node, dev i)]
  have hdev_point (i : Node) :
      ‖dev i‖ ^ 2 ≤ setup.L ^ 2 *
        ‖setup.primalState noise t i - avg‖ ^ 2 := by
    have h := setup.componentGradient_lipschitz_bound i
      (setup.primalState noise t i) avg
    dsimp [dev, componentGradient]
    simpa [mul_pow] using
      ((sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg setup.L_pos.le (norm_nonneg _))).2 h)
  have hdev :
      ‖∑ i : Node, dev i‖ ^ 2 ≤
        n * setup.L ^ 2 *
          frobeniusNormSq (Node := Node) (E := E)
            (setup.consensusState noise t) := by
    calc
      ‖∑ i : Node, dev i‖ ^ 2
          ≤ n * ∑ i : Node, ‖dev i‖ ^ 2 := hdev_sum
      _ ≤ n * ∑ i : Node,
            (setup.L ^ 2 * ‖setup.primalState noise t i - avg‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun i _hi => hdev_point i) hn_pos.le
      _ = n * setup.L ^ 2 *
          frobeniusNormSq (Node := Node) (E := E)
            (setup.consensusState noise t) := by
        rw [← Finset.mul_sum]
        simp only [frobeniusNormSq, consensusState_eq_state_sub_average, avg]
        ring
  rw [hsplit, hmean]
  have hadd :
      ‖(∑ i : Node, dev i) + n • setup.averageGradient avg‖ ≤
        ‖∑ i : Node, dev i‖ +
          ‖n • setup.averageGradient avg‖ := norm_add_le _ _
  have hmean_norm :
      ‖n • setup.averageGradient avg‖ =
        n * ‖setup.averageGradient avg‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hn_pos]
  rw [hmean_norm] at hadd
  have hsquare :
      ‖(∑ i : Node, dev i) + n • setup.averageGradient avg‖ ^ 2 ≤
        2 * ‖∑ i : Node, dev i‖ ^ 2 +
          2 * n ^ 2 * ‖setup.averageGradient avg‖ ^ 2 := by
    have hadd_sq := (sq_le_sq₀ (norm_nonneg _)
      (add_nonneg (norm_nonneg _) (mul_nonneg hn_pos.le (norm_nonneg _)))).2 hadd
    nlinarith [norm_nonneg (∑ i : Node, dev i),
      norm_nonneg (setup.averageGradient avg),
      sq_nonneg (‖∑ i : Node, dev i‖ -
        n * ‖setup.averageGradient avg‖)]
  calc
    _ ≤ 2 * ‖∑ i : Node, dev i‖ ^ 2 +
        2 * n ^ 2 * ‖setup.averageGradient avg‖ ^ 2 := hsquare
    _ ≤ 2 * (n * setup.L ^ 2 *
          frobeniusNormSq (Node := Node) (E := E)
            (setup.consensusState noise t)) +
        2 * n ^ 2 * ‖setup.averageGradient avg‖ ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hdev (by norm_num)) le_rfl
    _ = _ := by
      dsimp [n, avg]
      ring

/- Reindex a finite horizon of `K` complete blocks into block and phase
coordinates. -/
theorem sum_range_mul_eq_sum_blocks
    {M : Type*} [AddCommMonoid M] (f : ℕ → M) (K p : ℕ) :
    ∑ t ∈ Finset.range (K * p), f t =
      ∑ k ∈ Finset.range K, ∑ r ∈ Finset.range p, f (k * p + r) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

/- The gradient of the finite-average objective inherits the common
Lipschitz constant of the component gradients. -/
theorem averageGradient_lipschitz_bound (x y : E) :
    ‖setup.averageGradient x - setup.averageGradient y‖ ≤
      setup.L * ‖x - y‖ := by
  have hn : 0 < (nodeCount (Node := Node) : ℝ) := by
    exact_mod_cast nodeCount_pos (Node := Node)
  rw [setup.averageGradient_eq_componentGradient_average,
    setup.averageGradient_eq_componentGradient_average]
  rw [← smul_sub, ← Finset.sum_sub_distrib]
  calc
    ‖((nodeCount (Node := Node) : ℝ)⁻¹ •
        ∑ i : Node, (setup.componentGradient i x -
          setup.componentGradient i y))‖ =
        (nodeCount (Node := Node) : ℝ)⁻¹ *
          ‖∑ i : Node, (setup.componentGradient i x -
            setup.componentGradient i y)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
    _ ≤ (nodeCount (Node := Node) : ℝ)⁻¹ *
          ∑ i : Node, ‖setup.componentGradient i x -
            setup.componentGradient i y‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (nodeCount (Node := Node) : ℝ)⁻¹ *
          ∑ _i : Node, setup.L * ‖x - y‖ := by
      gcongr with i
      exact setup.componentGradient_lipschitz_bound i x y
    _ = setup.L * ‖x - y‖ := by
      simp [nodeCount]

/- The paper's arithmetic-average iterate is in `L²`, and the globally
Lipschitz average gradient transports that regularity directly.  This is the
coarse source-facing regularity interface used by all stationarity
expectations; it deliberately does not expand the average gradient into its
component gradients. -/
theorem averageGradient_randomAverageIterate_memLp_two
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) :
    ∀ t : ℕ, MemLp
      (fun ω => setup.averageGradient
        (setup.randomAverageIterate oracle t ω)) 2 μ := by
  classical
  intro t
  have hsum : MemLp
      (fun ω => ∑ i : Node, setup.primalState (oracle.noise ω) t i) 2 μ := by
    apply memLp_finset_sum Finset.univ
    intro i _hi
    exact (setup.generated_pushpull_coordinate_memLp μ oracle horacle t).1 i
  have havg : MemLp (fun ω => setup.randomAverageIterate oracle t ω) 2 μ := by
    have hscaled := hsum.const_smul
      ((nodeCount (Node := Node) : ℝ)⁻¹)
    simpa only [randomAverageIterate,
      setup.averageIterate_eq_arithmeticAverage] using hscaled
  have hlipschitz :
      LipschitzWith (Real.toNNReal setup.L) setup.averageGradient := by
    apply lipschitzWith_of_norm_sub_le_mul
    intro x y
    simpa [dist_eq_norm] using setup.averageGradient_lipschitz_bound x y
  exact memLp_two_comp_lipschitz setup.averageGradient
    (Real.toNNReal setup.L) hlipschitz havg

/-- Derived well-definedness of one stationarity expectation. This is a bridge
from the source assumptions to the Lean integral domain, not a source-facing
theorem-head assumption. -/
theorem expectedGradientNormSq_wellDefined
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) (t : ℕ) :
    setup.expectedGradientNormSqWellDefined μ oracle t := by
  unfold expectedGradientNormSqWellDefined
  have hmem := setup.averageGradient_randomAverageIterate_memLp_two
    μ oracle horacle t
  exact (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).1 hmem

/-- Derived well-definedness of the complete stationarity average. -/
theorem stationarityAverage_wellDefined
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) (T : ℕ) :
    setup.stationarityAverageWellDefined μ oracle T := by
  intro t _ht
  exact setup.expectedGradientNormSq_wellDefined μ oracle horacle t

/- Jensen's finite-average bound for the arithmetic average of two generated
distributed states. -/
theorem averageIterate_sub_sq_le
    (noise : NoisePath Node E) (s t : ℕ) :
    ‖setup.averageIterate noise t - setup.averageIterate noise s‖ ^ 2 ≤
      (nodeCount (Node := Node) : ℝ)⁻¹ *
        frobeniusNormSq (Node := Node) (E := E)
          (setup.primalState noise t - setup.primalState noise s) := by
  have h := norm_sq_inv_card_smul_sum_le_inv_card_mul_sum_norm_sq
    (Finset.univ : Finset Node)
    (fun i : Node => setup.primalState noise t i - setup.primalState noise s i)
    (by simp [Fintype.card_pos])
  simpa only [averageIterate, arithmeticAverage, Finset.card_univ,
    nodeCount, frobeniusNormSq, Pi.sub_apply, Finset.sum_sub_distrib,
    smul_sub] using h

/- A finite telescoping path has squared Frobenius displacement at most its
length times the sum of one-step squared displacements. -/
theorem state_displacement_telescope
    (noise : NoisePath Node E) (s r : ℕ) :
    frobeniusNormSq (Node := Node) (E := E)
        (setup.primalState noise (s + r) - setup.primalState noise s) ≤
      (r : ℝ) * ∑ j ∈ Finset.range r,
        frobeniusNormSq (Node := Node) (E := E)
          (setup.primalState noise (s + j + 1) -
            setup.primalState noise (s + j)) := by
  classical
  have hcoord (i : Node) :
      setup.primalState noise (s + r) i - setup.primalState noise s i =
        ∑ j ∈ Finset.range r,
          (setup.primalState noise (s + j + 1) i -
            setup.primalState noise (s + j) i) := by
    simpa [Nat.add_assoc] using
      (Finset.sum_range_sub (fun j => setup.primalState noise (s + j) i) r).symm
  have hpoint (i : Node) :
      ‖setup.primalState noise (s + r) i - setup.primalState noise s i‖ ^ 2 ≤
        (r : ℝ) * ∑ j ∈ Finset.range r,
          ‖setup.primalState noise (s + j + 1) i -
            setup.primalState noise (s + j) i‖ ^ 2 := by
    rw [hcoord]
    have hnorm :
        ‖∑ j ∈ Finset.range r,
            (setup.primalState noise (s + j + 1) i -
              setup.primalState noise (s + j) i)‖ ≤
          ∑ j ∈ Finset.range r,
            ‖setup.primalState noise (s + j + 1) i -
              setup.primalState noise (s + j) i‖ :=
      norm_sum_le _ _
    have hsquares := sq_sum_le_card_mul_sum_sq
      (s := Finset.range r)
      (f := fun j => ‖setup.primalState noise (s + j + 1) i -
        setup.primalState noise (s + j) i‖)
    simp only [Finset.card_range] at hsquares
    nlinarith [norm_nonneg (∑ j ∈ Finset.range r,
      (setup.primalState noise (s + j + 1) i -
        setup.primalState noise (s + j) i))]
  unfold frobeniusNormSq
  simp only [Pi.sub_apply]
  calc
    ∑ i : Node, ‖setup.primalState noise (s + r) i -
        setup.primalState noise s i‖ ^ 2 ≤
      ∑ i : Node, (r : ℝ) * ∑ j ∈ Finset.range r,
        ‖setup.primalState noise (s + j + 1) i -
          setup.primalState noise (s + j) i‖ ^ 2 :=
      Finset.sum_le_sum fun i _hi => hpoint i
    _ = (r : ℝ) * ∑ j ∈ Finset.range r, ∑ i : Node,
        ‖setup.primalState noise (s + j + 1) i -
          setup.primalState noise (s + j) i‖ ^ 2 := by
      rw [Finset.sum_comm, Finset.mul_sum]
    _ = _ := by rfl

/- The pathwise one-block form of equation (6.16). -/
theorem block_averageGradient_energy_bound
    (noise : NoisePath Node E) (k : ℕ) :
    ∑ r ∈ Finset.range setup.period,
        ‖setup.averageGradient
          (setup.averageIterate noise (setup.blockStart k + r))‖ ^ 2 ≤
      2 * (setup.period : ℝ) *
          ‖setup.blockAverageGradient noise k‖ ^ 2 +
        (2 * setup.L ^ 2 * (setup.period : ℝ) ^ 2 /
          (nodeCount (Node := Node) : ℝ)) *
          ∑ j ∈ Finset.range setup.period,
            frobeniusNormSq (Node := Node) (E := E)
              (setup.primalState noise (setup.blockStart k + j + 1) -
                setup.primalState noise (setup.blockStart k + j)) := by
  classical
  let s := setup.blockStart k
  let D := ∑ j ∈ Finset.range setup.period,
    frobeniusNormSq (Node := Node) (E := E)
      (setup.primalState noise (s + j + 1) - setup.primalState noise (s + j))
  have hn : 0 < (nodeCount (Node := Node) : ℝ) := by
    exact_mod_cast nodeCount_pos (Node := Node)
  have hD : 0 ≤ D := by
    dsimp [D]
    apply Finset.sum_nonneg
    intro j _hj
    unfold frobeniusNormSq
    exact Finset.sum_nonneg fun i _hi => sq_nonneg _
  have havg (r : ℕ) (hr : r ∈ Finset.range setup.period) :
      ‖setup.averageIterate noise (s + r) - setup.averageIterate noise s‖ ^ 2 ≤
        ((setup.period : ℝ) / (nodeCount (Node := Node) : ℝ)) * D := by
    have hrle : r ≤ setup.period := Nat.le_of_lt (Finset.mem_range.mp hr)
    have hsub :
        ∑ j ∈ Finset.range r,
            frobeniusNormSq (Node := Node) (E := E)
              (setup.primalState noise (s + j + 1) -
                setup.primalState noise (s + j)) ≤ D := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hrle)
      intro j _hj _hjr
      unfold frobeniusNormSq
      positivity
    have htelescope := setup.state_displacement_telescope noise s r
    have hstate :
        frobeniusNormSq (Node := Node) (E := E)
            (setup.primalState noise (s + r) - setup.primalState noise s) ≤
          (setup.period : ℝ) * D := by
      calc
        _ ≤ (r : ℝ) * ∑ j ∈ Finset.range r,
            frobeniusNormSq (Node := Node) (E := E)
              (setup.primalState noise (s + j + 1) -
                setup.primalState noise (s + j)) := htelescope
        _ ≤ (setup.period : ℝ) * D := by
          calc
            _ ≤ (r : ℝ) * D :=
              mul_le_mul_of_nonneg_left hsub (by positivity)
            _ ≤ (setup.period : ℝ) * D :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast hrle) hD
    calc
      _ ≤ (nodeCount (Node := Node) : ℝ)⁻¹ *
          frobeniusNormSq (Node := Node) (E := E)
            (setup.primalState noise (s + r) -
              setup.primalState noise s) :=
        setup.averageIterate_sub_sq_le noise s (s + r)
      _ ≤ (nodeCount (Node := Node) : ℝ)⁻¹ *
          ((setup.period : ℝ) * D) :=
        mul_le_mul_of_nonneg_left hstate (inv_nonneg.mpr hn.le)
      _ = ((setup.period : ℝ) /
          (nodeCount (Node := Node) : ℝ)) * D := by
        rw [div_eq_mul_inv]
        ring
  have hpoint (r : ℕ) (hr : r ∈ Finset.range setup.period) :
      ‖setup.averageGradient (setup.averageIterate noise (s + r))‖ ^ 2 ≤
        2 * ‖setup.averageGradient (setup.averageIterate noise s)‖ ^ 2 +
          (2 * setup.L ^ 2 * (setup.period : ℝ) /
            (nodeCount (Node := Node) : ℝ)) * D := by
    let gt := setup.averageGradient (setup.averageIterate noise (s + r))
    let gs := setup.averageGradient (setup.averageIterate noise s)
    have hlip := setup.averageGradient_lipschitz_bound
      (setup.averageIterate noise (s + r)) (setup.averageIterate noise s)
    have hdiff : ‖gt - gs‖ ^ 2 ≤
        setup.L ^ 2 *
          ‖setup.averageIterate noise (s + r) - setup.averageIterate noise s‖ ^ 2 := by
      dsimp [gt, gs]
      simpa [mul_pow] using
        ((sq_le_sq₀ (norm_nonneg _)
          (mul_nonneg setup.L_pos.le (norm_nonneg _))).2 hlip)
    have hdiff' : ‖gt - gs‖ ^ 2 ≤
        setup.L ^ 2 *
          (((setup.period : ℝ) / (nodeCount (Node := Node) : ℝ)) * D) :=
      hdiff.trans (mul_le_mul_of_nonneg_left (havg r hr) (sq_nonneg setup.L))
    have htri : ‖gt‖ ≤ ‖gt - gs‖ + ‖gs‖ := by
      have := norm_add_le (gt - gs) gs
      simpa only [sub_add_cancel] using this
    have hsquare : ‖gt‖ ^ 2 ≤ 2 * ‖gt - gs‖ ^ 2 + 2 * ‖gs‖ ^ 2 := by
      nlinarith [norm_nonneg gt, norm_nonneg (gt - gs), norm_nonneg gs,
        sq_nonneg (‖gt - gs‖ - ‖gs‖)]
    calc
      _ ≤ 2 * ‖gt - gs‖ ^ 2 + 2 * ‖gs‖ ^ 2 := hsquare
      _ ≤ 2 * (setup.L ^ 2 *
            (((setup.period : ℝ) / (nodeCount (Node := Node) : ℝ)) * D)) +
          2 * ‖gs‖ ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hdiff' (by norm_num)) le_rfl
      _ = _ := by
        dsimp [gt, gs]
        ring
  calc
    ∑ r ∈ Finset.range setup.period,
        ‖setup.averageGradient
          (setup.averageIterate noise (setup.blockStart k + r))‖ ^ 2 =
      ∑ r ∈ Finset.range setup.period,
        ‖setup.averageGradient (setup.averageIterate noise (s + r))‖ ^ 2 := by
      rfl
    _ ≤ ∑ _r ∈ Finset.range setup.period,
        (2 * ‖setup.averageGradient (setup.averageIterate noise s)‖ ^ 2 +
          (2 * setup.L ^ 2 * (setup.period : ℝ) /
            (nodeCount (Node := Node) : ℝ)) * D) :=
      Finset.sum_le_sum fun r hr => hpoint r hr
    _ = 2 * (setup.period : ℝ) * ‖setup.blockAverageGradient noise k‖ ^ 2 +
        (2 * setup.L ^ 2 * (setup.period : ℝ) ^ 2 /
          (nodeCount (Node := Node) : ℝ)) * D := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      dsimp [blockAverageGradient, s]
      ring
    _ = _ := by rfl

/- The pathwise complete-horizon form of equation (6.16). -/
theorem allTimeAverageGradient_pathwise_energy_bound
    (noise : NoisePath Node E) (K : ℕ) :
    let N := setup.completeBlockHorizon K
    ∑ t ∈ Finset.range N,
        ‖setup.averageGradient (setup.averageIterate noise t)‖ ^ 2 ≤
      2 * (setup.period : ℝ) *
          ∑ k ∈ Finset.range K, ‖setup.blockAverageGradient noise k‖ ^ 2 +
        (2 * setup.L ^ 2 * (setup.period : ℝ) ^ 2 /
          (nodeCount (Node := Node) : ℝ)) *
          ∑ t ∈ Finset.range N,
            frobeniusNormSq (Node := Node) (E := E)
              (setup.primalState noise (t + 1) - setup.primalState noise t) := by
  classical
  dsimp only
  rw [completeBlockHorizon,
    sum_range_mul_eq_sum_blocks
      (fun t => ‖setup.averageGradient (setup.averageIterate noise t)‖ ^ 2)]
  have hblocks := Finset.sum_le_sum fun k (_hk : k ∈ Finset.range K) =>
    setup.block_averageGradient_energy_bound noise k
  calc
    ∑ k ∈ Finset.range K, ∑ r ∈ Finset.range setup.period,
        ‖setup.averageGradient
          (setup.averageIterate noise (k * setup.period + r))‖ ^ 2 ≤
      ∑ k ∈ Finset.range K,
        (2 * (setup.period : ℝ) * ‖setup.blockAverageGradient noise k‖ ^ 2 +
          (2 * setup.L ^ 2 * (setup.period : ℝ) ^ 2 /
            (nodeCount (Node := Node) : ℝ)) *
            ∑ j ∈ Finset.range setup.period,
              frobeniusNormSq (Node := Node) (E := E)
                (setup.primalState noise (setup.blockStart k + j + 1) -
                  setup.primalState noise (setup.blockStart k + j))) := hblocks
    _ = 2 * (setup.period : ℝ) *
          ∑ k ∈ Finset.range K, ‖setup.blockAverageGradient noise k‖ ^ 2 +
        (2 * setup.L ^ 2 * (setup.period : ℝ) ^ 2 /
          (nodeCount (Node := Node) : ℝ)) *
          ∑ k ∈ Finset.range K, ∑ j ∈ Finset.range setup.period,
            frobeniusNormSq (Node := Node) (E := E)
              (setup.primalState noise (k * setup.period + j + 1) -
                setup.primalState noise (k * setup.period + j)) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, blockStart]
    _ = _ := by
      rw [← sum_range_mul_eq_sum_blocks
        (fun t => frobeniusNormSq (Node := Node) (E := E)
          (setup.primalState noise (t + 1) - setup.primalState noise t))]

/- Source equation (6.16): blockwise smoothness controls all-time gradients by
the block-start gradients and the primal displacement energy.  This exact
source-granularity declaration isolates the remaining finite-block reindexing
and telescoping argument from the tracker assembly. -/
theorem allTimeAverageGradient_energy_bound
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E) (K : ℕ)
    (_horacle : setup.StochasticOracleAssumptions μ oracle) :
    let N := setup.completeBlockHorizon K
    Finset.sum (Finset.range N) (fun t =>
        ∫ ω, ‖setup.averageGradient
          (setup.averageIterate (oracle.noise ω) t)‖ ^ 2 ∂μ) ≤
      2 * (setup.period : ℝ) * setup.blockGradientEnergy μ oracle K +
        (2 * setup.L ^ 2 * (setup.period : ℝ) ^ 2 /
          (nodeCount (Node := Node) : ℝ)) *
            setup.displacementEnergy μ oracle N := by
  classical
  dsimp only
  let N := setup.completeBlockHorizon K
  let n : ℝ := nodeCount (Node := Node)
  have hgenerated (t : ℕ) :=
    setup.generated_pushpull_coordinate_memLp μ oracle _horacle t
  have havgGrad (t : ℕ) : MemLp (fun ω =>
      setup.averageGradient (setup.averageIterate (oracle.noise ω) t)) 2 μ := by
    simpa only [randomAverageIterate] using
      setup.averageGradient_randomAverageIterate_memLp_two
        μ oracle _horacle t
  have hgrad_int (t : ℕ) : Integrable (fun ω =>
      ‖setup.averageGradient (setup.averageIterate (oracle.noise ω) t)‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (havgGrad t).aestronglyMeasurable).1
      (havgGrad t)
  have hdisp_int (t : ℕ) : Integrable (fun ω =>
      frobeniusNormSq (Node := Node) (E := E)
        (setup.primalState (oracle.noise ω) (t + 1) -
          setup.primalState (oracle.noise ω) t)) μ := by
    unfold frobeniusNormSq
    apply integrable_finset_sum Finset.univ
    intro i _hi
    have hmem := ((hgenerated (t + 1)).1 i).sub ((hgenerated t).1 i)
    exact (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).1 hmem
  have hgrad_sum := integrable_finset_sum (Finset.range N)
    (fun t _ht => hgrad_int t)
  have hblock_sum := integrable_finset_sum (Finset.range K)
    (fun k _hk => hgrad_int (setup.blockStart k))
  have hdisp_sum := integrable_finset_sum (Finset.range N)
    (fun t _ht => hdisp_int t)
  have hmono :
      (∫ ω, Finset.sum (Finset.range N) (fun t =>
          ‖setup.averageGradient
            (setup.averageIterate (oracle.noise ω) t)‖ ^ 2) ∂μ) ≤
        ∫ ω,
          2 * (setup.period : ℝ) *
            Finset.sum (Finset.range K) (fun k =>
              ‖setup.blockAverageGradient (oracle.noise ω) k‖ ^ 2) +
          (2 * setup.L ^ 2 * (setup.period : ℝ) ^ 2 / n) *
            Finset.sum (Finset.range N) (fun t =>
              frobeniusNormSq (Node := Node) (E := E)
                (setup.primalState (oracle.noise ω) (t + 1) -
                  setup.primalState (oracle.noise ω) t)) ∂μ := by
    apply MeasureTheory.integral_mono_ae hgrad_sum
      ((hblock_sum.const_mul (2 * (setup.period : ℝ))).add
        (hdisp_sum.const_mul
          (2 * setup.L ^ 2 * (setup.period : ℝ) ^ 2 / n)))
    exact Filter.Eventually.of_forall fun ω => by
      simpa [N, n] using
        setup.allTimeAverageGradient_pathwise_energy_bound (oracle.noise ω) K
  unfold blockGradientEnergy displacementEnergy
  calc
    Finset.sum (Finset.range N) (fun t =>
        ∫ ω, ‖setup.averageGradient
          (setup.averageIterate (oracle.noise ω) t)‖ ^ 2 ∂μ) =
      ∫ ω, Finset.sum (Finset.range N) (fun t =>
        ‖setup.averageGradient
          (setup.averageIterate (oracle.noise ω) t)‖ ^ 2) ∂μ := by
      rw [MeasureTheory.integral_finset_sum]
      exact fun t _ht => hgrad_int t
    _ ≤ _ := hmono
    _ = 2 * (setup.period : ℝ) *
          Finset.sum (Finset.range K) (fun k =>
            ∫ ω, ‖setup.blockAverageGradient (oracle.noise ω) k‖ ^ 2 ∂μ) +
        (2 * setup.L ^ 2 * (setup.period : ℝ) ^ 2 / n) *
          Finset.sum (Finset.range N) (fun t =>
            ∫ ω, frobeniusNormSq (Node := Node) (E := E)
              (setup.primalState (oracle.noise ω) (t + 1) -
                setup.primalState (oracle.noise ω) t) ∂μ) := by
      rw [MeasureTheory.integral_add,
        MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul,
        MeasureTheory.integral_finset_sum,
        MeasureTheory.integral_finset_sum]
      all_goals
        try intro i _hi
        first
        | exact hblock_sum.const_mul _
        | exact hdisp_sum.const_mul _
        | exact hgrad_int (setup.blockStart i)
        | exact hdisp_int i
    _ = _ := by rfl

/- A finite distributed state whose coordinates are in `L²` has integrable
Frobenius energy. -/
theorem frobeniusNormSq_integrable_of_coordinate_memLp
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure Ω} {X : Ω → State Node E}
    (hX : ∀ i : Node, MemLp (fun ω => X ω i) 2 μ) :
    Integrable (fun ω => frobeniusNormSq (Node := Node) (E := E) (X ω)) μ := by
  unfold frobeniusNormSq
  apply integrable_finset_sum Finset.univ
  intro i _hi
  exact (memLp_two_iff_integrable_sq_norm (hX i).aestronglyMeasurable).1 (hX i)

/- The squared norm of a finite sum of `L²` vectors is integrable. -/
theorem normSq_finsetSum_integrable_of_memLp
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure Ω} {X : Node → Ω → E}
    (hX : ∀ i : Node, MemLp (X i) 2 μ) :
    Integrable (fun ω => ‖∑ i : Node, X i ω‖ ^ 2) μ := by
  have hsum : MemLp (fun ω => ∑ i : Node, X i ω) 2 μ := by
    apply memLp_finset_sum Finset.univ
    intro i _hi
    exact hX i
  exact (memLp_two_iff_integrable_sq_norm hsum.aestronglyMeasurable).1 hsum

/- A small Bochner-integration normalization lemma.  Keeping this generic
prevents the large tracker expressions from being repeatedly unfolded while
the three source energies are transported through expectation. -/
theorem integral_linearCombination_three_finsetSums
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (N : ℕ)
    (f g h : ℕ → Ω → ℝ) (a b c : ℝ)
    (hf : ∀ t ∈ Finset.range N, Integrable (f t) μ)
    (hg : ∀ t ∈ Finset.range N, Integrable (g t) μ)
    (hh : ∀ t ∈ Finset.range N, Integrable (h t) μ) :
    (∫ ω,
        a * Finset.sum (Finset.range N) (fun t => f t ω) +
        b * Finset.sum (Finset.range N) (fun t => g t ω) +
        c * Finset.sum (Finset.range N) (fun t => h t ω) ∂μ) =
      a * Finset.sum (Finset.range N) (fun t => ∫ ω, f t ω ∂μ) +
      b * Finset.sum (Finset.range N) (fun t => ∫ ω, g t ω ∂μ) +
      c * Finset.sum (Finset.range N) (fun t => ∫ ω, h t ω ∂μ) := by
  have hfs := integrable_finset_sum (Finset.range N) hf
  have hgs := integrable_finset_sum (Finset.range N) hg
  have hhs := integrable_finset_sum (Finset.range N) hh
  rw [MeasureTheory.integral_add, MeasureTheory.integral_add,
      MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul,
      MeasureTheory.integral_finset_sum,
      MeasureTheory.integral_finset_sum,
      MeasureTheory.integral_finset_sum]
  all_goals
    first
    | exact hfs.const_mul _
    | exact hgs.const_mul _
    | exact hhs.const_mul _
    | exact (hfs.const_mul _).add (hgs.const_mul _)
    | exact (hgs.const_mul _).add (hhs.const_mul _)
    | assumption

/- Expectation lift of the already-proved pathwise tracker decomposition.  No
network or stochastic estimate is used here; this theorem only supplies the
finite-horizon `L²`/Bochner transport needed between (6.3) and the scalar
coefficient assembly. -/
set_option maxHeartbeats 800000 in
theorem trackerState_joint_expected_energy_bounds
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) (N : ℕ) :
    let Theta := Finset.sum (Finset.range N) (fun t =>
      ∫ ω, frobeniusNormSq (Node := Node) (E := E)
        (setup.meanJointCoordinate (oracle.noise ω) t) ∂μ)
    let Grad := Finset.sum (Finset.range N) (fun t =>
      ∫ ω, ‖∑ j : Node,
        setup.gradientTable (setup.primalState (oracle.noise ω) t) j‖ ^ 2 ∂μ)
    let J := Finset.sum (Finset.range N) (fun t =>
      ∫ ω, frobeniusNormSq (Node := Node) (E := E)
        (setup.noiseJointCoordinate (oracle.noise ω) t) ∂μ)
    let P := Finset.sum (Finset.range N) (fun t =>
      ∫ ω, frobeniusNormSq (Node := Node) (E := E)
        (consensusError (Node := Node) (E := E)
          (setup.trackerState (oracle.noise ω) t)) ∂μ)
    let Y := Finset.sum (Finset.range N) (fun t =>
      ∫ ω, frobeniusNormSq (Node := Node) (E := E)
        (setup.trackerState (oracle.noise ω) t) ∂μ)
    P ≤ 3 * Theta + 3 * setup.projectedPerronRightNormMax ^ 2 * Grad + 3 * J ∧
      2 * Y ≤ 6 * Theta + 6 * setup.perronRightNormMax ^ 2 * Grad + 6 * J := by
  classical
  dsimp only
  let K : NNReal := ⟨setup.L, setup.L_pos.le⟩
  have hgradient_lipschitz (i : Node) :
      LipschitzWith K (setup.componentGradient i) := by
    rw [lipschitzWith_iff_norm_sub_le]
    intro x y
    simpa [K, componentGradient] using
      setup.componentGradient_lipschitz_bound i x y
  have hgenerated (t : ℕ) :=
    setup.generated_pushpull_coordinate_memLp μ oracle horacle t
  have hgrad (t : ℕ) (i : Node) :
      MemLp (fun ω => setup.gradientTable
        (setup.primalState (oracle.noise ω) t) i) 2 μ := by
    simpa [gradientTable] using
      memLp_two_comp_lipschitz (setup.componentGradient i) K
        (hgradient_lipschitz i) ((hgenerated t).1 i)
  have htheta (t : ℕ) (i : Node) :
      MemLp (fun ω => setup.meanJointCoordinate (oracle.noise ω) t i) 2 μ :=
    setup.meanJointCoordinate_coordinate_memLp μ oracle horacle t i
  have hgradSum (t : ℕ) :
      MemLp (fun ω => ∑ j : Node,
        setup.gradientTable (setup.primalState (oracle.noise ω) t) j) 2 μ := by
    apply memLp_finset_sum Finset.univ
    intro j _hj
    exact hgrad t j
  have hjoint (t : ℕ) (i : Node) :
      MemLp (fun ω => setup.noiseJointCoordinate (oracle.noise ω) t i) 2 μ := by
    have hrank := (hgradSum t).const_smul (setup.perronRight t i)
    have hcandidate := ((hgenerated t).2 i).sub ((htheta t i).add hrank)
    refine MemLp.ae_eq ?_ hcandidate
    exact Filter.Eventually.of_forall fun ω => by
      have hdecomp := congrFun
        (setup.trackerState_eq_joint_decomposition_source (oracle.noise ω) t) i
      simp only [Pi.add_apply] at hdecomp
      change setup.trackerState (oracle.noise ω) t i -
          (setup.meanJointCoordinate (oracle.noise ω) t i +
            setup.perronRight t i • ∑ j : Node,
              setup.gradientTable (setup.primalState (oracle.noise ω) t) j) =
        setup.noiseJointCoordinate (oracle.noise ω) t i
      rw [hdecomp]
      abel
  have hprojected (t : ℕ) (i : Node) :
      MemLp (fun ω => consensusError (Node := Node) (E := E)
        (setup.trackerState (oracle.noise ω) t) i) 2 μ := by
    have havg : MemLp (fun ω =>
        ((nodeCount (Node := Node) : ℝ)⁻¹) •
          ∑ j : Node, setup.trackerState (oracle.noise ω) t j) 2 μ := by
      have hsum : MemLp (fun ω =>
          ∑ j : Node, setup.trackerState (oracle.noise ω) t j) 2 μ := by
        apply memLp_finset_sum Finset.univ
        intro j _hj
        exact (hgenerated t).2 j
      exact hsum.const_smul _
    simpa [consensusError, arithmeticAverage] using ((hgenerated t).2 i).sub havg
  have hTheta_int (t : ℕ) : Integrable (fun ω =>
      frobeniusNormSq (Node := Node) (E := E)
        (setup.meanJointCoordinate (oracle.noise ω) t)) μ :=
    frobeniusNormSq_integrable_of_coordinate_memLp (fun i => htheta t i)
  have hGrad_int (t : ℕ) : Integrable (fun ω =>
      ‖∑ j : Node,
        setup.gradientTable (setup.primalState (oracle.noise ω) t) j‖ ^ 2) μ :=
    normSq_finsetSum_integrable_of_memLp (fun i => hgrad t i)
  have hJ_int (t : ℕ) : Integrable (fun ω =>
      frobeniusNormSq (Node := Node) (E := E)
        (setup.noiseJointCoordinate (oracle.noise ω) t)) μ :=
    frobeniusNormSq_integrable_of_coordinate_memLp (fun i => hjoint t i)
  have hP_int (t : ℕ) : Integrable (fun ω =>
      frobeniusNormSq (Node := Node) (E := E)
        (consensusError (Node := Node) (E := E)
          (setup.trackerState (oracle.noise ω) t))) μ :=
    frobeniusNormSq_integrable_of_coordinate_memLp (fun i => hprojected t i)
  have hY_int (t : ℕ) : Integrable (fun ω =>
      frobeniusNormSq (Node := Node) (E := E)
        (setup.trackerState (oracle.noise ω) t)) μ :=
    frobeniusNormSq_integrable_of_coordinate_memLp (fun i => (hgenerated t).2 i)
  have hTheta_sum := integrable_finset_sum (Finset.range N)
    (fun t _ht => hTheta_int t)
  have hGrad_sum := integrable_finset_sum (Finset.range N)
    (fun t _ht => hGrad_int t)
  have hJ_sum := integrable_finset_sum (Finset.range N)
    (fun t _ht => hJ_int t)
  have hP_sum := integrable_finset_sum (Finset.range N)
    (fun t _ht => hP_int t)
  have hY_sum := integrable_finset_sum (Finset.range N)
    (fun t _ht => hY_int t)
  have hpath (ω : Ω) :=
    setup.trackerState_joint_pathwise_energy_bounds (oracle.noise ω) N
  have hrhsP_int : Integrable (fun ω =>
      3 * Finset.sum (Finset.range N) (fun t =>
        frobeniusNormSq (Node := Node) (E := E)
          (setup.meanJointCoordinate (oracle.noise ω) t)) +
      3 * setup.projectedPerronRightNormMax ^ 2 *
        Finset.sum (Finset.range N) (fun t =>
          ‖∑ j : Node,
            setup.gradientTable (setup.primalState (oracle.noise ω) t) j‖ ^ 2) +
      3 * Finset.sum (Finset.range N) (fun t =>
        frobeniusNormSq (Node := Node) (E := E)
          (setup.noiseJointCoordinate (oracle.noise ω) t))) μ :=
    ((hTheta_sum.const_mul 3).add
      (hGrad_sum.const_mul (3 * setup.projectedPerronRightNormMax ^ 2))).add
        (hJ_sum.const_mul 3)
  have hrhsY_int : Integrable (fun ω =>
      6 * Finset.sum (Finset.range N) (fun t =>
        frobeniusNormSq (Node := Node) (E := E)
          (setup.meanJointCoordinate (oracle.noise ω) t)) +
      6 * setup.perronRightNormMax ^ 2 *
        Finset.sum (Finset.range N) (fun t =>
          ‖∑ j : Node,
            setup.gradientTable (setup.primalState (oracle.noise ω) t) j‖ ^ 2) +
      6 * Finset.sum (Finset.range N) (fun t =>
        frobeniusNormSq (Node := Node) (E := E)
          (setup.noiseJointCoordinate (oracle.noise ω) t))) μ :=
    ((hTheta_sum.const_mul 6).add
      (hGrad_sum.const_mul (6 * setup.perronRightNormMax ^ 2))).add
        (hJ_sum.const_mul 6)
  have hmonoP :
      (∫ ω, Finset.sum (Finset.range N) (fun t =>
          frobeniusNormSq (Node := Node) (E := E)
            (consensusError (Node := Node) (E := E)
              (setup.trackerState (oracle.noise ω) t))) ∂μ) ≤
        ∫ ω,
          3 * Finset.sum (Finset.range N) (fun t =>
            frobeniusNormSq (Node := Node) (E := E)
              (setup.meanJointCoordinate (oracle.noise ω) t)) +
          3 * setup.projectedPerronRightNormMax ^ 2 *
            Finset.sum (Finset.range N) (fun t =>
              ‖∑ j : Node,
                setup.gradientTable (setup.primalState (oracle.noise ω) t) j‖ ^ 2) +
          3 * Finset.sum (Finset.range N) (fun t =>
            frobeniusNormSq (Node := Node) (E := E)
              (setup.noiseJointCoordinate (oracle.noise ω) t)) ∂μ := by
    apply MeasureTheory.integral_mono_ae hP_sum hrhsP_int
    exact Filter.Eventually.of_forall fun ω => (hpath ω).1
  have hmonoY :
      (∫ ω, 2 * Finset.sum (Finset.range N) (fun t =>
          frobeniusNormSq (Node := Node) (E := E)
            (setup.trackerState (oracle.noise ω) t)) ∂μ) ≤
        ∫ ω,
          6 * Finset.sum (Finset.range N) (fun t =>
            frobeniusNormSq (Node := Node) (E := E)
              (setup.meanJointCoordinate (oracle.noise ω) t)) +
          6 * setup.perronRightNormMax ^ 2 *
            Finset.sum (Finset.range N) (fun t =>
              ‖∑ j : Node,
                setup.gradientTable (setup.primalState (oracle.noise ω) t) j‖ ^ 2) +
          6 * Finset.sum (Finset.range N) (fun t =>
            frobeniusNormSq (Node := Node) (E := E)
              (setup.noiseJointCoordinate (oracle.noise ω) t)) ∂μ := by
    apply MeasureTheory.integral_mono_ae (hY_sum.const_mul 2) hrhsY_int
    exact Filter.Eventually.of_forall fun ω => (hpath ω).2
  constructor
  · calc
      _ = ∫ ω, Finset.sum (Finset.range N) (fun t =>
          frobeniusNormSq (Node := Node) (E := E)
            (consensusError (Node := Node) (E := E)
              (setup.trackerState (oracle.noise ω) t))) ∂μ := by
        rw [MeasureTheory.integral_finset_sum]
        exact fun t _ht => hP_int t
      _ ≤ _ := hmonoP
      _ = _ := by
        exact integral_linearCombination_three_finsetSums μ N
          (fun t ω => frobeniusNormSq (Node := Node) (E := E)
            (setup.meanJointCoordinate (oracle.noise ω) t))
          (fun t ω => ‖∑ j : Node,
            setup.gradientTable (setup.primalState (oracle.noise ω) t) j‖ ^ 2)
          (fun t ω => frobeniusNormSq (Node := Node) (E := E)
            (setup.noiseJointCoordinate (oracle.noise ω) t))
          3 (3 * setup.projectedPerronRightNormMax ^ 2) 3
          (fun t _ht => hTheta_int t) (fun t _ht => hGrad_int t)
          (fun t _ht => hJ_int t)
  · calc
      _ = ∫ ω, 2 * Finset.sum (Finset.range N) (fun t =>
          frobeniusNormSq (Node := Node) (E := E)
            (setup.trackerState (oracle.noise ω) t)) ∂μ := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_finset_sum]
        exact fun t _ht => hY_int t
      _ ≤ _ := hmonoY
      _ = _ := by
        exact integral_linearCombination_three_finsetSums μ N
          (fun t ω => frobeniusNormSq (Node := Node) (E := E)
            (setup.meanJointCoordinate (oracle.noise ω) t))
          (fun t ω => ‖∑ j : Node,
            setup.gradientTable (setup.primalState (oracle.noise ω) t) j‖ ^ 2)
          (fun t ω => frobeniusNormSq (Node := Node) (E := E)
            (setup.noiseJointCoordinate (oracle.noise ω) t))
          6 (6 * setup.perronRightNormMax ^ 2) 6
          (fun t _ht => hTheta_int t) (fun t _ht => hGrad_int t)
          (fun t _ht => hJ_int t)

/- Expected aggregate-gradient consequence of source equations (6.16) and
(6.17).  The proof below is the finite-dimensional `L²` transport of the
already-proved pointwise disagreement estimate. -/
set_option maxHeartbeats 4000000 in
theorem gradientTable_sum_energy_bound
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E) (K : ℕ)
    (horacle : setup.StochasticOracleAssumptions μ oracle)
    (hallgrad :
      let N := setup.completeBlockHorizon K
      Finset.sum (Finset.range N) (fun t =>
          ∫ ω, ‖setup.averageGradient
            (setup.averageIterate (oracle.noise ω) t)‖ ^ 2 ∂μ) ≤
        2 * (setup.period : ℝ) * setup.blockGradientEnergy μ oracle K +
          (2 * setup.L ^ 2 * (setup.period : ℝ) ^ 2 /
            (nodeCount (Node := Node) : ℝ)) *
              setup.displacementEnergy μ oracle N) :
    let N := setup.completeBlockHorizon K
    Finset.sum (Finset.range N) (fun t =>
        ∫ ω, ‖∑ i : Node,
          setup.gradientTable (setup.primalState (oracle.noise ω) t) i‖ ^ 2 ∂μ) ≤
      4 * (nodeCount (Node := Node) : ℝ) ^ 2 * (setup.period : ℝ) *
          setup.blockGradientEnergy μ oracle K +
        4 * (nodeCount (Node := Node) : ℝ) * (setup.period : ℝ) ^ 2 *
            setup.L ^ 2 * setup.displacementEnergy μ oracle N +
          2 * (nodeCount (Node := Node) : ℝ) * setup.L ^ 2 *
            setup.consensusEnergy μ oracle N := by
  classical
  dsimp only
  let n : ℝ := nodeCount (Node := Node)
  let N := setup.completeBlockHorizon K
  let KL : NNReal := ⟨setup.L, setup.L_pos.le⟩
  have hn_pos : 0 < n := by
    dsimp [n, nodeCount]
    exact_mod_cast Fintype.card_pos
  have hgradient_lipschitz (i : Node) :
      LipschitzWith KL (setup.componentGradient i) := by
    rw [lipschitzWith_iff_norm_sub_le]
    intro x y
    simpa [KL, componentGradient] using
      setup.componentGradient_lipschitz_bound i x y
  have hgenerated (t : ℕ) :=
    setup.generated_pushpull_coordinate_memLp μ oracle horacle t
  have havgIterate (t : ℕ) : MemLp (fun ω =>
      setup.averageIterate (oracle.noise ω) t) 2 μ := by
    have hsum : MemLp (fun ω =>
        ∑ i : Node, setup.primalState (oracle.noise ω) t i) 2 μ := by
      apply memLp_finset_sum Finset.univ
      intro i _hi
      exact (hgenerated t).1 i
    simpa [averageIterate, arithmeticAverage] using hsum.const_smul n⁻¹
  have havgGrad (t : ℕ) : MemLp (fun ω =>
      setup.averageGradient (setup.averageIterate (oracle.noise ω) t)) 2 μ := by
    simpa only [randomAverageIterate] using
      setup.averageGradient_randomAverageIterate_memLp_two
        μ oracle horacle t
  have hgrad (t : ℕ) (i : Node) : MemLp (fun ω =>
      setup.gradientTable (setup.primalState (oracle.noise ω) t) i) 2 μ := by
    simpa [gradientTable] using
      memLp_two_comp_lipschitz (setup.componentGradient i) KL
        (hgradient_lipschitz i) ((hgenerated t).1 i)
  have hconsensus (t : ℕ) (i : Node) : MemLp (fun ω =>
      setup.consensusState (oracle.noise ω) t i) 2 μ := by
    have havg := havgIterate t
    simpa [consensusState_eq_state_sub_average] using ((hgenerated t).1 i).sub havg
  have hGrad_int (t : ℕ) : Integrable (fun ω =>
      ‖∑ i : Node,
        setup.gradientTable (setup.primalState (oracle.noise ω) t) i‖ ^ 2) μ :=
    normSq_finsetSum_integrable_of_memLp (fun i => hgrad t i)
  have hAvg_int (t : ℕ) : Integrable (fun ω =>
      ‖setup.averageGradient (setup.averageIterate (oracle.noise ω) t)‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (havgGrad t).aestronglyMeasurable).1
      (havgGrad t)
  have hQ_int (t : ℕ) : Integrable (fun ω =>
      frobeniusNormSq (Node := Node) (E := E)
        (setup.consensusState (oracle.noise ω) t)) μ :=
    frobeniusNormSq_integrable_of_coordinate_memLp (fun i => hconsensus t i)
  have hGrad_sum := integrable_finset_sum (Finset.range N)
    (fun t _ht => hGrad_int t)
  have hAvg_sum := integrable_finset_sum (Finset.range N)
    (fun t _ht => hAvg_int t)
  have hQ_sum := integrable_finset_sum (Finset.range N)
    (fun t _ht => hQ_int t)
  have hmono :
      (∫ ω, Finset.sum (Finset.range N) (fun t =>
          ‖∑ i : Node,
            setup.gradientTable (setup.primalState (oracle.noise ω) t) i‖ ^ 2) ∂μ) ≤
        ∫ ω,
          2 * n ^ 2 * Finset.sum (Finset.range N) (fun t =>
            ‖setup.averageGradient (setup.averageIterate (oracle.noise ω) t)‖ ^ 2) +
          2 * n * setup.L ^ 2 * Finset.sum (Finset.range N) (fun t =>
            frobeniusNormSq (Node := Node) (E := E)
              (setup.consensusState (oracle.noise ω) t)) ∂μ := by
    apply MeasureTheory.integral_mono_ae hGrad_sum
      ((hAvg_sum.const_mul (2 * n ^ 2)).add
        (hQ_sum.const_mul (2 * n * setup.L ^ 2)))
    exact Filter.Eventually.of_forall fun ω => by
      have hsum := Finset.sum_le_sum fun t (_ht : t ∈ Finset.range N) =>
        setup.gradientTable_sum_sq_le_average_consensus (oracle.noise ω) t
      simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, n] using hsum
  have hraw :
      Finset.sum (Finset.range N) (fun t =>
          ∫ ω, ‖∑ i : Node,
            setup.gradientTable (setup.primalState (oracle.noise ω) t) i‖ ^ 2 ∂μ) ≤
        2 * n ^ 2 * Finset.sum (Finset.range N) (fun t =>
          ∫ ω, ‖setup.averageGradient
            (setup.averageIterate (oracle.noise ω) t)‖ ^ 2 ∂μ) +
          2 * n * setup.L ^ 2 * Finset.sum (Finset.range N) (fun t =>
            ∫ ω, frobeniusNormSq (Node := Node) (E := E)
              (setup.consensusState (oracle.noise ω) t) ∂μ) := by
    calc
      _ = ∫ ω, Finset.sum (Finset.range N) (fun t =>
          ‖∑ i : Node,
            setup.gradientTable (setup.primalState (oracle.noise ω) t) i‖ ^ 2) ∂μ := by
        rw [MeasureTheory.integral_finset_sum]
        exact fun t _ht => hGrad_int t
      _ ≤ _ := hmono
      _ = _ := by
        rw [MeasureTheory.integral_add,
          MeasureTheory.integral_const_mul,
          MeasureTheory.integral_const_mul,
          MeasureTheory.integral_finset_sum,
          MeasureTheory.integral_finset_sum]
        all_goals
          try intro i _hi
          first
          | assumption
          | exact hAvg_sum.const_mul _
          | exact hQ_sum.const_mul _
          | exact hAvg_int _
          | exact hQ_int _
  have hQrange :
      Finset.sum (Finset.range N) (fun t =>
          ∫ ω, frobeniusNormSq (Node := Node) (E := E)
            (setup.consensusState (oracle.noise ω) t) ∂μ) ≤
        setup.consensusEnergy μ oracle N := by
    unfold consensusEnergy
    rw [Finset.sum_range_succ]
    exact le_add_of_nonneg_right (integral_nonneg fun _ => by
      unfold frobeniusNormSq
      positivity)
  have hscaleAvg : 0 ≤ 2 * n ^ 2 := by positivity
  have hscaleQ : 0 ≤ 2 * n * setup.L ^ 2 := by positivity
  calc
    _ ≤ 2 * n ^ 2 *
          Finset.sum (Finset.range N) (fun t =>
            ∫ ω, ‖setup.averageGradient
              (setup.averageIterate (oracle.noise ω) t)‖ ^ 2 ∂μ) +
        2 * n * setup.L ^ 2 *
          Finset.sum (Finset.range N) (fun t =>
            ∫ ω, frobeniusNormSq (Node := Node) (E := E)
              (setup.consensusState (oracle.noise ω) t) ∂μ) := hraw
    _ ≤ 2 * n ^ 2 *
          (2 * (setup.period : ℝ) * setup.blockGradientEnergy μ oracle K +
            (2 * setup.L ^ 2 * (setup.period : ℝ) ^ 2 / n) *
              setup.displacementEnergy μ oracle N) +
        2 * n * setup.L ^ 2 * setup.consensusEnergy μ oracle N :=
      add_le_add (mul_le_mul_of_nonneg_left hallgrad hscaleAvg)
        (mul_le_mul_of_nonneg_left hQrange hscaleQ)
    _ = _ := by
      field_simp [ne_of_gt hn_pos]
      ring

/-- The diagonal input to source equation (6.6): summing the nodewise
conditional second-moment law gives the one-step Frobenius noise budget. -/
theorem noiseTable_expected_frobeniusNormSq_le
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) (t : ℕ) :
    (∫ ω, frobeniusNormSq (Node := Node) (E := E) (oracle.noise ω t) ∂μ) ≤
      (nodeCount (Node := Node) : ℝ) * setup.sigma ^ 2 := by
  unfold frobeniusNormSq
  rw [MeasureTheory.integral_finset_sum]
  · calc
      ∑ i : Node, ∫ ω, ‖oracle.noise ω t i‖ ^ 2 ∂μ ≤
          ∑ _i : Node, setup.sigma ^ 2 := by
        apply Finset.sum_le_sum
        intro i _hi
        simpa using setup.conditionalSecondMomentBound_setIntegral_le
          μ oracle horacle t i Set.univ MeasurableSet.univ
      _ = (nodeCount (Node := Node) : ℝ) * setup.sigma ^ 2 := by
        simp [nodeCount]
  · intro i _hi
    exact setup.conditionalSecondMomentBound_integrable μ oracle horacle t i

/- The deterministic coefficient multiplying the time-`j` noise table in the
source expansion of `J_t^ε`.  At the current time it is the identity; at a
strictly earlier time it is `C_{t-1:j+1}(C_j-I)`. -/
noncomputable def noiseJointCoefficient (t j : ℕ) : NodeMatrix Node :=
  if j = t then identityMatrix (Node := Node) else
    matrixMul (Node := Node) (setup.pullLiftProduct (j + 1) (t - 1 - j))
      (matrixSub (Node := Node) (setup.C j) (identityMatrix (Node := Node)))

/- The source unrolling is equivalently a single finite martingale-transform
sum indexed by all noise times `j ≤ t`. -/
theorem noiseJointCoordinate_eq_sum_coefficients
    (noise : NoisePath Node E) (t : ℕ) :
    setup.noiseJointCoordinate noise t =
      ∑ j ∈ Finset.range (t + 1),
        leftMul (Node := Node) (E := E) (setup.noiseJointCoefficient t j)
          (noise j) := by
  rw [setup.noiseJointCoordinate_unroll noise t, Finset.sum_range_succ]
  have hpast :
      (∑ j ∈ Finset.range t,
          leftMul (Node := Node) (E := E) (setup.noiseJointCoefficient t j)
            (noise j)) =
        ∑ j ∈ Finset.range t,
          leftMul (Node := Node) (E := E)
            (setup.pullLiftProduct (j + 1) (t - 1 - j))
            (leftMul (Node := Node) (E := E)
              (matrixSub (Node := Node) (setup.C j)
                (identityMatrix (Node := Node))) (noise j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [noiseJointCoefficient, if_neg (Nat.ne_of_lt (Finset.mem_range.mp hj)),
      leftMul_matrixMul]
  rw [hpast]
  simp [noiseJointCoefficient, leftMul_identity]
  abel

/- A deterministic node matrix applied to one noise table is square-integrable
coordinatewise. -/
theorem leftMul_noise_coordinate_memLp
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle)
    (A : NodeMatrix Node) (s : ℕ) (i : Node) :
    MemLp (fun ω => leftMul (Node := Node) (E := E) A
      (oracle.noise ω s) i) 2 μ := by
  unfold leftMul
  apply memLp_finset_sum Finset.univ
  intro k _hk
  have hk : MemLp (fun ω => oracle.noise ω s k) 2 μ :=
    (memLp_two_iff_integrable_sq_norm
      ((oracle.noiseStream_measurable s).eval.aestronglyMeasurable)).2
      (setup.conditionalSecondMomentBound_integrable μ oracle horacle s k)
  simpa only [Pi.smul_apply] using hk.const_smul (A i k)

/- A deterministic transform of an earlier noise table is measurable in every
later strict-past sigma-algebra. -/
theorem leftMul_noise_coordinate_strictPastMeasurable
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (oracle : OracleNoiseProcess Ω Node E) (A : NodeMatrix Node)
    {s u : ℕ} (hsu : s < u) (i : Node) :
    Measurable[oracle.strictPastMeasurableSpace u]
      (fun ω => leftMul (Node := Node) (E := E) A
        (oracle.noise ω s) i) := by
  unfold leftMul
  apply Finset.measurable_sum Finset.univ
  intro k _hk
  have hs : Measurable[oracle.strictPastMeasurableSpace u]
      (oracle.noiseStream s) := by
    exact SOptLib.measurable_sample_of_lt_prefixFiltration
      oracle.noiseStream oracle.noiseStream_measurable hsu
  have hsk : Measurable[oracle.strictPastMeasurableSpace u]
      (fun ω => oracle.noise ω s k) := by
    change Measurable[oracle.strictPastMeasurableSpace u]
      (fun ω => oracle.noiseStream s ω k)
    exact (measurable_pi_apply k).comp hs
  exact hsk.const_smul (A i k)

/- The scalar cross term of two square-integrable Hilbert random variables is
integrable. -/
theorem integrable_inner_of_memLp_two
    {Ω F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {μ : Measure Ω} {X Y : Ω → F}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Integrable (fun ω => ⟪X ω, Y ω⟫_ℝ) μ := by
  have hprod : Integrable (fun ω => ‖X ω‖ * ‖Y ω‖) μ := by
    simpa [Pi.mul_apply] using
      (MeasureTheory.MemLp.integrable_mul hX.norm hY.norm :
        Integrable ((fun ω => ‖X ω‖) * (fun ω => ‖Y ω‖)) μ)
  exact hprod.mono'
    (AEStronglyMeasurable.inner hX.aestronglyMeasurable hY.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs] using abs_real_inner_le_norm (X ω) (Y ω))

/- Cross-time martingale orthogonality after arbitrary deterministic node
matrix transforms.  This is the formula-level stochastic step used in (6.6). -/
theorem leftMul_noise_cross_integral_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle)
    (A B : NodeMatrix Node) {s u : ℕ} (hsu : s < u) (i : Node) :
    (∫ ω, ⟪leftMul (Node := Node) (E := E) A (oracle.noise ω s) i,
        leftMul (Node := Node) (E := E) B (oracle.noise ω u) i⟫_ℝ ∂μ) = 0 := by
  let X : Ω → E := fun ω =>
    leftMul (Node := Node) (E := E) A (oracle.noise ω s) i
  have hX : MemLp X 2 μ :=
    setup.leftMul_noise_coordinate_memLp μ oracle horacle A s i
  have hXmeas : Measurable[oracle.strictPastMeasurableSpace u] X :=
    leftMul_noise_coordinate_strictPastMeasurable
      (Node := Node) (E := E) oracle A hsu i
  have hterm_zero (k : Node) :
      (∫ ω, ⟪X ω, oracle.noise ω u k⟫_ℝ ∂μ) = 0 := by
    have hnoise : MemLp (fun ω => oracle.noise ω u k) 2 μ :=
      (memLp_two_iff_integrable_sq_norm
        ((oracle.noiseStream_measurable u).eval.aestronglyMeasurable)).2
        (setup.conditionalSecondMomentBound_integrable μ oracle horacle u k)
    have hinner : Integrable (fun ω =>
        ⟪oracle.noise ω u k, X ω - (0 : E)⟫_ℝ) μ := by
      simpa using integrable_inner_of_memLp_two hnoise hX
    let hm := strictPastMeasurableSpace_le
      (Node := Node) (E := E) oracle u
    letI : @SigmaFinite Ω (oracle.strictPastMeasurableSpace u) (μ.trim hm) :=
      strictPastMeasurableSpace_trim_sigmaFinite
        (Node := Node) (E := E) μ oracle u
    have hzero := integral_inner_sub_const_eq_zero_of_condExp_eq_zero
      (P := μ) (m := oracle.strictPastMeasurableSpace u) hm hXmeas
      (setup.conditionalMeanZero_condExp μ oracle horacle u k)
      (setup.conditionalMeanZero_integrable μ oracle horacle u k) hinner
    simpa [X, real_inner_comm] using hzero
  have hterm_int (k : Node) : Integrable (fun ω =>
      B i k * ⟪X ω, oracle.noise ω u k⟫_ℝ) μ := by
    have hnoise : MemLp (fun ω => oracle.noise ω u k) 2 μ :=
      (memLp_two_iff_integrable_sq_norm
        ((oracle.noiseStream_measurable u).eval.aestronglyMeasurable)).2
        (setup.conditionalSecondMomentBound_integrable μ oracle horacle u k)
    exact (integrable_inner_of_memLp_two hX hnoise).const_mul _
  change (∫ ω, ⟪X ω,
      leftMul (Node := Node) (E := E) B (oracle.noise ω u) i⟫_ℝ ∂μ) = 0
  simp only [leftMul_apply, inner_sum, real_inner_smul_right]
  rw [MeasureTheory.integral_finset_sum]
  · apply Finset.sum_eq_zero
    intro k _hk
    rw [MeasureTheory.integral_const_mul, hterm_zero k, mul_zero]
  · exact fun k _hk => hterm_int k

/- Orthogonal diagonalization of the exact finite martingale-transform
expansion of `J_t^ε`. -/
theorem noiseJointCoordinate_expected_frobenius_eq_sum
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) (t : ℕ) :
    (∫ ω, frobeniusNormSq (Node := Node) (E := E)
        (setup.noiseJointCoordinate (oracle.noise ω) t) ∂μ) =
      ∑ j ∈ Finset.range (t + 1),
        ∫ ω, frobeniusNormSq (Node := Node) (E := E)
          (leftMul (Node := Node) (E := E) (setup.noiseJointCoefficient t j)
            (oracle.noise ω j)) ∂μ := by
  classical
  let term (j : ℕ) (ω : Ω) : State Node E :=
    leftMul (Node := Node) (E := E) (setup.noiseJointCoefficient t j)
      (oracle.noise ω j)
  have hmem (j : ℕ) (i : Node) : MemLp (fun ω => term j ω i) 2 μ := by
    exact setup.leftMul_noise_coordinate_memLp μ oracle horacle
      (setup.noiseJointCoefficient t j) j i
  have hsq (j : ℕ) (i : Node) : Integrable (fun ω => ‖term j ω i‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (hmem j i).aestronglyMeasurable).1
      (hmem j i)
  have hcross (i : Node) (j : ℕ) (_hj : j ∈ Finset.range (t + 1))
      (k : ℕ) (_hk : k ∈ Finset.range (t + 1)) (hjk : j ≠ k) :
      (∫ ω, ⟪term j ω i, term k ω i⟫_ℝ ∂μ) = 0 := by
    rcases lt_or_gt_of_ne hjk with hjk_lt | hkj_lt
    · exact setup.leftMul_noise_cross_integral_eq_zero μ oracle horacle
        (setup.noiseJointCoefficient t j) (setup.noiseJointCoefficient t k)
        hjk_lt i
    · have hzero := setup.leftMul_noise_cross_integral_eq_zero μ oracle horacle
        (setup.noiseJointCoefficient t k) (setup.noiseJointCoefficient t j)
        hkj_lt i
      simpa [term, real_inner_comm] using hzero
  have hcoordinate (i : Node) :
      (∫ ω, ‖∑ j ∈ Finset.range (t + 1), term j ω i‖ ^ 2 ∂μ) =
        ∑ j ∈ Finset.range (t + 1), ∫ ω, ‖term j ω i‖ ^ 2 ∂μ := by
    exact integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero
      μ (Finset.range (t + 1)) (fun j ω => term j ω i)
      (fun j _hj => (hmem j i).aestronglyMeasurable)
      (fun j _hj => hsq j i) (hcross i)
  have hunroll :
      (fun ω => frobeniusNormSq (Node := Node) (E := E)
        (setup.noiseJointCoordinate (oracle.noise ω) t)) =
      (fun ω => frobeniusNormSq (Node := Node) (E := E)
        (∑ j ∈ Finset.range (t + 1), term j ω)) := by
    funext ω
    rw [setup.noiseJointCoordinate_eq_sum_coefficients]
  rw [hunroll]
  unfold frobeniusNormSq
  rw [MeasureTheory.integral_finset_sum]
  · calc
      ∑ i : Node, ∫ ω, ‖(∑ j ∈ Finset.range (t + 1), term j ω) i‖ ^ 2 ∂μ =
          ∑ i : Node, ∑ j ∈ Finset.range (t + 1),
            ∫ ω, ‖term j ω i‖ ^ 2 ∂μ := by
        apply Finset.sum_congr rfl
        intro i _hi
        simpa only [Finset.sum_apply] using hcoordinate i
      _ = ∑ j ∈ Finset.range (t + 1), ∑ i : Node,
            ∫ ω, ‖term j ω i‖ ^ 2 ∂μ := by rw [Finset.sum_comm]
      _ = ∑ j ∈ Finset.range (t + 1),
            ∫ ω, ∑ i : Node, ‖term j ω i‖ ^ 2 ∂μ := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [MeasureTheory.integral_finset_sum]
        exact fun i _hi => hsq j i
      _ = _ := by rfl
  · intro i _hi
    have hsum : MemLp
        (fun ω => ∑ j ∈ Finset.range (t + 1), term j ω i) 2 μ := by
      apply memLp_finset_sum (Finset.range (t + 1))
      intro j _hj
      exact hmem j i
    simpa only [Finset.sum_apply] using
      ((memLp_two_iff_integrable_sq_norm hsum.aestronglyMeasurable).1 hsum)

/- Cross-time martingale orthogonality diagonalizes the past-only tracker
error.  Unlike the corresponding identity for `J_t^ε`, this sum has no
current-noise diagonal and therefore no additive `1` in its eventual uniform
bound. -/
theorem noiseTrackerError_expected_frobenius_eq_sum
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) (t : ℕ) :
    (∫ ω, frobeniusNormSq (Node := Node) (E := E)
        (setup.noiseTrackerError (oracle.noise ω) t) ∂μ) =
      ∑ j ∈ Finset.range t,
        ∫ ω, frobeniusNormSq (Node := Node) (E := E)
          (leftMul (Node := Node) (E := E) (setup.noiseJointCoefficient t j)
            (oracle.noise ω j)) ∂μ := by
  classical
  let term (j : ℕ) (ω : Ω) : State Node E :=
    leftMul (Node := Node) (E := E) (setup.noiseJointCoefficient t j)
      (oracle.noise ω j)
  have hmem (j : ℕ) (i : Node) : MemLp (fun ω => term j ω i) 2 μ := by
    exact setup.leftMul_noise_coordinate_memLp μ oracle horacle
      (setup.noiseJointCoefficient t j) j i
  have hsq (j : ℕ) (i : Node) : Integrable (fun ω => ‖term j ω i‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (hmem j i).aestronglyMeasurable).1
      (hmem j i)
  have hcross (i : Node) (j : ℕ) (_hj : j ∈ Finset.range t)
      (k : ℕ) (_hk : k ∈ Finset.range t) (hjk : j ≠ k) :
      (∫ ω, ⟪term j ω i, term k ω i⟫_ℝ ∂μ) = 0 := by
    rcases lt_or_gt_of_ne hjk with hjk_lt | hkj_lt
    · exact setup.leftMul_noise_cross_integral_eq_zero μ oracle horacle
        (setup.noiseJointCoefficient t j) (setup.noiseJointCoefficient t k)
        hjk_lt i
    · have hzero := setup.leftMul_noise_cross_integral_eq_zero μ oracle horacle
        (setup.noiseJointCoefficient t k) (setup.noiseJointCoefficient t j)
        hkj_lt i
      simpa [term, real_inner_comm] using hzero
  have hcoordinate (i : Node) :
      (∫ ω, ‖∑ j ∈ Finset.range t, term j ω i‖ ^ 2 ∂μ) =
        ∑ j ∈ Finset.range t, ∫ ω, ‖term j ω i‖ ^ 2 ∂μ := by
    exact integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero
      μ (Finset.range t) (fun j ω => term j ω i)
      (fun j _hj => (hmem j i).aestronglyMeasurable)
      (fun j _hj => hsq j i) (hcross i)
  have hunroll :
      (fun ω => frobeniusNormSq (Node := Node) (E := E)
        (setup.noiseTrackerError (oracle.noise ω) t)) =
      (fun ω => frobeniusNormSq (Node := Node) (E := E)
        (∑ j ∈ Finset.range t, term j ω)) := by
    funext ω
    congr 1
    rw [setup.noiseTrackerError_unroll_source]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [term, noiseJointCoefficient,
      if_neg (Nat.ne_of_lt (Finset.mem_range.mp hj)), leftMul_matrixMul]
  rw [hunroll]
  unfold frobeniusNormSq
  rw [MeasureTheory.integral_finset_sum]
  · calc
      ∑ i : Node, ∫ ω, ‖(∑ j ∈ Finset.range t, term j ω) i‖ ^ 2 ∂μ =
          ∑ i : Node, ∑ j ∈ Finset.range t,
            ∫ ω, ‖term j ω i‖ ^ 2 ∂μ := by
        apply Finset.sum_congr rfl
        intro i _hi
        simpa only [Finset.sum_apply] using hcoordinate i
      _ = ∑ j ∈ Finset.range t, ∑ i : Node,
            ∫ ω, ‖term j ω i‖ ^ 2 ∂μ := by rw [Finset.sum_comm]
      _ = ∑ j ∈ Finset.range t,
            ∫ ω, ∑ i : Node, ‖term j ω i‖ ^ 2 ∂μ := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [MeasureTheory.integral_finset_sum]
        exact fun i _hi => hsq j i
      _ = _ := by rfl
  · intro i _hi
    have hsum : MemLp
        (fun ω => ∑ j ∈ Finset.range t, term j ω i) 2 μ := by
      apply memLp_finset_sum (Finset.range t)
      intro j _hj
      exact hmem j i
    simpa only [Finset.sum_apply] using
      ((memLp_two_iff_integrable_sq_norm hsum.aestronglyMeasurable).1 hsum)

theorem pullDeviationNormMax_nonneg :
    0 ≤ setup.pullDeviationNormMax := by
  let r : Fin setup.period := ⟨0, setup.period_pos⟩
  have hnorm : 0 ≤ matrixEuclideanOperatorNorm (Node := Node)
      (matrixSub (Node := Node) (setup.C r.1)
        (identityMatrix (Node := Node))) :=
    (matrixEuclideanOperatorNorm_spec (Node := Node) _).1
  exact hnorm.trans (by
    simpa [pullDeviationNormMax] using
      (setup.le_periodMax
        (fun q : Fin setup.period =>
          matrixEuclideanOperatorNorm (Node := Node)
            (matrixSub (Node := Node) (setup.C q.1)
              (identityMatrix (Node := Node)))) r))

/- Diagonal second-moment estimate for one summand in the martingale-transform
expansion.  Earlier inputs receive the squared pull-product decay; the current
input has coefficient one. -/
theorem noiseJointCoefficient_expected_frobenius_le
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle)
    (t j : ℕ) (hj : j ∈ Finset.range (t + 1)) :
    (∫ ω, frobeniusNormSq (Node := Node) (E := E)
        (leftMul (Node := Node) (E := E) (setup.noiseJointCoefficient t j)
          (oracle.noise ω j)) ∂μ) ≤
      (if j = t then 1 else
        setup.columnContractionConstant ^ 2 * setup.pullDeviationNormMax ^ 2 *
          (setup.contractionRate ^ 2) ^ (t - 1 - j)) *
        ((nodeCount (Node := Node) : ℝ) * setup.sigma ^ 2) := by
  classical
  by_cases hjt : j = t
  · subst j
    simp only [noiseJointCoefficient, if_pos, leftMul_identity, one_mul]
    exact setup.noiseTable_expected_frobeniusNormSq_le μ oracle horacle t
  · have hjlt : j < t := by
      have hjle : j ≤ t := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      exact lt_of_le_of_ne hjle hjt
    let innovation (ω : Ω) : State Node E :=
      leftMul (Node := Node) (E := E)
        (matrixSub (Node := Node) (setup.C j) (identityMatrix (Node := Node)))
        (oracle.noise ω j)
    let transformed (ω : Ω) : State Node E :=
      leftMul (Node := Node) (E := E)
        (setup.pullLiftProduct (j + 1) (t - 1 - j)) (innovation ω)
    have hzero (ω : Ω) : ∑ i : Node, innovation ω i = 0 := by
      exact setup.pull_innovation_sum_zero j (oracle.noise ω j)
    have hMC : 0 ≤ setup.columnContractionConstant := by
      rw [columnContractionConstant]
      exact div_nonneg (Real.sqrt_nonneg _) setup.contractionDelta_pos.le
    have hcC : 0 ≤ setup.pullDeviationNormMax :=
      setup.pullDeviationNormMax_nonneg
    have hr : 0 ≤ setup.contractionRate := setup.contractionRate_nonneg
    have hnorm (ω : Ω) :
        stateFrobeniusNorm (Node := Node) (E := E) (transformed ω) ≤
          (setup.columnContractionConstant *
              setup.contractionRate ^ (t - 1 - j) *
            setup.pullDeviationNormMax) *
            stateFrobeniusNorm (Node := Node) (E := E) (oracle.noise ω j) := by
      have hpull := setup.pullLiftProduct_frobenius_rate
        setup.contractionDelta_pos setup.contractionDelta_lt_one
        (j + 1) (t - 1 - j) ⟨innovation ω, hzero ω⟩
      have hdev := setup.pullDeviation_stateFrobenius_action j (oracle.noise ω j)
      calc
        _ ≤ setup.columnContractionConstant *
              setup.contractionRate ^ (t - 1 - j) *
              stateFrobeniusNorm (Node := Node) (E := E) (innovation ω) := hpull
        _ ≤ setup.columnContractionConstant *
              setup.contractionRate ^ (t - 1 - j) *
              (setup.pullDeviationNormMax *
                stateFrobeniusNorm (Node := Node) (E := E) (oracle.noise ω j)) :=
          mul_le_mul_of_nonneg_left hdev
            (mul_nonneg hMC (pow_nonneg hr _))
        _ = _ := by ring
    have hsq (ω : Ω) :
        frobeniusNormSq (Node := Node) (E := E) (transformed ω) ≤
          (setup.columnContractionConstant *
              setup.contractionRate ^ (t - 1 - j) *
            setup.pullDeviationNormMax) ^ 2 *
            frobeniusNormSq (Node := Node) (E := E) (oracle.noise ω j) := by
      have hsquare :
          stateFrobeniusNorm (Node := Node) (E := E) (transformed ω) ^ 2 ≤
            ((setup.columnContractionConstant *
                setup.contractionRate ^ (t - 1 - j) *
              setup.pullDeviationNormMax) *
              stateFrobeniusNorm (Node := Node) (E := E)
                (oracle.noise ω j)) ^ 2 :=
        (sq_le_sq₀ (Real.sqrt_nonneg _)
        (mul_nonneg (mul_nonneg
          (mul_nonneg hMC (pow_nonneg hr _)) hcC)
            (Real.sqrt_nonneg _))).2 (hnorm ω)
      calc
        frobeniusNormSq (Node := Node) (E := E) (transformed ω) =
            stateFrobeniusNorm (Node := Node) (E := E) (transformed ω) ^ 2 :=
          (stateFrobeniusNorm_sq _).symm
        _ ≤ ((setup.columnContractionConstant *
                setup.contractionRate ^ (t - 1 - j) *
              setup.pullDeviationNormMax) *
              stateFrobeniusNorm (Node := Node) (E := E)
                (oracle.noise ω j)) ^ 2 := hsquare
        _ = _ := by rw [mul_pow, stateFrobeniusNorm_sq]
    have htransform (ω : Ω) :
        transformed ω =
          leftMul (Node := Node) (E := E) (setup.noiseJointCoefficient t j)
            (oracle.noise ω j) := by
      simp only [transformed, innovation, noiseJointCoefficient, if_neg hjt,
        leftMul_matrixMul]
    have htransformed_mem (i : Node) :
        MemLp (fun ω => transformed ω i) 2 μ := by
      refine MemLp.ae_eq ?_
        (setup.leftMul_noise_coordinate_memLp μ oracle horacle
          (setup.noiseJointCoefficient t j) j i)
      exact Filter.Eventually.of_forall fun ω => (congrFun (htransform ω) i).symm
    have hterm_int : Integrable (fun ω =>
        frobeniusNormSq (Node := Node) (E := E) (transformed ω)) μ := by
      apply frobeniusNormSq_integrable_of_coordinate_memLp
      intro i
      exact htransformed_mem i
    have hnoise_int : Integrable (fun ω =>
        frobeniusNormSq (Node := Node) (E := E) (oracle.noise ω j)) μ :=
      frobeniusNormSq_integrable_of_coordinate_memLp fun i =>
        (memLp_two_iff_integrable_sq_norm
          ((oracle.noiseStream_measurable j).eval.aestronglyMeasurable)).2
          (setup.conditionalSecondMomentBound_integrable μ oracle horacle j i)
    have hmono :
        (∫ ω, frobeniusNormSq (Node := Node) (E := E) (transformed ω) ∂μ) ≤
          ∫ ω, (setup.columnContractionConstant *
              setup.contractionRate ^ (t - 1 - j) *
            setup.pullDeviationNormMax) ^ 2 *
              frobeniusNormSq (Node := Node) (E := E) (oracle.noise ω j) ∂μ := by
      apply MeasureTheory.integral_mono_ae hterm_int
        (hnoise_int.const_mul _)
      exact Filter.Eventually.of_forall hsq
    have hnoise := setup.noiseTable_expected_frobeniusNormSq_le
      μ oracle horacle j
    have hscale : 0 ≤ (setup.columnContractionConstant *
        setup.contractionRate ^ (t - 1 - j) * setup.pullDeviationNormMax) ^ 2 :=
      sq_nonneg _
    have hpowsq : (setup.contractionRate ^ (t - 1 - j)) ^ 2 =
        (setup.contractionRate ^ 2) ^ (t - 1 - j) := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      omega
    simp only [noiseJointCoefficient, if_neg hjt, leftMul_matrixMul]
    change (∫ ω, frobeniusNormSq (Node := Node) (E := E) (transformed ω) ∂μ) ≤ _
    calc
      _ ≤ ∫ ω, (setup.columnContractionConstant *
              setup.contractionRate ^ (t - 1 - j) *
            setup.pullDeviationNormMax) ^ 2 *
              frobeniusNormSq (Node := Node) (E := E) (oracle.noise ω j) ∂μ := hmono
      _ = (setup.columnContractionConstant *
              setup.contractionRate ^ (t - 1 - j) *
            setup.pullDeviationNormMax) ^ 2 *
              (∫ ω, frobeniusNormSq (Node := Node) (E := E)
                (oracle.noise ω j) ∂μ) := by
        rw [MeasureTheory.integral_const_mul]
      _ ≤ (setup.columnContractionConstant *
              setup.contractionRate ^ (t - 1 - j) *
            setup.pullDeviationNormMax) ^ 2 *
              ((nodeCount (Node := Node) : ℝ) * setup.sigma ^ 2) :=
        mul_le_mul_of_nonneg_left hnoise hscale
      _ = setup.columnContractionConstant ^ 2 *
            setup.pullDeviationNormMax ^ 2 *
            (setup.contractionRate ^ 2) ^ (t - 1 - j) *
              ((nodeCount (Node := Node) : ℝ) * setup.sigma ^ 2) := by
        rw [mul_pow, mul_pow, hpowsq]
        ring

/- Uniform source coefficient for the past-only noise-tracker error.  The
index set is `range t`, so every call to the diagonal coefficient estimate
uses its strict-past branch. -/
theorem noise_tracker_error_secondMoment_bound
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) (t : ℕ) :
    (∫ ω, frobeniusNormSq (Node := Node) (E := E)
        (setup.noiseTrackerError (oracle.noise ω) t) ∂μ) ≤
      (setup.columnContractionConstant ^ 2 *
          setup.pullDeviationNormMax ^ 2 * (nodeCount (Node := Node) : ℝ) /
        (1 - setup.contractionRate ^ 2)) * setup.sigma ^ 2 := by
  classical
  let q := setup.contractionRate ^ 2
  let a := setup.columnContractionConstant ^ 2 *
    setup.pullDeviationNormMax ^ 2
  let B := (nodeCount (Node := Node) : ℝ) * setup.sigma ^ 2
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    positivity
  have hq_lt : q < 1 := by
    dsimp [q]
    nlinarith [setup.contractionRate_nonneg,
      setup.contractionRate_lt_one]
  have hgap : 0 < 1 - q := sub_pos.mpr hq_lt
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hgeom_identity := geom_sum_mul q t
  have hqpow : 0 ≤ q ^ t := pow_nonneg hq_nonneg _
  have hgeom :
      ∑ k ∈ Finset.range t, q ^ k ≤ 1 / (1 - q) := by
    apply (le_div_iff₀ hgap).2
    nlinarith
  have hpast :
      ∑ j ∈ Finset.range t,
          (∫ ω, frobeniusNormSq (Node := Node) (E := E)
            (leftMul (Node := Node) (E := E)
              (setup.noiseJointCoefficient t j) (oracle.noise ω j)) ∂μ) ≤
        ∑ j ∈ Finset.range t, a * q ^ (t - 1 - j) * B := by
    apply Finset.sum_le_sum
    intro j hj
    have hjt : j ≠ t := Nat.ne_of_lt (Finset.mem_range.mp hj)
    simpa [a, q, B, hjt] using
      setup.noiseJointCoefficient_expected_frobenius_le
        μ oracle horacle t j (Finset.mem_range.mpr
          (Nat.lt_trans (Finset.mem_range.mp hj) (Nat.lt_succ_self t)))
  have hreflect :
      ∑ j ∈ Finset.range t, q ^ (t - 1 - j) =
        ∑ k ∈ Finset.range t, q ^ k := by
    exact Finset.sum_range_reflect (fun k => q ^ k) t
  have hweighted :
      a * (∑ k ∈ Finset.range t, q ^ k) * B ≤
        a * (1 / (1 - q)) * B := by
    calc
      a * (∑ k ∈ Finset.range t, q ^ k) * B =
          (a * B) * (∑ k ∈ Finset.range t, q ^ k) := by ring
      _ ≤ (a * B) * (1 / (1 - q)) :=
        mul_le_mul_of_nonneg_left hgeom (mul_nonneg ha hB)
      _ = a * (1 / (1 - q)) * B := by ring
  calc
    (∫ ω, frobeniusNormSq (Node := Node) (E := E)
        (setup.noiseTrackerError (oracle.noise ω) t) ∂μ) =
      ∑ j ∈ Finset.range t,
        ∫ ω, frobeniusNormSq (Node := Node) (E := E)
          (leftMul (Node := Node) (E := E)
            (setup.noiseJointCoefficient t j) (oracle.noise ω j)) ∂μ :=
      setup.noiseTrackerError_expected_frobenius_eq_sum μ oracle horacle t
    _ ≤ ∑ j ∈ Finset.range t, a * q ^ (t - 1 - j) * B := hpast
    _ = a * (∑ j ∈ Finset.range t, q ^ (t - 1 - j)) * B := by
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = a * (∑ k ∈ Finset.range t, q ^ k) * B := by rw [hreflect]
    _ ≤ a * (1 / (1 - q)) * B := hweighted
    _ = (setup.columnContractionConstant ^ 2 *
          setup.pullDeviationNormMax ^ 2 * (nodeCount (Node := Node) : ℝ) /
        (1 - setup.contractionRate ^ 2)) * setup.sigma ^ 2 := by
      dsimp [a, q, B]
      ring

/-- Source equation (6.6): the noise joint coordinate has a uniform second
moment.  `noiseJointCoordinate_unroll` exposes the exact martingale-transform
sum to which cross-time orthogonality and the nodewise conditional variance
bound are applied. -/
theorem noiseJointCoordinate_secondMoment_bound
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) (t : ℕ) :
    (∫ ω, frobeniusNormSq (Node := Node) (E := E)
        (setup.noiseJointCoordinate (oracle.noise ω) t) ∂μ) ≤
      setup.jointNoiseResidualConstant *
        (nodeCount (Node := Node) : ℝ) * setup.sigma ^ 2 := by
  classical
  let q := setup.contractionRate ^ 2
  let a := setup.columnContractionConstant ^ 2 *
    setup.pullDeviationNormMax ^ 2
  let B := (nodeCount (Node := Node) : ℝ) * setup.sigma ^ 2
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    positivity
  have hq_lt : q < 1 := by
    dsimp [q]
    nlinarith [setup.contractionRate_nonneg,
      setup.contractionRate_lt_one]
  have hgap : 0 < 1 - q := sub_pos.mpr hq_lt
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hgeom_identity := geom_sum_mul q t
  have hqpow : 0 ≤ q ^ t := pow_nonneg hq_nonneg _
  have hgeom :
      ∑ k ∈ Finset.range t, q ^ k ≤ 1 / (1 - q) := by
    apply (le_div_iff₀ hgap).2
    nlinarith
  have hpast :
      ∑ j ∈ Finset.range t,
          (∫ ω, frobeniusNormSq (Node := Node) (E := E)
            (leftMul (Node := Node) (E := E)
              (setup.noiseJointCoefficient t j) (oracle.noise ω j)) ∂μ) ≤
        ∑ j ∈ Finset.range t, a * q ^ (t - 1 - j) * B := by
    apply Finset.sum_le_sum
    intro j hj
    have hjt : j ≠ t := Nat.ne_of_lt (Finset.mem_range.mp hj)
    simpa [a, q, B, hjt] using
      setup.noiseJointCoefficient_expected_frobenius_le
        μ oracle horacle t j (Finset.mem_range.mpr
          (Nat.lt_trans (Finset.mem_range.mp hj) (Nat.lt_succ_self t)))
  have hcurrent :
      (∫ ω, frobeniusNormSq (Node := Node) (E := E)
          (leftMul (Node := Node) (E := E)
            (setup.noiseJointCoefficient t t) (oracle.noise ω t)) ∂μ) ≤ B := by
    simpa [B] using
      setup.noiseJointCoefficient_expected_frobenius_le
        μ oracle horacle t t (Finset.mem_range.mpr (Nat.lt_succ_self t))
  have hreflect :
      ∑ j ∈ Finset.range t, q ^ (t - 1 - j) =
        ∑ k ∈ Finset.range t, q ^ k := by
    exact Finset.sum_range_reflect (fun k => q ^ k) t
  have hweighted :
      a * (∑ k ∈ Finset.range t, q ^ k) * B ≤
        a * (1 / (1 - q)) * B := by
    calc
      a * (∑ k ∈ Finset.range t, q ^ k) * B =
          (a * B) * (∑ k ∈ Finset.range t, q ^ k) := by ring
      _ ≤ (a * B) * (1 / (1 - q)) :=
        mul_le_mul_of_nonneg_left hgeom (mul_nonneg ha hB)
      _ = a * (1 / (1 - q)) * B := by ring
  calc
    (∫ ω, frobeniusNormSq (Node := Node) (E := E)
        (setup.noiseJointCoordinate (oracle.noise ω) t) ∂μ) =
      ∑ j ∈ Finset.range (t + 1),
        ∫ ω, frobeniusNormSq (Node := Node) (E := E)
          (leftMul (Node := Node) (E := E)
            (setup.noiseJointCoefficient t j) (oracle.noise ω j)) ∂μ :=
      setup.noiseJointCoordinate_expected_frobenius_eq_sum
        μ oracle horacle t
    _ = (∑ j ∈ Finset.range t,
          ∫ ω, frobeniusNormSq (Node := Node) (E := E)
            (leftMul (Node := Node) (E := E)
              (setup.noiseJointCoefficient t j) (oracle.noise ω j)) ∂μ) +
        (∫ ω, frobeniusNormSq (Node := Node) (E := E)
          (leftMul (Node := Node) (E := E)
            (setup.noiseJointCoefficient t t) (oracle.noise ω t)) ∂μ) := by
      rw [Finset.sum_range_succ]
    _ ≤ (∑ j ∈ Finset.range t, a * q ^ (t - 1 - j) * B) + B :=
      add_le_add hpast hcurrent
    _ = a * (∑ j ∈ Finset.range t, q ^ (t - 1 - j)) * B + B := by
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = a * (∑ k ∈ Finset.range t, q ^ k) * B + B := by rw [hreflect]
    _ ≤ a * (1 / (1 - q)) * B + B := add_le_add hweighted le_rfl
    _ = setup.jointNoiseResidualConstant *
          (nodeCount (Node := Node) : ℝ) * setup.sigma ^ 2 := by
      dsimp [a, q, B]
      rw [jointNoiseResidualConstant]
      ring

/- Source-stage assembly after (6.5), (6.6), and (6.16).  Its three explicit
inputs are the filter and average-gradient estimates; the body is the
projected/unprojected use of (6.3) and (6.17), with the coefficients defined
above. -/
theorem tracker_budgets_of_joint_coordinate_bounds
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E) (K : ℕ)
    (horacle : setup.StochasticOracleAssumptions μ oracle)
    (hmean :
      let N := setup.completeBlockHorizon K
      Finset.sum (Finset.range (N + 1)) (fun t =>
          ∫ ω, frobeniusNormSq (Node := Node) (E := E)
            (setup.meanJointCoordinate (oracle.noise ω) t) ∂μ) ≤
        setup.thetaInitialConstant * setup.initialGradientHeterogeneity ^ 2 +
          setup.thetaDisplacementConstant * setup.L ^ 2 *
            setup.displacementEnergy μ oracle N)
    (hnoise : ∀ t : ℕ,
      (∫ ω, frobeniusNormSq (Node := Node) (E := E)
          (setup.noiseJointCoordinate (oracle.noise ω) t) ∂μ) ≤
        setup.jointNoiseResidualConstant *
          (nodeCount (Node := Node) : ℝ) * setup.sigma ^ 2)
    (hallgrad :
      let N := setup.completeBlockHorizon K
      Finset.sum (Finset.range N) (fun t =>
          ∫ ω, ‖setup.averageGradient
            (setup.averageIterate (oracle.noise ω) t)‖ ^ 2 ∂μ) ≤
        2 * (setup.period : ℝ) * setup.blockGradientEnergy μ oracle K +
          (2 * setup.L ^ 2 * (setup.period : ℝ) ^ 2 /
            (nodeCount (Node := Node) : ℝ)) *
              setup.displacementEnergy μ oracle N) :
    let N := setup.completeBlockHorizon K
    let I := setup.initialGradientHeterogeneity ^ 2
    let G := setup.blockGradientEnergy μ oracle K
    let V := (nodeCount (Node := Node) : ℝ) * setup.sigma ^ 2 * N
    let D := setup.displacementEnergy μ oracle N
    let Q := setup.consensusEnergy μ oracle N
    let P := Finset.sum (Finset.range N) (fun t =>
      ∫ ω, frobeniusNormSq (Node := Node) (E := E)
        (consensusError (Node := Node) (E := E)
          (setup.trackerState (oracle.noise ω) t)) ∂μ)
    let Y := Finset.sum (Finset.range N) (fun t =>
      ∫ ω, frobeniusNormSq (Node := Node) (E := E)
        (setup.trackerState (oracle.noise ω) t) ∂μ)
    P ≤ setup.projectedTrackerInitialCoefficient * I +
          setup.projectedTrackerGradientCoefficient * G +
          setup.projectedTrackerNoiseCoefficient * V +
          setup.projectedTrackerDisplacementCoefficient * setup.L ^ 2 * D +
          setup.projectedTrackerConsensusCoefficient * setup.L ^ 2 * Q ∧
      2 * Y ≤ setup.unprojectedTrackerInitialCoefficient * I +
          setup.unprojectedTrackerGradientCoefficient * G +
          setup.unprojectedTrackerNoiseCoefficient * V +
          setup.unprojectedTrackerDisplacementCoefficient * setup.L ^ 2 * D +
          setup.unprojectedTrackerConsensusCoefficient * setup.L ^ 2 * Q := by
  classical
  dsimp only
  let N := setup.completeBlockHorizon K
  let I := setup.initialGradientHeterogeneity ^ 2
  let G := setup.blockGradientEnergy μ oracle K
  let V := (nodeCount (Node := Node) : ℝ) * setup.sigma ^ 2 * N
  let D := setup.displacementEnergy μ oracle N
  let Q := setup.consensusEnergy μ oracle N
  let Theta := Finset.sum (Finset.range N) (fun t =>
    ∫ ω, frobeniusNormSq (Node := Node) (E := E)
      (setup.meanJointCoordinate (oracle.noise ω) t) ∂μ)
  let Grad := Finset.sum (Finset.range N) (fun t =>
    ∫ ω, ‖∑ j : Node,
      setup.gradientTable (setup.primalState (oracle.noise ω) t) j‖ ^ 2 ∂μ)
  let J := Finset.sum (Finset.range N) (fun t =>
    ∫ ω, frobeniusNormSq (Node := Node) (E := E)
      (setup.noiseJointCoordinate (oracle.noise ω) t) ∂μ)
  let P := Finset.sum (Finset.range N) (fun t =>
    ∫ ω, frobeniusNormSq (Node := Node) (E := E)
      (consensusError (Node := Node) (E := E)
        (setup.trackerState (oracle.noise ω) t)) ∂μ)
  let Y := Finset.sum (Finset.range N) (fun t =>
    ∫ ω, frobeniusNormSq (Node := Node) (E := E)
      (setup.trackerState (oracle.noise ω) t) ∂μ)
  have hexpected :
      P ≤ 3 * Theta +
          3 * setup.projectedPerronRightNormMax ^ 2 * Grad + 3 * J ∧
        2 * Y ≤ 6 * Theta +
          6 * setup.perronRightNormMax ^ 2 * Grad + 6 * J := by
    simpa [P, Y, Theta, Grad, J, N] using
      setup.trackerState_joint_expected_energy_bounds μ oracle horacle N
  have hTheta :
      Theta ≤ setup.thetaInitialConstant * I +
        setup.thetaDisplacementConstant * setup.L ^ 2 * D := by
    dsimp [Theta, I, D, N]
    calc
      Finset.sum (Finset.range (setup.completeBlockHorizon K)) (fun t =>
          ∫ ω, frobeniusNormSq (Node := Node) (E := E)
            (setup.meanJointCoordinate (oracle.noise ω) t) ∂μ) ≤
        Finset.sum (Finset.range (setup.completeBlockHorizon K + 1)) (fun t =>
          ∫ ω, frobeniusNormSq (Node := Node) (E := E)
            (setup.meanJointCoordinate (oracle.noise ω) t) ∂μ) := by
          rw [Finset.sum_range_succ]
          exact le_add_of_nonneg_right (integral_nonneg fun _ => by
            unfold frobeniusNormSq
            positivity)
      _ ≤ _ := hmean
  have hGrad :
      Grad ≤ 4 * (nodeCount (Node := Node) : ℝ) ^ 2 *
            (setup.period : ℝ) * G +
          4 * (nodeCount (Node := Node) : ℝ) * (setup.period : ℝ) ^ 2 *
            setup.L ^ 2 * D +
          2 * (nodeCount (Node := Node) : ℝ) * setup.L ^ 2 * Q := by
    simpa [Grad, G, D, Q, N] using
      setup.gradientTable_sum_energy_bound μ oracle K horacle hallgrad
  have hJ : J ≤ setup.jointNoiseResidualConstant * V := by
    dsimp [J, V, N]
    calc
      Finset.sum (Finset.range (setup.completeBlockHorizon K)) (fun t =>
          ∫ ω, frobeniusNormSq (Node := Node) (E := E)
            (setup.noiseJointCoordinate (oracle.noise ω) t) ∂μ) ≤
        Finset.sum (Finset.range (setup.completeBlockHorizon K)) (fun _ =>
          setup.jointNoiseResidualConstant *
            (nodeCount (Node := Node) : ℝ) * setup.sigma ^ 2) := by
          apply Finset.sum_le_sum
          intro t _ht
          exact hnoise t
      _ = setup.jointNoiseResidualConstant *
          ((nodeCount (Node := Node) : ℝ) * setup.sigma ^ 2 *
            setup.completeBlockHorizon K) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
  have hprojGradScale :
      0 ≤ 3 * setup.projectedPerronRightNormMax ^ 2 := by positivity
  have hrawGradScale : 0 ≤ 6 * setup.perronRightNormMax ^ 2 := by positivity
  constructor
  · calc
      P ≤ 3 * Theta +
          3 * setup.projectedPerronRightNormMax ^ 2 * Grad + 3 * J :=
        hexpected.1
      _ ≤ 3 * (setup.thetaInitialConstant * I +
              setup.thetaDisplacementConstant * setup.L ^ 2 * D) +
          3 * setup.projectedPerronRightNormMax ^ 2 *
            (4 * (nodeCount (Node := Node) : ℝ) ^ 2 *
                (setup.period : ℝ) * G +
              4 * (nodeCount (Node := Node) : ℝ) *
                (setup.period : ℝ) ^ 2 * setup.L ^ 2 * D +
              2 * (nodeCount (Node := Node) : ℝ) * setup.L ^ 2 * Q) +
          3 * (setup.jointNoiseResidualConstant * V) := by
        exact add_le_add
          (add_le_add (mul_le_mul_of_nonneg_left hTheta (by norm_num))
            (mul_le_mul_of_nonneg_left hGrad hprojGradScale))
          (mul_le_mul_of_nonneg_left hJ (by norm_num))
      _ = setup.projectedTrackerInitialCoefficient * I +
          setup.projectedTrackerGradientCoefficient * G +
          setup.projectedTrackerNoiseCoefficient * V +
          setup.projectedTrackerDisplacementCoefficient * setup.L ^ 2 * D +
          setup.projectedTrackerConsensusCoefficient * setup.L ^ 2 * Q := by
        unfold projectedTrackerInitialCoefficient
          projectedTrackerGradientCoefficient projectedTrackerNoiseCoefficient
          projectedTrackerDisplacementCoefficient
          projectedTrackerConsensusCoefficient
        ring
  · calc
      2 * Y ≤ 6 * Theta +
          6 * setup.perronRightNormMax ^ 2 * Grad + 6 * J := hexpected.2
      _ ≤ 6 * (setup.thetaInitialConstant * I +
              setup.thetaDisplacementConstant * setup.L ^ 2 * D) +
          6 * setup.perronRightNormMax ^ 2 *
            (4 * (nodeCount (Node := Node) : ℝ) ^ 2 *
                (setup.period : ℝ) * G +
              4 * (nodeCount (Node := Node) : ℝ) *
                (setup.period : ℝ) ^ 2 * setup.L ^ 2 * D +
              2 * (nodeCount (Node := Node) : ℝ) * setup.L ^ 2 * Q) +
          6 * (setup.jointNoiseResidualConstant * V) := by
        exact add_le_add
          (add_le_add (mul_le_mul_of_nonneg_left hTheta (by norm_num))
            (mul_le_mul_of_nonneg_left hGrad hrawGradScale))
          (mul_le_mul_of_nonneg_left hJ (by norm_num))
      _ = setup.unprojectedTrackerInitialCoefficient * I +
          setup.unprojectedTrackerGradientCoefficient * G +
          setup.unprojectedTrackerNoiseCoefficient * V +
          setup.unprojectedTrackerDisplacementCoefficient * setup.L ^ 2 * D +
          setup.unprojectedTrackerConsensusCoefficient * setup.L ^ 2 * Q := by
        unfold unprojectedTrackerInitialCoefficient
          unprojectedTrackerGradientCoefficient unprojectedTrackerNoiseCoefficient
          unprojectedTrackerDisplacementCoefficient
          unprojectedTrackerConsensusCoefficient
        ring

/-- Min with a paper quotient whose zero denominator is interpreted as `+∞`.
When the denominator is zero, the term imposes no additional upper-bound
constraint. -/
noncomputable def minWithPaperInfinity
    (current numerator denominator : ℝ) : ℝ :=
  if denominator = 0 then current else min current (numerator / denominator)

/-- A positive current ceiling stays positive after imposing a paper quotient
whose numerator is positive and whose denominator is nonnegative. -/
theorem minWithPaperInfinity_pos_of_pos_of_nonneg
    {current numerator denominator : ℝ}
    (hcurrent : 0 < current) (hnumerator : 0 < numerator)
    (hdenominator : 0 ≤ denominator) :
    0 < minWithPaperInfinity current numerator denominator := by
  unfold minWithPaperInfinity
  by_cases hzero : denominator = 0
  · rw [if_pos hzero]
    exact hcurrent
  · rw [if_neg hzero]
    have hdenominator_pos : 0 < denominator :=
      lt_of_le_of_ne hdenominator (Ne.symm hzero)
    exact (lt_min_iff).2 ⟨hcurrent, div_pos hnumerator hdenominator_pos⟩

/-- Imposing a paper quotient never raises the current ceiling. -/
theorem minWithPaperInfinity_le_current
    (current numerator denominator : ℝ) :
    minWithPaperInfinity current numerator denominator ≤ current := by
  unfold minWithPaperInfinity
  by_cases hzero : denominator = 0
  · rw [if_pos hzero]
  · rw [if_neg hzero]
    exact min_le_left _ _

/-- A paper quotient ceiling implies its cross-multiplied budget.  This form
also covers a zero denominator, where the paper regards the quotient as
non-constraining. -/
theorem mul_denominator_le_of_le_minWithPaperInfinity
    {current numerator denominator y : ℝ}
    (hnumerator : 0 ≤ numerator) (hdenominator : 0 ≤ denominator)
    (hy : y ≤ minWithPaperInfinity current numerator denominator) :
    y * denominator ≤ numerator := by
  unfold minWithPaperInfinity at hy
  by_cases hzero : denominator = 0
  · rw [hzero, mul_zero]
    exact hnumerator
  · rw [if_neg hzero] at hy
    have hdenominator_pos : 0 < denominator :=
      lt_of_le_of_ne hdenominator (Ne.symm hzero)
    exact (le_div_iff₀ hdenominator_pos).mp (hy.trans (min_le_right _ _))

/-- A paper quotient by an inverse square root enforces the corresponding
quadratic absorption bound, including the convention that a zero denominator
imposes no constraint. -/
theorem sq_mul_le_one_of_le_paper_inv_sqrt
    {current x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hy_le : y ≤ minWithPaperInfinity current 1 (Real.sqrt x)) :
    y ^ 2 * x ≤ 1 := by
  by_cases hzero : Real.sqrt x = 0
  · have hsqrt_sq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx
    rw [hzero] at hsqrt_sq
    nlinarith
  · have hsqrt_pos : 0 < Real.sqrt x :=
      lt_of_le_of_ne (Real.sqrt_nonneg x) (Ne.symm hzero)
    have hy_div : y ≤ 1 / Real.sqrt x := by
      unfold minWithPaperInfinity at hy_le
      rw [if_neg hzero] at hy_le
      exact hy_le.trans (min_le_right _ _)
    have hy_sqrt : y * Real.sqrt x ≤ 1 :=
      (le_div_iff₀ hsqrt_pos).mp hy_div
    have hprod_nonneg : 0 ≤ y * Real.sqrt x :=
      mul_nonneg hy (Real.sqrt_nonneg x)
    have hprod_sq : (y * Real.sqrt x) ^ 2 ≤ 1 := by
      nlinarith
    rw [mul_pow, Real.sq_sqrt hx] at hprod_sq
    exact hprod_sq

/-- Source-shaped Section 6 stability ceiling property: every
`0 < α ≤ α_st` satisfies the small-gain side conditions used to derive
(6.25)--(6.27). This is a theorem obligation, not setup data. -/
def AlphaStableSpec (alphaSt : ℝ) : Prop :=
  0 < alphaSt ∧
    ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaSt →
      ∃ LambdaQ GR aQ aD dD : ℝ,
        0 ≤ LambdaQ ∧ 0 ≤ GR ∧ 0 ≤ aQ ∧ 0 ≤ aD ∧ 0 ≤ dD ∧
          alpha ^ 2 * setup.L ^ 2 ≤ 1 ∧
            alpha ^ 2 * setup.L ^ 2 * GR * aQ ≤ 1 / 2 ∧
              alpha ^ 2 * setup.L ^ 2 * dD ≤ 1 / 2 ∧
                4 * LambdaQ * alpha ^ 2 * GR * aD * setup.L ^ 2 ≤ 1 / 2

/-- Paper formula (6.22) for `α_st` from the Section 6 constants
`Λ_Q`, `G_R`, `a_Q`, `d_D`, and `a_D`. -/
noncomputable def sectionSixAlphaStableFromConstants
    (constants : Fin 5 → ℝ) : ℝ :=
  let LambdaQ := constants ⟨0, by decide⟩
  let GR := constants ⟨1, by decide⟩
  let aQ := constants ⟨2, by decide⟩
  let dD := constants ⟨3, by decide⟩
  let aD := constants ⟨4, by decide⟩
  let m1 := minWithPaperInfinity 1 1
    (Real.sqrt (2 * GR * aQ))
  let m2 := minWithPaperInfinity m1 1
    (Real.sqrt (2 * dD))
  let m3 := minWithPaperInfinity m2 1
    (Real.sqrt (8 * LambdaQ * GR * aD))
  setup.L⁻¹ * m3

/-- Source-shaped specification for the Section 6 constants that define
`α_st` in (6.22). -/
def SectionSixStabilityConstantsSpec (constants : Fin 5 → ℝ) : Prop :=
  (∀ r : Fin 5, 0 ≤ constants r) ∧
    setup.AlphaStableSpec (setup.sectionSixAlphaStableFromConstants constants)

/-- Source-derived Section 6 constants used in the displayed `α_st` formula.
Their construction is formula-defined from the Section 6 network constants. -/
noncomputable def sectionSixStabilityConstants : Fin 5 → ℝ :=
  fun r =>
    if r = ⟨0, by decide⟩ then setup.sectionSixLambdaQFormula
    else if r = ⟨1, by decide⟩ then setup.sectionSixGradientResponseFormula
    else if r = ⟨2, by decide⟩ then setup.projectedTrackerConsensusCoefficient
    else if r = ⟨3, by decide⟩ then setup.unprojectedTrackerDisplacementCoefficient
    else setup.projectedTrackerDisplacementCoefficient

/-- The five formula-defined constants in the Section 6 stability threshold
are nonnegative. -/
theorem sectionSixStabilityConstants_nonneg
    (r : Fin 5) : 0 ≤ setup.sectionSixStabilityConstants r := by
  have hn_pos : 0 < (nodeCount (Node := Node) : ℝ) := by
    exact_mod_cast nodeCount_pos (Node := Node)
  have hp_pos : 0 < (setup.period : ℝ) := by
    exact_mod_cast setup.period_pos
  have hrate_lt : setup.contractionRate < 1 :=
    setup.PeriodicProductContraction.2.2.1
  have hden_pos : 0 < (1 - setup.contractionRate) ^ 2 :=
    pow_pos (sub_pos.mpr hrate_lt) _
  have htheta : 0 ≤ setup.thetaDisplacementConstant := by
    rw [thetaDisplacementConstant]
    exact div_nonneg (by positivity) hden_pos.le
  have hLambdaQ : 0 ≤ setup.sectionSixLambdaQFormula := by
    rw [sectionSixLambdaQFormula, unprojectedTrackerConsensusCoefficient]
    positivity
  have hGR : 0 ≤ setup.sectionSixGradientResponseFormula := by
    rw [sectionSixGradientResponseFormula]
    exact div_nonneg (sq_nonneg _) hden_pos.le
  have haQ : 0 ≤ setup.projectedTrackerConsensusCoefficient := by
    rw [projectedTrackerConsensusCoefficient]
    positivity
  have hdD : 0 ≤ setup.unprojectedTrackerDisplacementCoefficient := by
    rw [unprojectedTrackerDisplacementCoefficient]
    positivity
  have haD : 0 ≤ setup.projectedTrackerDisplacementCoefficient := by
    rw [projectedTrackerDisplacementCoefficient]
    positivity
  fin_cases r
  · simpa [sectionSixStabilityConstants] using hLambdaQ
  · simpa [sectionSixStabilityConstants] using hGR
  · simpa [sectionSixStabilityConstants] using haQ
  · simpa [sectionSixStabilityConstants] using hdD
  · simpa [sectionSixStabilityConstants] using haD

/-- The selected Section 6 stability constants satisfy the source contract. -/
theorem sectionSixStabilityConstants_spec :
    setup.SectionSixStabilityConstantsSpec setup.sectionSixStabilityConstants := by
  refine ⟨setup.sectionSixStabilityConstants_nonneg, ?_⟩
  unfold AlphaStableSpec
  simp only [sectionSixAlphaStableFromConstants]
  let LambdaQ := setup.sectionSixStabilityConstants ⟨0, by decide⟩
  let GR := setup.sectionSixStabilityConstants ⟨1, by decide⟩
  let aQ := setup.sectionSixStabilityConstants ⟨2, by decide⟩
  let dD := setup.sectionSixStabilityConstants ⟨3, by decide⟩
  let aD := setup.sectionSixStabilityConstants ⟨4, by decide⟩
  let m1 := minWithPaperInfinity 1 1 (Real.sqrt (2 * GR * aQ))
  let m2 := minWithPaperInfinity m1 1 (Real.sqrt (2 * dD))
  let m3 := minWithPaperInfinity m2 1
    (Real.sqrt (8 * LambdaQ * GR * aD))
  change 0 < setup.L⁻¹ * m3 ∧
    ∀ alpha : ℝ, 0 < alpha → alpha ≤ setup.L⁻¹ * m3 →
      ∃ LambdaQ GR aQ aD dD : ℝ,
        0 ≤ LambdaQ ∧ 0 ≤ GR ∧ 0 ≤ aQ ∧ 0 ≤ aD ∧ 0 ≤ dD ∧
          alpha ^ 2 * setup.L ^ 2 ≤ 1 ∧
            alpha ^ 2 * setup.L ^ 2 * GR * aQ ≤ 1 / 2 ∧
              alpha ^ 2 * setup.L ^ 2 * dD ≤ 1 / 2 ∧
                4 * LambdaQ * alpha ^ 2 * GR * aD * setup.L ^ 2 ≤ 1 / 2
  have hLambdaQ : 0 ≤ LambdaQ :=
    setup.sectionSixStabilityConstants_nonneg ⟨0, by decide⟩
  have hGR : 0 ≤ GR :=
    setup.sectionSixStabilityConstants_nonneg ⟨1, by decide⟩
  have haQ : 0 ≤ aQ :=
    setup.sectionSixStabilityConstants_nonneg ⟨2, by decide⟩
  have hdD : 0 ≤ dD :=
    setup.sectionSixStabilityConstants_nonneg ⟨3, by decide⟩
  have haD : 0 ≤ aD :=
    setup.sectionSixStabilityConstants_nonneg ⟨4, by decide⟩
  have hx1 : 0 ≤ 2 * GR * aQ := by positivity
  have hx2 : 0 ≤ 2 * dD := by positivity
  have hx3 : 0 ≤ 8 * LambdaQ * GR * aD := by positivity
  have hm1 : 0 < m1 :=
    minWithPaperInfinity_pos_of_pos_of_nonneg (by norm_num) (by norm_num)
      (Real.sqrt_nonneg _)
  have hm2 : 0 < m2 :=
    minWithPaperInfinity_pos_of_pos_of_nonneg hm1 (by norm_num)
      (Real.sqrt_nonneg _)
  have hm3 : 0 < m3 :=
    minWithPaperInfinity_pos_of_pos_of_nonneg hm2 (by norm_num)
      (Real.sqrt_nonneg _)
  constructor
  · exact mul_pos (inv_pos.mpr setup.L_pos) hm3
  · intro alpha halpha_pos halpha_le
    have hy_nonneg : 0 ≤ alpha * setup.L :=
      (mul_pos halpha_pos setup.L_pos).le
    have hy_le_m3 : alpha * setup.L ≤ m3 := by
      calc
        alpha * setup.L ≤ (setup.L⁻¹ * m3) * setup.L :=
          mul_le_mul_of_nonneg_right halpha_le setup.L_pos.le
        _ = m3 := by
          field_simp [ne_of_gt setup.L_pos]
    have hy_le_m2 : alpha * setup.L ≤ m2 :=
      hy_le_m3.trans
        (minWithPaperInfinity_le_current m2 1
          (Real.sqrt (8 * LambdaQ * GR * aD)))
    have hy_le_m1 : alpha * setup.L ≤ m1 :=
      hy_le_m2.trans
        (minWithPaperInfinity_le_current m1 1 (Real.sqrt (2 * dD)))
    have hy_le_one : alpha * setup.L ≤ 1 :=
      hy_le_m1.trans
        (minWithPaperInfinity_le_current 1 1 (Real.sqrt (2 * GR * aQ)))
    have hbase : (alpha * setup.L) ^ 2 ≤ 1 := by
      nlinarith
    have hgain1 : (alpha * setup.L) ^ 2 * (2 * GR * aQ) ≤ 1 :=
      sq_mul_le_one_of_le_paper_inv_sqrt hx1 hy_nonneg hy_le_m1
    have hgain2 : (alpha * setup.L) ^ 2 * (2 * dD) ≤ 1 :=
      sq_mul_le_one_of_le_paper_inv_sqrt hx2 hy_nonneg hy_le_m2
    have hgain3 :
        (alpha * setup.L) ^ 2 * (8 * LambdaQ * GR * aD) ≤ 1 :=
      sq_mul_le_one_of_le_paper_inv_sqrt hx3 hy_nonneg hy_le_m3
    refine ⟨LambdaQ, GR, aQ, aD, dD, hLambdaQ, hGR, haQ, haD, hdD, ?_⟩
    constructor
    · nlinarith [hbase]
    constructor
    · nlinarith [hgain1]
    constructor
    · nlinarith [hgain2]
    · nlinarith [hgain3]

/-- Formula-defined `Λ_Q` from the Section 6 small-gain calculation. -/
noncomputable def sectionSixLambdaQ : ℝ :=
  setup.sectionSixLambdaQFormula

/-- Formula-defined `G_R` from the Section 6 small-gain calculation. -/
noncomputable def sectionSixGradientResponse : ℝ :=
  setup.sectionSixGradientResponseFormula

/-- Formula-defined `a_Q` from the Section 6 small-gain calculation. -/
noncomputable def sectionSixConsensusFeedback : ℝ :=
  setup.projectedTrackerConsensusCoefficient

/-- Formula-defined `d_D` from the Section 6 small-gain calculation. -/
noncomputable def sectionSixDisplacementNoiseFeedback : ℝ :=
  setup.unprojectedTrackerDisplacementCoefficient

/-- Formula-defined `a_D` from the Section 6 small-gain calculation. -/
noncomputable def sectionSixDisplacementFeedback : ℝ :=
  setup.projectedTrackerDisplacementCoefficient

/-- Stability stepsize constant `α_st`, defined by the paper formula (6.22). -/
noncomputable def alphaStable : ℝ :=
  setup.sectionSixAlphaStableFromConstants setup.sectionSixStabilityConstants

/-- The selected stability ceiling satisfies its source-shaped contract. -/
theorem alphaStable_spec : setup.AlphaStableSpec setup.alphaStable :=
  by
    simpa [alphaStable] using setup.sectionSixStabilityConstants_spec.2

/-- Positivity of the selected stability ceiling. -/
theorem alphaStable_pos : 0 < setup.alphaStable :=
  setup.alphaStable_spec.1

/-- Source-shaped specification of the six final Section 6 constants
`Dhat_0`, `Dhat_g`, `Dhat_sigma`, `Qhat_0`, `Qhat_g`, and `Qhat_sigma` from
(6.25)--(6.26). The estimates are stated for the generated run at a constant
stepsize `α` satisfying `0 < α ≤ α_st`. -/
def SectionSixFinalConstantsSpec (constants : Fin 6 → ℝ) : Prop :=
  (∀ r : Fin 6, 0 ≤ constants r) ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (oracle : OracleNoiseProcess Ω Node E) (alpha : ℝ) (K : ℕ),
        setup.StochasticOracleAssumptions μ oracle →
          0 < alpha → alpha ≤ setup.alphaStable →
            let stepped := setup.withStepsize alpha
            let N := setup.completeBlockHorizon K
            stepped.displacementEnergy μ oracle N ≤
                alpha ^ 2 *
                  (constants ⟨0, by decide⟩ * setup.initialGradientHeterogeneity ^ 2 +
                    constants ⟨1, by decide⟩ *
                      stepped.blockGradientEnergy μ oracle K +
                    constants ⟨2, by decide⟩ *
                      (nodeCount (Node := Node) : ℝ) * setup.sigma ^ 2 * N) ∧
              stepped.consensusEnergy μ oracle N ≤
                alpha ^ 2 *
                  (constants ⟨3, by decide⟩ * setup.initialGradientHeterogeneity ^ 2 +
                    constants ⟨4, by decide⟩ *
                      stepped.blockGradientEnergy μ oracle K +
                    constants ⟨5, by decide⟩ *
                      (nodeCount (Node := Node) : ℝ) * setup.sigma ^ 2 * N)

/-- Formula-defined `Dhat_0 = 8Λ_QG_Ra_0+4d_0` from (6.25). -/
noncomputable def finalDisplacementInitialConstant : ℝ :=
  8 * setup.sectionSixLambdaQ * setup.sectionSixGradientResponse *
      setup.projectedTrackerInitialCoefficient +
    4 * setup.unprojectedTrackerInitialCoefficient

/-- Formula-defined `Dhat_g = 8Λ_QG_Ra_g+4d_g` from (6.25). -/
noncomputable def finalDisplacementGradientConstant : ℝ :=
  8 * setup.sectionSixLambdaQ * setup.sectionSixGradientResponse *
      setup.projectedTrackerGradientCoefficient +
    4 * setup.unprojectedTrackerGradientCoefficient

/-- Formula-defined `Dhat_sigma = 8Λ_QG_Ra_sigma+4d_sigma` from (6.25). -/
noncomputable def finalDisplacementNoiseConstant : ℝ :=
  8 * setup.sectionSixLambdaQ * setup.sectionSixGradientResponse *
      setup.projectedTrackerNoiseCoefficient +
    4 * setup.unprojectedTrackerNoiseCoefficient

/-- Formula-defined `Qhat_0 = 2G_R(a_0+a_D Dhat_0)` from (6.26). -/
noncomputable def finalConsensusInitialConstant : ℝ :=
  2 * setup.sectionSixGradientResponse *
    (setup.projectedTrackerInitialCoefficient +
      setup.projectedTrackerDisplacementCoefficient *
        setup.finalDisplacementInitialConstant)

/-- Formula-defined `Qhat_g = 2G_R(a_g+a_D Dhat_g)` from (6.26). -/
noncomputable def finalConsensusGradientConstant : ℝ :=
  2 * setup.sectionSixGradientResponse *
    (setup.projectedTrackerGradientCoefficient +
      setup.projectedTrackerDisplacementCoefficient *
        setup.finalDisplacementGradientConstant)

/-- Formula-defined `Qhat_sigma = 2G_R(a_sigma+a_D Dhat_sigma)` from (6.26). -/
noncomputable def finalConsensusNoiseConstant : ℝ :=
  2 * setup.sectionSixGradientResponse *
    (setup.projectedTrackerNoiseCoefficient +
      setup.projectedTrackerDisplacementCoefficient *
        setup.finalDisplacementNoiseConstant)

/-- Formula-defined Section 6 final constants
`(Dhat_0,Dhat_g,Dhat_sigma,Qhat_0,Qhat_g,Qhat_sigma)`. -/
noncomputable def sectionSixFinalConstants : Fin 6 → ℝ :=
  fun r =>
    if r = ⟨0, by decide⟩ then setup.finalDisplacementInitialConstant
    else if r = ⟨1, by decide⟩ then setup.finalDisplacementGradientConstant
    else if r = ⟨2, by decide⟩ then setup.finalDisplacementNoiseConstant
    else if r = ⟨3, by decide⟩ then setup.finalConsensusInitialConstant
    else if r = ⟨4, by decide⟩ then setup.finalConsensusGradientConstant
    else setup.finalConsensusNoiseConstant

/-- The six formula-defined constants in the final Section 6 estimates are
nonnegative. -/
theorem sectionSixFinalConstants_nonneg
    (r : Fin 6) : 0 ≤ setup.sectionSixFinalConstants r := by
  have hn_nonneg : 0 ≤ (nodeCount (Node := Node) : ℝ) := by positivity
  have hp_nonneg : 0 ≤ (setup.period : ℝ) := by positivity
  have hrate_nonneg : 0 ≤ setup.contractionRate :=
    setup.PeriodicProductContraction.2.1
  have hrate_lt : setup.contractionRate < 1 :=
    setup.PeriodicProductContraction.2.2.1
  have hrate_sq_lt : setup.contractionRate ^ 2 < 1 := by
    nlinarith [mul_nonneg hrate_nonneg (sub_pos.mpr hrate_lt).le]
  have hden_sq_nonneg : 0 ≤ 1 - setup.contractionRate ^ 2 :=
    (sub_pos.mpr hrate_sq_lt).le
  have htheta_initial : 0 ≤ setup.thetaInitialConstant := by
    rw [thetaInitialConstant]
    exact div_nonneg (by positivity) hden_sq_nonneg
  have hjoint_noise : 0 ≤ setup.jointNoiseResidualConstant := by
    rw [jointNoiseResidualConstant]
    exact add_nonneg (by norm_num)
      (div_nonneg (by positivity) hden_sq_nonneg)
  have ha0 : 0 ≤ setup.projectedTrackerInitialCoefficient := by
    rw [projectedTrackerInitialCoefficient]
    positivity
  have hag : 0 ≤ setup.projectedTrackerGradientCoefficient := by
    rw [projectedTrackerGradientCoefficient]
    positivity
  have hasigma : 0 ≤ setup.projectedTrackerNoiseCoefficient := by
    rw [projectedTrackerNoiseCoefficient]
    positivity
  have hd0 : 0 ≤ setup.unprojectedTrackerInitialCoefficient := by
    rw [unprojectedTrackerInitialCoefficient]
    positivity
  have hdg : 0 ≤ setup.unprojectedTrackerGradientCoefficient := by
    rw [unprojectedTrackerGradientCoefficient]
    positivity
  have hdsigma : 0 ≤ setup.unprojectedTrackerNoiseCoefficient := by
    rw [unprojectedTrackerNoiseCoefficient]
    positivity
  have hLambdaQ : 0 ≤ setup.sectionSixLambdaQ := by
    simpa [sectionSixLambdaQ, sectionSixStabilityConstants] using
      setup.sectionSixStabilityConstants_nonneg ⟨0, by decide⟩
  have hGR : 0 ≤ setup.sectionSixGradientResponse := by
    simpa [sectionSixGradientResponse, sectionSixStabilityConstants] using
      setup.sectionSixStabilityConstants_nonneg ⟨1, by decide⟩
  have haD : 0 ≤ setup.projectedTrackerDisplacementCoefficient := by
    simpa [sectionSixStabilityConstants] using
      setup.sectionSixStabilityConstants_nonneg ⟨4, by decide⟩
  have hD0 : 0 ≤ setup.finalDisplacementInitialConstant := by
    rw [finalDisplacementInitialConstant]
    positivity
  have hDg : 0 ≤ setup.finalDisplacementGradientConstant := by
    rw [finalDisplacementGradientConstant]
    positivity
  have hDsigma : 0 ≤ setup.finalDisplacementNoiseConstant := by
    rw [finalDisplacementNoiseConstant]
    positivity
  have hQ0 : 0 ≤ setup.finalConsensusInitialConstant := by
    rw [finalConsensusInitialConstant]
    positivity
  have hQg : 0 ≤ setup.finalConsensusGradientConstant := by
    rw [finalConsensusGradientConstant]
    positivity
  have hQsigma : 0 ≤ setup.finalConsensusNoiseConstant := by
    rw [finalConsensusNoiseConstant]
    positivity
  fin_cases r
  · simpa [sectionSixFinalConstants] using hD0
  · simpa [sectionSixFinalConstants] using hDg
  · simpa [sectionSixFinalConstants] using hDsigma
  · simpa [sectionSixFinalConstants] using hQ0
  · simpa [sectionSixFinalConstants] using hQg
  · simpa [sectionSixFinalConstants] using hQsigma

/-- The explicit formula for `alphaStable` enforces the four small-gain
inequalities for the actual Section 6 constants, not merely for existential
witnesses in `AlphaStableSpec`. -/
theorem alphaStable_formula_absorption
    {alpha : ℝ} (halpha_pos : 0 < alpha)
    (halpha_le : alpha ≤ setup.alphaStable) :
    alpha ^ 2 * setup.L ^ 2 ≤ 1 ∧
      alpha ^ 2 * setup.L ^ 2 * setup.sectionSixGradientResponse *
          setup.sectionSixConsensusFeedback ≤ 1 / 2 ∧
        alpha ^ 2 * setup.L ^ 2 * setup.sectionSixDisplacementNoiseFeedback ≤
            1 / 2 ∧
          4 * setup.sectionSixLambdaQ * alpha ^ 2 *
              setup.sectionSixGradientResponse * setup.sectionSixDisplacementFeedback *
              setup.L ^ 2 ≤ 1 / 2 := by
  let LambdaQ := setup.sectionSixLambdaQ
  let GR := setup.sectionSixGradientResponse
  let aQ := setup.sectionSixConsensusFeedback
  let dD := setup.sectionSixDisplacementNoiseFeedback
  let aD := setup.sectionSixDisplacementFeedback
  let m1 := minWithPaperInfinity 1 1 (Real.sqrt (2 * GR * aQ))
  let m2 := minWithPaperInfinity m1 1 (Real.sqrt (2 * dD))
  let m3 := minWithPaperInfinity m2 1
    (Real.sqrt (8 * LambdaQ * GR * aD))
  change alpha ≤ setup.L⁻¹ * m3 at halpha_le
  have hLambdaQ : 0 ≤ LambdaQ := by
    simpa [LambdaQ, sectionSixLambdaQ, sectionSixStabilityConstants] using
      setup.sectionSixStabilityConstants_nonneg ⟨0, by decide⟩
  have hGR : 0 ≤ GR := by
    simpa [GR, sectionSixGradientResponse, sectionSixStabilityConstants] using
      setup.sectionSixStabilityConstants_nonneg ⟨1, by decide⟩
  have haQ : 0 ≤ aQ := by
    simpa [aQ, sectionSixConsensusFeedback, sectionSixStabilityConstants] using
      setup.sectionSixStabilityConstants_nonneg ⟨2, by decide⟩
  have hdD : 0 ≤ dD := by
    simpa [dD, sectionSixDisplacementNoiseFeedback,
      sectionSixStabilityConstants] using
      setup.sectionSixStabilityConstants_nonneg ⟨3, by decide⟩
  have haD : 0 ≤ aD := by
    simpa [aD, sectionSixDisplacementFeedback, sectionSixStabilityConstants] using
      setup.sectionSixStabilityConstants_nonneg ⟨4, by decide⟩
  have hx1 : 0 ≤ 2 * GR * aQ := by positivity
  have hx2 : 0 ≤ 2 * dD := by positivity
  have hx3 : 0 ≤ 8 * LambdaQ * GR * aD := by positivity
  have hy_nonneg : 0 ≤ alpha * setup.L :=
    (mul_pos halpha_pos setup.L_pos).le
  have hy_le_m3 : alpha * setup.L ≤ m3 := by
    calc
      alpha * setup.L ≤ (setup.L⁻¹ * m3) * setup.L :=
        mul_le_mul_of_nonneg_right halpha_le setup.L_pos.le
      _ = m3 := by field_simp [ne_of_gt setup.L_pos]
  have hy_le_m2 : alpha * setup.L ≤ m2 :=
    hy_le_m3.trans
      (minWithPaperInfinity_le_current m2 1
        (Real.sqrt (8 * LambdaQ * GR * aD)))
  have hy_le_m1 : alpha * setup.L ≤ m1 :=
    hy_le_m2.trans
      (minWithPaperInfinity_le_current m1 1 (Real.sqrt (2 * dD)))
  have hy_le_one : alpha * setup.L ≤ 1 :=
    hy_le_m1.trans
      (minWithPaperInfinity_le_current 1 1 (Real.sqrt (2 * GR * aQ)))
  have hbase : (alpha * setup.L) ^ 2 ≤ 1 := by nlinarith
  have hgain1 : (alpha * setup.L) ^ 2 * (2 * GR * aQ) ≤ 1 :=
    sq_mul_le_one_of_le_paper_inv_sqrt hx1 hy_nonneg hy_le_m1
  have hgain2 : (alpha * setup.L) ^ 2 * (2 * dD) ≤ 1 :=
    sq_mul_le_one_of_le_paper_inv_sqrt hx2 hy_nonneg hy_le_m2
  have hgain3 : (alpha * setup.L) ^ 2 * (8 * LambdaQ * GR * aD) ≤ 1 :=
    sq_mul_le_one_of_le_paper_inv_sqrt hx3 hy_nonneg hy_le_m3
  change alpha ^ 2 * setup.L ^ 2 ≤ 1 ∧
    alpha ^ 2 * setup.L ^ 2 * GR * aQ ≤ 1 / 2 ∧
      alpha ^ 2 * setup.L ^ 2 * dD ≤ 1 / 2 ∧
        4 * LambdaQ * alpha ^ 2 * GR * aD * setup.L ^ 2 ≤ 1 / 2
  constructor
  · nlinarith [hbase]
  constructor
  · nlinarith [hgain1]
  constructor
  · nlinarith [hgain2]
  · nlinarith [hgain3]

/-- Scalar small-gain calculation taking the raw Section 6 recurrences
(6.19) and (6.21) to the closed estimates (6.25) and (6.26). -/
theorem sectionSix_coupled_energy_absorption
    {alpha L LambdaQ GR kappa dQL a0 ag aD aQ asigma
      d0 dg dD dsigma I G V D Q : ℝ}
    (halpha : 0 ≤ alpha) (hL : 0 ≤ L)
    (hLambdaQ : 0 ≤ LambdaQ) (hGR : 0 ≤ GR)
    (hkappa : 0 ≤ kappa) (hdQL : 0 ≤ dQL)
    (ha0 : 0 ≤ a0) (hag : 0 ≤ ag) (haD : 0 ≤ aD)
    (haQ : 0 ≤ aQ) (hasigma : 0 ≤ asigma)
    (hd0 : 0 ≤ d0) (hdg : 0 ≤ dg) (hdD : 0 ≤ dD)
    (hdsigma : 0 ≤ dsigma)
    (hI : 0 ≤ I) (hG : 0 ≤ G) (hV : 0 ≤ V)
    (hD : 0 ≤ D) (hQ : 0 ≤ Q)
    (hLambdaQ_eq : LambdaQ = kappa + dQL)
    (hbase : alpha ^ 2 * L ^ 2 ≤ 1)
    (hQfeedback : alpha ^ 2 * L ^ 2 * GR * aQ ≤ 1 / 2)
    (hDfeedback : alpha ^ 2 * L ^ 2 * dD ≤ 1 / 2)
    (hcross : 4 * LambdaQ * alpha ^ 2 * GR * aD * L ^ 2 ≤ 1 / 2)
    (hrawQ :
      Q ≤ alpha ^ 2 * GR *
        (a0 * I + ag * G + asigma * V + aD * L ^ 2 * D + aQ * L ^ 2 * Q))
    (hrawD :
      D ≤ kappa * Q + alpha ^ 2 *
        (d0 * I + dg * G + dsigma * V + dD * L ^ 2 * D + dQL * L ^ 2 * Q)) :
    D ≤ alpha ^ 2 *
        ((8 * LambdaQ * GR * a0 + 4 * d0) * I +
          (8 * LambdaQ * GR * ag + 4 * dg) * G +
          (8 * LambdaQ * GR * asigma + 4 * dsigma) * V) ∧
      Q ≤ alpha ^ 2 *
        (2 * GR * (a0 + aD * (8 * LambdaQ * GR * a0 + 4 * d0)) * I +
          2 * GR * (ag + aD * (8 * LambdaQ * GR * ag + 4 * dg)) * G +
          2 * GR * (asigma + aD *
            (8 * LambdaQ * GR * asigma + 4 * dsigma)) * V) := by
  let UQ : ℝ := a0 * I + ag * G + asigma * V
  let UD : ℝ := d0 * I + dg * G + dsigma * V
  let DH : ℝ := 8 * LambdaQ * GR * UQ + 4 * UD
  have hUQ : 0 ≤ UQ := by
    dsimp [UQ]
    positivity
  have hUD : 0 ≤ UD := by
    dsimp [UD]
    positivity
  have hDH : 0 ≤ DH := by
    dsimp [DH]
    positivity
  have hQfeedback_mul :
      alpha ^ 2 * L ^ 2 * GR * aQ * Q ≤ (1 / 2) * Q :=
    mul_le_mul_of_nonneg_right hQfeedback hQ
  have hQabs : Q ≤ 2 * alpha ^ 2 * GR * (UQ + aD * L ^ 2 * D) := by
    dsimp [UQ]
    nlinarith [hrawQ, hQfeedback_mul]
  have hdQL_scaled :
      alpha ^ 2 * dQL * L ^ 2 * Q ≤ dQL * Q := by
    have := mul_le_mul_of_nonneg_right hbase (mul_nonneg hdQL hQ)
    nlinarith
  have hDfeedback_mul :
      alpha ^ 2 * dD * L ^ 2 * D ≤ (1 / 2) * D := by
    have := mul_le_mul_of_nonneg_right hDfeedback hD
    nlinarith
  have hrawD' :
      D ≤ kappa * Q + alpha ^ 2 * UD +
        alpha ^ 2 * dD * L ^ 2 * D + alpha ^ 2 * dQL * L ^ 2 * Q := by
    calc
      D ≤ kappa * Q + alpha ^ 2 *
          (d0 * I + dg * G + dsigma * V +
            dD * L ^ 2 * D + dQL * L ^ 2 * Q) := hrawD
      _ = kappa * Q + alpha ^ 2 * UD +
          alpha ^ 2 * dD * L ^ 2 * D +
            alpha ^ 2 * dQL * L ^ 2 * Q := by
        dsimp [UD]
        ring
  have hDraw_absorbed :
      D ≤ kappa * Q + alpha ^ 2 * UD + (1 / 2) * D + dQL * Q :=
    hrawD'.trans
      (add_le_add (add_le_add le_rfl hDfeedback_mul) hdQL_scaled)
  have hDabs : D ≤ 2 * LambdaQ * Q + 2 * alpha ^ 2 * UD := by
    rw [hLambdaQ_eq]
    linarith
  have hQabs_scaled :
      2 * LambdaQ * Q ≤
        2 * LambdaQ * (2 * alpha ^ 2 * GR * (UQ + aD * L ^ 2 * D)) := by
    exact mul_le_mul_of_nonneg_left hQabs
      (mul_nonneg (by norm_num) hLambdaQ)
  have hDpre :
      D ≤ 4 * LambdaQ * alpha ^ 2 * GR * UQ + 2 * alpha ^ 2 * UD +
        4 * LambdaQ * alpha ^ 2 * GR * aD * L ^ 2 * D := by
    calc
      D ≤ 2 * LambdaQ * Q + 2 * alpha ^ 2 * UD := hDabs
      _ ≤ 2 * LambdaQ * (2 * alpha ^ 2 * GR *
            (UQ + aD * L ^ 2 * D)) + 2 * alpha ^ 2 * UD :=
        add_le_add hQabs_scaled le_rfl
      _ = 4 * LambdaQ * alpha ^ 2 * GR * UQ + 2 * alpha ^ 2 * UD +
            4 * LambdaQ * alpha ^ 2 * GR * aD * L ^ 2 * D := by ring
  have hcross_mul :
      4 * LambdaQ * alpha ^ 2 * GR * aD * L ^ 2 * D ≤ (1 / 2) * D :=
    mul_le_mul_of_nonneg_right hcross hD
  have hDclosed_aggregate : D ≤ alpha ^ 2 * DH := by
    calc
      D ≤ 2 * (4 * LambdaQ * alpha ^ 2 * GR * UQ +
          2 * alpha ^ 2 * UD) := by linarith [hDpre, hcross_mul]
      _ = alpha ^ 2 * DH := by
        dsimp [DH]
        ring
  have hL2D : L ^ 2 * D ≤ DH := by
    calc
      L ^ 2 * D ≤ L ^ 2 * (alpha ^ 2 * DH) :=
        mul_le_mul_of_nonneg_left hDclosed_aggregate (sq_nonneg L)
      _ = (alpha ^ 2 * L ^ 2) * DH := by ring
      _ ≤ 1 * DH := mul_le_mul_of_nonneg_right hbase hDH
      _ = DH := one_mul DH
  have hQclosed_aggregate : Q ≤ alpha ^ 2 * (2 * GR * (UQ + aD * DH)) := by
    have haD_scaled : aD * L ^ 2 * D ≤ aD * DH := by
      calc
        aD * L ^ 2 * D = aD * (L ^ 2 * D) := by ring
        _ ≤ aD * DH := mul_le_mul_of_nonneg_left hL2D haD
    have hinside : UQ + aD * L ^ 2 * D ≤ UQ + aD * DH :=
      add_le_add le_rfl haD_scaled
    have hscale : 0 ≤ 2 * alpha ^ 2 * GR := by positivity
    calc
      Q ≤ 2 * alpha ^ 2 * GR * (UQ + aD * L ^ 2 * D) := hQabs
      _ ≤ 2 * alpha ^ 2 * GR * (UQ + aD * DH) :=
        mul_le_mul_of_nonneg_left hinside hscale
      _ = alpha ^ 2 * (2 * GR * (UQ + aD * DH)) := by ring
  constructor
  · calc
      D ≤ alpha ^ 2 * DH := hDclosed_aggregate
      _ = alpha ^ 2 *
          ((8 * LambdaQ * GR * a0 + 4 * d0) * I +
            (8 * LambdaQ * GR * ag + 4 * dg) * G +
            (8 * LambdaQ * GR * asigma + 4 * dsigma) * V) := by
        dsimp [DH, UQ, UD]
        ring
  · calc
      Q ≤ alpha ^ 2 * (2 * GR * (UQ + aD * DH)) := hQclosed_aggregate
      _ = alpha ^ 2 *
          (2 * GR * (a0 + aD * (8 * LambdaQ * GR * a0 + 4 * d0)) * I +
            2 * GR * (ag + aD * (8 * LambdaQ * GR * ag + 4 * dg)) * G +
            2 * GR * (asigma + aD *
              (8 * LambdaQ * GR * asigma + 4 * dsigma)) * V) := by
        dsimp [DH, UQ, UD]
        ring

/-- The formula-defined Section 6 constants satisfy the final D/Q estimates. -/
theorem sectionSixFinalConstants_spec :
    setup.SectionSixFinalConstantsSpec setup.sectionSixFinalConstants := by
  unfold SectionSixFinalConstantsSpec
  constructor
  · exact setup.sectionSixFinalConstants_nonneg
  · intro Ω _ _ _ μ _ oracle alpha K horacle halpha_pos halpha_le
    let stepped := setup.withStepsize alpha
    let N := setup.completeBlockHorizon K
    let I := setup.initialGradientHeterogeneity ^ 2
    let G := stepped.blockGradientEnergy μ oracle K
    let V := (nodeCount (Node := Node) : ℝ) * setup.sigma ^ 2 * N
    let D := stepped.displacementEnergy μ oracle N
    let Q := stepped.consensusEnergy μ oracle N
    have _hsourceWitness :=
      setup.alphaStable_spec.2 alpha halpha_pos halpha_le
    have hsmall := setup.alphaStable_formula_absorption halpha_pos halpha_le
    have hrate_nonneg : 0 ≤ setup.contractionRate :=
      setup.PeriodicProductContraction.2.1
    have hrate_lt : setup.contractionRate < 1 :=
      setup.PeriodicProductContraction.2.2.1
    have hrate_sq_lt : setup.contractionRate ^ 2 < 1 := by
      nlinarith [mul_nonneg hrate_nonneg (sub_pos.mpr hrate_lt).le]
    have hden_sq_nonneg : 0 ≤ 1 - setup.contractionRate ^ 2 :=
      (sub_pos.mpr hrate_sq_lt).le
    have htheta_initial : 0 ≤ setup.thetaInitialConstant := by
      rw [thetaInitialConstant]
      exact div_nonneg (by positivity) hden_sq_nonneg
    have hjoint_noise : 0 ≤ setup.jointNoiseResidualConstant := by
      rw [jointNoiseResidualConstant]
      exact add_nonneg (by norm_num)
        (div_nonneg (by positivity) hden_sq_nonneg)
    have hLambdaQ : 0 ≤ setup.sectionSixLambdaQ := by
      simpa [sectionSixLambdaQ, sectionSixStabilityConstants] using
        setup.sectionSixStabilityConstants_nonneg ⟨0, by decide⟩
    have hGR : 0 ≤ setup.sectionSixGradientResponse := by
      simpa [sectionSixGradientResponse, sectionSixStabilityConstants] using
        setup.sectionSixStabilityConstants_nonneg ⟨1, by decide⟩
    have haQ : 0 ≤ setup.projectedTrackerConsensusCoefficient := by
      simpa [sectionSixStabilityConstants] using
        setup.sectionSixStabilityConstants_nonneg ⟨2, by decide⟩
    have hdD : 0 ≤ setup.unprojectedTrackerDisplacementCoefficient := by
      simpa [sectionSixStabilityConstants] using
        setup.sectionSixStabilityConstants_nonneg ⟨3, by decide⟩
    have haD : 0 ≤ setup.projectedTrackerDisplacementCoefficient := by
      simpa [sectionSixStabilityConstants] using
        setup.sectionSixStabilityConstants_nonneg ⟨4, by decide⟩
    have ha0 : 0 ≤ setup.projectedTrackerInitialCoefficient := by
      rw [projectedTrackerInitialCoefficient]
      positivity
    have hag : 0 ≤ setup.projectedTrackerGradientCoefficient := by
      rw [projectedTrackerGradientCoefficient]
      positivity
    have hasigma : 0 ≤ setup.projectedTrackerNoiseCoefficient := by
      rw [projectedTrackerNoiseCoefficient]
      positivity
    have hd0 : 0 ≤ setup.unprojectedTrackerInitialCoefficient := by
      rw [unprojectedTrackerInitialCoefficient]
      positivity
    have hdg : 0 ≤ setup.unprojectedTrackerGradientCoefficient := by
      rw [unprojectedTrackerGradientCoefficient]
      positivity
    have hdQL : 0 ≤ setup.unprojectedTrackerConsensusCoefficient := by
      rw [unprojectedTrackerConsensusCoefficient]
      positivity
    have hdsigma : 0 ≤ setup.unprojectedTrackerNoiseCoefficient := by
      rw [unprojectedTrackerNoiseCoefficient]
      positivity
    have hI : 0 ≤ I := by
      dsimp [I]
      positivity
    have hG : 0 ≤ G := by
      dsimp [G, stepped, blockGradientEnergy]
      positivity
    have hV : 0 ≤ V := by
      dsimp [V]
      positivity
    have hD : 0 ≤ D := by
      dsimp [D, stepped, displacementEnergy]
      apply Finset.sum_nonneg
      intro t _ht
      apply integral_nonneg
      intro ω
      unfold frobeniusNormSq
      positivity
    have hQ : 0 ≤ Q := by
      dsimp [Q, stepped, consensusEnergy]
      apply Finset.sum_nonneg
      intro t _ht
      apply integral_nonneg
      intro ω
      unfold frobeniusNormSq
      positivity
    let P := Finset.sum (Finset.range N) (fun t =>
      ∫ ω, frobeniusNormSq (Node := Node) (E := E)
        (consensusError (Node := Node) (E := E)
          (stepped.trackerState (oracle.noise ω) t)) ∂μ)
    let Y := Finset.sum (Finset.range N) (fun t =>
      ∫ ω, frobeniusNormSq (Node := Node) (E := E)
        (stepped.trackerState (oracle.noise ω) t) ∂μ)
    have hsourceBudgets :
        P ≤ setup.projectedTrackerInitialCoefficient * I +
              setup.projectedTrackerGradientCoefficient * G +
              setup.projectedTrackerNoiseCoefficient * V +
              setup.projectedTrackerDisplacementCoefficient * setup.L ^ 2 * D +
              setup.projectedTrackerConsensusCoefficient * setup.L ^ 2 * Q ∧
          2 * Y ≤ setup.unprojectedTrackerInitialCoefficient * I +
              setup.unprojectedTrackerGradientCoefficient * G +
              setup.unprojectedTrackerNoiseCoefficient * V +
              setup.unprojectedTrackerDisplacementCoefficient * setup.L ^ 2 * D +
              setup.unprojectedTrackerConsensusCoefficient * setup.L ^ 2 * Q ∧
          D ≤ (2 * setup.pushDeviationNormMax ^ 2) * Q +
              2 * alpha ^ 2 * Y := by
      have horacle_stepped : stepped.StochasticOracleAssumptions μ oracle := by
        simpa [stepped, withStepsize, StochasticOracleAssumptions] using horacle
      have hdisplacement :
          D ≤ (2 * setup.pushDeviationNormMax ^ 2) * Q +
              2 * alpha ^ 2 * Y := by
        simpa [D, Q, Y, stepped, pushDeviationNormMax, periodMax] using
          (stepped.displacement_energy_le_consensus_tracker
            μ oracle horacle_stepped N)
      have htrackerBudgets :
          P ≤ setup.projectedTrackerInitialCoefficient * I +
                setup.projectedTrackerGradientCoefficient * G +
                setup.projectedTrackerNoiseCoefficient * V +
                setup.projectedTrackerDisplacementCoefficient * setup.L ^ 2 * D +
                setup.projectedTrackerConsensusCoefficient * setup.L ^ 2 * Q ∧
            2 * Y ≤ setup.unprojectedTrackerInitialCoefficient * I +
                setup.unprojectedTrackerGradientCoefficient * G +
                setup.unprojectedTrackerNoiseCoefficient * V +
                setup.unprojectedTrackerDisplacementCoefficient * setup.L ^ 2 * D +
                setup.unprojectedTrackerConsensusCoefficient * setup.L ^ 2 * Q := by
        have hmean := stepped.meanJointCoordinate_energy_bound
          μ oracle horacle_stepped N
        have hnoise := stepped.noiseJointCoordinate_secondMoment_bound
          μ oracle horacle_stepped
        have hallgrad := stepped.allTimeAverageGradient_energy_bound
          μ oracle K horacle_stepped
        simpa [P, Y, I, G, V, D, Q, N, stepped, withStepsize] using
          (stepped.tracker_budgets_of_joint_coordinate_bounds
            μ oracle K horacle_stepped hmean hnoise hallgrad)
      exact ⟨htrackerBudgets.1, htrackerBudgets.2, hdisplacement⟩
    have hQ_convolution :
        Q ≤ alpha ^ 2 * setup.sectionSixGradientResponse * P := by
      simpa [Q, P, stepped, sectionSixGradientResponse] using
        setup.expectation_level_consensus_convolution
          μ oracle alpha horacle halpha_pos N
    have hraw :
        Q ≤ alpha ^ 2 * setup.sectionSixGradientResponse *
            (setup.projectedTrackerInitialCoefficient * I +
              setup.projectedTrackerGradientCoefficient * G +
              setup.projectedTrackerNoiseCoefficient * V +
              setup.projectedTrackerDisplacementCoefficient * setup.L ^ 2 * D +
              setup.projectedTrackerConsensusCoefficient * setup.L ^ 2 * Q) ∧
          D ≤ (2 * setup.pushDeviationNormMax ^ 2) * Q + alpha ^ 2 *
            (setup.unprojectedTrackerInitialCoefficient * I +
              setup.unprojectedTrackerGradientCoefficient * G +
              setup.unprojectedTrackerNoiseCoefficient * V +
              setup.unprojectedTrackerDisplacementCoefficient * setup.L ^ 2 * D +
              setup.unprojectedTrackerConsensusCoefficient * setup.L ^ 2 * Q) := by
      constructor
      · exact hQ_convolution.trans
          (mul_le_mul_of_nonneg_left hsourceBudgets.1
            (mul_nonneg (sq_nonneg alpha) hGR))
      · calc
          D ≤ (2 * setup.pushDeviationNormMax ^ 2) * Q +
                2 * alpha ^ 2 * Y := hsourceBudgets.2.2
          _ = (2 * setup.pushDeviationNormMax ^ 2) * Q +
                alpha ^ 2 * (2 * Y) := by ring
          _ ≤ (2 * setup.pushDeviationNormMax ^ 2) * Q + alpha ^ 2 *
              (setup.unprojectedTrackerInitialCoefficient * I +
                setup.unprojectedTrackerGradientCoefficient * G +
                setup.unprojectedTrackerNoiseCoefficient * V +
                setup.unprojectedTrackerDisplacementCoefficient * setup.L ^ 2 * D +
                setup.unprojectedTrackerConsensusCoefficient * setup.L ^ 2 * Q) :=
            add_le_add le_rfl
              (mul_le_mul_of_nonneg_left hsourceBudgets.2.1 (sq_nonneg alpha))
    have hclosed := sectionSix_coupled_energy_absorption
      (halpha := halpha_pos.le) (hL := setup.L_pos.le)
      (hLambdaQ := hLambdaQ) (hGR := hGR)
      (hkappa := by positivity) (hdQL := hdQL)
      (ha0 := ha0) (hag := hag) (haD := haD) (haQ := haQ)
      (hasigma := hasigma) (hd0 := hd0) (hdg := hdg) (hdD := hdD)
      (hdsigma := hdsigma) (hI := hI) (hG := hG) (hV := hV)
      (hD := hD) (hQ := hQ)
      (hLambdaQ_eq := by
        rw [sectionSixLambdaQ, sectionSixLambdaQFormula])
      (hbase := hsmall.1) (hQfeedback := hsmall.2.1)
      (hDfeedback := hsmall.2.2.1) (hcross := hsmall.2.2.2)
      (hrawQ := hraw.1) (hrawD := hraw.2)
    simpa [stepped, N, I, G, V, D, Q, sectionSixFinalConstants,
      finalDisplacementInitialConstant, finalDisplacementGradientConstant,
      finalDisplacementNoiseConstant, finalConsensusInitialConstant,
      finalConsensusGradientConstant, finalConsensusNoiseConstant,
      sectionSixGradientResponse, sectionSixConsensusFeedback,
      sectionSixDisplacementNoiseFeedback, sectionSixDisplacementFeedback,
      mul_assoc] using hclosed

/-- Universe-polymorphic form of the final displacement and consensus estimates
from equations (6.25)--(6.26). -/
theorem SectionSixFinalDisplacementConsensusEstimates_universe
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E) (alpha : ℝ) (K : ℕ)
    (horacle : setup.StochasticOracleAssumptions μ oracle)
    (halpha_pos : 0 < alpha) (halpha_le : alpha ≤ setup.alphaStable) :
    let stepped := setup.withStepsize alpha
    let N := setup.completeBlockHorizon K
    stepped.displacementEnergy μ oracle N ≤
        alpha ^ 2 *
          (setup.finalDisplacementInitialConstant *
              setup.initialGradientHeterogeneity ^ 2 +
            setup.finalDisplacementGradientConstant *
              stepped.blockGradientEnergy μ oracle K +
            setup.finalDisplacementNoiseConstant *
              (nodeCount (Node := Node) : ℝ) * setup.sigma ^ 2 * N) ∧
      stepped.consensusEnergy μ oracle N ≤
        alpha ^ 2 *
          (setup.finalConsensusInitialConstant *
              setup.initialGradientHeterogeneity ^ 2 +
            setup.finalConsensusGradientConstant *
              stepped.blockGradientEnergy μ oracle K +
            setup.finalConsensusNoiseConstant *
              (nodeCount (Node := Node) : ℝ) * setup.sigma ^ 2 * N) := by
  simpa [finalDisplacementInitialConstant, finalDisplacementGradientConstant,
    finalDisplacementNoiseConstant, finalConsensusInitialConstant,
    finalConsensusGradientConstant, finalConsensusNoiseConstant] using
    setup.sectionSixFinalConstants_spec.2 μ oracle alpha K horacle halpha_pos halpha_le

/-- Equations (6.25)--(6.26): final displacement and consensus estimates for
the complete block horizon `N = Kp`. This named theorem exposes the Section 6
output layer used later in Theorem 7.1. -/
theorem SectionSixFinalDisplacementConsensusEstimates
    {Ω : Type} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E) (alpha : ℝ) (K : ℕ)
    (horacle : setup.StochasticOracleAssumptions μ oracle)
    (halpha_pos : 0 < alpha) (halpha_le : alpha ≤ setup.alphaStable) :
    let stepped := setup.withStepsize alpha
    let N := setup.completeBlockHorizon K
    stepped.displacementEnergy μ oracle N ≤
        alpha ^ 2 *
          (setup.finalDisplacementInitialConstant *
              setup.initialGradientHeterogeneity ^ 2 +
            setup.finalDisplacementGradientConstant *
              stepped.blockGradientEnergy μ oracle K +
            setup.finalDisplacementNoiseConstant *
              (nodeCount (Node := Node) : ℝ) * setup.sigma ^ 2 * N) ∧
      stepped.consensusEnergy μ oracle N ≤
        alpha ^ 2 *
          (setup.finalConsensusInitialConstant *
              setup.initialGradientHeterogeneity ^ 2 +
            setup.finalConsensusGradientConstant *
              stepped.blockGradientEnergy μ oracle K +
            setup.finalConsensusNoiseConstant *
              (nodeCount (Node := Node) : ℝ) * setup.sigma ^ 2 * N) := by
  exact setup.SectionSixFinalDisplacementConsensusEstimates_universe
    μ oracle alpha K horacle halpha_pos halpha_le

/- A scalar row acting on a Hilbert-valued state is controlled by the
Euclidean/Frobenius product.  This is the tensor Cauchy--Schwarz estimate used
for the weighted-center term in (6.13). -/
theorem weightedState_sq_le_rowNormSq_mul_frobeniusNormSq
    (w : RowVector Node) (X : State Node E) :
    ‖weightedState (Node := Node) (E := E) w X‖ ^ 2 ≤
      rowNormSq (Node := Node) w *
        frobeniusNormSq (Node := Node) (E := E) X := by
  classical
  have hnorm :
      ‖weightedState (Node := Node) (E := E) w X‖ ≤
        ∑ i : Node, |w i| * ‖X i‖ := by
    calc
      ‖weightedState (Node := Node) (E := E) w X‖ =
          ‖∑ i : Node, w i • X i‖ := rfl
      _ ≤ ∑ i : Node, ‖w i • X i‖ := norm_sum_le _ _
      _ = ∑ i : Node, |w i| * ‖X i‖ := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [norm_smul, Real.norm_eq_abs]
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset Node)
    (fun i : Node => |w i|) (fun i : Node => ‖X i‖)
  have hsqrt_nonneg :
      0 ≤ Real.sqrt (∑ i : Node, |w i| ^ 2) *
        Real.sqrt (∑ i : Node, ‖X i‖ ^ 2) := by positivity
  have hbound := hnorm.trans hcs
  have hsquare :=
    (sq_le_sq₀ (norm_nonneg _) hsqrt_nonneg).2 hbound
  rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at hsquare
  simpa [rowNormSq, frobeniusNormSq, sq_abs] using hsquare

/- Cauchy--Schwarz across a finite family of row-state contractions.  Applying
the one-row tensor estimate before the outer scalar Cauchy--Schwarz avoids the
cardinality loss from a generic squared norm-of-sum bound. -/
theorem finset_weightedState_sum_sq_le_product_energies
    {ι : Type*} (s : Finset ι) (w : ι → RowVector Node)
    (X : ι → State Node E) :
    ‖∑ r ∈ s, weightedState (Node := Node) (E := E) (w r) (X r)‖ ^ 2 ≤
      (∑ r ∈ s, rowNormSq (Node := Node) (w r)) *
        ∑ r ∈ s, frobeniusNormSq (Node := Node) (E := E) (X r) := by
  classical
  have hrow_nonneg (r : ι) :
      0 ≤ rowNormSq (Node := Node) (w r) := by
    unfold rowNormSq
    positivity
  have hfrob_nonneg (r : ι) :
      0 ≤ frobeniusNormSq (Node := Node) (E := E) (X r) := by
    unfold frobeniusNormSq
    positivity
  have hpoint (r : ι) :
      ‖weightedState (Node := Node) (E := E) (w r) (X r)‖ ≤
        Real.sqrt (rowNormSq (Node := Node) (w r)) *
          Real.sqrt (frobeniusNormSq (Node := Node) (E := E) (X r)) := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt (hrow_nonneg r),
      Real.sq_sqrt (hfrob_nonneg r)]
    exact weightedState_sq_le_rowNormSq_mul_frobeniusNormSq
      (Node := Node) (E := E) (w r) (X r)
  have hnorm :
      ‖∑ r ∈ s, weightedState (Node := Node) (E := E) (w r) (X r)‖ ≤
        ∑ r ∈ s,
          Real.sqrt (rowNormSq (Node := Node) (w r)) *
            Real.sqrt (frobeniusNormSq (Node := Node) (E := E) (X r)) := by
    calc
      _ ≤ ∑ r ∈ s,
          ‖weightedState (Node := Node) (E := E) (w r) (X r)‖ :=
        norm_sum_le _ _
      _ ≤ _ := Finset.sum_le_sum fun r _hr => hpoint r
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt s
    (fun r => Real.sqrt (rowNormSq (Node := Node) (w r)))
    (fun r => Real.sqrt (frobeniusNormSq (Node := Node) (E := E) (X r)))
  have hsqrt_nonneg :
      0 ≤ Real.sqrt
          (∑ r ∈ s, Real.sqrt (rowNormSq (Node := Node) (w r)) ^ 2) *
        Real.sqrt
          (∑ r ∈ s,
            Real.sqrt (frobeniusNormSq (Node := Node) (E := E) (X r)) ^ 2) := by
    positivity
  have hsquare := (sq_le_sq₀ (norm_nonneg _) hsqrt_nonneg).2 (hnorm.trans hcs)
  rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at hsquare
  simpa only [Real.sq_sqrt (hrow_nonneg _), Real.sq_sqrt (hfrob_nonneg _)]
    using hsquare

theorem finset_sum_norm_sq_le_card_mul_sum_norm_sq
    {ι : Type*} (s : Finset ι) (f : ι → E) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  classical
  have hnorm : ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := norm_sum_le _ _
  have hnormsq := (sq_le_sq₀ (norm_nonneg _)
    (Finset.sum_nonneg fun i _hi => norm_nonneg (f i))).2 hnorm
  exact hnormsq.trans (sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => ‖f i‖))

/- Source equation (6.13), before expectation and block summation. -/
theorem blockStartHybridCenter_mismatch_sq_le
    (noise : NoisePath Node E) (k : ℕ) :
    ‖setup.blockStartHybridCenter noise k -
        setup.averageIterate noise (setup.blockStart k)‖ ^ 2 ≤
      setup.hybridWeightDeviationNorm ^ 2 *
        frobeniusNormSq (Node := Node) (E := E)
          (setup.consensusState noise (setup.blockStart k)) := by
  let w : RowVector Node :=
    setup.perronLeft 0 - uniformAverageRow (Node := Node)
  have hmismatch :
      setup.blockStartHybridCenter noise k -
          setup.averageIterate noise (setup.blockStart k) =
        weightedState (Node := Node) (E := E) w
          (setup.consensusState noise (setup.blockStart k)) := by
    classical
    have hperron : ∑ i : Node, setup.perronLeft 0 i = 1 := by
      simpa [rowSum] using setup.perronLeft_sum 0
    have huniform : ∑ i : Node, uniformAverageRow (Node := Node) i = 1 := by
      simp [uniformAverageRow, nodeCount,
        nodeCount_real_ne_zero (Node := Node)]
    have hw_sum : ∑ i : Node, w i = 0 := by
      dsimp [w]
      simp only [Pi.sub_apply, Finset.sum_sub_distrib, hperron, huniform,
        sub_self]
    have hweighted_uniform :
        weightedState (Node := Node) (E := E)
            (uniformAverageRow (Node := Node))
            (setup.primalState noise (setup.blockStart k)) =
          setup.averageIterate noise (setup.blockStart k) := by
      unfold weightedState uniformAverageRow averageIterate arithmeticAverage
      rw [← Finset.smul_sum]
    calc
      setup.blockStartHybridCenter noise k -
          setup.averageIterate noise (setup.blockStart k) =
        weightedState (Node := Node) (E := E) (setup.perronLeft 0)
            (setup.primalState noise (setup.blockStart k)) -
          weightedState (Node := Node) (E := E)
            (uniformAverageRow (Node := Node))
            (setup.primalState noise (setup.blockStart k)) := by
              rw [hweighted_uniform]
              rfl
      _ = weightedState (Node := Node) (E := E) w
            (setup.primalState noise (setup.blockStart k)) := by
          unfold weightedState w
          simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
      _ = weightedState (Node := Node) (E := E) w
            (setup.consensusState noise (setup.blockStart k)) := by
          rw [setup.consensusState_eq_state_sub_average]
          unfold weightedState
          simp only [Pi.sub_apply, smul_sub, Finset.sum_sub_distrib,
            ← Finset.sum_smul, hw_sum, zero_smul, sub_zero]
  rw [hmismatch]
  have hrow := weightedState_sq_le_rowNormSq_mul_frobeniusNormSq
    (Node := Node) (E := E) w
      (setup.consensusState noise (setup.blockStart k))
  unfold hybridWeightDeviationNorm rowEuclideanNorm
  have hw_nonneg : 0 ≤ rowNormSq (Node := Node) w := by
    unfold rowNormSq
    positivity
  rw [Real.sq_sqrt]
  · simpa [w] using hrow
  · simpa [w] using hw_nonneg

/- Pathwise complete-block aggregation of (6.13).  The block starts form a
sparse subset of the first `Kp` time indices. -/
theorem blockStartHybridCenter_mismatch_pathwise_energy_bound
    (noise : NoisePath Node E) (K : ℕ) :
    ∑ k ∈ Finset.range K,
        ‖setup.blockStartHybridCenter noise k -
          setup.averageIterate noise (setup.blockStart k)‖ ^ 2 ≤
      setup.hybridWeightDeviationNorm ^ 2 *
        ∑ t ∈ Finset.range (setup.completeBlockHorizon K),
          frobeniusNormSq (Node := Node) (E := E)
            (setup.consensusState noise t) := by
  let q : ℕ → ℝ := fun t =>
    frobeniusNormSq (Node := Node) (E := E) (setup.consensusState noise t)
  have hq (t : ℕ) : 0 ≤ q t := by
    dsimp [q]
    unfold frobeniusNormSq
    positivity
  have hsparse : ∀ M : ℕ,
      (∑ k ∈ Finset.range M, q (setup.blockStart k)) ≤
        ∑ t ∈ Finset.range (setup.completeBlockHorizon M), q t := by
    intro M
    induction M with
    | zero => simp [completeBlockHorizon]
    | succ M ih =>
        have hphase : q (M * setup.period) ≤
            ∑ r ∈ Finset.range setup.period, q (M * setup.period + r) := by
          have hsingle := Finset.single_le_sum
            (s := Finset.range setup.period)
            (f := fun r => q (M * setup.period + r))
            (fun r _hr => hq (M * setup.period + r))
            (Finset.mem_range.mpr setup.period_pos)
          simpa using hsingle
        rw [Finset.sum_range_succ, completeBlockHorizon, Nat.succ_mul,
          Finset.sum_range_add]
        exact add_le_add ih hphase
  calc
    ∑ k ∈ Finset.range K,
        ‖setup.blockStartHybridCenter noise k -
          setup.averageIterate noise (setup.blockStart k)‖ ^ 2 ≤
      ∑ k ∈ Finset.range K,
        setup.hybridWeightDeviationNorm ^ 2 * q (setup.blockStart k) := by
          exact Finset.sum_le_sum fun k _hk =>
            setup.blockStartHybridCenter_mismatch_sq_le noise k
    _ = setup.hybridWeightDeviationNorm ^ 2 *
        ∑ k ∈ Finset.range K, q (setup.blockStart k) := by
          rw [Finset.mul_sum]
    _ ≤ setup.hybridWeightDeviationNorm ^ 2 *
        ∑ t ∈ Finset.range (setup.completeBlockHorizon K), q t :=
      mul_le_mul_of_nonneg_left (hsparse K) (sq_nonneg _)
    _ = _ := by rfl

/- Source equation (6.7): the high-pass increment is the corrected lift of
the two joint-coordinate endpoints minus the phase-zero gradient residual
increment. -/
theorem highPassIncrement_eq_correctedLift_joint_endpoints
    (noise : NoisePath Node E) (k : ℕ) :
    setup.highPassIncrement noise k =
      setup.correctedLift 0
        ⟨(setup.meanJointCoordinate noise (setup.blockStart (k + 1)) -
              setup.meanJointCoordinate noise (setup.blockStart k)) -
            (setup.perronResidual 0
                (setup.gradientTable
                  (setup.primalState noise (setup.blockStart (k + 1)))) -
              setup.perronResidual 0
                (setup.gradientTable
                  (setup.primalState noise (setup.blockStart k)))),
          by
            simp only [Pi.sub_apply, Finset.sum_sub_distrib,
              setup.meanJointCoordinate_zeroSum,
              setup.perronResidual_sum_zero_source, sub_self]⟩ := by
  have hright_block (m : ℕ) :
      setup.perronRight (setup.blockStart m) = setup.perronRight 0 := by
    induction m with
    | zero => simp [blockStart]
    | succ m ih =>
        calc
          setup.perronRight (setup.blockStart (m + 1)) =
              setup.perronRight (setup.blockStart m + setup.period) := by
                congr 1
                simp [blockStart, Nat.succ_mul]
          _ = setup.perronRight (setup.blockStart m) :=
            setup.perronRight_periodic (setup.blockStart m)
          _ = setup.perronRight 0 := ih
  have hresidual_block (m : ℕ) (Z : State Node E) :
      setup.perronResidual (setup.blockStart m) Z =
        setup.perronResidual 0 Z := by
    unfold perronResidual
    rw [hright_block]
  let Z : ℕ → State Node E := fun m =>
    setup.gradientTable (setup.primalState noise (setup.blockStart m))
  let W : ℕ → ZeroSumState Node E := fun m =>
    ⟨setup.meanJointCoordinate noise (setup.blockStart m) -
        setup.perronResidual 0 (Z m), by
      simp only [Pi.sub_apply, Finset.sum_sub_distrib,
        setup.meanJointCoordinate_zeroSum,
        setup.perronResidual_sum_zero_source, sub_self]⟩
  have hmean (m : ℕ) :
      setup.meanTrackerErrorZeroSum noise (setup.blockStart m) = W m := by
    apply Subtype.ext
    dsimp [W, Z, meanTrackerErrorZeroSum]
    rw [← hresidual_block]
    unfold meanJointCoordinate
    abel
  unfold highPassIncrement meanLiftCorrection
  rw [hmean (k + 1), hmean k,
    ← setup.correctedLift_sub 0 (W (k + 1)) (W k)]
  congr 1
  apply Subtype.ext
  dsimp [W, Z]
  module

/- The pointwise operator-norm part of (6.8), before controlling the residual
gradient increment by within-block displacement. -/
theorem highPassIncrement_sq_le_joint_endpoint_energy
    (noise : NoisePath Node E) (k : ℕ) :
    ‖setup.highPassIncrement noise k‖ ^ 2 ≤
      3 * setup.correctedLiftNormZero ^ 2 *
        (frobeniusNormSq (Node := Node) (E := E)
            (setup.meanJointCoordinate noise (setup.blockStart (k + 1))) +
          frobeniusNormSq (Node := Node) (E := E)
            (setup.meanJointCoordinate noise (setup.blockStart k)) +
          frobeniusNormSq (Node := Node) (E := E)
            (setup.perronResidual 0
                (setup.gradientTable
                  (setup.primalState noise (setup.blockStart (k + 1)))) -
              setup.perronResidual 0
                (setup.gradientTable
                  (setup.primalState noise (setup.blockStart k))))) := by
  rw [setup.highPassIncrement_eq_correctedLift_joint_endpoints noise k]
  let W : ZeroSumState Node E :=
    ⟨(setup.meanJointCoordinate noise (setup.blockStart (k + 1)) -
          setup.meanJointCoordinate noise (setup.blockStart k)) -
        (setup.perronResidual 0
            (setup.gradientTable
              (setup.primalState noise (setup.blockStart (k + 1)))) -
          setup.perronResidual 0
            (setup.gradientTable
              (setup.primalState noise (setup.blockStart k)))), by
      simp only [Pi.sub_apply, Finset.sum_sub_distrib,
        setup.meanJointCoordinate_zeroSum,
        setup.perronResidual_sum_zero_source, sub_self]⟩
  change ‖setup.correctedLift 0 W‖ ^ 2 ≤ _
  have hop := setup.correctedLiftOperatorNorm_spec 0
  have hact := hop.2 W
  have hsq := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg hop.1 (Real.sqrt_nonneg _))).2 hact
  rw [mul_pow] at hsq
  have hW_nonneg : 0 ≤ frobeniusNormSq (Node := Node) (E := E) W.1 := by
    unfold frobeniusNormSq
    positivity
  rw [Real.sq_sqrt hW_nonneg] at hsq
  have hdecomp : W.1 =
      setup.meanJointCoordinate noise (setup.blockStart (k + 1)) +
        (-setup.meanJointCoordinate noise (setup.blockStart k)) +
        (-(setup.perronResidual 0
              (setup.gradientTable
                (setup.primalState noise (setup.blockStart (k + 1)))) -
            setup.perronResidual 0
              (setup.gradientTable
                (setup.primalState noise (setup.blockStart k))))) := by
    funext i
    dsimp [W]
    module
  have hfro := frobeniusNormSq_add_add_le_three
    (Node := Node) (E := E)
    (setup.meanJointCoordinate noise (setup.blockStart (k + 1)))
    (-setup.meanJointCoordinate noise (setup.blockStart k))
    (-(setup.perronResidual 0
        (setup.gradientTable
          (setup.primalState noise (setup.blockStart (k + 1)))) -
      setup.perronResidual 0
        (setup.gradientTable
          (setup.primalState noise (setup.blockStart k)))))
  have hfroW : frobeniusNormSq (Node := Node) (E := E) W.1 ≤
      3 * frobeniusNormSq (Node := Node) (E := E)
          (setup.meanJointCoordinate noise (setup.blockStart (k + 1))) +
        3 * frobeniusNormSq (Node := Node) (E := E)
          (-setup.meanJointCoordinate noise (setup.blockStart k)) +
        3 * frobeniusNormSq (Node := Node) (E := E)
          (-(setup.perronResidual 0
              (setup.gradientTable
                (setup.primalState noise (setup.blockStart (k + 1)))) -
            setup.perronResidual 0
              (setup.gradientTable
                (setup.primalState noise (setup.blockStart k))))) := by
    rw [hdecomp]
    exact hfro
  calc
    ‖setup.correctedLift 0 W‖ ^ 2 ≤
        setup.correctedLiftNormZero ^ 2 *
          frobeniusNormSq (Node := Node) (E := E) W.1 := by
      simpa [correctedLiftNormZero] using hsq
    _ ≤ setup.correctedLiftNormZero ^ 2 *
        (3 * frobeniusNormSq (Node := Node) (E := E)
            (setup.meanJointCoordinate noise (setup.blockStart (k + 1))) +
          3 * frobeniusNormSq (Node := Node) (E := E)
            (-setup.meanJointCoordinate noise (setup.blockStart k)) +
          3 * frobeniusNormSq (Node := Node) (E := E)
            (-(setup.perronResidual 0
                (setup.gradientTable
                  (setup.primalState noise (setup.blockStart (k + 1)))) -
              setup.perronResidual 0
                (setup.gradientTable
                  (setup.primalState noise (setup.blockStart k)))))) :=
      mul_le_mul_of_nonneg_left hfroW (sq_nonneg _)
    _ = _ := by
      simp only [frobeniusNormSq, Pi.neg_apply, norm_neg]
      ring

/- The phase-zero residual-gradient jump across one complete block is
controlled by the sum of the `p` primal increments in that block.  This is
the second estimate displayed in the high-pass paragraph of Appendix B. -/
theorem perronResidual_gradient_block_sq_le
    (noise : NoisePath Node E) (k : ℕ) :
    frobeniusNormSq (Node := Node) (E := E)
        (setup.perronResidual 0
            (setup.gradientTable
              (setup.primalState noise (setup.blockStart (k + 1)))) -
          setup.perronResidual 0
            (setup.gradientTable
              (setup.primalState noise (setup.blockStart k)))) ≤
      (setup.period : ℝ) *
        matrixEuclideanOperatorNorm (Node := Node)
            (setup.perronResidualMatrix 0) ^ 2 * setup.L ^ 2 *
          ∑ j ∈ Finset.range setup.period,
            frobeniusNormSq (Node := Node) (E := E)
              (setup.primalState noise (setup.blockStart k + j + 1) -
                setup.primalState noise (setup.blockStart k + j)) := by
  let Z₁ := setup.gradientTable
    (setup.primalState noise (setup.blockStart (k + 1)))
  let Z₀ := setup.gradientTable
    (setup.primalState noise (setup.blockStart k))
  let S₀ := setup.perronResidualMatrix 0
  have hrewrite :
      setup.perronResidual 0 Z₁ - setup.perronResidual 0 Z₀ =
        leftMul (Node := Node) (E := E) S₀ (Z₁ - Z₀) := by
    dsimp [S₀]
    rw [← setup.leftMul_perronResidualMatrix 0 Z₁,
      ← setup.leftMul_perronResidualMatrix 0 Z₀,
      leftMul_sub_state]
  have hop := matrixEuclideanOperatorNorm_stateFrobenius_action
    (Node := Node) (E := E) S₀ (Z₁ - Z₀)
  have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg
      (matrixEuclideanOperatorNorm_spec (Node := Node) S₀).1
      (Real.sqrt_nonneg _))).2 hop
  have hgradient := setup.gradientTable_difference_frobeniusSq_le
    (setup.primalState noise (setup.blockStart (k + 1)))
    (setup.primalState noise (setup.blockStart k))
  have htelescope := setup.state_displacement_telescope noise
    (setup.blockStart k) setup.period
  have hleft_nonneg : 0 ≤ frobeniusNormSq (Node := Node) (E := E)
      (leftMul (Node := Node) (E := E) S₀ (Z₁ - Z₀)) := by
    unfold frobeniusNormSq
    positivity
  have hright_nonneg : 0 ≤ frobeniusNormSq (Node := Node) (E := E)
      (Z₁ - Z₀) := by
    unfold frobeniusNormSq
    positivity
  rw [Real.sq_sqrt hleft_nonneg, mul_pow,
    Real.sq_sqrt hright_nonneg] at hsq
  rw [hrewrite]
  calc
    frobeniusNormSq (Node := Node) (E := E)
        (leftMul (Node := Node) (E := E) S₀ (Z₁ - Z₀)) ≤
      matrixEuclideanOperatorNorm (Node := Node) S₀ ^ 2 *
        frobeniusNormSq (Node := Node) (E := E) (Z₁ - Z₀) := hsq
    _ ≤ matrixEuclideanOperatorNorm (Node := Node) S₀ ^ 2 *
        (setup.L ^ 2 * frobeniusNormSq (Node := Node) (E := E)
          (setup.primalState noise (setup.blockStart (k + 1)) -
            setup.primalState noise (setup.blockStart k))) :=
      mul_le_mul_of_nonneg_left hgradient (sq_nonneg _)
    _ ≤ matrixEuclideanOperatorNorm (Node := Node) S₀ ^ 2 *
        (setup.L ^ 2 * ((setup.period : ℝ) *
          ∑ j ∈ Finset.range setup.period,
            frobeniusNormSq (Node := Node) (E := E)
              (setup.primalState noise (setup.blockStart k + j + 1) -
                setup.primalState noise (setup.blockStart k + j)))) := by
      apply mul_le_mul_of_nonneg_left
      apply mul_le_mul_of_nonneg_left
      · simpa [blockStart, Nat.succ_mul, Nat.add_assoc] using htelescope
      · exact sq_nonneg setup.L
      · exact sq_nonneg _
    _ = _ := by
      dsimp [S₀]
      ring

/- Both endpoint families of `K` complete blocks embed in `0, ..., Kp`;
consequently every internal endpoint is counted at most twice. -/
theorem completeBlockEndpoint_pair_sum_le
    (q : ℕ → ℝ) (hq : ∀ t, 0 ≤ q t) (K : ℕ) :
    ∑ k ∈ Finset.range K,
        (q (setup.blockStart (k + 1)) + q (setup.blockStart k)) ≤
      2 * ∑ t ∈ Finset.range (setup.completeBlockHorizon K + 1), q t := by
  have hstart : ∀ M : ℕ,
      (∑ k ∈ Finset.range M, q (setup.blockStart k)) ≤
        ∑ t ∈ Finset.range (setup.completeBlockHorizon M), q t := by
    intro M
    induction M with
    | zero => simp [completeBlockHorizon]
    | succ M ih =>
        have hphase : q (M * setup.period) ≤
            ∑ r ∈ Finset.range setup.period, q (M * setup.period + r) := by
          have hsingle := Finset.single_le_sum
            (s := Finset.range setup.period)
            (f := fun r => q (M * setup.period + r))
            (fun r _hr => hq (M * setup.period + r))
            (Finset.mem_range.mpr setup.period_pos)
          simpa using hsingle
        rw [Finset.sum_range_succ, completeBlockHorizon, Nat.succ_mul,
          Finset.sum_range_add]
        exact add_le_add ih hphase
  have hend : ∀ M : ℕ,
      (∑ k ∈ Finset.range M, q (setup.blockStart (k + 1))) ≤
        ∑ t ∈ Finset.range (setup.completeBlockHorizon M + 1), q t := by
    intro M
    induction M with
    | zero =>
        simpa [completeBlockHorizon] using hq 0
    | succ M ih =>
        have hp_pred : setup.period - 1 < setup.period := by
          have hp := setup.period_pos
          omega
        have hphase : q ((M + 1) * setup.period) ≤
            ∑ r ∈ Finset.range setup.period,
              q (M * setup.period + 1 + r) := by
          have hsingle := Finset.single_le_sum
            (s := Finset.range setup.period)
            (f := fun r => q (M * setup.period + 1 + r))
            (fun r _hr => hq (M * setup.period + 1 + r))
            (Finset.mem_range.mpr hp_pred)
          have hindex : M * setup.period + 1 + (setup.period - 1) =
              (M + 1) * setup.period := by
            rw [Nat.add_mul]
            have hp := setup.period_pos
            omega
          change q (M * setup.period + 1 + (setup.period - 1)) ≤
            ∑ r ∈ Finset.range setup.period,
              q (M * setup.period + 1 + r) at hsingle
          rw [hindex] at hsingle
          exact hsingle
        rw [Finset.sum_range_succ, completeBlockHorizon, Nat.succ_mul]
        rw [show M * setup.period + setup.period + 1 =
            (M * setup.period + 1) + setup.period by omega,
          Finset.sum_range_add]
        exact add_le_add ih hphase
  rw [Finset.sum_add_distrib]
  have hs := hstart K
  have he := hend K
  have hprefix :
      (∑ t ∈ Finset.range (setup.completeBlockHorizon K), q t) ≤
        ∑ t ∈ Finset.range (setup.completeBlockHorizon K + 1), q t := by
    rw [Finset.sum_range_succ]
    exact le_add_of_nonneg_right (hq (setup.completeBlockHorizon K))
  linarith

/- Pathwise aggregation of (6.8): endpoint multiplicity contributes the
factor six, while the residual-gradient jump contributes the complete-block
displacement window. -/
theorem highPassIncrement_pathwise_energy_bound
    (noise : NoisePath Node E) (K : ℕ) :
    ∑ k ∈ Finset.range K, ‖setup.highPassIncrement noise k‖ ^ 2 ≤
      6 * setup.correctedLiftNormZero ^ 2 *
          ∑ t ∈ Finset.range (setup.completeBlockHorizon K + 1),
            frobeniusNormSq (Node := Node) (E := E)
              (setup.meanJointCoordinate noise t) +
        3 * (setup.period : ℝ) * setup.correctedLiftNormZero ^ 2 *
            matrixEuclideanOperatorNorm (Node := Node)
              (setup.perronResidualMatrix 0) ^ 2 * setup.L ^ 2 *
          ∑ t ∈ Finset.range (setup.completeBlockHorizon K),
            frobeniusNormSq (Node := Node) (E := E)
              (setup.primalState noise (t + 1) -
                setup.primalState noise t) := by
  let q : ℕ → ℝ := fun t =>
    frobeniusNormSq (Node := Node) (E := E)
      (setup.meanJointCoordinate noise t)
  let d : ℕ → ℝ := fun t =>
    frobeniusNormSq (Node := Node) (E := E)
      (setup.primalState noise (t + 1) - setup.primalState noise t)
  let c : ℝ := (setup.period : ℝ) *
    matrixEuclideanOperatorNorm (Node := Node)
      (setup.perronResidualMatrix 0) ^ 2 * setup.L ^ 2
  have hq (t : ℕ) : 0 ≤ q t := by
    dsimp [q]
    unfold frobeniusNormSq
    positivity
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hpoint (k : ℕ) :
      ‖setup.highPassIncrement noise k‖ ^ 2 ≤
        3 * setup.correctedLiftNormZero ^ 2 *
          (q (setup.blockStart (k + 1)) + q (setup.blockStart k) +
            c * ∑ j ∈ Finset.range setup.period,
              d (setup.blockStart k + j)) := by
    have hbase := setup.highPassIncrement_sq_le_joint_endpoint_energy noise k
    have hresidual := setup.perronResidual_gradient_block_sq_le noise k
    have hinside :
        q (setup.blockStart (k + 1)) + q (setup.blockStart k) +
          frobeniusNormSq (Node := Node) (E := E)
            (setup.perronResidual 0
                (setup.gradientTable
                  (setup.primalState noise (setup.blockStart (k + 1)))) -
              setup.perronResidual 0
                (setup.gradientTable
                  (setup.primalState noise (setup.blockStart k)))) ≤
        q (setup.blockStart (k + 1)) + q (setup.blockStart k) +
          c * ∑ j ∈ Finset.range setup.period,
            d (setup.blockStart k + j) := by
      dsimp [q, d, c]
      simpa [add_assoc, add_comm, add_left_comm] using
        add_le_add_left hresidual
          (frobeniusNormSq (Node := Node) (E := E)
              (setup.meanJointCoordinate noise (setup.blockStart (k + 1))) +
            frobeniusNormSq (Node := Node) (E := E)
              (setup.meanJointCoordinate noise (setup.blockStart k)))
    exact hbase.trans
      (mul_le_mul_of_nonneg_left hinside (by positivity))
  have hendpoints := setup.completeBlockEndpoint_pair_sum_le q hq K
  have hsum := Finset.sum_le_sum (s := Finset.range K)
    (fun k _hk => hpoint k)
  calc
    ∑ k ∈ Finset.range K, ‖setup.highPassIncrement noise k‖ ^ 2 ≤
        ∑ k ∈ Finset.range K,
          3 * setup.correctedLiftNormZero ^ 2 *
            (q (setup.blockStart (k + 1)) + q (setup.blockStart k) +
              c * ∑ j ∈ Finset.range setup.period,
                d (setup.blockStart k + j)) := hsum
    _ = 3 * setup.correctedLiftNormZero ^ 2 *
          (∑ k ∈ Finset.range K,
            (q (setup.blockStart (k + 1)) + q (setup.blockStart k))) +
        3 * setup.correctedLiftNormZero ^ 2 * c *
          ∑ k ∈ Finset.range K,
            ∑ j ∈ Finset.range setup.period,
              d (setup.blockStart k + j) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib,
        ← Finset.mul_sum]
      ring
    _ ≤ 3 * setup.correctedLiftNormZero ^ 2 *
          (2 * ∑ t ∈ Finset.range (setup.completeBlockHorizon K + 1), q t) +
        3 * setup.correctedLiftNormZero ^ 2 * c *
          ∑ k ∈ Finset.range K,
            ∑ j ∈ Finset.range setup.period,
              d (setup.blockStart k + j) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hendpoints (by positivity)) le_rfl
    _ = _ := by
      rw [show
        (∑ k ∈ Finset.range K,
          ∑ j ∈ Finset.range setup.period,
            d (setup.blockStart k + j)) =
          ∑ t ∈ Finset.range (K * setup.period), d t by
            simpa only [blockStart] using
              (sum_range_mul_eq_sum_blocks d K setup.period).symm]
      dsimp [q, d, c, blockStart, completeBlockHorizon]
      ring

/- Expected complete-block high-pass estimate (6.8)--(6.9), with the
formula-defined constants used by the state-feedback bound. -/
set_option maxHeartbeats 800000 in
theorem highPassIncrement_energy_bound
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) (K : ℕ) :
    ∑ k ∈ Finset.range K,
        ∫ ω, ‖setup.highPassIncrement (oracle.noise ω) k‖ ^ 2 ∂μ ≤
      setup.rhoInitialConstant * setup.initialGradientHeterogeneity ^ 2 +
        setup.rhoDisplacementConstant * setup.L ^ 2 *
          setup.displacementEnergy μ oracle (setup.completeBlockHorizon K) := by
  let N := setup.completeBlockHorizon K
  let a : ℝ := 6 * setup.correctedLiftNormZero ^ 2
  let b : ℝ := 3 * (setup.period : ℝ) *
    setup.correctedLiftNormZero ^ 2 *
      matrixEuclideanOperatorNorm (Node := Node)
        (setup.perronResidualMatrix 0) ^ 2 * setup.L ^ 2
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hhigh_mem (k : ℕ) : MemLp (fun ω =>
      setup.highPassIncrement (oracle.noise ω) k) 2 μ := by
    simpa only [highPassIncrement] using
      (setup.meanLiftCorrection_memLp_two μ oracle horacle (k + 1)).sub
        (setup.meanLiftCorrection_memLp_two μ oracle horacle k)
  have hhigh_int (k : ℕ) : Integrable (fun ω =>
      ‖setup.highPassIncrement (oracle.noise ω) k‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (hhigh_mem k).aestronglyMeasurable).1
      (hhigh_mem k)
  have htheta_int (t : ℕ) : Integrable (fun ω =>
      frobeniusNormSq (Node := Node) (E := E)
        (setup.meanJointCoordinate (oracle.noise ω) t)) μ :=
    frobeniusNormSq_integrable_of_coordinate_memLp fun i =>
      setup.meanJointCoordinate_coordinate_memLp μ oracle horacle t i
  have hdisp_int (t : ℕ) : Integrable (fun ω =>
      frobeniusNormSq (Node := Node) (E := E)
        (setup.primalState (oracle.noise ω) (t + 1) -
          setup.primalState (oracle.noise ω) t)) μ := by
    apply frobeniusNormSq_integrable_of_coordinate_memLp
    intro i
    simpa only [Pi.sub_apply] using
      ((setup.generated_pushpull_coordinate_memLp μ oracle horacle (t + 1)).1 i).sub
        ((setup.generated_pushpull_coordinate_memLp μ oracle horacle t).1 i)
  have hleft_int : Integrable (fun ω =>
      ∑ k ∈ Finset.range K,
        ‖setup.highPassIncrement (oracle.noise ω) k‖ ^ 2) μ :=
    integrable_finset_sum _ fun k _hk => hhigh_int k
  have htheta_sum_int : Integrable (fun ω =>
      ∑ t ∈ Finset.range (N + 1),
        frobeniusNormSq (Node := Node) (E := E)
          (setup.meanJointCoordinate (oracle.noise ω) t)) μ :=
    integrable_finset_sum _ fun t _ht => htheta_int t
  have hdisp_sum_int : Integrable (fun ω =>
      ∑ t ∈ Finset.range N,
        frobeniusNormSq (Node := Node) (E := E)
          (setup.primalState (oracle.noise ω) (t + 1) -
            setup.primalState (oracle.noise ω) t)) μ :=
    integrable_finset_sum _ fun t _ht => hdisp_int t
  have hright_int : Integrable (fun ω =>
      a * (∑ t ∈ Finset.range (N + 1),
        frobeniusNormSq (Node := Node) (E := E)
          (setup.meanJointCoordinate (oracle.noise ω) t)) +
      b * (∑ t ∈ Finset.range N,
        frobeniusNormSq (Node := Node) (E := E)
          (setup.primalState (oracle.noise ω) (t + 1) -
            setup.primalState (oracle.noise ω) t))) μ :=
    (htheta_sum_int.const_mul a).add (hdisp_sum_int.const_mul b)
  have hint :
      (∫ ω, ∑ k ∈ Finset.range K,
          ‖setup.highPassIncrement (oracle.noise ω) k‖ ^ 2 ∂μ) ≤
        ∫ ω,
          a * (∑ t ∈ Finset.range (N + 1),
            frobeniusNormSq (Node := Node) (E := E)
              (setup.meanJointCoordinate (oracle.noise ω) t)) +
          b * (∑ t ∈ Finset.range N,
            frobeniusNormSq (Node := Node) (E := E)
              (setup.primalState (oracle.noise ω) (t + 1) -
                setup.primalState (oracle.noise ω) t)) ∂μ := by
    apply MeasureTheory.integral_mono_ae hleft_int hright_int
    exact Filter.Eventually.of_forall fun ω => by
      simpa [N, a, b] using
        setup.highPassIncrement_pathwise_energy_bound (oracle.noise ω) K
  have hraw :
      (∑ k ∈ Finset.range K,
        ∫ ω, ‖setup.highPassIncrement (oracle.noise ω) k‖ ^ 2 ∂μ) ≤
        a * (∑ t ∈ Finset.range (N + 1),
          ∫ ω, frobeniusNormSq (Node := Node) (E := E)
            (setup.meanJointCoordinate (oracle.noise ω) t) ∂μ) +
        b * (∑ t ∈ Finset.range N,
          ∫ ω, frobeniusNormSq (Node := Node) (E := E)
            (setup.primalState (oracle.noise ω) (t + 1) -
              setup.primalState (oracle.noise ω) t) ∂μ) := by
    calc
      _ = ∫ ω, ∑ k ∈ Finset.range K,
          ‖setup.highPassIncrement (oracle.noise ω) k‖ ^ 2 ∂μ := by
            rw [MeasureTheory.integral_finset_sum]
            intro k _hk
            exact hhigh_int k
      _ ≤ _ := hint
      _ = _ := by
        rw [MeasureTheory.integral_add,
          MeasureTheory.integral_const_mul,
          MeasureTheory.integral_const_mul,
          MeasureTheory.integral_finset_sum,
          MeasureTheory.integral_finset_sum]
        all_goals
          first
          | exact htheta_sum_int.const_mul _
          | exact hdisp_sum_int.const_mul _
          | exact fun t _ht => htheta_int t
          | exact fun t _ht => hdisp_int t
  have hmean := setup.meanJointCoordinate_energy_bound
    μ oracle horacle N
  calc
    _ ≤ a * (∑ t ∈ Finset.range (N + 1),
          ∫ ω, frobeniusNormSq (Node := Node) (E := E)
            (setup.meanJointCoordinate (oracle.noise ω) t) ∂μ) +
        b * (∑ t ∈ Finset.range N,
          ∫ ω, frobeniusNormSq (Node := Node) (E := E)
            (setup.primalState (oracle.noise ω) (t + 1) -
              setup.primalState (oracle.noise ω) t) ∂μ) := hraw
    _ ≤ a * (setup.thetaInitialConstant *
          setup.initialGradientHeterogeneity ^ 2 +
        setup.thetaDisplacementConstant * setup.L ^ 2 *
          setup.displacementEnergy μ oracle N) +
        b * setup.displacementEnergy μ oracle N :=
      add_le_add (mul_le_mul_of_nonneg_left hmean ha) le_rfl
    _ = _ := by
      dsimp [N, a, b]
      unfold rhoInitialConstant rhoDisplacementConstant
      unfold thetaInitialConstant thetaDisplacementConstant
      ring

/- Equation (6.10), first part: the centered influence has zero total mass
over one period.  This is derived from the source DC-gain identities rather
than assumed as a separate periodic-cancellation hypothesis. -/
theorem centeredInfluence_period_sum_zero :
    (∑ r ∈ Finset.range setup.period, setup.centeredInfluence r) = 0 := by
  classical
  have hsource := setup.AverageGainEffectiveNodes
  have havg := hsource.2.1
  have hgain := hsource.2.2.1
  have hp : 0 < (setup.period : ℝ) := by
    exact_mod_cast setup.period_pos
  have hn : 0 < (nodeCount (Node := Node) : ℝ) := by
    exact_mod_cast nodeCount_pos (Node := Node)
  funext i
  have havgi := congrFun havg i
  unfold averageInfluence at havgi
  rw [Fin.sum_univ_eq_sum_range
    (fun r : ℕ => setup.influence r i)] at havgi
  have hinfluence :
      (∑ r ∈ Finset.range setup.period, setup.influence r i) =
        (setup.period : ℝ) * setup.averagePerronOverlap := by
    calc
      _ = (setup.period : ℝ) *
          ((setup.period : ℝ)⁻¹ *
            ∑ r ∈ Finset.range setup.period, setup.influence r i) := by
              field_simp
      _ = _ := by rw [havgi]
  have hgain_div :
      setup.influenceGain / (nodeCount (Node := Node) : ℝ) =
        setup.averagePerronOverlap := by
    rw [hgain]
    field_simp
  simp only [Finset.sum_apply, centeredInfluence, Pi.sub_apply,
    Pi.smul_apply, oneRow, smul_eq_mul]
  rw [Finset.sum_sub_distrib, hinfluence, hgain_div]
  simp

theorem influencePartialSum_terminal_eq_zero :
    setup.influencePartialSum (setup.period - 1) = 0 := by
  unfold influencePartialSum
  have hp : 1 ≤ setup.period := setup.period_pos
  rw [Nat.sub_add_cancel hp]
  exact setup.centeredInfluence_period_sum_zero

/- Finite Abel summation with the partial sums on the scalar coefficients.
The endpoint is kept explicitly; the source cancellation removes it below. -/
theorem sum_range_smul_eq_terminal_add_abel
    (d : ℕ → ℝ) (z : ℕ → E) (n : ℕ) :
    (∑ r ∈ Finset.range n, d r • z r) =
      (∑ r ∈ Finset.range n, d r) • z (n - 1) +
        ∑ r ∈ Finset.range (n - 1),
          (∑ j ∈ Finset.range (r + 1), d j) • (z r - z (r + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        simp
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        have hnrepr : n = (n - 1) + 1 := by omega
        have hpartial :
            (∑ r ∈ Finset.range (n + 1), d r) =
              (∑ r ∈ Finset.range n, d r) + d n := by
          rw [Finset.sum_range_succ]
        have habel :
            (∑ r ∈ Finset.range n,
              (∑ j ∈ Finset.range (r + 1), d j) •
                (z r - z (r + 1))) =
              (∑ r ∈ Finset.range (n - 1),
                (∑ j ∈ Finset.range (r + 1), d j) •
                  (z r - z (r + 1))) +
                (∑ j ∈ Finset.range n, d j) •
                  (z (n - 1) - z n) := by
          conv_lhs => rw [hnrepr, Finset.sum_range_succ]
          simp only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)]
        rw [Finset.sum_range_succ, ih, Nat.succ_sub_one,
          hpartial, habel]
        module

/- Equation (6.10), complete form: terminal cancellation turns finite Abel
summation into a sum over the `p-1` adjacent gradient-table differences. -/
theorem centeredInfluence_period_abel_identity
    (Z : ℕ → State Node E) :
    (∑ r ∈ Finset.range setup.period,
        weightedState (Node := Node) (E := E)
          (setup.centeredInfluence r) (Z r)) =
      ∑ r ∈ Finset.range (setup.period - 1),
        weightedState (Node := Node) (E := E)
          (setup.influencePartialSum r) (Z r - Z (r + 1)) := by
  classical
  have hcoord (i : Node) :
      (∑ r ∈ Finset.range setup.period,
          setup.centeredInfluence r i • Z r i) =
        ∑ r ∈ Finset.range (setup.period - 1),
          setup.influencePartialSum r i • (Z r i - Z (r + 1) i) := by
    have hterminal :
        (∑ r ∈ Finset.range setup.period,
          setup.centeredInfluence r i) = 0 := by
      have hz := congrFun setup.centeredInfluence_period_sum_zero i
      simpa only [Finset.sum_apply, Pi.zero_apply] using hz
    have hab := sum_range_smul_eq_terminal_add_abel
      (E := E) (fun r => setup.centeredInfluence r i) (fun r => Z r i)
        setup.period
    rw [hterminal, zero_smul, zero_add] at hab
    simpa only [influencePartialSum, Finset.sum_apply, Pi.sub_apply] using hab
  unfold weightedState
  simp only [Pi.sub_apply]
  calc
    (∑ r ∈ Finset.range setup.period,
        ∑ i : Node, setup.centeredInfluence r i • Z r i) =
      ∑ i : Node, ∑ r ∈ Finset.range setup.period,
        setup.centeredInfluence r i • Z r i := by
          rw [Finset.sum_comm]
    _ = ∑ i : Node, ∑ r ∈ Finset.range (setup.period - 1),
        setup.influencePartialSum r i • (Z r i - Z (r + 1) i) := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact hcoord i
    _ = ∑ r ∈ Finset.range (setup.period - 1),
        ∑ i : Node,
          setup.influencePartialSum r i • (Z r i - Z (r + 1) i) := by
            rw [Finset.sum_comm]

/- Source estimate (6.11) for one time: the aggregate component-gradient
disagreement from the gradient at the arithmetic average is controlled by
the consensus Frobenius energy. -/
theorem gradientTable_disagreement_sq_le
    (X : State Node E) :
    ‖(∑ i : Node, setup.gradientTable X i) -
        (nodeCount (Node := Node) : ℝ) •
          setup.averageGradient
            (arithmeticAverage (Node := Node) (E := E) X)‖ ^ 2 ≤
      (nodeCount (Node := Node) : ℝ) * setup.L ^ 2 *
        frobeniusNormSq (Node := Node) (E := E)
          (consensusError (Node := Node) (E := E) X) := by
  classical
  let avg := arithmeticAverage (Node := Node) (E := E) X
  let dev : Node → E := fun i =>
    setup.componentGradient i (X i) - setup.componentGradient i avg
  have hn : 0 ≤ (nodeCount (Node := Node) : ℝ) := by positivity
  have hrewrite :
      (∑ i : Node, setup.gradientTable X i) -
          (nodeCount (Node := Node) : ℝ) • setup.averageGradient avg =
        ∑ i : Node, dev i := by
    have havg := setup.averageGradient_eq_componentGradient_average avg
    have hmean :
        (nodeCount (Node := Node) : ℝ) • setup.averageGradient avg =
          ∑ i : Node, setup.componentGradient i avg := by
      rw [havg, smul_smul,
        mul_inv_cancel₀ (nodeCount_real_ne_zero (Node := Node)), one_smul]
    rw [hmean]
    simp only [gradientTable, dev]
    rw [← Finset.sum_sub_distrib]
  have hsum :
      ‖∑ i : Node, dev i‖ ^ 2 ≤
        (nodeCount (Node := Node) : ℝ) *
          ∑ i : Node, ‖dev i‖ ^ 2 := by
    have hnorm : ‖∑ i : Node, dev i‖ ≤ ∑ i : Node, ‖dev i‖ :=
      norm_sum_le _ _
    have hsquares := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset Node)) (f := fun i => ‖dev i‖)
    simp only [Finset.card_univ, nodeCount] at hsquares
    have hnormsq := (sq_le_sq₀ (norm_nonneg _)
      (Finset.sum_nonneg fun i _hi => norm_nonneg (dev i))).2 hnorm
    exact hnormsq.trans hsquares
  have hpoint (i : Node) :
      ‖dev i‖ ^ 2 ≤ setup.L ^ 2 * ‖X i - avg‖ ^ 2 := by
    have hlip := setup.componentGradient_lipschitz_bound i (X i) avg
    dsimp [dev, componentGradient]
    simpa [mul_pow] using
      ((sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg setup.L_pos.le (norm_nonneg _))).2 hlip)
  rw [hrewrite]
  calc
    ‖∑ i : Node, dev i‖ ^ 2 ≤
        (nodeCount (Node := Node) : ℝ) *
          ∑ i : Node, ‖dev i‖ ^ 2 := hsum
    _ ≤ (nodeCount (Node := Node) : ℝ) *
          ∑ i : Node, setup.L ^ 2 * ‖X i - avg‖ ^ 2 :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i _hi => hpoint i) hn
    _ = _ := by
      rw [← Finset.mul_sum]
      simp only [frobeniusNormSq, consensusError, Pi.sub_apply, avg]
      ring

/- Appendix B's three-term decomposition of the block phase error: node
disagreement, average displacement, and the Abel-transformed centered phase. -/
theorem blockPhaseError_eq_three_terms
    (noise : NoisePath Node E) (k : ℕ) :
    setup.blockPhaseError noise k =
      (setup.influenceGain / (nodeCount (Node := Node) : ℝ)) •
        (∑ r ∈ Finset.range setup.period,
          ((∑ i : Node,
              setup.gradientTable
                (setup.primalState noise (setup.blockStart k + r)) i) -
            (nodeCount (Node := Node) : ℝ) •
              setup.averageGradient
                (setup.averageIterate noise (setup.blockStart k + r)))) +
      setup.influenceGain •
        (∑ r ∈ Finset.range setup.period,
          (setup.averageGradient
              (setup.averageIterate noise (setup.blockStart k + r)) -
            setup.blockAverageGradient noise k)) +
      ∑ r ∈ Finset.range (setup.period - 1),
        weightedState (Node := Node) (E := E)
          (setup.influencePartialSum r)
          (setup.gradientTable
              (setup.primalState noise (setup.blockStart k + r)) -
            setup.gradientTable
              (setup.primalState noise (setup.blockStart k + r + 1))) := by
  classical
  let Z : ℕ → State Node E := fun r =>
    setup.gradientTable
      (setup.primalState noise (setup.blockStart k + r))
  have hinfluence (r : ℕ) :
      weightedState (Node := Node) (E := E) (setup.influence r) (Z r) =
        weightedState (Node := Node) (E := E)
            (setup.centeredInfluence r) (Z r) +
          (setup.influenceGain / (nodeCount (Node := Node) : ℝ)) •
            ∑ i : Node, Z r i := by
    have hrow : setup.influence r = setup.centeredInfluence r +
        (setup.influenceGain / (nodeCount (Node := Node) : ℝ)) •
          oneRow (Node := Node) := by
      unfold centeredInfluence
      module
    rw [hrow, weightedState_add_weight]
    congr 1
    unfold weightedState oneRow
    simp only [Pi.smul_apply, one_smul, smul_smul, Finset.smul_sum,
      smul_eq_mul, mul_one]
  have hsplit :
      (∑ r ∈ Finset.range setup.period,
        weightedState (Node := Node) (E := E) (setup.influence r) (Z r)) =
        (∑ r ∈ Finset.range setup.period,
          weightedState (Node := Node) (E := E)
            (setup.centeredInfluence r) (Z r)) +
        (setup.influenceGain / (nodeCount (Node := Node) : ℝ)) •
          ∑ r ∈ Finset.range setup.period, ∑ i : Node, Z r i := by
    calc
      _ = ∑ r ∈ Finset.range setup.period,
          (weightedState (Node := Node) (E := E)
              (setup.centeredInfluence r) (Z r) +
            (setup.influenceGain / (nodeCount (Node := Node) : ℝ)) •
              ∑ i : Node, Z r i) := by
                apply Finset.sum_congr rfl
                intro r _hr
                exact hinfluence r
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.smul_sum]
  have hab := setup.centeredInfluence_period_abel_identity Z
  have hn : (nodeCount (Node := Node) : ℝ) ≠ 0 :=
    nodeCount_real_ne_zero (Node := Node)
  have hcancel :
      (setup.influenceGain / (nodeCount (Node := Node) : ℝ)) *
          (nodeCount (Node := Node) : ℝ) = setup.influenceGain := by
    field_simp
  have hconst :
      (∑ _r ∈ Finset.range setup.period,
        setup.blockAverageGradient noise k) =
        (setup.period : ℝ) • setup.blockAverageGradient noise k := by
    simp only [Finset.sum_const, Finset.card_range]
    exact (Nat.cast_smul_eq_nsmul ℝ setup.period
      (setup.blockAverageGradient noise k)).symm
  have hscaledZ :
      (∑ r ∈ Finset.range setup.period,
        ∑ i : Node,
          (setup.influenceGain / (nodeCount (Node := Node) : ℝ)) • Z r i) =
        (setup.influenceGain / (nodeCount (Node := Node) : ℝ)) •
          ∑ r ∈ Finset.range setup.period, ∑ i : Node, Z r i := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro r _hr
    rw [Finset.smul_sum]
  have hscaledAvg :
      (setup.influenceGain / (nodeCount (Node := Node) : ℝ)) •
          (∑ r ∈ Finset.range setup.period,
            (nodeCount (Node := Node) : ℝ) •
              setup.averageGradient
                (setup.averageIterate noise (setup.blockStart k + r))) =
        setup.influenceGain •
          ∑ r ∈ Finset.range setup.period,
            setup.averageGradient
              (setup.averageIterate noise (setup.blockStart k + r)) := by
    rw [Finset.smul_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro r _hr
    rw [smul_smul, hcancel]
  unfold blockPhaseError
  rw [Fin.sum_univ_eq_sum_range
    (fun r : ℕ => weightedState (Node := Node) (E := E)
      (setup.influence r)
      (setup.gradientTable
        (setup.primalState noise (setup.blockStart k + r))))]
  change (∑ r ∈ Finset.range setup.period,
      weightedState (Node := Node) (E := E) (setup.influence r) (Z r)) -
      setup.blockGain • setup.blockAverageGradient noise k = _
  rw [hsplit, hab]
  simp only [Finset.smul_sum, Finset.sum_sub_distrib]
  rw [hconst]
  simp only [smul_sub, smul_smul, Z]
  unfold blockGain
  rw [hscaledZ, hscaledAvg]
  module

theorem blockPhaseError_disagreement_sq_le
    (noise : NoisePath Node E) (k : ℕ) :
    ‖(setup.influenceGain / (nodeCount (Node := Node) : ℝ)) •
        (∑ r ∈ Finset.range setup.period,
          ((∑ i : Node,
              setup.gradientTable
                (setup.primalState noise (setup.blockStart k + r)) i) -
            (nodeCount (Node := Node) : ℝ) •
              setup.averageGradient
                (setup.averageIterate noise (setup.blockStart k + r))))‖ ^ 2 ≤
      (setup.influenceGain ^ 2 * (setup.period : ℝ) /
          (nodeCount (Node := Node) : ℝ)) * setup.L ^ 2 *
        ∑ r ∈ Finset.range setup.period,
          frobeniusNormSq (Node := Node) (E := E)
            (setup.consensusState noise (setup.blockStart k + r)) := by
  let n : ℝ := nodeCount (Node := Node)
  let d : ℕ → E := fun r =>
    (∑ i : Node,
        setup.gradientTable
          (setup.primalState noise (setup.blockStart k + r)) i) -
      n • setup.averageGradient
        (setup.averageIterate noise (setup.blockStart k + r))
  have hn : n ≠ 0 := by
    dsimp [n]
    exact nodeCount_real_ne_zero (Node := Node)
  have hsum := finset_sum_norm_sq_le_card_mul_sum_norm_sq
    (E := E) (Finset.range setup.period) d
  simp only [Finset.card_range] at hsum
  have hgradient :
      (∑ r ∈ Finset.range setup.period, ‖d r‖ ^ 2) ≤
        n * setup.L ^ 2 *
          ∑ r ∈ Finset.range setup.period,
            frobeniusNormSq (Node := Node) (E := E)
              (setup.consensusState noise (setup.blockStart k + r)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun r _hr => by
      dsimp [d, n]
      exact setup.gradientTable_disagreement_sq_le
        (setup.primalState noise (setup.blockStart k + r))
  have hsum' :
      ‖∑ r ∈ Finset.range setup.period, d r‖ ^ 2 ≤
        (setup.period : ℝ) *
          (n * setup.L ^ 2 *
            ∑ r ∈ Finset.range setup.period,
              frobeniusNormSq (Node := Node) (E := E)
                (setup.consensusState noise (setup.blockStart k + r))) :=
    hsum.trans (mul_le_mul_of_nonneg_left hgradient (by positivity))
  change ‖(setup.influenceGain / n) •
      (∑ r ∈ Finset.range setup.period, d r)‖ ^ 2 ≤ _
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  calc
    (setup.influenceGain / n) ^ 2 *
        ‖∑ r ∈ Finset.range setup.period, d r‖ ^ 2 ≤
      (setup.influenceGain / n) ^ 2 *
        ((setup.period : ℝ) *
          (n * setup.L ^ 2 *
            ∑ r ∈ Finset.range setup.period,
              frobeniusNormSq (Node := Node) (E := E)
                (setup.consensusState noise (setup.blockStart k + r)))) :=
      mul_le_mul_of_nonneg_left hsum' (sq_nonneg _)
    _ = _ := by
      dsimp [n]
      field_simp
      <;> ring

theorem blockPhaseError_averageDisplacement_sq_le
    (noise : NoisePath Node E) (k : ℕ) :
    ‖setup.influenceGain •
        (∑ r ∈ Finset.range setup.period,
          (setup.averageGradient
              (setup.averageIterate noise (setup.blockStart k + r)) -
            setup.blockAverageGradient noise k))‖ ^ 2 ≤
      setup.influenceGain ^ 2 * setup.L ^ 2 *
          (setup.period : ℝ) ^ 3 /
          (nodeCount (Node := Node) : ℝ) *
        ∑ j ∈ Finset.range setup.period,
          frobeniusNormSq (Node := Node) (E := E)
            (setup.primalState noise (setup.blockStart k + j + 1) -
              setup.primalState noise (setup.blockStart k + j)) := by
  classical
  let s := setup.blockStart k
  let n : ℝ := nodeCount (Node := Node)
  let D := ∑ j ∈ Finset.range setup.period,
    frobeniusNormSq (Node := Node) (E := E)
      (setup.primalState noise (s + j + 1) -
        setup.primalState noise (s + j))
  let g : ℕ → E := fun r =>
    setup.averageGradient (setup.averageIterate noise (s + r)) -
      setup.averageGradient (setup.averageIterate noise s)
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast nodeCount_pos (Node := Node)
  have hD : 0 ≤ D := by
    dsimp [D]
    unfold frobeniusNormSq
    positivity
  have hpoint (r : ℕ) (hr : r ∈ Finset.range setup.period) :
      ‖g r‖ ^ 2 ≤
        setup.L ^ 2 *
          (((setup.period : ℝ) / n) * D) := by
    have hrle : r ≤ setup.period := Nat.le_of_lt (Finset.mem_range.mp hr)
    have hprefix :
        (∑ j ∈ Finset.range r,
          frobeniusNormSq (Node := Node) (E := E)
            (setup.primalState noise (s + j + 1) -
              setup.primalState noise (s + j))) ≤ D := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hrle)
      intro j _hj _hjr
      unfold frobeniusNormSq
      positivity
    have htelescope := setup.state_displacement_telescope noise s r
    have hstate :
        frobeniusNormSq (Node := Node) (E := E)
            (setup.primalState noise (s + r) -
              setup.primalState noise s) ≤
          (setup.period : ℝ) * D := by
      calc
        _ ≤ (r : ℝ) *
            ∑ j ∈ Finset.range r,
              frobeniusNormSq (Node := Node) (E := E)
                (setup.primalState noise (s + j + 1) -
                  setup.primalState noise (s + j)) := htelescope
        _ ≤ (r : ℝ) * D :=
          mul_le_mul_of_nonneg_left hprefix (by positivity)
        _ ≤ (setup.period : ℝ) * D :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hrle) hD
    have havg :
        ‖setup.averageIterate noise (s + r) -
            setup.averageIterate noise s‖ ^ 2 ≤
          ((setup.period : ℝ) / n) * D := by
      calc
        _ ≤ n⁻¹ *
            frobeniusNormSq (Node := Node) (E := E)
              (setup.primalState noise (s + r) -
                setup.primalState noise s) := by
          simpa only [n] using setup.averageIterate_sub_sq_le noise s (s + r)
        _ ≤ n⁻¹ * ((setup.period : ℝ) * D) :=
          mul_le_mul_of_nonneg_left hstate (inv_nonneg.mpr hn.le)
        _ = ((setup.period : ℝ) / n) * D := by
          rw [div_eq_mul_inv]
          ring
    have hlip := setup.averageGradient_lipschitz_bound
      (setup.averageIterate noise (s + r)) (setup.averageIterate noise s)
    have hsq :
        ‖g r‖ ^ 2 ≤ setup.L ^ 2 *
          ‖setup.averageIterate noise (s + r) -
            setup.averageIterate noise s‖ ^ 2 := by
      dsimp [g]
      simpa [mul_pow] using
        ((sq_le_sq₀ (norm_nonneg _)
          (mul_nonneg setup.L_pos.le (norm_nonneg _))).2 hlip)
    exact hsq.trans (mul_le_mul_of_nonneg_left havg (sq_nonneg setup.L))
  have hpoints :
      (∑ r ∈ Finset.range setup.period, ‖g r‖ ^ 2) ≤
        (setup.period : ℝ) *
          (setup.L ^ 2 * (((setup.period : ℝ) / n) * D)) := by
    calc
      _ ≤ ∑ _r ∈ Finset.range setup.period,
          setup.L ^ 2 * (((setup.period : ℝ) / n) * D) :=
        Finset.sum_le_sum fun r hr => hpoint r hr
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsum := finset_sum_norm_sq_le_card_mul_sum_norm_sq
    (E := E) (Finset.range setup.period) g
  simp only [Finset.card_range] at hsum
  have hsum' :
      ‖∑ r ∈ Finset.range setup.period, g r‖ ^ 2 ≤
        (setup.period : ℝ) *
          ((setup.period : ℝ) *
            (setup.L ^ 2 * (((setup.period : ℝ) / n) * D))) :=
    hsum.trans (mul_le_mul_of_nonneg_left hpoints (by positivity))
  change ‖setup.influenceGain •
      (∑ r ∈ Finset.range setup.period, g r)‖ ^ 2 ≤
    setup.influenceGain ^ 2 * setup.L ^ 2 *
      (setup.period : ℝ) ^ 3 / n * D
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  calc
    setup.influenceGain ^ 2 *
        ‖∑ r ∈ Finset.range setup.period, g r‖ ^ 2 ≤
      setup.influenceGain ^ 2 *
        ((setup.period : ℝ) *
          ((setup.period : ℝ) *
            (setup.L ^ 2 * (((setup.period : ℝ) / n) * D)))) :=
      mul_le_mul_of_nonneg_left hsum' (sq_nonneg _)
    _ = _ := by ring

/- Appendix B's Abel contribution with the exact `P_d L^2` coefficient.
The combined finite Cauchy--Schwarz estimate is essential here: applying a
generic norm-of-sum square bound would introduce an inadmissible factor `p`. -/
theorem blockPhaseError_abel_sq_le
    (noise : NoisePath Node E) (k : ℕ) :
    ‖∑ r ∈ Finset.range (setup.period - 1),
        weightedState (Node := Node) (E := E)
          (setup.influencePartialSum r)
          (setup.gradientTable
              (setup.primalState noise (setup.blockStart k + r)) -
            setup.gradientTable
              (setup.primalState noise (setup.blockStart k + r + 1)))‖ ^ 2 ≤
      setup.influenceAbelConstant * setup.L ^ 2 *
        ∑ r ∈ Finset.range (setup.period - 1),
          frobeniusNormSq (Node := Node) (E := E)
            (setup.primalState noise (setup.blockStart k + r) -
              setup.primalState noise (setup.blockStart k + r + 1)) := by
  have hgeneric := finset_weightedState_sum_sq_le_product_energies
    (Node := Node) (E := E) (Finset.range (setup.period - 1))
    (fun r => setup.influencePartialSum r)
    (fun r =>
      setup.gradientTable
          (setup.primalState noise (setup.blockStart k + r)) -
        setup.gradientTable
          (setup.primalState noise (setup.blockStart k + r + 1)))
  have hgradient :
      (∑ r ∈ Finset.range (setup.period - 1),
          frobeniusNormSq (Node := Node) (E := E)
            (setup.gradientTable
                (setup.primalState noise (setup.blockStart k + r)) -
              setup.gradientTable
                (setup.primalState noise (setup.blockStart k + r + 1)))) ≤
        setup.L ^ 2 *
          ∑ r ∈ Finset.range (setup.period - 1),
            frobeniusNormSq (Node := Node) (E := E)
              (setup.primalState noise (setup.blockStart k + r) -
                setup.primalState noise (setup.blockStart k + r + 1)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun r _hr =>
      setup.gradientTable_difference_frobeniusSq_le
        (setup.primalState noise (setup.blockStart k + r))
        (setup.primalState noise (setup.blockStart k + r + 1))
  have habel_nonneg : 0 ≤ setup.influenceAbelConstant := by
    unfold influenceAbelConstant rowNormSq
    positivity
  calc
    _ ≤ setup.influenceAbelConstant *
        ∑ r ∈ Finset.range (setup.period - 1),
          frobeniusNormSq (Node := Node) (E := E)
            (setup.gradientTable
                (setup.primalState noise (setup.blockStart k + r)) -
              setup.gradientTable
                (setup.primalState noise (setup.blockStart k + r + 1))) := by
          simpa only [influenceAbelConstant] using hgeneric
    _ ≤ setup.influenceAbelConstant *
        (setup.L ^ 2 *
          ∑ r ∈ Finset.range (setup.period - 1),
            frobeniusNormSq (Node := Node) (E := E)
              (setup.primalState noise (setup.blockStart k + r) -
                setup.primalState noise (setup.blockStart k + r + 1))) :=
      mul_le_mul_of_nonneg_left hgradient habel_nonneg
    _ = _ := by ring

theorem blockPhaseError_pathwise_energy_bound
    (noise : NoisePath Node E) (K : ℕ) :
    ∑ k ∈ Finset.range K, ‖setup.blockPhaseError noise k‖ ^ 2 ≤
      setup.L ^ 2 *
        (setup.phaseConsensusCoefficient *
            ∑ t ∈ Finset.range (setup.completeBlockHorizon K + 1),
              frobeniusNormSq (Node := Node) (E := E)
                (setup.consensusState noise t) +
          setup.phaseDisplacementCoefficient *
            ∑ t ∈ Finset.range (setup.completeBlockHorizon K),
              frobeniusNormSq (Node := Node) (E := E)
                (setup.primalState noise (t + 1) -
                  setup.primalState noise t)) := by
  classical
  let q : ℕ → ℝ := fun t =>
    frobeniusNormSq (Node := Node) (E := E) (setup.consensusState noise t)
  let d : ℕ → ℝ := fun t =>
    frobeniusNormSq (Node := Node) (E := E)
      (setup.primalState noise (t + 1) - setup.primalState noise t)
  have hq_nonneg (t : ℕ) : 0 ≤ q t := by
    dsimp [q]
    unfold frobeniusNormSq
    positivity
  have hd_nonneg (t : ℕ) : 0 ≤ d t := by
    dsimp [d]
    unfold frobeniusNormSq
    positivity
  have hsub_comm (X Y : State Node E) :
      frobeniusNormSq (Node := Node) (E := E) (X - Y) =
        frobeniusNormSq (Node := Node) (E := E) (Y - X) := by
    unfold frobeniusNormSq
    apply Finset.sum_congr rfl
    intro i _hi
    simp only [Pi.sub_apply]
    rw [show X i - Y i = -(Y i - X i) by module, norm_neg]
  have hthree (a b c : E) :
      ‖a + b + c‖ ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
    have hnorm : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
      calc
        _ ≤ ‖a + b‖ + ‖c‖ := norm_add_le _ _
        _ ≤ (‖a‖ + ‖b‖) + ‖c‖ := by
          gcongr
          exact norm_add_le _ _
    have hsq := (sq_le_sq₀ (norm_nonneg _)
      (add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))
        (norm_nonneg _))).2 hnorm
    nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖a‖ - ‖c‖),
      sq_nonneg (‖b‖ - ‖c‖)]
  have hblock (k : ℕ) :
      ‖setup.blockPhaseError noise k‖ ^ 2 ≤
        setup.L ^ 2 *
          (setup.phaseConsensusCoefficient *
              ∑ r ∈ Finset.range setup.period,
                q (setup.blockStart k + r) +
            setup.phaseDisplacementCoefficient *
              ∑ r ∈ Finset.range setup.period,
                d (setup.blockStart k + r)) := by
    let a : E :=
      (setup.influenceGain / (nodeCount (Node := Node) : ℝ)) •
        (∑ r ∈ Finset.range setup.period,
          ((∑ i : Node,
              setup.gradientTable
                (setup.primalState noise (setup.blockStart k + r)) i) -
            (nodeCount (Node := Node) : ℝ) •
              setup.averageGradient
                (setup.averageIterate noise (setup.blockStart k + r))))
    let b : E := setup.influenceGain •
      (∑ r ∈ Finset.range setup.period,
        (setup.averageGradient
            (setup.averageIterate noise (setup.blockStart k + r)) -
          setup.blockAverageGradient noise k))
    let c : E :=
      ∑ r ∈ Finset.range (setup.period - 1),
        weightedState (Node := Node) (E := E)
          (setup.influencePartialSum r)
          (setup.gradientTable
              (setup.primalState noise (setup.blockStart k + r)) -
            setup.gradientTable
              (setup.primalState noise (setup.blockStart k + r + 1)))
    have ha :
        ‖a‖ ^ 2 ≤
          (setup.influenceGain ^ 2 * (setup.period : ℝ) /
              (nodeCount (Node := Node) : ℝ)) * setup.L ^ 2 *
            ∑ r ∈ Finset.range setup.period,
              q (setup.blockStart k + r) := by
      simpa only [a, q] using setup.blockPhaseError_disagreement_sq_le noise k
    have hb :
        ‖b‖ ^ 2 ≤
          setup.influenceGain ^ 2 * setup.L ^ 2 *
              (setup.period : ℝ) ^ 3 /
              (nodeCount (Node := Node) : ℝ) *
            ∑ r ∈ Finset.range setup.period,
              d (setup.blockStart k + r) := by
      simpa only [b, d] using
        setup.blockPhaseError_averageDisplacement_sq_le noise k
    have hd_sub :
        (∑ r ∈ Finset.range (setup.period - 1),
          frobeniusNormSq (Node := Node) (E := E)
            (setup.primalState noise (setup.blockStart k + r) -
              setup.primalState noise (setup.blockStart k + r + 1))) ≤
          ∑ r ∈ Finset.range setup.period,
            d (setup.blockStart k + r) := by
      calc
        _ = ∑ r ∈ Finset.range (setup.period - 1),
            d (setup.blockStart k + r) := by
          apply Finset.sum_congr rfl
          intro r _hr
          dsimp [d]
          exact hsub_comm _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_mono (Nat.sub_le setup.period 1))
          intro r _hr _hnot
          exact hd_nonneg (setup.blockStart k + r)
    have hc0 := setup.blockPhaseError_abel_sq_le noise k
    have hc :
        ‖c‖ ^ 2 ≤ setup.influenceAbelConstant * setup.L ^ 2 *
          ∑ r ∈ Finset.range setup.period,
            d (setup.blockStart k + r) := by
      have hcoeff : 0 ≤ setup.influenceAbelConstant * setup.L ^ 2 := by
        unfold influenceAbelConstant rowNormSq
        positivity
      exact hc0.trans (mul_le_mul_of_nonneg_left hd_sub hcoeff)
    rw [setup.blockPhaseError_eq_three_terms noise k]
    change ‖a + b + c‖ ^ 2 ≤ _
    calc
      _ ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := hthree a b c
      _ ≤ 3 *
          (((setup.influenceGain ^ 2 * (setup.period : ℝ) /
                (nodeCount (Node := Node) : ℝ)) * setup.L ^ 2 *
              ∑ r ∈ Finset.range setup.period,
                q (setup.blockStart k + r)) +
            (setup.influenceGain ^ 2 * setup.L ^ 2 *
                (setup.period : ℝ) ^ 3 /
                (nodeCount (Node := Node) : ℝ) *
              ∑ r ∈ Finset.range setup.period,
                d (setup.blockStart k + r)) +
            setup.influenceAbelConstant * setup.L ^ 2 *
              ∑ r ∈ Finset.range setup.period,
                d (setup.blockStart k + r)) := by
        gcongr
      _ = _ := by
        unfold phaseConsensusCoefficient phaseDisplacementCoefficient
        ring
  have hblocks :
      (∑ k ∈ Finset.range K, ‖setup.blockPhaseError noise k‖ ^ 2) ≤
        setup.L ^ 2 *
          (setup.phaseConsensusCoefficient *
              ∑ k ∈ Finset.range K,
                ∑ r ∈ Finset.range setup.period,
                  q (setup.blockStart k + r) +
            setup.phaseDisplacementCoefficient *
              ∑ k ∈ Finset.range K,
                ∑ r ∈ Finset.range setup.period,
                  d (setup.blockStart k + r)) := by
    calc
      _ ≤ ∑ k ∈ Finset.range K,
          setup.L ^ 2 *
            (setup.phaseConsensusCoefficient *
                ∑ r ∈ Finset.range setup.period,
                  q (setup.blockStart k + r) +
              setup.phaseDisplacementCoefficient *
                ∑ r ∈ Finset.range setup.period,
                  d (setup.blockStart k + r)) :=
        Finset.sum_le_sum fun k _hk => hblock k
      _ = _ := by
        rw [Finset.mul_sum]
        simp only [mul_add, Finset.sum_add_distrib]
        rw [← Finset.mul_sum, ← Finset.mul_sum,
          ← Finset.mul_sum, ← Finset.mul_sum]
  have hq_blocks :
      (∑ k ∈ Finset.range K,
          ∑ r ∈ Finset.range setup.period,
            q (setup.blockStart k + r)) =
        ∑ t ∈ Finset.range (setup.completeBlockHorizon K), q t := by
    simpa only [blockStart, completeBlockHorizon] using
      (sum_range_mul_eq_sum_blocks q K setup.period).symm
  have hd_blocks :
      (∑ k ∈ Finset.range K,
          ∑ r ∈ Finset.range setup.period,
            d (setup.blockStart k + r)) =
        ∑ t ∈ Finset.range (setup.completeBlockHorizon K), d t := by
    simpa only [blockStart, completeBlockHorizon] using
      (sum_range_mul_eq_sum_blocks d K setup.period).symm
  have hq_extend :
      (∑ t ∈ Finset.range (setup.completeBlockHorizon K), q t) ≤
        ∑ t ∈ Finset.range (setup.completeBlockHorizon K + 1), q t := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (Nat.le_succ _))
    intro t _ht _hnot
    exact hq_nonneg t
  have hEQ : 0 ≤ setup.phaseConsensusCoefficient := by
    unfold phaseConsensusCoefficient
    positivity
  calc
    _ ≤ setup.L ^ 2 *
          (setup.phaseConsensusCoefficient *
              ∑ k ∈ Finset.range K,
                ∑ r ∈ Finset.range setup.period,
                  q (setup.blockStart k + r) +
            setup.phaseDisplacementCoefficient *
              ∑ k ∈ Finset.range K,
                ∑ r ∈ Finset.range setup.period,
                  d (setup.blockStart k + r)) := hblocks
    _ = setup.L ^ 2 *
          (setup.phaseConsensusCoefficient *
              ∑ t ∈ Finset.range (setup.completeBlockHorizon K), q t +
            setup.phaseDisplacementCoefficient *
              ∑ t ∈ Finset.range (setup.completeBlockHorizon K), d t) := by
      rw [hq_blocks, hd_blocks]
    _ ≤ setup.L ^ 2 *
          (setup.phaseConsensusCoefficient *
              ∑ t ∈ Finset.range (setup.completeBlockHorizon K + 1), q t +
            setup.phaseDisplacementCoefficient *
              ∑ t ∈ Finset.range (setup.completeBlockHorizon K), d t) := by
      gcongr
    _ = _ := by rfl

theorem blockPhaseError_memLp_two
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) (k : ℕ) :
    MemLp (fun ω => setup.blockPhaseError (oracle.noise ω) k) 2 μ := by
  classical
  let KL : NNReal := ⟨setup.L, setup.L_pos.le⟩
  have hgradient_lipschitz (i : Node) :
      LipschitzWith KL (setup.componentGradient i) := by
    rw [lipschitzWith_iff_norm_sub_le]
    intro x y
    simpa [KL, componentGradient] using
      setup.componentGradient_lipschitz_bound i x y
  have hgrad (t : ℕ) (i : Node) : MemLp (fun ω =>
      setup.gradientTable (setup.primalState (oracle.noise ω) t) i) 2 μ := by
    simpa [gradientTable] using
      memLp_two_comp_lipschitz (setup.componentGradient i) KL
        (hgradient_lipschitz i)
        ((setup.generated_pushpull_coordinate_memLp μ oracle horacle t).1 i)
  have hweighted (r : Fin setup.period) : MemLp (fun ω =>
      weightedState (Node := Node) (E := E) (setup.influence r.1)
        (setup.gradientTable
          (setup.primalState (oracle.noise ω)
            (setup.blockStart k + r.1)))) 2 μ := by
    unfold weightedState
    apply memLp_finset_sum Finset.univ
    intro i _hi
    exact (hgrad (setup.blockStart k + r.1) i).const_smul
      (setup.influence r.1 i)
  have hsum : MemLp (fun ω =>
      ∑ r : Fin setup.period,
        weightedState (Node := Node) (E := E) (setup.influence r.1)
          (setup.gradientTable
            (setup.primalState (oracle.noise ω)
              (setup.blockStart k + r.1)))) 2 μ := by
    apply memLp_finset_sum Finset.univ
    intro r _hr
    exact hweighted r
  have havg : MemLp (fun ω =>
      setup.averageGradient
        (setup.averageIterate (oracle.noise ω) (setup.blockStart k))) 2 μ := by
    simpa only [randomAverageIterate] using
      setup.averageGradient_randomAverageIterate_memLp_two
        μ oracle horacle (setup.blockStart k)
  simpa only [blockPhaseError, blockAverageGradient] using
    hsum.sub (havg.const_smul setup.blockGain)

set_option maxHeartbeats 800000 in
theorem blockPhaseError_energy_bound
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) (K : ℕ) :
    ∑ k ∈ Finset.range K,
        ∫ ω, ‖setup.blockPhaseError (oracle.noise ω) k‖ ^ 2 ∂μ ≤
      setup.L ^ 2 *
        (setup.phaseConsensusCoefficient * setup.consensusEnergy μ oracle
            (setup.completeBlockHorizon K) +
          setup.phaseDisplacementCoefficient * setup.displacementEnergy μ oracle
            (setup.completeBlockHorizon K)) := by
  classical
  let N := setup.completeBlockHorizon K
  let KL : NNReal := ⟨setup.L, setup.L_pos.le⟩
  have hgradient_lipschitz (i : Node) :
      LipschitzWith KL (setup.componentGradient i) := by
    rw [lipschitzWith_iff_norm_sub_le]
    intro x y
    simpa [KL, componentGradient] using
      setup.componentGradient_lipschitz_bound i x y
  have hgenerated (t : ℕ) :=
    setup.generated_pushpull_coordinate_memLp μ oracle horacle t
  have hgrad (t : ℕ) (i : Node) : MemLp (fun ω =>
      setup.gradientTable (setup.primalState (oracle.noise ω) t) i) 2 μ := by
    simpa [gradientTable] using
      memLp_two_comp_lipschitz (setup.componentGradient i) KL
        (hgradient_lipschitz i) ((hgenerated t).1 i)
  have havgGrad (t : ℕ) : MemLp (fun ω =>
      setup.averageGradient (setup.averageIterate (oracle.noise ω) t)) 2 μ := by
    simpa only [randomAverageIterate] using
      setup.averageGradient_randomAverageIterate_memLp_two μ oracle horacle t
  have hphase_mem (k : ℕ) : MemLp (fun ω =>
      setup.blockPhaseError (oracle.noise ω) k) 2 μ := by
    have hweighted (r : Fin setup.period) : MemLp (fun ω =>
        weightedState (Node := Node) (E := E) (setup.influence r.1)
          (setup.gradientTable
            (setup.primalState (oracle.noise ω)
              (setup.blockStart k + r.1)))) 2 μ := by
      unfold weightedState
      apply memLp_finset_sum Finset.univ
      intro i _hi
      exact (hgrad (setup.blockStart k + r.1) i).const_smul
        (setup.influence r.1 i)
    have hsum : MemLp (fun ω =>
        ∑ r : Fin setup.period,
          weightedState (Node := Node) (E := E) (setup.influence r.1)
            (setup.gradientTable
              (setup.primalState (oracle.noise ω)
                (setup.blockStart k + r.1)))) 2 μ := by
      apply memLp_finset_sum Finset.univ
      intro r _hr
      exact hweighted r
    have havg := (havgGrad (setup.blockStart k)).const_smul setup.blockGain
    simpa only [blockPhaseError, blockAverageGradient] using hsum.sub havg
  have hphase_int (k : ℕ) : Integrable (fun ω =>
      ‖setup.blockPhaseError (oracle.noise ω) k‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (hphase_mem k).aestronglyMeasurable).1
      (hphase_mem k)
  have havgIterate (t : ℕ) : MemLp (fun ω =>
      setup.averageIterate (oracle.noise ω) t) 2 μ := by
    have hsum : MemLp (fun ω =>
        ∑ i : Node, setup.primalState (oracle.noise ω) t i) 2 μ := by
      apply memLp_finset_sum Finset.univ
      intro i _hi
      exact (hgenerated t).1 i
    simpa [averageIterate, arithmeticAverage] using
      hsum.const_smul ((nodeCount (Node := Node) : ℝ)⁻¹)
  have hconsensus (t : ℕ) (i : Node) : MemLp (fun ω =>
      setup.consensusState (oracle.noise ω) t i) 2 μ := by
    simpa [consensusState_eq_state_sub_average] using
      ((hgenerated t).1 i).sub (havgIterate t)
  have hQ_int (t : ℕ) : Integrable (fun ω =>
      frobeniusNormSq (Node := Node) (E := E)
        (setup.consensusState (oracle.noise ω) t)) μ :=
    frobeniusNormSq_integrable_of_coordinate_memLp
      (fun i => hconsensus t i)
  have hD_int (t : ℕ) : Integrable (fun ω =>
      frobeniusNormSq (Node := Node) (E := E)
        (setup.primalState (oracle.noise ω) (t + 1) -
          setup.primalState (oracle.noise ω) t)) μ := by
    apply frobeniusNormSq_integrable_of_coordinate_memLp
    intro i
    exact ((hgenerated (t + 1)).1 i).sub ((hgenerated t).1 i)
  have hleft_int := integrable_finset_sum (Finset.range K)
    (fun k _hk => hphase_int k)
  have hQ_sum := integrable_finset_sum (Finset.range (N + 1))
    (fun t _ht => hQ_int t)
  have hD_sum := integrable_finset_sum (Finset.range N)
    (fun t _ht => hD_int t)
  have hright_int : Integrable (fun ω =>
      setup.L ^ 2 *
        (setup.phaseConsensusCoefficient *
            ∑ t ∈ Finset.range (N + 1),
              frobeniusNormSq (Node := Node) (E := E)
                (setup.consensusState (oracle.noise ω) t) +
          setup.phaseDisplacementCoefficient *
            ∑ t ∈ Finset.range N,
              frobeniusNormSq (Node := Node) (E := E)
                (setup.primalState (oracle.noise ω) (t + 1) -
                  setup.primalState (oracle.noise ω) t))) μ :=
    ((hQ_sum.const_mul setup.phaseConsensusCoefficient).add
      (hD_sum.const_mul setup.phaseDisplacementCoefficient)).const_mul
        (setup.L ^ 2)
  have hmono :
      (∫ ω, ∑ k ∈ Finset.range K,
          ‖setup.blockPhaseError (oracle.noise ω) k‖ ^ 2 ∂μ) ≤
        ∫ ω, setup.L ^ 2 *
          (setup.phaseConsensusCoefficient *
              ∑ t ∈ Finset.range (N + 1),
                frobeniusNormSq (Node := Node) (E := E)
                  (setup.consensusState (oracle.noise ω) t) +
            setup.phaseDisplacementCoefficient *
              ∑ t ∈ Finset.range N,
                frobeniusNormSq (Node := Node) (E := E)
                  (setup.primalState (oracle.noise ω) (t + 1) -
                    setup.primalState (oracle.noise ω) t)) ∂μ := by
    apply MeasureTheory.integral_mono_ae hleft_int hright_int
    exact Filter.Eventually.of_forall fun ω => by
      simpa only [N] using
        setup.blockPhaseError_pathwise_energy_bound (oracle.noise ω) K
  calc
    (∑ k ∈ Finset.range K,
        ∫ ω, ‖setup.blockPhaseError (oracle.noise ω) k‖ ^ 2 ∂μ) =
      ∫ ω, ∑ k ∈ Finset.range K,
        ‖setup.blockPhaseError (oracle.noise ω) k‖ ^ 2 ∂μ := by
      rw [MeasureTheory.integral_finset_sum]
      exact fun k _hk => hphase_int k
    _ ≤ _ := hmono
    _ = setup.L ^ 2 *
        (setup.phaseConsensusCoefficient *
            ∑ t ∈ Finset.range (N + 1),
              ∫ ω, frobeniusNormSq (Node := Node) (E := E)
                (setup.consensusState (oracle.noise ω) t) ∂μ +
          setup.phaseDisplacementCoefficient *
            ∑ t ∈ Finset.range N,
              ∫ ω, frobeniusNormSq (Node := Node) (E := E)
                (setup.primalState (oracle.noise ω) (t + 1) -
                  setup.primalState (oracle.noise ω) t) ∂μ) := by
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add,
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_finset_sum, MeasureTheory.integral_finset_sum]
      all_goals
        first
        | exact (hQ_sum.const_mul setup.phaseConsensusCoefficient).add
            (hD_sum.const_mul setup.phaseDisplacementCoefficient)
        | exact hQ_sum.const_mul _
        | exact hD_sum.const_mul _
        | exact fun t _ht => hQ_int t
        | exact fun t _ht => hD_int t
    _ = _ := by
      dsimp [N]
      rfl

set_option maxHeartbeats 800000 in
theorem stateFeedbackEnergy_pre_bound
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) (K : ℕ) :
    setup.stateFeedbackEnergySum μ oracle K ≤
      setup.rhoInitialConstant * setup.initialGradientHeterogeneity ^ 2 +
        setup.L ^ 2 *
          (setup.stateFeedbackConsensusCoefficient *
              setup.consensusEnergy μ oracle (setup.completeBlockHorizon K) +
            setup.stateFeedbackDisplacementCoefficient *
              setup.displacementEnergy μ oracle
                (setup.completeBlockHorizon K)) := by
  classical
  let N := setup.completeBlockHorizon K
  have hgenerated (t : ℕ) :=
    setup.generated_pushpull_coordinate_memLp μ oracle horacle t
  have havg (t : ℕ) : MemLp (fun ω =>
      setup.averageIterate (oracle.noise ω) t) 2 μ := by
    have hsum : MemLp (fun ω =>
        ∑ i : Node, setup.primalState (oracle.noise ω) t i) 2 μ := by
      apply memLp_finset_sum Finset.univ
      intro i _hi
      exact (hgenerated t).1 i
    simpa [averageIterate, arithmeticAverage] using
      hsum.const_smul ((nodeCount (Node := Node) : ℝ)⁻¹)
  have hhybrid (k : ℕ) : MemLp (fun ω =>
      setup.blockStartHybridCenter (oracle.noise ω) k) 2 μ := by
    unfold blockStartHybridCenter weightedState
    apply memLp_finset_sum Finset.univ
    intro i _hi
    exact ((hgenerated (setup.blockStart k)).1 i).const_smul
      (setup.perronLeft 0 i)
  have hcenter_mem (k : ℕ) : MemLp (fun ω =>
      setup.blockStartHybridCenter (oracle.noise ω) k -
        setup.averageIterate (oracle.noise ω) (setup.blockStart k)) 2 μ :=
    (hhybrid k).sub (havg (setup.blockStart k))
  have hcenter_int (k : ℕ) : Integrable (fun ω =>
      ‖setup.blockStartHybridCenter (oracle.noise ω) k -
        setup.averageIterate (oracle.noise ω) (setup.blockStart k)‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (hcenter_mem k).aestronglyMeasurable).1
      (hcenter_mem k)
  have hconsensus (t : ℕ) (i : Node) : MemLp (fun ω =>
      setup.consensusState (oracle.noise ω) t i) 2 μ := by
    simpa [consensusState_eq_state_sub_average] using
      ((hgenerated t).1 i).sub (havg t)
  have hQ_int (t : ℕ) : Integrable (fun ω =>
      frobeniusNormSq (Node := Node) (E := E)
        (setup.consensusState (oracle.noise ω) t)) μ :=
    frobeniusNormSq_integrable_of_coordinate_memLp
      (fun i => hconsensus t i)
  have hcenter_sum_int := integrable_finset_sum (Finset.range K)
    (fun k _hk => hcenter_int k)
  have hQ_sum_int := integrable_finset_sum (Finset.range (N + 1))
    (fun t _ht => hQ_int t)
  have hcenter_bound :
      (∑ k ∈ Finset.range K,
        ∫ ω, ‖setup.blockStartHybridCenter (oracle.noise ω) k -
          setup.averageIterate (oracle.noise ω) (setup.blockStart k)‖ ^ 2 ∂μ) ≤
        setup.hybridWeightDeviationNorm ^ 2 *
          setup.consensusEnergy μ oracle N := by
    have hmono :
        (∫ ω, ∑ k ∈ Finset.range K,
          ‖setup.blockStartHybridCenter (oracle.noise ω) k -
            setup.averageIterate (oracle.noise ω) (setup.blockStart k)‖ ^ 2 ∂μ) ≤
          ∫ ω, setup.hybridWeightDeviationNorm ^ 2 *
            ∑ t ∈ Finset.range (N + 1),
              frobeniusNormSq (Node := Node) (E := E)
                (setup.consensusState (oracle.noise ω) t) ∂μ := by
      apply MeasureTheory.integral_mono_ae hcenter_sum_int
        (hQ_sum_int.const_mul _)
      exact Filter.Eventually.of_forall fun ω => by
        have hpath := setup.blockStartHybridCenter_mismatch_pathwise_energy_bound
          (oracle.noise ω) K
        have hextend :
            (∑ t ∈ Finset.range N,
              frobeniusNormSq (Node := Node) (E := E)
                (setup.consensusState (oracle.noise ω) t)) ≤
              ∑ t ∈ Finset.range (N + 1),
                frobeniusNormSq (Node := Node) (E := E)
                  (setup.consensusState (oracle.noise ω) t) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_mono (Nat.le_succ _))
          intro t _ht _hnot
          unfold frobeniusNormSq
          positivity
        have hpathN :
            (∑ k ∈ Finset.range K,
              ‖setup.blockStartHybridCenter (oracle.noise ω) k -
                setup.averageIterate (oracle.noise ω)
                  (setup.blockStart k)‖ ^ 2) ≤
              setup.hybridWeightDeviationNorm ^ 2 *
                ∑ t ∈ Finset.range N,
                  frobeniusNormSq (Node := Node) (E := E)
                    (setup.consensusState (oracle.noise ω) t) := by
          simpa only [N] using hpath
        exact hpathN.trans
          (mul_le_mul_of_nonneg_left hextend (sq_nonneg _))
    calc
      _ = ∫ ω, ∑ k ∈ Finset.range K,
          ‖setup.blockStartHybridCenter (oracle.noise ω) k -
            setup.averageIterate (oracle.noise ω) (setup.blockStart k)‖ ^ 2 ∂μ := by
        rw [MeasureTheory.integral_finset_sum]
        exact fun k _hk => hcenter_int k
      _ ≤ _ := hmono
      _ = setup.hybridWeightDeviationNorm ^ 2 *
          (∑ t ∈ Finset.range (N + 1),
            ∫ ω, frobeniusNormSq (Node := Node) (E := E)
              (setup.consensusState (oracle.noise ω) t) ∂μ) := by
        rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_finset_sum]
        · exact fun t _ht => hQ_int t
      _ = _ := by rfl
  have hphase_int (k : ℕ) : Integrable (fun ω =>
      ‖setup.blockPhaseError (oracle.noise ω) k‖ ^ 2) μ := by
    have hmem := setup.blockPhaseError_memLp_two μ oracle horacle k
    exact (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).1 hmem
  have hhigh_mem (k : ℕ) : MemLp (fun ω =>
      setup.highPassIncrement (oracle.noise ω) k) 2 μ := by
    simpa only [highPassIncrement] using
      (setup.meanLiftCorrection_memLp_two μ oracle horacle (k + 1)).sub
        (setup.meanLiftCorrection_memLp_two μ oracle horacle k)
  have hhigh_int (k : ℕ) : Integrable (fun ω =>
      ‖setup.highPassIncrement (oracle.noise ω) k‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (hhigh_mem k).aestronglyMeasurable).1
      (hhigh_mem k)
  have hphase := setup.blockPhaseError_energy_bound μ oracle horacle K
  have hhigh := setup.highPassIncrement_energy_bound μ oracle horacle K
  have hdecomp :
      setup.stateFeedbackEnergySum μ oracle K =
        setup.blockGain ^ 2 * setup.L ^ 2 *
            (∑ k ∈ Finset.range K,
              ∫ ω, ‖setup.blockStartHybridCenter (oracle.noise ω) k -
                setup.averageIterate (oracle.noise ω)
                  (setup.blockStart k)‖ ^ 2 ∂μ) +
          (∑ k ∈ Finset.range K,
            ∫ ω, ‖setup.blockPhaseError (oracle.noise ω) k‖ ^ 2 ∂μ) +
          ∑ k ∈ Finset.range K,
            ∫ ω, ‖setup.highPassIncrement (oracle.noise ω) k‖ ^ 2 ∂μ := by
    unfold stateFeedbackEnergySum stateFeedbackEnergy
    calc
      _ = ∑ k ∈ Finset.range K,
          (setup.blockGain ^ 2 * setup.L ^ 2 *
              (∫ ω, ‖setup.blockStartHybridCenter (oracle.noise ω) k -
                setup.averageIterate (oracle.noise ω)
                  (setup.blockStart k)‖ ^ 2 ∂μ) +
            (∫ ω, ‖setup.blockPhaseError (oracle.noise ω) k‖ ^ 2 ∂μ) +
            ∫ ω, ‖setup.highPassIncrement (oracle.noise ω) k‖ ^ 2 ∂μ) := by
        apply Finset.sum_congr rfl
        intro k _hk
        rw [MeasureTheory.integral_add, MeasureTheory.integral_add,
          MeasureTheory.integral_const_mul]
        all_goals
          first
          | exact ((hcenter_int k).const_mul _).add (hphase_int k)
          | exact (hcenter_int k).const_mul _
          | exact hphase_int k
          | exact hhigh_int k
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum]
  rw [hdecomp]
  calc
    _ ≤ setup.blockGain ^ 2 * setup.L ^ 2 *
          (setup.hybridWeightDeviationNorm ^ 2 *
            setup.consensusEnergy μ oracle N) +
        setup.L ^ 2 *
          (setup.phaseConsensusCoefficient * setup.consensusEnergy μ oracle N +
            setup.phaseDisplacementCoefficient * setup.displacementEnergy μ oracle N) +
        (setup.rhoInitialConstant * setup.initialGradientHeterogeneity ^ 2 +
          setup.rhoDisplacementConstant * setup.L ^ 2 *
            setup.displacementEnergy μ oracle N) := by
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_left hcenter_bound (by positivity)) hphase)
        hhigh
    _ = _ := by
      dsimp [N]
      unfold stateFeedbackConsensusCoefficient
        stateFeedbackDisplacementCoefficient
      ring

/-- Source-shaped specification of the finite noise-tracker filter constant
`V_tau` from (7.1): it uniformly bounds the second moment of `η_k`. -/
def NoiseTrackerFilterConstantSpec (Vtau : ℝ) : Prop :=
  0 ≤ Vtau ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (oracle : OracleNoiseProcess Ω Node E),
        setup.StochasticOracleAssumptions μ oracle →
          ∀ k : ℕ,
            ∫ ω, ‖setup.noiseLiftCorrection (oracle.noise ω) k‖ ^ 2 ∂μ ≤
              Vtau * setup.sigma ^ 2

/-- Formula-defined finite noise-tracker filter constant `V_tau`; the paper
notes that one may take `d_*^2 M_C^2 c_C^2 n/(1-r_*^2)`. -/
noncomputable def noiseTrackerFilterConstant : ℝ :=
  setup.correctedLiftNormZero ^ 2 * setup.columnContractionConstant ^ 2 *
    setup.pullDeviationNormMax ^ 2 * (nodeCount (Node := Node) : ℝ) /
      (1 - setup.contractionRate ^ 2)

/- The predicate below records the retired contract verbatim.  It is kept
private because strict positivity was not asserted by the source; its only
purpose is to state the formal counterexample which justified correcting the
public contract above. -/
def LegacyStrictNoiseTrackerFilterConstantSpec (Vtau : ℝ) : Prop :=
  0 < Vtau ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (oracle : OracleNoiseProcess Ω Node E),
        setup.StochasticOracleAssumptions μ oracle →
          ∀ k : ℕ,
            ∫ ω, ‖setup.noiseLiftCorrection (oracle.noise ω) k‖ ^ 2 ∂μ ≤
              Vtau * setup.sigma ^ 2

/- A feasible one-node instance used only to certify the degenerate case
omitted by the retired strict contract.  Its objective is the smooth,
bounded-below quadratic `x ↦ x²`, and both network schedules are the period-one
identity schedule. -/
noncomputable def singletonQuadraticSetup : Setup Unit ℝ where
  componentObjective := fun _ x => x ^ 2
  x0 := 1
  L := 2
  L_pos := by norm_num
  component_lsmooth := by
    intro _
    constructor
    · fun_prop
    · intro x y
      have hgradient (z : ℝ) : ∇ (fun w : ℝ => w ^ 2) z = 2 * z := by
        simpa using ((hasDerivAt_id z).pow 2).hasGradientAt'.gradient
      rw [hgradient x, hgradient y]
      rw [← mul_sub]
      simp
  objective_bddBelow := by
    refine ⟨0, ?_⟩
    rintro y ⟨x, rfl⟩
    simp [finiteAverageObjectiveOf, SOptLib.finiteUniformAverage]
    positivity
  Delta_pos := by
    have hobjective :
        finiteAverageObjectiveOf (Node := Unit) (E := ℝ)
            (fun _ x => x ^ 2) = fun x : ℝ => x ^ 2 := by
      funext x
      simp [finiteAverageObjectiveOf, SOptLib.finiteUniformAverage]
    have hinf :
        SOptLib.objectiveInfimumValue (Set.univ : Set ℝ)
            (fun x : ℝ => x ^ 2) = 0 := by
      unfold SOptLib.objectiveInfimumValue
      apply (show IsLeast ((fun x : ℝ => x ^ 2) '' Set.univ) 0 by
        constructor
        · exact ⟨0, Set.mem_univ 0, by norm_num⟩
        · rintro y ⟨x, _hx, rfl⟩
          positivity).csInf_eq
    rw [hobjective, hinf]
    norm_num
  sigma := 0
  sigma_nonneg := by norm_num
  alpha := 1
  period := 1
  period_pos := by norm_num
  minPositiveWeight := 1
  minPositiveWeight_pos := by norm_num
  R := fun _ => identityMatrix (Node := Unit)
  C := fun _ => identityMatrix (Node := Unit)
  R_periodic := by intros; rfl
  C_periodic := by intros; rfl
  R_rowStochastic := fun _ => identityMatrix_rowStochastic
  C_columnStochastic := fun _ => identityMatrix_columnStochastic
  R_positiveDiagonal := fun _ => identityMatrix_positiveDiagonal
  C_positiveDiagonal := fun _ => identityMatrix_positiveDiagonal
  R_positiveEntriesLowerBounded := by
    intro _ i j hij
    cases i
    cases j
    simp [identityMatrix]
  C_positiveEntriesLowerBounded := by
    intro _ i j hij
    cases i
    cases j
    simp [identityMatrix]
  R_stronglyConnected := by
    intro _ i j
    cases i
    cases j
    exact Relation.ReflTransGen.refl
  C_stronglyConnected := by
    intro _ i j
    cases i
    cases j
    exact Relation.ReflTransGen.refl

theorem matrixEuclideanOperatorNorm_matrixSub_self
    (A : NodeMatrix Node) :
    matrixEuclideanOperatorNorm (Node := Node)
        (matrixSub (Node := Node) A A) = 0 := by
  apply le_antisymm
  · unfold matrixEuclideanOperatorNorm
    apply csInf_le
    · refine ⟨0, ?_⟩
      intro c hc
      exact hc.1
    · constructor
      · exact le_rfl
      · intro x
        simp [matrixMulVector, matrixSub, rowEuclideanNorm, rowNormSq]
  · exact (matrixEuclideanOperatorNorm_spec
      (Node := Node) (matrixSub (Node := Node) A A)).1

theorem singletonQuadraticSetup_pullDeviationNormMax_eq_zero :
    singletonQuadraticSetup.pullDeviationNormMax = 0 := by
  unfold pullDeviationNormMax periodMax
  simp [singletonQuadraticSetup,
    matrixEuclideanOperatorNorm_matrixSub_self]

theorem singletonQuadraticSetup_noiseTrackerFilterConstant_eq_zero :
    singletonQuadraticSetup.noiseTrackerFilterConstant = 0 := by
  unfold noiseTrackerFilterConstant
  rw [singletonQuadraticSetup_pullDeviationNormMax_eq_zero]
  ring

/- Formal falsity certificate for the old interface.  The instance above
satisfies every field of `Setup`, but its exact source formula has `c_C = 0`,
so no proof of the legacy strict-positivity conjunct can exist. -/
theorem singletonQuadraticSetup_not_legacyStrictNoiseTrackerFilterConstantSpec :
    ¬ singletonQuadraticSetup.LegacyStrictNoiseTrackerFilterConstantSpec
        singletonQuadraticSetup.noiseTrackerFilterConstant := by
  intro hlegacy
  rw [singletonQuadraticSetup_noiseTrackerFilterConstant_eq_zero] at hlegacy
  exact (lt_irrefl 0) hlegacy.1

/-- Nonnegativity of the exact source formula for `V_tau`.  Strict positivity
is not source-valid: for a singleton network the pull-deviation factor is
zero, while the paper's zero-denominator convention still leaves `alpha_max`
well-defined. -/
theorem noiseTrackerFilterConstant_nonneg :
    0 ≤ setup.noiseTrackerFilterConstant := by
  have hdenominator : 0 < 1 - setup.contractionRate ^ 2 := by
    nlinarith [setup.contractionRate_nonneg, setup.contractionRate_lt_one]
  unfold noiseTrackerFilterConstant
  exact div_nonneg (by positivity) hdenominator.le

/-- The selected filter constant satisfies its source-shaped contract. -/
theorem noiseTrackerFilterConstant_spec :
    setup.NoiseTrackerFilterConstantSpec setup.noiseTrackerFilterConstant := by
  refine ⟨setup.noiseTrackerFilterConstant_nonneg, ?_⟩
  intro Ω _ _ _ μ _ oracle horacle k
  have hop := setup.correctedLiftOperatorNorm_spec 0
  have herr := setup.noise_tracker_error_secondMoment_bound
    μ oracle horacle (setup.blockStart k)
  have hpoint (ω : Ω) :
      ‖setup.noiseLiftCorrection (oracle.noise ω) k‖ ^ 2 ≤
        setup.correctedLiftNormZero ^ 2 *
          frobeniusNormSq (Node := Node) (E := E)
            (setup.noiseTrackerError (oracle.noise ω) (setup.blockStart k)) := by
    have hact := hop.2
      (setup.noiseTrackerErrorZeroSum (oracle.noise ω) (setup.blockStart k))
    have hsq := (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hop.1 (Real.sqrt_nonneg _))).2 hact
    rw [mul_pow] at hsq
    have hfrobenius_nonneg : 0 ≤ frobeniusNormSq (Node := Node) (E := E)
        (setup.noiseTrackerErrorZeroSum
          (oracle.noise ω) (setup.blockStart k)).1 := by
      unfold frobeniusNormSq
      positivity
    rw [Real.sq_sqrt hfrobenius_nonneg] at hsq
    simpa [noiseLiftCorrection, correctedLiftNormZero,
      noiseTrackerErrorZeroSum] using hsq
  have hlift_mem := setup.noiseLiftCorrection_memLp_two
    μ oracle horacle k
  have hlift_int : Integrable
      (fun ω => ‖setup.noiseLiftCorrection (oracle.noise ω) k‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hlift_mem.aestronglyMeasurable).1
      hlift_mem
  have herror_int : Integrable (fun ω =>
      frobeniusNormSq (Node := Node) (E := E)
        (setup.noiseTrackerError (oracle.noise ω) (setup.blockStart k))) μ := by
    apply frobeniusNormSq_integrable_of_coordinate_memLp
    intro i
    exact (setup.splitTrackerErrors_coordinate_memLp μ oracle horacle
      (setup.blockStart k)).2 i
  have hint :
      (∫ ω, ‖setup.noiseLiftCorrection (oracle.noise ω) k‖ ^ 2 ∂μ) ≤
        ∫ ω, setup.correctedLiftNormZero ^ 2 *
          frobeniusNormSq (Node := Node) (E := E)
            (setup.noiseTrackerError (oracle.noise ω) (setup.blockStart k)) ∂μ := by
    apply MeasureTheory.integral_mono_ae hlift_int
      (herror_int.const_mul _)
    exact Filter.Eventually.of_forall hpoint
  calc
    (∫ ω, ‖setup.noiseLiftCorrection (oracle.noise ω) k‖ ^ 2 ∂μ) ≤
        setup.correctedLiftNormZero ^ 2 *
          (∫ ω, frobeniusNormSq (Node := Node) (E := E)
            (setup.noiseTrackerError (oracle.noise ω) (setup.blockStart k)) ∂μ) := by
      simpa only [MeasureTheory.integral_const_mul] using hint
    _ ≤ setup.correctedLiftNormZero ^ 2 *
        ((setup.columnContractionConstant ^ 2 *
            setup.pullDeviationNormMax ^ 2 * (nodeCount (Node := Node) : ℝ) /
          (1 - setup.contractionRate ^ 2)) * setup.sigma ^ 2) :=
      mul_le_mul_of_nonneg_left herr (sq_nonneg _)
    _ = setup.noiseTrackerFilterConstant * setup.sigma ^ 2 := by
      unfold noiseTrackerFilterConstant
      ring

/-- Universe-polymorphic form of the noise-driven lift correction bound (7.1). -/
theorem NoiseTrackerFilterBound_universe
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) :
    ∀ k : ℕ,
      ∫ ω, ‖setup.noiseLiftCorrection (oracle.noise ω) k‖ ^ 2 ∂μ ≤
        setup.noiseTrackerFilterConstant * setup.sigma ^ 2 :=
  setup.noiseTrackerFilterConstant_spec.2 μ oracle horacle

/-- Section 7 / (7.1): uniform second-moment bound for the noise-driven lift
correction `η_k`. -/
theorem NoiseTrackerFilterBound
    {Ω : Type} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E)
    (horacle : setup.StochasticOracleAssumptions μ oracle) :
    ∀ k : ℕ,
      ∫ ω, ‖setup.noiseLiftCorrection (oracle.noise ω) k‖ ^ 2 ∂μ ≤
        setup.noiseTrackerFilterConstant * setup.sigma ^ 2 :=
  setup.NoiseTrackerFilterBound_universe μ oracle horacle

/-- Source-shaped Lemma 6.1 constant specification: the selected
`C_{B,0}`, `C_g`, and `C_sigma` are tied to the actual ST inequality (6.27),
not merely to isolated formula witnesses. -/
def JointStateEstimateConstantsSpec (CB0 Cg Csigma : ℝ) : Prop :=
  0 ≤ CB0 ∧ 0 ≤ Cg ∧ 0 ≤ Csigma ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (oracle : OracleNoiseProcess Ω Node E) (alpha : ℝ) (K : ℕ),
        setup.StochasticOracleAssumptions μ oracle →
          0 < alpha → alpha ≤ setup.alphaStable →
            (setup.withStepsize alpha).stateFeedbackEnergySum μ oracle K ≤
              CB0 * setup.initialGradientHeterogeneity ^ 2 +
                Cg * alpha ^ 2 * setup.blockGain ^ 2 * setup.L ^ 2 *
                  (setup.withStepsize alpha).blockGradientEnergy μ oracle K +
                Csigma * alpha ^ 2 * setup.L ^ 2 *
                  (nodeCount (Node := Node) : ℝ) * setup.sigma ^ 2 * K

/-- Formula-defined transient-feedback constant
`C_{B,0}=C_{rho,0}+A_B Qhat_0+D_B Dhat_0`. -/
noncomputable def stateFeedbackInitialConstant : ℝ :=
  setup.rhoInitialConstant +
    setup.stateFeedbackConsensusCoefficient * setup.finalConsensusInitialConstant +
      setup.stateFeedbackDisplacementCoefficient *
        setup.finalDisplacementInitialConstant

/-- Formula-defined stationary-feedback constant
`C_g=(A_B Qhat_g+D_B Dhat_g)/H^2`. -/
noncomputable def stationaryFeedbackConstant : ℝ :=
  (setup.stateFeedbackConsensusCoefficient * setup.finalConsensusGradientConstant +
      setup.stateFeedbackDisplacementCoefficient *
        setup.finalDisplacementGradientConstant) /
    setup.blockGain ^ 2

/-- Formula-defined random-feedback constant
`C_sigma=p(A_B Qhat_sigma+D_B Dhat_sigma)`. -/
noncomputable def randomFeedbackConstant : ℝ :=
  (setup.period : ℝ) *
    (setup.stateFeedbackConsensusCoefficient * setup.finalConsensusNoiseConstant +
      setup.stateFeedbackDisplacementCoefficient *
        setup.finalDisplacementNoiseConstant)

/-- Formula-defined triple `(C_{B,0}, C_g, C_sigma)` from Lemma 6.1. -/
noncomputable def jointStateEstimateConstants : ℝ × ℝ × ℝ :=
  (setup.stateFeedbackInitialConstant,
    setup.stationaryFeedbackConstant,
    setup.randomFeedbackConstant)

/- The three B-pre constants are network quantities and hence invariant under
replacing only the algorithmic stepsize.  The proof explicitly transports the
unique Perron sequences because their canonical selection is noncomputable. -/
theorem withStepsize_feedback_constants_eq (alpha : ℝ) :
    let stepped := setup.withStepsize alpha
    stepped.rhoInitialConstant = setup.rhoInitialConstant ∧
      stepped.stateFeedbackConsensusCoefficient =
          setup.stateFeedbackConsensusCoefficient ∧
        stepped.stateFeedbackDisplacementCoefficient =
          setup.stateFeedbackDisplacementCoefficient := by
  classical
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
  have hright (t : ℕ) : stepped.perronRight t = setup.perronRight t := by
    unfold perronRight
    exact congrArg (fun seqs => seqs.2 t) hperron
  have hpullLift (t j : ℕ) :
      stepped.pullLiftProduct t j = setup.pullLiftProduct t j := by
    induction j with
    | zero => rfl
    | succ j ih =>
        simp only [pullLiftProduct]
        rw [ih]
        rfl
  have hpullWindow (r j : ℕ) :
      stepped.pullWindowProduct r j = setup.pullWindowProduct r j := by
    induction j with
    | zero => rfl
    | succ j ih =>
        simp only [pullWindowProduct]
        rw [ih]
        rfl
  have hinfluenceSeries (r j : ℕ) :
      stepped.influenceSeriesTerm r j = setup.influenceSeriesTerm r j := by
    unfold influenceSeriesTerm
    rw [hleft, hpullWindow]
    rfl
  have hinfluence (r : ℕ) : stepped.influence r = setup.influence r := by
    unfold influence
    rw [hleft]
    congr 1
    apply tsum_congr
    intro j
    exact hinfluenceSeries r j
  have hinfluenceGain : stepped.influenceGain = setup.influenceGain := by
    unfold influenceGain
    congr 1
    apply Finset.sum_congr rfl
    intro r _hr
    rw [hinfluence]
  have hblockGain : stepped.blockGain = setup.blockGain := by
    unfold blockGain
    rw [hinfluenceGain]
    rfl
  have hcentered (r : ℕ) :
      stepped.centeredInfluence r = setup.centeredInfluence r := by
    unfold centeredInfluence
    rw [hinfluence, hinfluenceGain]
  have hpartial (r : ℕ) :
      stepped.influencePartialSum r = setup.influencePartialSum r := by
    unfold influencePartialSum
    apply Finset.sum_congr rfl
    intro j _hj
    exact hcentered j
  have habel : stepped.influenceAbelConstant = setup.influenceAbelConstant := by
    unfold influenceAbelConstant
    apply Finset.sum_congr rfl
    intro r _hr
    rw [hpartial]
  have hresidualMatrix (t : ℕ) :
      stepped.perronResidualMatrix t = setup.perronResidualMatrix t := by
    unfold perronResidualMatrix
    rw [hright]
  have hresidualMax :
      stepped.perronResidualNormMax = setup.perronResidualNormMax := by
    unfold perronResidualNormMax periodMax
    congr 1
  have hcorrectedSeries (t j : ℕ) (W : ZeroSumState Node E) :
      stepped.correctedLiftSeriesTerm t j W =
        setup.correctedLiftSeriesTerm t j W := by
    unfold correctedLiftSeriesTerm
    rw [hleft, hpullLift]
  have hcorrected (t : ℕ) (W : ZeroSumState Node E) :
      stepped.correctedLift t W = setup.correctedLift t W := by
    unfold correctedLift
    apply tsum_congr
    intro j
    exact hcorrectedSeries t j W
  have hcorrectedNorm :
      stepped.correctedLiftNormZero = setup.correctedLiftNormZero := by
    unfold correctedLiftNormZero correctedLiftOperatorNorm
    congr 1
    ext c
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hc, hbound⟩
      exact ⟨hc, fun W => by simpa only [hcorrected] using hbound W⟩
    · rintro ⟨hc, hbound⟩
      exact ⟨hc, fun W => by simpa only [hcorrected] using hbound W⟩
  have hhybrid :
      stepped.hybridWeightDeviationNorm = setup.hybridWeightDeviationNorm := by
    unfold hybridWeightDeviationNorm
    rw [hleft]
  have hrho0 : stepped.rhoInitialConstant = setup.rhoInitialConstant := by
    unfold rhoInitialConstant
    rw [hcorrectedNorm]
    rfl
  have hrhoD :
      stepped.rhoDisplacementConstant = setup.rhoDisplacementConstant := by
    unfold rhoDisplacementConstant
    rw [hcorrectedNorm, hresidualMax, hresidualMatrix]
    rfl
  have hphaseQ :
      stepped.phaseConsensusCoefficient = setup.phaseConsensusCoefficient := by
    unfold phaseConsensusCoefficient
    rw [hinfluenceGain]
    rfl
  have hphaseD :
      stepped.phaseDisplacementCoefficient = setup.phaseDisplacementCoefficient := by
    unfold phaseDisplacementCoefficient
    rw [hinfluenceGain, habel]
    rfl
  refine ⟨hrho0, ?_, ?_⟩
  · unfold stateFeedbackConsensusCoefficient
    rw [hblockGain, hhybrid, hphaseQ]
  · unfold stateFeedbackDisplacementCoefficient
    rw [hphaseD, hrhoD]

/-- The formula-defined ST constants satisfy Lemma 6.1. -/
theorem jointStateEstimateConstants_spec :
    setup.JointStateEstimateConstantsSpec setup.jointStateEstimateConstants.1
      setup.jointStateEstimateConstants.2.1 setup.jointStateEstimateConstants.2.2 := by
  have hrate_nonneg : 0 ≤ setup.contractionRate :=
    setup.PeriodicProductContraction.2.1
  have hrate_lt : setup.contractionRate < 1 :=
    setup.PeriodicProductContraction.2.2.1
  have hden : 0 ≤ 1 - setup.contractionRate := by linarith
  have hden_sq : 0 ≤ 1 - setup.contractionRate ^ 2 := by
    nlinarith [mul_nonneg hrate_nonneg (sub_pos.mpr hrate_lt).le]
  have habel : 0 ≤ setup.influenceAbelConstant := by
    unfold influenceAbelConstant rowNormSq
    positivity
  have hrho0 : 0 ≤ setup.rhoInitialConstant := by
    unfold rhoInitialConstant
    exact div_nonneg (by positivity) hden_sq
  have hrhoD : 0 ≤ setup.rhoDisplacementConstant := by
    unfold rhoDisplacementConstant
    positivity
  have hEQ : 0 ≤ setup.phaseConsensusCoefficient := by
    unfold phaseConsensusCoefficient
    positivity
  have hED : 0 ≤ setup.phaseDisplacementCoefficient := by
    unfold phaseDisplacementCoefficient
    positivity
  have hA : 0 ≤ setup.stateFeedbackConsensusCoefficient := by
    unfold stateFeedbackConsensusCoefficient
    positivity
  have hB : 0 ≤ setup.stateFeedbackDisplacementCoefficient := by
    unfold stateFeedbackDisplacementCoefficient
    positivity
  have hD0 : 0 ≤ setup.finalDisplacementInitialConstant := by
    simpa [sectionSixFinalConstants] using
      setup.sectionSixFinalConstants_nonneg ⟨0, by decide⟩
  have hDg : 0 ≤ setup.finalDisplacementGradientConstant := by
    simpa [sectionSixFinalConstants] using
      setup.sectionSixFinalConstants_nonneg ⟨1, by decide⟩
  have hDs : 0 ≤ setup.finalDisplacementNoiseConstant := by
    simpa [sectionSixFinalConstants] using
      setup.sectionSixFinalConstants_nonneg ⟨2, by decide⟩
  have hQ0 : 0 ≤ setup.finalConsensusInitialConstant := by
    simpa [sectionSixFinalConstants] using
      setup.sectionSixFinalConstants_nonneg ⟨3, by decide⟩
  have hQg : 0 ≤ setup.finalConsensusGradientConstant := by
    simpa [sectionSixFinalConstants] using
      setup.sectionSixFinalConstants_nonneg ⟨4, by decide⟩
  have hQs : 0 ≤ setup.finalConsensusNoiseConstant := by
    simpa [sectionSixFinalConstants] using
      setup.sectionSixFinalConstants_nonneg ⟨5, by decide⟩
  have hCB0 : 0 ≤ setup.stateFeedbackInitialConstant := by
    unfold stateFeedbackInitialConstant
    positivity
  have hCg : 0 ≤ setup.stationaryFeedbackConstant := by
    unfold stationaryFeedbackConstant
    exact div_nonneg (by positivity) (sq_nonneg _)
  have hCs : 0 ≤ setup.randomFeedbackConstant := by
    unfold randomFeedbackConstant
    positivity
  change setup.JointStateEstimateConstantsSpec
    setup.stateFeedbackInitialConstant setup.stationaryFeedbackConstant
      setup.randomFeedbackConstant
  unfold JointStateEstimateConstantsSpec
  refine ⟨hCB0, hCg, hCs, ?_⟩
  intro Ω _ _ _ μ _ oracle alpha K horacle halpha_pos halpha_le
  let stepped := setup.withStepsize alpha
  let N := setup.completeBlockHorizon K
  let I := setup.initialGradientHeterogeneity ^ 2
  let G := stepped.blockGradientEnergy μ oracle K
  let V := (nodeCount (Node := Node) : ℝ) * setup.sigma ^ 2 * N
  let D := stepped.displacementEnergy μ oracle N
  let Q := stepped.consensusEnergy μ oracle N
  let C0 := setup.stateFeedbackConsensusCoefficient *
      setup.finalConsensusInitialConstant +
    setup.stateFeedbackDisplacementCoefficient *
      setup.finalDisplacementInitialConstant
  let CgRaw := setup.stateFeedbackConsensusCoefficient *
      setup.finalConsensusGradientConstant +
    setup.stateFeedbackDisplacementCoefficient *
      setup.finalDisplacementGradientConstant
  let CsRaw := setup.stateFeedbackConsensusCoefficient *
      setup.finalConsensusNoiseConstant +
    setup.stateFeedbackDisplacementCoefficient *
      setup.finalDisplacementNoiseConstant
  have horacle_stepped : stepped.StochasticOracleAssumptions μ oracle := by
    simpa [stepped, withStepsize, StochasticOracleAssumptions] using horacle
  have hpre0 := stepped.stateFeedbackEnergy_pre_bound
    μ oracle horacle_stepped K
  have hfeedbackConstants := setup.withStepsize_feedback_constants_eq alpha
  dsimp only at hfeedbackConstants
  have hpre :
      stepped.stateFeedbackEnergySum μ oracle K ≤
        setup.rhoInitialConstant * I +
          setup.L ^ 2 *
            (setup.stateFeedbackConsensusCoefficient * Q +
              setup.stateFeedbackDisplacementCoefficient * D) := by
    rw [hfeedbackConstants.1, hfeedbackConstants.2.1,
      hfeedbackConstants.2.2] at hpre0
    simpa [I, Q, D, N, stepped, withStepsize] using hpre0
  have hDQ0 := setup.SectionSixFinalDisplacementConsensusEstimates_universe
    μ oracle alpha K horacle halpha_pos halpha_le
  have hD :
      D ≤ alpha ^ 2 *
        (setup.finalDisplacementInitialConstant * I +
          setup.finalDisplacementGradientConstant * G +
          setup.finalDisplacementNoiseConstant * V) := by
    convert hDQ0.1 using 1 <;> dsimp [D, I, G, V, N, stepped] <;> ring
  have hQ :
      Q ≤ alpha ^ 2 *
        (setup.finalConsensusInitialConstant * I +
          setup.finalConsensusGradientConstant * G +
          setup.finalConsensusNoiseConstant * V) := by
    convert hDQ0.2 using 1 <;> dsimp [Q, I, G, V, N, stepped] <;> ring
  have hcombined :
      setup.stateFeedbackConsensusCoefficient * Q +
          setup.stateFeedbackDisplacementCoefficient * D ≤
        alpha ^ 2 * (C0 * I + CgRaw * G + CsRaw * V) := by
    calc
      _ ≤ setup.stateFeedbackConsensusCoefficient *
            (alpha ^ 2 *
              (setup.finalConsensusInitialConstant * I +
                setup.finalConsensusGradientConstant * G +
                setup.finalConsensusNoiseConstant * V)) +
          setup.stateFeedbackDisplacementCoefficient *
            (alpha ^ 2 *
              (setup.finalDisplacementInitialConstant * I +
                setup.finalDisplacementGradientConstant * G +
                setup.finalDisplacementNoiseConstant * V)) :=
        add_le_add (mul_le_mul_of_nonneg_left hQ hA)
          (mul_le_mul_of_nonneg_left hD hB)
      _ = _ := by
        dsimp [C0, CgRaw, CsRaw]
        ring
  have hsmall := setup.alphaStable_formula_absorption halpha_pos halpha_le
  have hC0 : 0 ≤ C0 := by
    dsimp [C0]
    positivity
  have hI : 0 ≤ I := by
    dsimp [I]
    positivity
  have hinitial_absorb :
      (alpha ^ 2 * setup.L ^ 2) * (C0 * I) ≤ C0 * I := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hsmall.1 (mul_nonneg hC0 hI)
  calc
    stepped.stateFeedbackEnergySum μ oracle K ≤
        setup.rhoInitialConstant * I +
          setup.L ^ 2 *
            (setup.stateFeedbackConsensusCoefficient * Q +
              setup.stateFeedbackDisplacementCoefficient * D) := hpre
    _ ≤ setup.rhoInitialConstant * I +
          setup.L ^ 2 * (alpha ^ 2 * (C0 * I + CgRaw * G + CsRaw * V)) :=
      add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hcombined (sq_nonneg setup.L))
    _ = setup.rhoInitialConstant * I +
          (alpha ^ 2 * setup.L ^ 2) * (C0 * I) +
          alpha ^ 2 * setup.L ^ 2 * CgRaw * G +
          alpha ^ 2 * setup.L ^ 2 * CsRaw * V := by ring
    _ ≤ setup.rhoInitialConstant * I + C0 * I +
          alpha ^ 2 * setup.L ^ 2 * CgRaw * G +
          alpha ^ 2 * setup.L ^ 2 * CsRaw * V := by
      gcongr
    _ = setup.stateFeedbackInitialConstant *
          setup.initialGradientHeterogeneity ^ 2 +
        setup.stationaryFeedbackConstant * alpha ^ 2 * setup.blockGain ^ 2 *
          setup.L ^ 2 * stepped.blockGradientEnergy μ oracle K +
        setup.randomFeedbackConstant * alpha ^ 2 * setup.L ^ 2 *
          (nodeCount (Node := Node) : ℝ) * setup.sigma ^ 2 * K := by
      have hH : setup.blockGain ≠ 0 := ne_of_gt setup.blockGain_pos
      dsimp [I, G, V, C0, CgRaw, CsRaw, N]
      unfold stateFeedbackInitialConstant stationaryFeedbackConstant
        randomFeedbackConstant completeBlockHorizon
      rw [Nat.cast_mul]
      field_simp [hH]
      ring

/-- Nonnegativity of `C_{B,0}`. -/
theorem stateFeedbackInitialConstant_nonneg :
    0 ≤ setup.stateFeedbackInitialConstant := by
  exact (jointStateEstimateConstants_spec (setup := setup) :
    JointStateEstimateConstantsSpec.{_, _, 0} (setup := setup)
      setup.jointStateEstimateConstants.1
      setup.jointStateEstimateConstants.2.1
      setup.jointStateEstimateConstants.2.2).1

/-- Nonnegativity of `C_g`. -/
theorem stationaryFeedbackConstant_nonneg :
    0 ≤ setup.stationaryFeedbackConstant := by
  exact (jointStateEstimateConstants_spec (setup := setup) :
    JointStateEstimateConstantsSpec.{_, _, 0} (setup := setup)
      setup.jointStateEstimateConstants.1
      setup.jointStateEstimateConstants.2.1
      setup.jointStateEstimateConstants.2.2).2.1

/-- Nonnegativity of `C_sigma`. -/
theorem randomFeedbackConstant_nonneg :
    0 ≤ setup.randomFeedbackConstant := by
  exact (jointStateEstimateConstants_spec (setup := setup) :
    JointStateEstimateConstantsSpec.{_, _, 0} (setup := setup)
      setup.jointStateEstimateConstants.1
      setup.jointStateEstimateConstants.2.1
      setup.jointStateEstimateConstants.2.2).2.2.1

/-- Universe-polymorphic form of the joint state estimate ST (6.27). -/
theorem JointStateEstimateST_universe
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E) (alpha : ℝ) (K : ℕ)
    (horacle : setup.StochasticOracleAssumptions μ oracle)
    (halpha_pos : 0 < alpha) (halpha_le : alpha ≤ setup.alphaStable) :
    (setup.withStepsize alpha).stateFeedbackEnergySum μ oracle K ≤
      setup.stateFeedbackInitialConstant * setup.initialGradientHeterogeneity ^ 2 +
        setup.stationaryFeedbackConstant * alpha ^ 2 * setup.blockGain ^ 2 *
          setup.L ^ 2 * (setup.withStepsize alpha).blockGradientEnergy μ oracle K +
        setup.randomFeedbackConstant * alpha ^ 2 * setup.L ^ 2 *
          (nodeCount (Node := Node) : ℝ) * setup.sigma ^ 2 * K := by
  exact setup.jointStateEstimateConstants_spec.2.2.2 μ oracle alpha K
    horacle halpha_pos halpha_le

/-- Lemma 6.1 / (6.27): joint state estimate ST. -/
theorem JointStateEstimateST
    {Ω : Type} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node E) (alpha : ℝ) (K : ℕ)
    (horacle : setup.StochasticOracleAssumptions μ oracle)
    (halpha_pos : 0 < alpha) (halpha_le : alpha ≤ setup.alphaStable) :
    (setup.withStepsize alpha).stateFeedbackEnergySum μ oracle K ≤
      setup.stateFeedbackInitialConstant * setup.initialGradientHeterogeneity ^ 2 +
        setup.stationaryFeedbackConstant * alpha ^ 2 * setup.blockGain ^ 2 *
          setup.L ^ 2 * (setup.withStepsize alpha).blockGradientEnergy μ oracle K +
        setup.randomFeedbackConstant * alpha ^ 2 * setup.L ^ 2 *
          (nodeCount (Node := Node) : ℝ) * setup.sigma ^ 2 * K := by
  exact setup.JointStateEstimateST_universe μ oracle alpha K horacle
    halpha_pos halpha_le

/-- The asymptotic scale `o(T^{-1/2})`. -/
def LittleOInvSqrt (r : ℕ → ℝ) : Prop :=
  Asymptotics.IsLittleO Filter.atTop r
    (fun T : ℕ => (Real.sqrt (T : ℝ))⁻¹)

/-- Homogeneous one-dimensional quadratic components `f_i(x)=λx^2/2`. -/
def HomogeneousQuadraticComponents (quad : Setup Node ℝ) (lambda : ℝ) : Prop :=
  0 < lambda ∧ lambda ≤ quad.L ∧
    ∀ i : Node, ∀ x : ℝ, quad.componentObjective i x = lambda * x ^ 2 / 2

/-- A fixed deterministic two-node periodic network instance used by the
Section 3 counterexamples. The node type is `Bool`, so the construction is
literally two-node; the remaining clauses expose the paper's minimum positive
weight and fixed exogenous periodic schedule. -/
def FixedTwoNodeDeterministicPeriodicNetwork (inst : Setup Bool ℝ) (a : ℝ) : Prop :=
  inst.minPositiveWeight = a ∧ 0 < a ∧ 0 < inst.period ∧
    (∀ t : ℕ, inst.R (t + inst.period) = inst.R t) ∧
      ∀ t : ℕ, inst.C (t + inst.period) = inst.C t

/-- The original conjecture's residual condition
`sqrt(T) r_N(T) -> 0`. -/
def OriginalLinearSpeedupResidualSmall (residual : ℕ → ℝ) : Prop :=
  Filter.Tendsto (fun T : ℕ => Real.sqrt (T : ℝ) * residual T)
    Filter.atTop (nhds 0)

/-- Source-shaped failure of the original network-independent leading
constant: a homogeneous two-node quadratic construction whose required
dominant constant is forced to scale like `1/a`. -/
def NetworkIndependentDominantConstantCounterexample (C : ℝ) : Prop :=
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
                  ∀ residual : ℕ → ℝ, OriginalLinearSpeedupResidualSmall residual →
                    ∃ T : ℕ, 1 ≤ T ∧
                      C * inst.sigma *
                          Real.sqrt (inst.L * inst.Delta /
                            ((nodeCount (Node := Bool) : ℝ) * (T : ℝ))) +
                          residual T <
                        inst.infConstantStepsizeStationarity μ oracle T

/-- A horizon-independent predictable rule choosing a pair of push/pull
matrices from the past. This is only used to state Theorem 3.3's forbidden
network model; the positive theory keeps the network exogenous. -/
abbrev PredictableMatrixRule :=
  ℕ → (ℕ → State Bool ℝ) → NodeMatrix Bool × NodeMatrix Bool

/-- Two-node disagreement coordinate `(x_1-x_2)/2` used by the feedback rule
in Theorem 3.3. -/
noncomputable def twoNodeDisagreement (X : State Bool ℝ) : ℝ :=
  (X true - X false) / 2

theorem twoNodeDisagreement_eq_coordinates (X : State Bool ℝ) :
    twoNodeDisagreement X = X true * (1 / 2) + X false * (-1 / 2) := by
  simp [twoNodeDisagreement]
  ring

/-- The averaging pull matrix `J = 11^T/2` from the proof of Theorem 3.3. -/
noncomputable def twoNodeAveragingMatrix : NodeMatrix Bool :=
  fun _ _ => 1 / 2

/-- The push matrix `R_+ = 1(3/4,1/4)` from the proof of Theorem 3.3. -/
noncomputable def twoNodePushPlus : NodeMatrix Bool :=
  fun _ j => if j then 3 / 4 else 1 / 4

/-- The push matrix `R_- = 1(1/4,3/4)` from the proof of Theorem 3.3. -/
noncomputable def twoNodePushMinus : NodeMatrix Bool :=
  fun _ j => if j then 1 / 4 else 3 / 4

@[simp] theorem twoNodeAveragingMatrix_apply (i j : Bool) :
    twoNodeAveragingMatrix i j = 1 / 2 := rfl

@[simp] theorem twoNodePushPlus_apply (i j : Bool) :
    twoNodePushPlus i j = if j then 3 / 4 else 1 / 4 := rfl

@[simp] theorem twoNodePushMinus_apply (i j : Bool) :
    twoNodePushMinus i j = if j then 1 / 4 else 3 / 4 := rfl

/-- The fixed two-matrix set `{(R_+,J),(R_-,J)}` used by Theorem 3.3. -/
noncomputable def predictableFeedbackMatrixSet :
    Fin 2 → NodeMatrix Bool × NodeMatrix Bool :=
  fun r =>
    if r.1 = 0 then
      (twoNodePushPlus, twoNodeAveragingMatrix)
    else
      (twoNodePushMinus, twoNodeAveragingMatrix)

/-- Horizon-independent predictable feedback rule: before the current sample,
choose `R_+` when the current disagreement is nonnegative and `R_-` otherwise. -/
noncomputable def signPredictableFeedbackRule : PredictableMatrixRule :=
  fun t history =>
    if 0 ≤ twoNodeDisagreement (history t) then
      (twoNodePushPlus, twoNodeAveragingMatrix)
    else
      (twoNodePushMinus, twoNodeAveragingMatrix)

/-- Concrete homogeneous two-node sampled gradient used by Theorem 3.3's
adaptive counterexample. For `f_i(x)=x^2/2`, the exact gradient row is `x_i`;
the source Rademacher innovation `ζ_t = 2 r_t` is added only at node one. -/
noncomputable def predictableFeedbackSampledGradient
    (halfNoise : ℕ → ℝ) (t : ℕ) (X : State Bool ℝ) : State Bool ℝ :=
  fun i => X i + if i then 2 * halfNoise t else 0

/-- The concrete scalar objective used in Theorem 3.3:
`f_1(x)=f_2(x)=x^2/2`, hence `f(x)=x^2/2`. -/
noncomputable def predictableFeedbackQuadraticObjective (x : ℝ) : ℝ :=
  x ^ 2 / 2

/-- The concrete initial point in Theorem 3.3. -/
def predictableFeedbackInitialPoint : ℝ := 1

/-- Source object for Theorem 3.3's problem instance: two nodes, homogeneous
quadratic objective, and common initialization at `x_0=1`.

Book JSON: `#/key_lemmas/10` states a fixed two-node smooth convex quadratic
instance with the predictable rule and lower bound `(T-2)/(64T)`. -/
def PredictableFeedbackConcreteProblem : Prop :=
  (∀ x : ℝ, predictableFeedbackQuadraticObjective x = x ^ 2 / 2) ∧
    predictableFeedbackInitialPoint = 1

/-- Concrete adaptive push-pull state for Theorem 3.3. -/
structure PredictableFeedbackAlgorithmState where
  primal : State Bool ℝ
  tracker : State Bool ℝ

/-- The Theorem 3.3 adaptive run starts at `X_0=1 x_0^T` with `x_0=1` and
`Y_0=G_0`. -/
noncomputable def predictableFeedbackAlgorithmInitial
    (halfNoise : ℕ → ℝ) : PredictableFeedbackAlgorithmState :=
  let X0 : State Bool ℝ := fun _ => predictableFeedbackInitialPoint
  { primal := X0
    tracker := predictableFeedbackSampledGradient halfNoise 0 X0 }

/-- One generated adaptive push-pull step for Theorem 3.3, using the sign rule
to choose one of the two fixed matrix pairs before the next oracle sample. -/
noncomputable def predictableFeedbackAlgorithmStep
    (halfNoise : ℕ → ℝ) (alpha : ℝ) (t : ℕ)
    (state : PredictableFeedbackAlgorithmState) :
    PredictableFeedbackAlgorithmState :=
  let matrices :=
    if 0 ≤ twoNodeDisagreement state.primal then
      (twoNodePushPlus, twoNodeAveragingMatrix)
    else
      (twoNodePushMinus, twoNodeAveragingMatrix)
  let Xnext : State Bool ℝ :=
    leftMul (Node := Bool) (E := ℝ) matrices.1 state.primal -
      alpha • state.tracker
  let Gcur := predictableFeedbackSampledGradient halfNoise t state.primal
  let Gnext := predictableFeedbackSampledGradient halfNoise (t + 1) Xnext
  { primal := Xnext
    tracker :=
      leftMul (Node := Bool) (E := ℝ) matrices.2 state.tracker + Gnext - Gcur }

/-- Generated adaptive push-pull trajectory for Theorem 3.3. -/
noncomputable def predictableFeedbackAlgorithmTrajectory
    (halfNoise : ℕ → ℝ) (alpha : ℝ) :
    ℕ → PredictableFeedbackAlgorithmState :=
  fun t =>
    SOptLib.recursiveIterateProcess
      (predictableFeedbackAlgorithmInitial halfNoise)
      (fun k state (_ : Unit) =>
        predictableFeedbackAlgorithmStep halfNoise alpha k state) t ()

/-- The stationarity average of the concrete adaptive push-pull run. For the
homogeneous quadratic average objective `f(x)=x^2/2`, this is the squared
arithmetic average of the generated primal state. -/
noncomputable def predictableFeedbackAlgorithmStationarityAverage
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (halfNoise : Ω → ℕ → ℝ) (T : ℕ) (alpha : ℝ) : ℝ :=
  ((T : ℝ)⁻¹) *
    Finset.sum (Finset.range T) fun t =>
      ∫ ω, |arithmeticAverage (Node := Bool) (E := ℝ)
        ((predictableFeedbackAlgorithmTrajectory
          (fun k => halfNoise ω k) alpha t).primal)| ^ 2 ∂μ

/-- Scalar state obtained in the proof of Theorem 3.3 after the concrete
feedback matrices are fixed:
`m_t=(x_{1,t}+x_{2,t})/2`, `d_t=(x_{1,t}-x_{2,t})/2`, plus one-step memory for
the disagreement and the half-Rademacher noise. -/
structure PredictableFeedbackScalarState where
  mean : ℝ
  disagreement : ℝ
  previousDisagreement : ℝ
  previousHalfNoise : ℝ

/-- The scalar feedback counterexample starts from
`x_{1,0}=x_{2,0}=1`, hence `m_0=1` and `d_0=0`. -/
def predictableFeedbackScalarInitial : PredictableFeedbackScalarState :=
  { mean := 1
    disagreement := 0
    previousDisagreement := 0
    previousHalfNoise := 0 }

/-- One scalar step from equations (3.3)--(3.4), with `r_t=ζ_t/2`. -/
noncomputable def predictableFeedbackScalarStep
    (halfNoise : ℕ → ℝ) (alpha : ℝ) (t : ℕ)
    (state : PredictableFeedbackScalarState) : PredictableFeedbackScalarState :=
  let rt := halfNoise t
  let dnext :=
    if t = 0 then
      -alpha * rt
    else
      -alpha * (state.disagreement - state.previousDisagreement) -
        alpha * (rt - state.previousHalfNoise)
  { mean := (1 - alpha) * state.mean + |state.disagreement| / 2 - alpha * rt
    disagreement := dnext
    previousDisagreement := state.disagreement
    previousHalfNoise := rt }

/-- Generated scalar trajectory for the predictable-feedback counterexample. -/
noncomputable def predictableFeedbackScalarTrajectory
    (halfNoise : ℕ → ℝ) (alpha : ℝ) :
    ℕ → PredictableFeedbackScalarState :=
  fun t =>
    SOptLib.recursiveIterateProcess predictableFeedbackScalarInitial
      (fun k state (_ : Unit) =>
        predictableFeedbackScalarStep halfNoise alpha k state) t ()

/-- The half-Rademacher source oracle used in Theorem 3.3's proof:
`r_t=ζ_t/2` takes values `±1/2` with equal mass and is independent over time. -/
def HalfRademacherNoise {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (halfNoise : Ω → ℕ → ℝ) : Prop :=
  iIndepFun (fun t : ℕ => fun ω : Ω => halfNoise ω t) μ ∧
    ∀ t : ℕ,
      μ.real {ω : Ω | halfNoise ω t = 1 / 2} = 1 / 2 ∧
        μ.real {ω : Ω | halfNoise ω t = -(1 / 2)} = 1 / 2

/-- Concrete generated stationarity average for the adaptive
predictable-feedback counterexample of Theorem 3.3. For the homogeneous
quadratic `f(x)=x^2/2`, the gradient at the arithmetic average is the scalar
mean `m_t`. -/
noncomputable def predictableFeedbackStationarityAverage
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (halfNoise : Ω → ℕ → ℝ) (T : ℕ) (alpha : ℝ) : ℝ :=
  ((T : ℝ)⁻¹) *
    Finset.sum (Finset.range T) fun t =>
      ∫ ω, |(predictableFeedbackScalarTrajectory
        (fun k => halfNoise ω k) alpha t).mean| ^ 2 ∂μ

set_option maxHeartbeats 500000

theorem predictableFeedbackAlgorithmStep_coordinates
    (halfNoise : ℕ → ℝ) (alpha : ℝ) (t : ℕ)
    (state : PredictableFeedbackAlgorithmState) :
    let next := predictableFeedbackAlgorithmStep halfNoise alpha t state
    arithmeticAverage (Node := Bool) (E := ℝ) next.primal =
        arithmeticAverage (Node := Bool) (E := ℝ) state.primal +
          |twoNodeDisagreement state.primal| / 2 -
          alpha * arithmeticAverage (Node := Bool) (E := ℝ) state.tracker ∧
      twoNodeDisagreement next.primal =
        -alpha * twoNodeDisagreement state.tracker ∧
      arithmeticAverage (Node := Bool) (E := ℝ) next.tracker =
        arithmeticAverage (Node := Bool) (E := ℝ) state.tracker +
          (arithmeticAverage (Node := Bool) (E := ℝ) next.primal +
            halfNoise (t + 1)) -
          (arithmeticAverage (Node := Bool) (E := ℝ) state.primal + halfNoise t) ∧
      twoNodeDisagreement next.tracker =
        twoNodeDisagreement next.primal + halfNoise (t + 1) -
          (twoNodeDisagreement state.primal + halfNoise t) := by
  let next := predictableFeedbackAlgorithmStep halfNoise alpha t state
  change arithmeticAverage (Node := Bool) (E := ℝ) next.primal = _ ∧
    twoNodeDisagreement next.primal = _ ∧
    arithmeticAverage (Node := Bool) (E := ℝ) next.tracker = _ ∧
    twoNodeDisagreement next.tracker = _
  have hprimalMean :
      arithmeticAverage (Node := Bool) (E := ℝ) next.primal =
        arithmeticAverage (Node := Bool) (E := ℝ) state.primal +
          |twoNodeDisagreement state.primal| / 2 -
          alpha * arithmeticAverage (Node := Bool) (E := ℝ) state.tracker := by
    by_cases hsign : 0 ≤ twoNodeDisagreement state.primal
    · rw [abs_of_nonneg hsign]
      simp only [next, predictableFeedbackAlgorithmStep, if_pos hsign]
      simp [
        arithmeticAverage, twoNodeDisagreement, leftMul, twoNodePushPlus,
        nodeCount]
      <;> norm_num [twoNodePushPlus] <;> ring_nf <;> rfl
    · have hneg : twoNodeDisagreement state.primal < 0 := lt_of_not_ge hsign
      rw [abs_of_neg hneg]
      simp only [next, predictableFeedbackAlgorithmStep, if_neg hsign]
      simp [
        arithmeticAverage, twoNodeDisagreement, leftMul, twoNodePushMinus,
        nodeCount]
      <;> norm_num [twoNodePushMinus] <;> ring_nf <;> rfl
  have hprimalDis :
      twoNodeDisagreement next.primal =
        -alpha * twoNodeDisagreement state.tracker := by
    by_cases hsign : 0 ≤ twoNodeDisagreement state.primal
    · simp only [next, predictableFeedbackAlgorithmStep, if_pos hsign]
      simp [
        arithmeticAverage, twoNodeDisagreement, leftMul, nodeCount]
      <;> norm_num [twoNodePushPlus] <;> ring_nf <;> rfl
    · simp only [next, predictableFeedbackAlgorithmStep, if_neg hsign]
      simp [
        arithmeticAverage, twoNodeDisagreement, leftMul, nodeCount]
      <;> norm_num [twoNodePushMinus] <;> ring_nf <;> rfl
  have htrackerMean :
      arithmeticAverage (Node := Bool) (E := ℝ) next.tracker =
        arithmeticAverage (Node := Bool) (E := ℝ) state.tracker +
          (arithmeticAverage (Node := Bool) (E := ℝ) next.primal +
            halfNoise (t + 1)) -
          (arithmeticAverage (Node := Bool) (E := ℝ) state.primal + halfNoise t) := by
    by_cases hsign : 0 ≤ twoNodeDisagreement state.primal
    · simp only [next, predictableFeedbackAlgorithmStep, if_pos hsign]
      simp [
        predictableFeedbackSampledGradient, arithmeticAverage,
        twoNodeDisagreement, leftMul, twoNodePushPlus,
        twoNodeAveragingMatrix, nodeCount, Nat.add_comm]
      <;> norm_num [twoNodePushPlus, twoNodeAveragingMatrix]
      <;> ring_nf <;> rfl
    · simp only [next, predictableFeedbackAlgorithmStep, if_neg hsign]
      simp [
        predictableFeedbackSampledGradient, arithmeticAverage,
        twoNodeDisagreement, leftMul, twoNodePushMinus,
        twoNodeAveragingMatrix, nodeCount, Nat.add_comm]
      <;> norm_num [twoNodePushMinus, twoNodeAveragingMatrix]
      <;> ring_nf <;> rfl
  have htrackerDis :
      twoNodeDisagreement next.tracker =
        twoNodeDisagreement next.primal + halfNoise (t + 1) -
          (twoNodeDisagreement state.primal + halfNoise t) := by
    by_cases hsign : 0 ≤ twoNodeDisagreement state.primal
    · simp only [next, predictableFeedbackAlgorithmStep, if_pos hsign]
      simp [
        predictableFeedbackSampledGradient, arithmeticAverage,
        twoNodeDisagreement, leftMul, twoNodePushPlus,
        twoNodeAveragingMatrix, nodeCount, Nat.add_comm]
      <;> norm_num [twoNodePushPlus, twoNodeAveragingMatrix]
      <;> ring_nf <;> rfl
    · simp only [next, predictableFeedbackAlgorithmStep, if_neg hsign]
      simp [
        predictableFeedbackSampledGradient, arithmeticAverage,
        twoNodeDisagreement, leftMul, twoNodePushMinus,
        twoNodeAveragingMatrix, nodeCount, Nat.add_comm]
      <;> norm_num [twoNodePushMinus, twoNodeAveragingMatrix]
      <;> ring_nf <;> rfl
  exact ⟨hprimalMean, hprimalDis, htrackerMean, htrackerDis⟩

/-- The coordinate calculation behind equations (3.3)--(3.4).  Besides the
primal mean and disagreement, the two tracker coordinates are retained because
they are the induction invariants that make the generated algorithm coincide
with the scalar recursion. -/
theorem predictableFeedback_trajectory_scalar_coordinates
    (halfNoise : ℕ → ℝ) (alpha : ℝ) (t : ℕ) :
    let alg := predictableFeedbackAlgorithmTrajectory halfNoise alpha t
    let scalar := predictableFeedbackScalarTrajectory halfNoise alpha t
    arithmeticAverage (Node := Bool) (E := ℝ) alg.primal = scalar.mean ∧
      twoNodeDisagreement alg.primal = scalar.disagreement ∧
      arithmeticAverage (Node := Bool) (E := ℝ) alg.tracker =
        scalar.mean + halfNoise t ∧
      twoNodeDisagreement alg.tracker =
        scalar.disagreement - scalar.previousDisagreement + halfNoise t -
          scalar.previousHalfNoise := by
  induction t with
  | zero =>
      simp [predictableFeedbackAlgorithmTrajectory,
        predictableFeedbackScalarTrajectory, SOptLib.recursiveIterateProcess,
        predictableFeedbackAlgorithmInitial, predictableFeedbackScalarInitial,
        predictableFeedbackSampledGradient, predictableFeedbackInitialPoint,
        arithmeticAverage, twoNodeDisagreement, nodeCount, Fintype.sum_bool]
      <;> ring
  | succ t ih =>
      dsimp only at ih ⊢
      have halgSucc :
          predictableFeedbackAlgorithmTrajectory halfNoise alpha (t + 1) =
            predictableFeedbackAlgorithmStep halfNoise alpha t
              (predictableFeedbackAlgorithmTrajectory halfNoise alpha t) := rfl
      have hscalarSucc :
          predictableFeedbackScalarTrajectory halfNoise alpha (t + 1) =
            predictableFeedbackScalarStep halfNoise alpha t
              (predictableFeedbackScalarTrajectory halfNoise alpha t) := rfl
      rw [halgSucc, hscalarSucc]
      rcases ih with ⟨hmean, hdis, htrackerMean, htrackerDis⟩
      have hstep := predictableFeedbackAlgorithmStep_coordinates
        halfNoise alpha t
          (predictableFeedbackAlgorithmTrajectory halfNoise alpha t)
      dsimp only at hstep
      rcases hstep with ⟨hnextMean, hnextDis, hnextTrackerMean,
        hnextTrackerDis⟩
      by_cases ht : t = 0
      · subst t
        simp [predictableFeedbackScalarTrajectory,
          SOptLib.recursiveIterateProcess, predictableFeedbackScalarInitial,
          predictableFeedbackScalarStep] at hmean hdis htrackerMean htrackerDis ⊢
        simp [hnextMean, hnextDis, hnextTrackerMean, hnextTrackerDis,
          hmean, hdis, htrackerMean, htrackerDis]
        <;> ring
      · simp only [predictableFeedbackScalarStep, ht, if_false]
        rw [hnextTrackerMean, hnextTrackerDis, hnextMean, hnextDis,
          hmean, hdis, htrackerMean, htrackerDis]
        constructor
        · ring
        constructor
        · ring
        constructor <;> ring

set_option maxHeartbeats 200000

/-- The generated adaptive push-pull stationarity average agrees with the
scalar recursion (3.3)--(3.4), by the trajectory coordinate invariant. -/
theorem predictableFeedbackAlgorithmStationarity_eq_scalar
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (halfNoise : Ω → ℕ → ℝ) (T : ℕ) (alpha : ℝ) :
    predictableFeedbackAlgorithmStationarityAverage μ halfNoise T alpha =
      predictableFeedbackStationarityAverage μ halfNoise T alpha := by
  unfold predictableFeedbackAlgorithmStationarityAverage
    predictableFeedbackStationarityAverage
  congr 1
  apply Finset.sum_congr rfl
  intro t _ht
  apply integral_congr_ae
  filter_upwards with ω
  rw [(predictableFeedback_trajectory_scalar_coordinates
    (fun k => halfNoise ω k) alpha t).1]

/-- Source-shaped Theorem 3.3 counterexample: fixed two-node quadratic
problem, fixed matrix set, and predictable feedback rule with a nonvanishing
stationarity lower bound for every constant stepsize.

Book/PDF: `book/TimeVaryingPushPull/TimeVaryingPushPull.json` key lemma
`PredictableFeedbackNonconvergence`; `paper/TimeVaryingPushPull.pdf`,
Theorem 3.3 and equations (3.3)--(3.4). -/
def PredictableFeedbackCounterexample : Prop :=
  PredictableFeedbackConcreteProblem ∧
    ∃ Ω : Type, ∃ mΩ : MeasurableSpace Ω,
      letI : MeasurableSpace Ω := mΩ
      ∃ μ : Measure Ω, ∃ hprob : IsProbabilityMeasure μ,
        letI : IsProbabilityMeasure μ := hprob
        ∃ halfNoise : Ω → ℕ → ℝ,
          HalfRademacherNoise μ halfNoise ∧
            (∀ t history, ∃ r : Fin 2,
              signPredictableFeedbackRule t history =
                predictableFeedbackMatrixSet r) ∧
              ∀ T : ℕ, 3 ≤ T → ∀ alpha : ℝ, 0 ≤ alpha →
                ((T : ℝ) - 2) / (64 * (T : ℝ)) ≤
                  predictableFeedbackAlgorithmStationarityAverage μ halfNoise T alpha

/-- A residual rule depending only on the aggregate quantities listed in
Theorem 3.4 and not on the initial gradient heterogeneity `H_0`. -/
abbrev HeterogeneityFreeResidualRule :=
  ℕ → ℝ → ℝ → ℝ → ℝ → ℕ → ℝ → ℝ → ℝ → ℕ → ℝ

/-- A uniform onset-threshold rule depending on the same aggregate quantities
as the forbidden residual in Theorem 3.4. -/
abbrev HeterogeneityFreeThresholdRule :=
  ℕ → ℝ → ℝ → ℝ → ℝ → ℕ → ℝ → ℝ → ℝ → ℕ

/-- Fixed static push matrix `R = 1 (3/4,1/4)` used in Theorem 3.4. -/
noncomputable def heterogeneousQuadraticPush : NodeMatrix Bool :=
  twoNodePushPlus

/-- Fixed pull matrix `C=J` used in Theorem 3.4. -/
noncomputable def heterogeneousQuadraticPull : NodeMatrix Bool :=
  twoNodeAveragingMatrix

/-- Exact local-gradient table for
`f_{1,H}(x)=x^2/2+Hx`, `f_{2,H}(x)=x^2/2-Hx`. -/
noncomputable def heterogeneousQuadraticGradient
    (H : ℝ) (X : State Bool ℝ) : State Bool ℝ :=
  fun i => if i then X i + H else X i - H

/-- Initial state for the deterministic heterogeneous quadratic family:
`X_0=1 x_0^T` with `x_0=1`, and `Y_0=G_0`. -/
noncomputable def heterogeneousQuadraticInitial
    (H : ℝ) : PredictableFeedbackAlgorithmState :=
  let X0 : State Bool ℝ := fun _ => 1
  { primal := X0
    tracker := heterogeneousQuadraticGradient H X0 }

/-- One exact-gradient push-pull step for the static heterogeneous quadratic
counterexample of Theorem 3.4. -/
noncomputable def heterogeneousQuadraticStep
    (alpha H : ℝ) (_t : ℕ) (state : PredictableFeedbackAlgorithmState) :
    PredictableFeedbackAlgorithmState :=
  let Xnext : State Bool ℝ :=
    leftMul (Node := Bool) (E := ℝ) heterogeneousQuadraticPush state.primal -
      alpha • state.tracker
  let Gcur := heterogeneousQuadraticGradient H state.primal
  let Gnext := heterogeneousQuadraticGradient H Xnext
  { primal := Xnext
    tracker :=
      leftMul (Node := Bool) (E := ℝ) heterogeneousQuadraticPull state.tracker +
        Gnext - Gcur }

/-- Generated deterministic trajectory for Theorem 3.4's heterogeneous
quadratic family. -/
noncomputable def heterogeneousQuadraticTrajectory
    (alpha H : ℝ) : ℕ → PredictableFeedbackAlgorithmState :=
  fun t =>
    SOptLib.recursiveIterateProcess
      (heterogeneousQuadraticInitial H)
      (fun k state (_ : Unit) =>
        heterogeneousQuadraticStep alpha H k state) t ()

/-- Generated arithmetic-average iterate for Theorem 3.4's deterministic
heterogeneous quadratic family. -/
noncomputable def heterogeneousQuadraticAverageIterate
    (alpha H : ℝ) (t : ℕ) : ℝ :=
  arithmeticAverage (Node := Bool) (E := ℝ)
    ((heterogeneousQuadraticTrajectory alpha H t).primal)

/-- Finite-horizon stationarity average for the actual generated
heterogeneous quadratic run. Since the average objective is `x^2/2`, the
gradient at `bar x_t` is `bar x_t`. -/
noncomputable def heterogeneousQuadraticStationarityAverage
    (T : ℕ) (alpha H : ℝ) : ℝ :=
  ((T : ℝ)⁻¹) *
    Finset.sum (Finset.range T) fun t =>
      |heterogeneousQuadraticAverageIterate alpha H t| ^ 2

/-- The explicit two-step obstruction from equation (3.5) for the heterogeneous
quadratic family `f_{1,H}(x)=x^2/2+Hx`, `f_{2,H}(x)=x^2/2-Hx`. -/
noncomputable def heterogeneousQuadraticAverageAfterTwo
    (alpha H : ℝ) : ℝ :=
  (1 - alpha) ^ 2 - alpha * H / 2

/-- The fixed period `p=1` in Theorem 3.4's static two-node network. -/
def heterogeneousQuadraticAggregatePeriod : ℕ := 1

/-- The fixed minimum positive matrix weight `a=1/4` for
`R=1(3/4,1/4)` and `C=J` in Theorem 3.4. -/
noncomputable def heterogeneousQuadraticAggregateMinWeight : ℝ := 1 / 4

/-- A fixed mixing-gap parameter for the static network used in Theorem 3.4.
The proof only uses that this value is fixed by the chosen network and
independent of the heterogeneity parameter `H`. -/
noncomputable def heterogeneousQuadraticAggregateMixingGap : ℝ := 1 / 2

/-- The fixed average gain `h=1` for Theorem 3.4's static network. -/
noncomputable def heterogeneousQuadraticAggregateGain : ℝ := 1

/-- The fixed influence second moment `q=1/2` for Theorem 3.4's static
network. -/
noncomputable def heterogeneousQuadraticAggregateInfluenceSecondMoment : ℝ := 1 / 2

/-- The fixed node count `n=2` in Theorem 3.4. -/
def heterogeneousQuadraticAggregateNodeCount : ℕ := 2

/-- The fixed smoothness parameter `L=1` in Theorem 3.4's quadratic family. -/
noncomputable def heterogeneousQuadraticAggregateSmoothness : ℝ := 1

/-- The fixed objective gap `Delta=1/2` from `x0=1` and
`f(x)=x^2/2` in Theorem 3.4. -/
noncomputable def heterogeneousQuadraticAggregateDelta : ℝ := 1 / 2

/-- The deterministic exact-gradient case `sigma=0` used in Theorem 3.4. -/
noncomputable def heterogeneousQuadraticAggregateNoiseLevel : ℝ := 0

/-- Specialization of a heterogeneity-free residual rule to the single valid
aggregate tuple fixed in Theorem 3.4's proof. -/
noncomputable def heterogeneousQuadraticResidualAtSourceTuple
    (residual : HeterogeneityFreeResidualRule) (T : ℕ) : ℝ :=
  residual heterogeneousQuadraticAggregatePeriod
    heterogeneousQuadraticAggregateMinWeight
    heterogeneousQuadraticAggregateMixingGap
    heterogeneousQuadraticAggregateGain
    heterogeneousQuadraticAggregateInfluenceSecondMoment
    heterogeneousQuadraticAggregateNodeCount
    heterogeneousQuadraticAggregateSmoothness
    heterogeneousQuadraticAggregateDelta
    heterogeneousQuadraticAggregateNoiseLevel T

/-- Specialization of a heterogeneity-free stepsize rule to the single valid
aggregate tuple fixed in Theorem 3.4's proof. -/
noncomputable def heterogeneousQuadraticStepsizeAtSourceTuple
    (stepsize : HeterogeneityFreeResidualRule) (T : ℕ) : ℝ :=
  stepsize heterogeneousQuadraticAggregatePeriod
    heterogeneousQuadraticAggregateMinWeight
    heterogeneousQuadraticAggregateMixingGap
    heterogeneousQuadraticAggregateGain
    heterogeneousQuadraticAggregateInfluenceSecondMoment
    heterogeneousQuadraticAggregateNodeCount
    heterogeneousQuadraticAggregateSmoothness
    heterogeneousQuadraticAggregateDelta
    heterogeneousQuadraticAggregateNoiseLevel T

/-- Specialization of a heterogeneity-free onset threshold to the single valid
aggregate tuple fixed in Theorem 3.4's proof. -/
noncomputable def heterogeneousQuadraticThresholdAtSourceTuple
    (threshold : HeterogeneityFreeThresholdRule) : ℕ :=
  threshold heterogeneousQuadraticAggregatePeriod
    heterogeneousQuadraticAggregateMinWeight
    heterogeneousQuadraticAggregateMixingGap
    heterogeneousQuadraticAggregateGain
    heterogeneousQuadraticAggregateInfluenceSecondMoment
    heterogeneousQuadraticAggregateNodeCount
    heterogeneousQuadraticAggregateSmoothness
    heterogeneousQuadraticAggregateDelta
    heterogeneousQuadraticAggregateNoiseLevel

/-- Equation (3.5): the generated heterogeneous quadratic run has
`bar x_2=(1-alpha)^2-alpha H/2`. -/
theorem heterogeneousQuadraticAverageIterate_two
    (alpha H : ℝ) :
    heterogeneousQuadraticAverageIterate alpha H 2 =
      heterogeneousQuadraticAverageAfterTwo alpha H := by
  have hp (i : Bool) :
      (heterogeneousQuadraticTrajectory alpha H 1).primal i =
        if i then 1 - alpha * (1 + H) else 1 - alpha * (1 - H) := by
    cases i <;>
      simp [heterogeneousQuadraticTrajectory, SOptLib.recursiveIterateProcess,
        heterogeneousQuadraticStep, heterogeneousQuadraticInitial,
        heterogeneousQuadraticGradient, heterogeneousQuadraticPush,
        heterogeneousQuadraticPull, leftMul, Fintype.sum_bool,
        twoNodePushPlus, twoNodeAveragingMatrix] <;>
      ring
  have ht (i : Bool) :
      (heterogeneousQuadraticTrajectory alpha H 1).tracker i =
        if i then 1 - alpha * (1 + H) else 1 - alpha * (1 - H) := by
    cases i <;>
      simp [heterogeneousQuadraticTrajectory, SOptLib.recursiveIterateProcess,
        heterogeneousQuadraticStep, heterogeneousQuadraticInitial,
        heterogeneousQuadraticGradient, heterogeneousQuadraticPush,
        heterogeneousQuadraticPull, leftMul, Fintype.sum_bool,
        twoNodePushPlus, twoNodeAveragingMatrix] <;>
      ring
  change arithmeticAverage (Node := Bool) (E := ℝ)
      (heterogeneousQuadraticStep alpha H 1
        (heterogeneousQuadraticTrajectory alpha H 1)).primal =
    heterogeneousQuadraticAverageAfterTwo alpha H
  simp [arithmeticAverage, heterogeneousQuadraticStep, leftMul,
    Fintype.sum_bool, heterogeneousQuadraticPush, twoNodePushPlus,
    hp, ht, nodeCount, heterogeneousQuadraticAverageAfterTwo] <;>
    ring

/-- With zero stepsize the generated heterogeneous quadratic trajectory keeps
the common primal initialization, independently of the heterogeneity. -/
theorem heterogeneous_quadratic_average_iterate_zero_stepsize
    (H : ℝ) (t : ℕ) :
    heterogeneousQuadraticAverageIterate 0 H t = 1 := by
  have hp : ∀ k : ℕ, ∀ i : Bool,
      (heterogeneousQuadraticTrajectory 0 H k).primal i = 1 := by
    intro k
    induction k with
    | zero =>
        intro i
        simp [heterogeneousQuadraticTrajectory,
          SOptLib.recursiveIterateProcess, heterogeneousQuadraticInitial]
    | succ k ih =>
        intro i
        change
          (heterogeneousQuadraticStep 0 H k
            (heterogeneousQuadraticTrajectory 0 H k)).primal i = 1
        simp only [heterogeneousQuadraticStep, Pi.sub_apply, zero_smul,
          sub_zero, leftMul_apply]
        simp_rw [ih]
        cases i <;>
          norm_num [heterogeneousQuadraticPush, twoNodePushPlus,
            Fintype.sum_bool]
  simp [heterogeneousQuadraticAverageIterate, arithmeticAverage,
    Fintype.sum_bool, nodeCount, hp]

/-- For horizons containing time two, its nonnegative stationarity summand is
a lower bound for the full finite-horizon average. -/
theorem heterogeneous_quadratic_stationarity_average_ge_two_step
    (T : ℕ) (alpha H : ℝ) (hT : 3 ≤ T) :
    (T : ℝ)⁻¹ * |heterogeneousQuadraticAverageAfterTwo alpha H| ^ 2 ≤
      heterogeneousQuadraticStationarityAverage T alpha H := by
  unfold heterogeneousQuadraticStationarityAverage
  apply mul_le_mul_of_nonneg_left
  · rw [← heterogeneousQuadraticAverageIterate_two alpha H]
    exact Finset.single_le_sum
      (fun t _ht => sq_nonneg |heterogeneousQuadraticAverageIterate alpha H t|)
      (Finset.mem_range.mpr (by omega))
  · exact inv_nonneg.mpr (Nat.cast_nonneg T)

/-- A positive stepsize lets finite heterogeneity make the two-step
contribution exceed any prescribed real bound. -/
theorem exists_heterogeneity_two_step_exceeds
    (T : ℕ) (alpha B : ℝ) (hT : 0 < (T : ℝ)) (halpha : 0 < alpha) :
    ∃ H : ℝ,
      B < (T : ℝ)⁻¹ * |heterogeneousQuadraticAverageAfterTwo alpha H| ^ 2 := by
  let S : ℝ := Real.sqrt ((T : ℝ) * (|B| + 1)) + 1
  let H : ℝ := 2 * ((1 - alpha) ^ 2 + S) / alpha
  refine ⟨H, ?_⟩
  have hrad_nonneg : 0 ≤ (T : ℝ) * (|B| + 1) := by positivity
  have hsqrt_sq :
      Real.sqrt ((T : ℝ) * (|B| + 1)) ^ 2 =
        (T : ℝ) * (|B| + 1) :=
    Real.sq_sqrt hrad_nonneg
  have hsqrt_nonneg :
      0 ≤ Real.sqrt ((T : ℝ) * (|B| + 1)) := Real.sqrt_nonneg _
  have hS_sq_gt : (T : ℝ) * (|B| + 1) < S ^ 2 := by
    dsimp [S]
    nlinarith
  have hB_lt : B < |B| + 1 := by linarith [le_abs_self B]
  have hTB_lt : (T : ℝ) * B < S ^ 2 :=
    lt_trans (mul_lt_mul_of_pos_left hB_lt hT) hS_sq_gt
  have hformula : heterogeneousQuadraticAverageAfterTwo alpha H = -S := by
    dsimp [heterogeneousQuadraticAverageAfterTwo, H]
    field_simp [ne_of_gt halpha]
    <;> ring
  rw [hformula, sq_abs]
  have hneg_sq : (-S) ^ 2 = S ^ 2 := by ring
  rw [hneg_sq]
  have hT_ne : (T : ℝ) ≠ 0 := ne_of_gt hT
  calc
    B = (T : ℝ)⁻¹ * ((T : ℝ) * B) := by
      rw [← mul_assoc, inv_mul_cancel₀ hT_ne, one_mul]
    _ < (T : ℝ)⁻¹ * S ^ 2 :=
      mul_lt_mul_of_pos_left hTB_lt (inv_pos.mpr hT)

/-- Leading-plus-residual right side of the original linear-speedup conjecture,
parameterized only by the aggregate tuple listed in Theorem 3.4. -/
noncomputable def heterogeneityFreeLinearSpeedupBound
    (C : ℝ) (residual : HeterogeneityFreeResidualRule)
    (p : ℕ) (a gap h q : ℝ) (n : ℕ) (L Delta sigma : ℝ) (T : ℕ) : ℝ :=
  C * sigma * Real.sqrt (L * Delta / ((n : ℝ) * (T : ℝ))) +
    residual p a gap h q n L Delta sigma T

/-- Source convergence-bound obligation that the forbidden Theorem 3.4 claim
would have to satisfy for the generated finite-horizon stationarity averages
uniformly in the heterogeneity parameter `H`, despite its residual, stepsize,
and threshold depending only on aggregate quantities.

Book/PDF: `book/TimeVaryingPushPull/TimeVaryingPushPull.json` key lemma
`NoUniformHeterogeneityResidual`; `paper/TimeVaryingPushPull.pdf`,
Theorem 3.4 and equation (3.5). -/
def HeterogeneityFreeUniformConvergenceBound
    (C : ℝ) (residual stepsize : HeterogeneityFreeResidualRule)
    (threshold : HeterogeneityFreeThresholdRule) : Prop :=
  ∀ T,
    heterogeneousQuadraticThresholdAtSourceTuple threshold ≤ T →
      let alphaT := heterogeneousQuadraticStepsizeAtSourceTuple stepsize T
      0 ≤ alphaT ∧
        ∀ H : ℝ,
          heterogeneousQuadraticStationarityAverage T alphaT H ≤
            heterogeneityFreeLinearSpeedupBound C residual
              heterogeneousQuadraticAggregatePeriod
              heterogeneousQuadraticAggregateMinWeight
              heterogeneousQuadraticAggregateMixingGap
              heterogeneousQuadraticAggregateGain
              heterogeneousQuadraticAggregateInfluenceSecondMoment
              heterogeneousQuadraticAggregateNodeCount
              heterogeneousQuadraticAggregateSmoothness
              heterogeneousQuadraticAggregateDelta
              heterogeneousQuadraticAggregateNoiseLevel T

/-- The source assertion whose negation is Theorem 3.4: a uniform stepsize
rule and `o(T^{-1/2})` residual depending only on
`(p,a,mixing gap,h,q,n,L,Delta,sigma)`. -/
def UniformHeterogeneityFreeResidualRuleExists : Prop :=
  ∃ C : ℝ, ∃ residual : HeterogeneityFreeResidualRule,
    ∃ stepsize : HeterogeneityFreeResidualRule,
      ∃ threshold : HeterogeneityFreeThresholdRule,
        OriginalLinearSpeedupResidualSmall
          (heterogeneousQuadraticResidualAtSourceTuple residual) ∧
          HeterogeneityFreeUniformConvergenceBound C residual stepsize threshold

/-- Real-analytic matrix family on `|α| < α₁`, the hypothesis of Lemma A.1. -/
def RealAnalyticMatrixFamilyNear (A : ℝ → NodeMatrix Node) (alpha1 : ℝ) : Prop :=
  0 < alpha1 ∧ ∀ alpha : ℝ, |alpha| < alpha1 → AnalyticAt ℝ A alpha

/-- Real right eigenvectors for the unit eigenvalue of a node matrix. -/
def IsRightUnitEigenvector (A0 : NodeMatrix Node) (right : RowVector Node) : Prop :=
  right ≠ 0 ∧ matrixMulVector (Node := Node) A0 right = right

/-- Real left eigenvectors for the unit eigenvalue of a node matrix. -/
def IsLeftUnitEigenvector (A0 : NodeMatrix Node) (left : RowVector Node) : Prop :=
  left ≠ 0 ∧ rowMulMatrix (Node := Node) left A0 = left

/-- Complex scalar row vector indexed by nodes. -/
abbrev ComplexRowVector (Node : Type*) := Node → ℂ

/-- Real row vector embedded into the complex node space. -/
def complexOfRealRow (w : RowVector Node) : ComplexRowVector Node :=
  fun i => (w i : ℂ)

/-- Real node matrix acting on a complex node vector. -/
noncomputable def complexMatrixMulVector
    (A : NodeMatrix Node) (v : ComplexRowVector Node) : ComplexRowVector Node :=
  fun i => ∑ j : Node, (A i j : ℂ) * v j

/-- Residual `(A - I)v` for the complex scalar extension. -/
noncomputable def complexUnitEigenResidual
    (A : NodeMatrix Node) (v : ComplexRowVector Node) : ComplexRowVector Node :=
  complexMatrixMulVector (Node := Node) A v - v

/-- Complex right eigenvalue predicate for the real matrix after complex scalar
extension. -/
def IsComplexRightEigenvalue (A0 : NodeMatrix Node) (gamma : ℂ) : Prop :=
  ∃ v : ComplexRowVector Node,
    v ≠ 0 ∧ complexMatrixMulVector (Node := Node) A0 v = gamma • v

/-- Algebraic simplicity of the unit eigenvalue over the complex scalar
extension: the unit eigenspace is one-dimensional and there is no
length-two generalized eigenvector chain. This is the finite-dimensional
source meaning of "simple eigenvalue 1" in Lemma A.1. -/
def UnitEigenvalueAlgebraicallySimple
    (A0 : NodeMatrix Node) (right : RowVector Node) : Prop :=
  (∀ v : ComplexRowVector Node,
    complexMatrixMulVector (Node := Node) A0 v = (1 : ℂ) • v →
      ∃ c : ℂ, v = c • complexOfRealRow (Node := Node) right) ∧
    ∀ v : ComplexRowVector Node,
      complexMatrixMulVector (Node := Node) A0
          (complexUnitEigenResidual (Node := Node) A0 v) =
        (1 : ℂ) • complexUnitEigenResidual (Node := Node) A0 v →
        complexMatrixMulVector (Node := Node) A0 v = (1 : ℂ) • v

/-- Rank-one projection property for the slow Riesz projection appearing in
Appendix A. This records the algebraic surface used downstream; identifying
the projection with a contour integral is a proof obligation for Lemma A.1. -/
def RankOneProjection (P : NodeMatrix Node) : Prop :=
  matrixMul (Node := Node) P P = P ∧
    ∃ right left : RowVector Node,
      right ≠ 0 ∧ left ≠ 0 ∧ rowDot (Node := Node) left right = 1 ∧
        ∀ x : RowVector Node,
          matrixMulVector (Node := Node) P x =
            rowDot (Node := Node) left x • right

/-- Finite-dimensional source specification of the Riesz projection for the
isolated real multiplier `lambda`.

Appendix A first chooses a contour around the unit multiplier at `alpha = 0`,
then follows the enclosed multiplier as `gamma(alpha)`.  The Riesz projection
therefore satisfies the projection/eigen-relation at the moving eigenvalue,
not at the fixed value `1` away from the base point.  This predicate records
the algebraic consequences of that contour construction used by the
slow/stable splitting. -/
def RieszProjectionAtEigenvalueSpec
    (Aalpha : NodeMatrix Node) (lambda : ℝ) (P : NodeMatrix Node) : Prop :=
  matrixMul (Node := Node) Aalpha P = lambda • P ∧
    matrixMul (Node := Node) P Aalpha = lambda • P ∧
      (∀ x : RowVector Node,
        matrixMulVector (Node := Node) P x = x ↔
          matrixMulVector (Node := Node) Aalpha x = lambda • x) ∧
        ∃ radius : ℝ, 0 < radius ∧
          ∀ z : ℂ, ‖z - (lambda : ℂ)‖ = radius →
            ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z

/-- Specialization of the Riesz-projection specification to the unit
multiplier. This is the base-point surface used at `alpha = 0`; the moving
Appendix A splitting uses `IsRieszProjectionAtEigenvalue` with
`lambda = gamma alpha`. -/
def UnitRieszProjectionSpec
    (Aalpha : NodeMatrix Node) (P : NodeMatrix Node) : Prop :=
  RieszProjectionAtEigenvalueSpec (Node := Node) Aalpha 1 P

/-- Source-facing Riesz-projection clause at a specified isolated eigenvalue.
This is the finite-dimensional algebraic surface of the contour projection
used in Lemma A.1 after the enclosed unit multiplier has moved to
`gamma(alpha)`. -/
def IsRieszProjectionAtEigenvalue
    (Aalpha : NodeMatrix Node) (lambda : ℝ) (P : NodeMatrix Node) : Prop :=
  RankOneProjection (Node := Node) P ∧
    RieszProjectionAtEigenvalueSpec (Node := Node) Aalpha lambda P

/-- Base-point unit Riesz-projection clause.  This is the specialization of
`IsRieszProjectionAtEigenvalue` to eigenvalue `1`; the perturbed spectral
splitting below consumes the gamma-parameterized predicate instead. -/
def IsUnitRieszProjection
    (A : ℝ → NodeMatrix Node) (alpha : ℝ) (P : NodeMatrix Node) : Prop :=
  IsRieszProjectionAtEigenvalue (Node := Node) (A alpha) 1 P

theorem IsRieszProjectionAtEigenvalue.rankOne
    {Aalpha : NodeMatrix Node} {lambda : ℝ} {P : NodeMatrix Node}
    (h : IsRieszProjectionAtEigenvalue (Node := Node) Aalpha lambda P) :
    RankOneProjection (Node := Node) P :=
  h.1

theorem IsRieszProjectionAtEigenvalue.matrix_mul_left
    {Aalpha : NodeMatrix Node} {lambda : ℝ} {P : NodeMatrix Node}
    (h : IsRieszProjectionAtEigenvalue (Node := Node) Aalpha lambda P) :
    matrixMul (Node := Node) Aalpha P = lambda • P :=
  h.2.1

theorem IsRieszProjectionAtEigenvalue.matrix_mul_right
    {Aalpha : NodeMatrix Node} {lambda : ℝ} {P : NodeMatrix Node}
    (h : IsRieszProjectionAtEigenvalue (Node := Node) Aalpha lambda P) :
    matrixMul (Node := Node) P Aalpha = lambda • P :=
  h.2.2.1

theorem IsRieszProjectionAtEigenvalue.fixed_iff
    {Aalpha : NodeMatrix Node} {lambda : ℝ} {P : NodeMatrix Node}
    (h : IsRieszProjectionAtEigenvalue (Node := Node) Aalpha lambda P)
    (x : RowVector Node) :
    matrixMulVector (Node := Node) P x = x ↔
      matrixMulVector (Node := Node) Aalpha x = lambda • x :=
  h.2.2.2.1 x

theorem IsRieszProjectionAtEigenvalue.exists_separating_circle
    {Aalpha : NodeMatrix Node} {lambda : ℝ} {P : NodeMatrix Node}
    (h : IsRieszProjectionAtEigenvalue (Node := Node) Aalpha lambda P) :
    ∃ radius : ℝ, 0 < radius ∧
      ∀ z : ℂ, ‖z - (lambda : ℂ)‖ = radius →
        ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z :=
  h.2.2.2.2

theorem IsUnitRieszProjection.isRieszProjectionAtEigenvalue_one
    {A : ℝ → NodeMatrix Node} {alpha : ℝ} {P : NodeMatrix Node}
    (h : IsUnitRieszProjection (Node := Node) A alpha P) :
    IsRieszProjectionAtEigenvalue (Node := Node) (A alpha) 1 P :=
  h

theorem IsUnitRieszProjection.rankOne
    {A : ℝ → NodeMatrix Node} {alpha : ℝ} {P : NodeMatrix Node}
    (h : IsUnitRieszProjection (Node := Node) A alpha P) :
    RankOneProjection (Node := Node) P :=
  h.1

theorem IsUnitRieszProjection.matrix_mul_left
    {A : ℝ → NodeMatrix Node} {alpha : ℝ} {P : NodeMatrix Node}
    (h : IsUnitRieszProjection (Node := Node) A alpha P) :
    matrixMul (Node := Node) (A alpha) P = P :=
  by simpa using h.2.1

theorem IsUnitRieszProjection.matrix_mul_right
    {A : ℝ → NodeMatrix Node} {alpha : ℝ} {P : NodeMatrix Node}
    (h : IsUnitRieszProjection (Node := Node) A alpha P) :
    matrixMul (Node := Node) P (A alpha) = P :=
  by simpa using h.2.2.1

theorem IsUnitRieszProjection.fixed_iff
    {A : ℝ → NodeMatrix Node} {alpha : ℝ} {P : NodeMatrix Node}
    (h : IsUnitRieszProjection (Node := Node) A alpha P)
    (x : RowVector Node) :
    matrixMulVector (Node := Node) P x = x ↔
      matrixMulVector (Node := Node) (A alpha) x = x :=
  by simpa using h.2.2.2.1 x

theorem IsUnitRieszProjection.exists_separating_circle
    {A : ℝ → NodeMatrix Node} {alpha : ℝ} {P : NodeMatrix Node}
    (h : IsUnitRieszProjection (Node := Node) A alpha P) :
    ∃ radius : ℝ, 0 < radius ∧
      ∀ z : ℂ, ‖z - 1‖ = radius →
        ¬ IsComplexRightEigenvalue (Node := Node) (A alpha) z :=
  by simpa using h.2.2.2.2

/-- Lemma A.1's source spectral hypothesis: the unit eigenvalue of `A(0)` is
simple and isolated over the complex scalar extension, with every other
eigenvalue in the stable disk `|z| ≤ r₀`. -/
def SimpleIsolatedUnitEigenvalueStableSpectrum
    (A0 : NodeMatrix Node) (r0 : ℝ)
    (right left : RowVector Node) : Prop :=
  0 ≤ r0 ∧ r0 < 1 ∧
    IsRightUnitEigenvector (Node := Node) A0 right ∧
      IsLeftUnitEigenvector (Node := Node) A0 left ∧
        rowDot (Node := Node) left right = 1 ∧
          UnitEigenvalueAlgebraicallySimple (Node := Node) A0 right ∧
            ∀ gamma : ℂ,
              IsComplexRightEigenvalue (Node := Node) A0 gamma →
                gamma ≠ (1 : ℂ) → ‖gamma‖ ≤ r0

/-- Projection of Lemma A.1's source-facing spectral hypothesis: the unit
eigenvalue is algebraically simple over the complex scalar extension. -/
theorem SimpleIsolatedUnitEigenvalueStableSpectrum.unit_algebraicallySimple
    {A0 : NodeMatrix Node} {r0 : ℝ} {right left : RowVector Node}
    (h :
      SimpleIsolatedUnitEigenvalueStableSpectrum (Node := Node) A0 r0 right left) :
    UnitEigenvalueAlgebraicallySimple (Node := Node) A0 right :=
  h.2.2.2.2.2.1

/-- Lemma A.1's slow-stable splitting conclusion: a slow Riesz projection,
stable propagator, and uniform power bound.

Book/PDF: `book/TimeVaryingPushPull/TimeVaryingPushPull.json` key lemma
`PeriodicSpectralDecomposition`; `paper/TimeVaryingPushPull.pdf`, Appendix A
Lemma A.1 states analytic `γ`, rank-one Riesz projection `P(α)`, `A=γP+F`,
`PF=FP=0`, a stable power bound, and the derivative formula. -/
def PeriodicSpectralSplitting
    (A : ℝ → NodeMatrix Node) (r0 alpha0 theta K : ℝ)
    (right left : RowVector Node)
    (gamma : ℝ → ℝ) (P F : ℝ → NodeMatrix Node) : Prop :=
  0 < alpha0 ∧ r0 < theta ∧ theta < 1 ∧ 0 ≤ K ∧ gamma 0 = 1 ∧
    (∀ alpha : ℝ, |alpha| < alpha0 → AnalyticAt ℝ gamma alpha) ∧
      (∀ alpha : ℝ, |alpha| < alpha0 → AnalyticAt ℝ P alpha) ∧
        (∃ Aderiv : NodeMatrix Node,
          HasDerivAt A Aderiv 0 ∧
          HasDerivAt gamma
              (rowDot (Node := Node) left
                (matrixMulVector (Node := Node) Aderiv right)) 0) ∧
          ∀ alpha : ℝ, |alpha| ≤ alpha0 →
            IsRieszProjectionAtEigenvalue (Node := Node)
              (A alpha) (gamma alpha) (P alpha) ∧
              A alpha = matrixAdd (Node := Node) ((gamma alpha) • P alpha) (F alpha) ∧
                matrixMul (Node := Node) (P alpha) (F alpha) = 0 ∧
                  matrixMul (Node := Node) (F alpha) (P alpha) = 0 ∧
                    ∀ j : ℕ,
                      matrixEuclideanOperatorNorm (Node := Node)
                          (matrixPower (Node := Node) (F alpha) j) ≤
                        K * theta ^ j

/-- The fixed push matrix `R_ε` from the Section 3.1 counterexample. -/
noncomputable def twoNodeCounterexamplePush (epsilon : ℝ) : NodeMatrix Bool :=
  fun i j =>
    if i then
      if j then 1 - epsilon / 2 else epsilon / 2
    else
      if j then (1 - epsilon) / 2 else (1 + epsilon) / 2

/-- The even-phase pull matrix `A_ε` from the Section 3.1 counterexample. -/
noncomputable def twoNodeCounterexamplePullA (epsilon : ℝ) : NodeMatrix Bool :=
  fun i j =>
    if i then
      if j then 1 / 2 else epsilon
    else
      if j then 1 / 2 else 1 - epsilon

/-- The odd-phase pull matrix `B_ε` from the Section 3.1 counterexample. -/
noncomputable def twoNodeCounterexamplePullB (epsilon : ℝ) : NodeMatrix Bool :=
  fun i j =>
    if i then
      if j then 3 / 4 else epsilon
    else
      if j then 1 / 4 else 1 - epsilon

/-- One reduced lifted step `M_t(α)` from Appendix A.1 in coordinates
`(x_1,x_2,h)` with zero-sum tracker state `w=(h,-h)`. The matrix encodes
`X_{t+1}=(R_ε-αλI)X_t-αw_t` and
`w_{t+1}=C_t w_t + L(C_t-I)X_t`. -/
noncomputable def twoStepCounterexampleLiftedStep
    (R C : NodeMatrix Bool) (lambda alpha : ℝ) : NodeMatrix (Fin 3) :=
  fun i j =>
    if i = 0 then
      if j = 0 then R true true - alpha * lambda
      else if j = 1 then R true false
      else -alpha
    else if i = 1 then
      if j = 0 then R false true
      else if j = 1 then R false false - alpha * lambda
      else alpha
    else
      if j = 0 then lambda * (C true true - 1)
      else if j = 1 then lambda * C true false
      else C true true - C true false

/-- The two-step reduced lifted propagator surface
`A_ε(α)=M_1(α)M_0(α)` from Appendix A.1, on
`E=R^2 × {w : 1^T w = 0}` represented by `(x_1,x_2,h)`. -/
noncomputable def twoStepCounterexamplePropagator
    (epsilon lambda alpha : ℝ) : NodeMatrix (Fin 3) :=
  matrixMul (Node := Fin 3)
    (twoStepCounterexampleLiftedStep
      (twoNodeCounterexamplePush epsilon)
      (twoNodeCounterexamplePullB epsilon) lambda alpha)
    (twoStepCounterexampleLiftedStep
      (twoNodeCounterexamplePush epsilon)
      (twoNodeCounterexamplePullA epsilon) lambda alpha)

/-- First-order slow multiplier printed in Appendix A.1:
`λ(α)=1-2αLs_ε+O(α^2)`. -/
noncomputable def twoStepSlowMultiplierApprox
    (lambda spectralSlope alpha : ℝ) : ℝ :=
  1 - 2 * alpha * lambda * spectralSlope

/-- First-order phase-noise variance coefficient printed in Appendix A.1:
`2α^2 σ^2 q_ε+O(α^3)`, without the common `σ^2` factor. -/
noncomputable def twoStepPhaseNoiseApprox
    (noiseCoefficient alpha : ℝ) : ℝ :=
  2 * alpha ^ 2 * noiseCoefficient

/-- The two input phases of the period-two counterexample: phase `A` followed
by phase `B`. -/
inductive TwoStepPhase where
  | phaseA
  | phaseB
deriving DecidableEq, Inhabited

/-- Denominator `D = 5/8 + 5ε/4 - ε²` in the stable tracker tail coefficients
for the Section 3.1 / Appendix A.1 counterexample. -/
noncomputable def twoStepCounterexampleTailDenominator
    (epsilon : ℝ) : ℝ :=
  5 / 8 + 5 / 4 * epsilon - epsilon ^ 2

/-- Stable tracker tail coefficient `k_A=(7/4-ε)/D` for phase `A`. -/
noncomputable def twoStepCounterexampleTailA
    (epsilon : ℝ) : ℝ :=
  (7 / 4 - epsilon) / twoStepCounterexampleTailDenominator epsilon

/-- Stable tracker tail coefficient `k_B=(3/2-ε)/D` for phase `B`. -/
noncomputable def twoStepCounterexampleTailB
    (epsilon : ℝ) : ℝ :=
  (3 / 2 - epsilon) / twoStepCounterexampleTailDenominator epsilon

/-- Concrete phase-`A` noise channel for the two-step counterexample. This is
the source coefficient `b_A` with the stable tracker tail/resolvent feedback
already included, not only the current input `(A_ε-I)`. -/
noncomputable def twoStepCounterexampleNoiseChannelA
    (epsilon : ℝ) : RowVector Bool :=
  fun i =>
    if i then
      1 - epsilon -
        (1 - 2 * epsilon) * twoStepCounterexampleTailA epsilon / 2
    else
      epsilon +
        (1 - 2 * epsilon) * epsilon * twoStepCounterexampleTailA epsilon

/-- Concrete phase-`B` noise channel for the two-step counterexample. This is
the source coefficient `b_B` with the stable tracker tail/resolvent feedback
already included, not only the current input `(B_ε-I)`. -/
noncomputable def twoStepCounterexampleNoiseChannelB
    (epsilon : ℝ) : RowVector Bool :=
  fun i =>
    if i then
      1 - epsilon -
        (1 - 2 * epsilon) * twoStepCounterexampleTailB epsilon / 4
    else
      epsilon +
        (1 - 2 * epsilon) * epsilon * twoStepCounterexampleTailB epsilon

/-- Source formula for the phase-`A` coefficient `b_A`. -/
theorem twoStepCounterexampleNoiseChannelA_apply
    (epsilon : ℝ) (i : Bool) :
    twoStepCounterexampleNoiseChannelA epsilon i =
      if i then
        1 - epsilon -
          (1 - 2 * epsilon) * twoStepCounterexampleTailA epsilon / 2
      else
        epsilon +
          (1 - 2 * epsilon) * epsilon * twoStepCounterexampleTailA epsilon := by
  rfl

/-- Source formula for the phase-`B` coefficient `b_B`. -/
theorem twoStepCounterexampleNoiseChannelB_apply
    (epsilon : ℝ) (i : Bool) :
    twoStepCounterexampleNoiseChannelB epsilon i =
      if i then
        1 - epsilon -
          (1 - 2 * epsilon) * twoStepCounterexampleTailB epsilon / 4
      else
        epsilon +
          (1 - 2 * epsilon) * epsilon * twoStepCounterexampleTailB epsilon := by
  rfl

/-- Epsilon-dependent slow-drift coefficient `s_ε` for Appendix A.1, defined
from the concrete two-step matrix surface rather than supplied as a witness. -/
noncomputable def twoStepCounterexampleSpectralSlope (epsilon : ℝ) : ℝ :=
  (rowSum (Node := Bool) (twoStepCounterexampleNoiseChannelA epsilon) +
    rowSum (Node := Bool) (twoStepCounterexampleNoiseChannelB epsilon)) / 2

/-- Epsilon-dependent phase-noise coefficient `q_ε`, defined from the concrete
`b_A` and `b_B` channels. -/
noncomputable def twoStepCounterexampleNoiseCoefficient (epsilon : ℝ) : ℝ :=
  (rowNormSq (Node := Bool) (twoStepCounterexampleNoiseChannelA epsilon) +
    rowNormSq (Node := Bool) (twoStepCounterexampleNoiseChannelB epsilon)) / 2

/-- Concrete phase-noise variance coefficient as a function of stepsize. -/
noncomputable def twoStepCounterexamplePhaseNoise
    (epsilon alpha : ℝ) : ℝ :=
  2 * alpha ^ 2 * twoStepCounterexampleNoiseCoefficient epsilon

/-- One-step lifted noise input `N_t(α)` in reduced coordinates
`(x_1,x_2,h)`, specialized to a basis innovation at one node. -/
noncomputable def twoStepCounterexampleOneStepNoiseInput
    (C : NodeMatrix Bool) (alpha : ℝ) (node : Bool) :
    RowVector (Fin 3) :=
  fun coord =>
    if coord = 0 then
      if node then -alpha else 0
    else if coord = 1 then
      if node then 0 else -alpha
    else
      if node then C true true - 1 else C true false

/-- Period-end phase input channel `B_r^(2)(α)` from Appendix A.1. A phase-A
innovation is propagated through the following `B` step; a phase-B innovation
enters at the period end. -/
noncomputable def twoStepCounterexamplePhaseInputChannel
    (epsilon lambda alpha : ℝ) (phase : TwoStepPhase) (node : Bool) :
    RowVector (Fin 3) :=
  match phase with
  | TwoStepPhase.phaseA =>
      matrixMulVector (Node := Fin 3)
        (twoStepCounterexampleLiftedStep
          (twoNodeCounterexamplePush epsilon)
          (twoNodeCounterexamplePullB epsilon) lambda alpha)
        (twoStepCounterexampleOneStepNoiseInput
          (twoNodeCounterexamplePullA epsilon) alpha node)
  | TwoStepPhase.phaseB =>
      twoStepCounterexampleOneStepNoiseInput
        (twoNodeCounterexamplePullB epsilon) alpha node

/-- Arithmetic-average output row `(1/2) 1^T` on the primal coordinates of the
reduced two-node lifted state. -/
noncomputable def twoStepCounterexampleArithmeticAverageOutput
    (v : RowVector (Fin 3)) : ℝ :=
  (v 0 + v 1) / 2

/-- Stable output row
`(1/2)1^T F_ε(α)^j B_r^(2)(α)` for a fixed input phase and a locally supplied
stable branch `F`. This keeps Appendix A.1 local in `|α| ≤ α0` instead of
selecting a global spectral branch. -/
noncomputable def twoStepCounterexampleStableImpulseVectorFrom
    (F : ℝ → NodeMatrix (Fin 3)) (epsilon lambda alpha : ℝ)
    (phase : TwoStepPhase) (j : ℕ) :
    RowVector Bool :=
  fun node =>
    twoStepCounterexampleArithmeticAverageOutput
      (matrixMulVector (Node := Fin 3)
        (matrixPower (Node := Fin 3)
          (F alpha) j)
        (twoStepCounterexamplePhaseInputChannel epsilon lambda alpha phase node))

/-- Concrete stable impulse profile for the two-step counterexample:
the norm of `(1/n)1^T F_ε(α)^j B_r^(2)(α)`. Appendix A.1 bounds this stable
component/action by `K α θ^j`. -/
noncomputable def twoStepCounterexampleStableImpulseFrom
    (F : ℝ → NodeMatrix (Fin 3)) (epsilon lambda alpha : ℝ)
    (phase : TwoStepPhase) (j : ℕ) : ℝ :=
  rowEuclideanNorm (Node := Bool)
    (twoStepCounterexampleStableImpulseVectorFrom F epsilon lambda alpha phase j)

/-- Appendix A.1 coefficient statement for the concrete two-step
counterexample propagator and phase-noise channels. The statement is
epsilon-uniform over the source counterexample surface; it no longer hides the
paper coefficients behind an existentially selected package.

Book/PDF: `book/TimeVaryingPushPull/TimeVaryingPushPull.json` key lemma
`CounterexampleTwoStepSpectralCoefficients`; `paper/TimeVaryingPushPull.pdf`,
Appendix A.1 describes the `R_ε,A_ε,B_ε` construction and the slow/noise
coefficients `s_ε,q_ε`. -/
def TwoStepSpectralCoefficientStatement : Prop :=
  ∀ epsilon lambda : ℝ, 0 < epsilon → epsilon < 1 → 0 < lambda →
    ∃ r0 alpha0 K theta : ℝ, ∃ right left : RowVector (Fin 3),
      ∃ gamma : ℝ → ℝ, ∃ P F : ℝ → NodeMatrix (Fin 3),
      twoStepCounterexampleTailDenominator epsilon ≠ 0 ∧
        0 < twoStepCounterexampleSpectralSlope epsilon ∧
          0 < twoStepCounterexampleNoiseCoefficient epsilon ∧
            PeriodicSpectralSplitting (Node := Fin 3)
              (fun alpha => twoStepCounterexamplePropagator epsilon lambda alpha)
              r0 alpha0 theta K right left gamma P F ∧
              Asymptotics.IsBigO (nhds 0)
                (fun alpha =>
                  gamma alpha -
                    twoStepSlowMultiplierApprox lambda
                      (twoStepCounterexampleSpectralSlope epsilon) alpha)
                (fun alpha => alpha ^ 2) ∧
                Asymptotics.IsBigO (nhds 0)
                  (fun alpha =>
                    twoStepCounterexamplePhaseNoise epsilon alpha -
                      twoStepPhaseNoiseApprox
                        (twoStepCounterexampleNoiseCoefficient epsilon) alpha)
                  (fun alpha => alpha ^ 3) ∧
                  ∀ alpha phase j, 0 ≤ alpha → alpha ≤ alpha0 →
                    twoStepCounterexampleStableImpulseFrom F epsilon lambda alpha phase j ≤
                      K * alpha * theta ^ j

/-- Periodic scalar coefficient `c_t = b_t^T 1` used in the comparison process
(8.5). -/
noncomputable def scalarComparisonGain (quad : Setup Node ℝ) (t : ℕ) : ℝ :=
  rowSum (Node := Node) (quad.influence t)

/-- One step of the scalar comparison process (8.5):
`u_{t+1}=(1-αλc_t)u_t-α b_t^T ε_t`. -/
noncomputable def quadraticScalarComparisonStep
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    (noise : NoisePath Node ℝ) (t : ℕ) (u : ℝ) : ℝ :=
  (1 - alpha * lambda * quad.scalarComparisonGain t) * u -
    alpha * weightedState (Node := Node) (E := ℝ) (quad.influence t) (noise t)

/-- Canonical scalar comparison process `u_t` from equation (8.5), initialized
at the paper's `x_0`.

Book/PDF: `book/TimeVaryingPushPull/TimeVaryingPushPull.json` key lemmas for
Appendix C; `paper/TimeVaryingPushPull.pdf`, equation (8.5). -/
noncomputable def quadraticScalarComparisonProcess
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    (noise : NoisePath Node ℝ) : ℕ → ℝ :=
  fun t =>
    SOptLib.recursiveIterateProcess quad.x0
      (fun k u (_ : Unit) =>
        quad.quadraticScalarComparisonStep lambda alpha noise k u) t ()

/-- Moment functional for the scalar comparison process used in (8.7). -/
noncomputable def quadraticScalarMomentFunctional
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (oracle : OracleNoiseProcess Ω Node ℝ) (T : ℕ) : ℝ :=
  ((T : ℝ)⁻¹) *
    Finset.sum (Finset.range T) fun t =>
      ∫ ω, |lambda *
        quad.quadraticScalarComparisonProcess lambda alpha (oracle.noise ω) t| ^ 2 ∂μ

/-- Appendix C.1 comparison statement for the generated quadratic run and the
canonical scalar process (8.5):
`T^{-1} sum_{t<T} E |bar x_t-u_t|^2 <= C₂ α²` uniformly for
`0 < α <= α₀` and `αT >= 1`. -/
def QuadraticSlowComparisonStatement
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (oracle : OracleNoiseProcess Ω Node ℝ) : Prop :=
  ∃ C2 alpha0 : ℝ, 0 < C2 ∧ 0 < alpha0 ∧
    ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
      ∀ T : ℕ, 1 ≤ alpha * (T : ℝ) →
        ((T : ℝ)⁻¹) *
            Finset.sum (Finset.range T) (fun t =>
              ∫ ω,
                |(quad.withStepsize alpha).averageIterate (oracle.noise ω) t -
                  quad.quadraticScalarComparisonProcess lambda alpha
                    (oracle.noise ω) t| ^ 2 ∂μ) ≤
          C2 * alpha ^ 2

/-- Appendix C.2 scalar periodic moment expansion (8.7), uniformly for all
sufficiently small positive stepsizes. The constants `alpha0`, `c`, and `C`
are chosen before `alpha`, matching the paper's local asymptotic statement. -/
def QuadraticScalarMomentExpansion
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (oracle : OracleNoiseProcess Ω Node ℝ) : Prop :=
  ∃ alpha0 c C : ℝ, 0 < alpha0 ∧ 0 < c ∧ 0 ≤ C ∧
    ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
      ∀ T : ℕ, 1 ≤ T →
        |quad.quadraticScalarMomentFunctional lambda alpha μ oracle T -
            (quad.Delta / (quad.influenceGain * alpha * (T : ℝ)) +
              (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
                (2 * quad.influenceGain)) * alpha)| ≤
          C * ((T : ℝ)⁻¹ + alpha ^ 2 +
            Real.exp (-(c * alpha * (T : ℝ))) /
              (alpha * (T : ℝ)))

/-- Appendix C.2 asymptotic consequence of the uniform scalar expansion:
whenever `alpha_T -> 0` and `alpha_T T -> infinity`, the scalar moment
remainder is `o((alpha_T T)^{-1} + alpha_T)`. -/
def QuadraticScalarMomentAsymptoticConsequence
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (oracle : OracleNoiseProcess Ω Node ℝ) : Prop :=
  ∀ alphaSeq : ℕ → ℝ,
    (∀ᶠ T in Filter.atTop, 0 < alphaSeq T) →
      Filter.Tendsto alphaSeq Filter.atTop (nhds 0) →
        Filter.Tendsto (fun T : ℕ => alphaSeq T * (T : ℝ))
          Filter.atTop Filter.atTop →
          Asymptotics.IsLittleO Filter.atTop
            (fun T : ℕ =>
              quad.quadraticScalarMomentFunctional lambda (alphaSeq T) μ oracle T -
                (quad.Delta /
                    (quad.influenceGain * alphaSeq T * (T : ℝ)) +
                  (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
                    (2 * quad.influenceGain)) * alphaSeq T))
            (fun T : ℕ => (alphaSeq T * (T : ℝ))⁻¹ + alphaSeq T)

/-- The quadratic lower-bound stationarity functional `J_T(α)` from Appendix C:
run the paper recursion with the deterministic constant stepsize `α` and take
the finite-horizon stationarity average. -/
noncomputable def quadraticLowerBoundStationarityFunctional
    (quad : Setup Node ℝ) {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (oracle : OracleNoiseProcess Ω Node ℝ)
    (T : ℕ) (alpha : ℝ) : ℝ :=
  (quad.withStepsize alpha).stationarityAverage μ oracle T

/-- Appendix C.3 all-stepsize trichotomy around near minimizers of the
quadratic lower-bound stationarity functional `J_T(α)`. -/
def AllStepsizeTrichotomyStatement
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (oracle : OracleNoiseProcess Ω Node ℝ) : Prop :=
  ∃ alphaStar alphaNearOpt : ℕ → ℝ,
    (∀ T : ℕ, 1 ≤ T →
      alphaStar T =
        Real.sqrt (2 * quad.Delta /
          (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment * (T : ℝ)))) ∧
      (∀ T : ℕ, 1 ≤ T → 0 ≤ alphaNearOpt T) ∧
        (∀ T : ℕ, 1 ≤ T →
          quad.quadraticLowerBoundStationarityFunctional μ oracle T
              (alphaNearOpt T) ≤
            sInf { value : ℝ |
              ∃ alpha : ℝ, 0 ≤ alpha ∧
                value =
                  quad.quadraticLowerBoundStationarityFunctional μ oracle T alpha } +
            (T : ℝ)⁻¹) ∧
          Filter.Tendsto alphaNearOpt Filter.atTop (nhds 0) ∧
            Filter.Tendsto (fun T : ℕ => alphaNearOpt T * (T : ℝ))
              Filter.atTop Filter.atTop ∧
              ∃ T0 : ℕ, ∀ T : ℕ, T0 ≤ T →
                1 ≤ T ∧ 0 < alphaNearOpt T ∧
                  quad.Delta /
                      (quad.influenceGain * alphaNearOpt T * (T : ℝ)) +
                    (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
                        (2 * quad.influenceGain)) * alphaNearOpt T ≥
                      quad.sigma *
                        Real.sqrt (2 * lambda * quad.Delta /
                          (quad.effectiveNodeCount * (T : ℝ)))

/-- The leading expression in the matching lower bound (8.1). -/
noncomputable def matchingQuadraticLeadingTerm
    (quad : Setup Node ℝ) (lambda : ℝ) (T : ℕ) : ℝ :=
  quad.sigma *
    Real.sqrt (2 * lambda * quad.Delta /
      (quad.effectiveNodeCount * (T : ℝ)))

/-- Source/coarser Appendix C.3 interface for bounded scaled stepsizes.

This is the mean-square floor that the paper's slow-mode persistence argument
needs before the Jensen stationarity endpoint.  It deliberately does not name
the old all-raw upper-half route; a block-boundary or any other
positive-density supplier can prove this predicate. -/
def BoundedScaledStepsizeMeanSquareFloorStatement
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (oracle : OracleNoiseProcess Ω Node ℝ) : Prop :=
  ∀ M : ℝ, 0 ≤ M →
    ∃ c alpha0 T0, 0 < c ∧ 0 < alpha0 ∧
      ∀ T : ℕ, ∀ alpha : ℝ, T0 ≤ T → 0 ≤ alpha →
        alpha ≤ alpha0 → alpha * (T : ℝ) ≤ M →
          c ≤ ((T : ℝ)⁻¹) *
            Finset.sum (Finset.range T) (fun t =>
              lambda ^ 2 *
                |∫ ω,
                  (quad.withStepsize alpha).averageIterate
                    (oracle.noise ω) t ∂μ| ^ 2)

/-- Source/coarser Appendix C.3 interface after the Jensen stationarity
endpoint.  This is the supplier consumed by the filter contradiction proving
`alpha_T T -> infinity`. -/
def BoundedScaledStepsizeStationarityFloorStatement
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (oracle : OracleNoiseProcess Ω Node ℝ) : Prop :=
  ∀ M : ℝ, 0 ≤ M →
    ∃ c alpha0 T0, 0 < c ∧ 0 < alpha0 ∧
      ∀ T : ℕ, ∀ alpha : ℝ, T0 ≤ T → 0 ≤ alpha →
        alpha ≤ alpha0 → alpha * (T : ℝ) ≤ M →
          c ≤ quad.quadraticLowerBoundStationarityFunctional μ oracle T alpha

/-- Source/coarser Appendix C.3 block-boundary persistence supplier.

This names the replacement interface requested by the Phase 2b audit: for
every bounded scaled-stepsize regime `alpha*T <= M`, the deterministic mean of
the arithmetic average remains uniformly separated from zero at complete
period block starts.  The finite positive-density endpoint below is what
turns this source step into a mean-square floor. -/
def BlockBoundaryAbsMeanPersistenceStatement
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (oracle : OracleNoiseProcess Ω Node ℝ) : Prop :=
  ∀ M : ℝ, 0 ≤ M →
    ∃ cmean alpha0 T0, 0 < cmean ∧ 0 < alpha0 ∧
      ∀ T : ℕ, ∀ alpha : ℝ, T0 ≤ T → 0 ≤ alpha →
        alpha ≤ alpha0 → alpha * (T : ℝ) ≤ M →
          ∀ k : ℕ, k < T / quad.period →
            cmean ≤
                  |∫ ω,
                    (quad.withStepsize alpha).averageIterate
                      (oracle.noise ω) (k * quad.period) ∂μ|

/-- Source/coarser Appendix C.3 positive-density persistence supplier.

The source proof only needs the deterministic mean of the arithmetic average
to stay separated from zero on a finite subset occupying a fixed positive
fraction of the horizon.  Block-boundary persistence is one way to provide
such a subset, but this is the coarser interface consumed by the finite
counting endpoint below. -/
def PositiveDensityAbsMeanPersistenceStatement
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (oracle : OracleNoiseProcess Ω Node ℝ) : Prop :=
  ∀ M : ℝ, 0 ≤ M →
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
                          (oracle.noise ω) t ∂μ|

/-- Finite positive-density endpoint for the C.3 mean-persistence argument.

If a deterministic lower bound holds on any finite subset occupying a fixed
positive fraction of the horizon, then the averaged squared mean has the
corresponding floor.  This upstream theorem is source-neutral infrastructure
for the block-boundary replacement route. -/
theorem average_iterate_mean_square_floor_of_positive_density_abs_lower_source
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

/-- Block-boundary representatives occupy a fixed positive fraction of any
large horizon.

This is the finite counting part of the Appendix C.3 replacement route.  It
selects complete-period block starts `k * p` and records both their membership
in `range T` and their density lower bound. -/
theorem block_boundary_positive_density_subset_source
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

/-- Block-boundary persistence is a concrete source supplier for the coarser
positive-density persistence interface.

This keeps Appendix C.3's source route at the finite positive-density level:
complete-period block starts provide the subset, and the density is the
explicit counting constant `1 / (2 * period)` for large enough horizons. -/
theorem positiveDensityAbsMeanPersistence_of_blockBoundaryAbsMeanPersistence_source
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (oracle : OracleNoiseProcess Ω Node ℝ)
    (hblock :
      BlockBoundaryAbsMeanPersistenceStatement
        (Node := Node) quad lambda μ oracle) :
    PositiveDensityAbsMeanPersistenceStatement
      (Node := Node) quad lambda μ oracle := by
  classical
  intro M hM_nonneg
  rcases hblock M hM_nonneg with
    ⟨cmean, alpha0, Tblock, hcmean_pos, halpha0_pos, hblock_lower⟩
  let density : ℝ := (1 : ℝ) / (2 * (quad.period : ℝ))
  let T0 : ℕ := max Tblock (2 * quad.period)
  have hdensity_pos : 0 < density := by
    dsimp [density]
    have hperiod_pos : 0 < (quad.period : ℝ) := by
      exact_mod_cast quad.period_pos
    positivity
  refine ⟨cmean, density, alpha0, T0,
    hcmean_pos, hdensity_pos, halpha0_pos, ?_⟩
  intro T alpha hT halpha_nonneg halpha_le hscaled
  have hTblock : Tblock ≤ T := le_trans (Nat.le_max_left Tblock _) hT
  have hT_period : 2 * quad.period ≤ T :=
    le_trans (Nat.le_max_right Tblock _) hT
  rcases
      block_boundary_positive_density_subset_source
        quad.period T quad.period_pos hT_period with
    ⟨S, hS_subset, hcard_lower, hS_mem⟩
  refine ⟨S, hS_subset, ?_, ?_⟩
  · simpa [density] using hcard_lower
  · intro t ht
    rcases hS_mem t ht with ⟨k, hk, rfl⟩
    exact hblock_lower T alpha hTblock halpha_nonneg halpha_le hscaled k hk

/-- Block-boundary endpoint for the C.3 mean-persistence argument.

If the arithmetic-average mean is bounded below at all complete-period block
starts in a large horizon, then the averaged squared mean has a positive
floor.  This is the public upstream counting endpoint named by the
block-boundary replacement route. -/
theorem average_iterate_mean_square_floor_of_block_boundary_abs_lower
    (signal : ℕ → ℝ) (lambda cmean : ℝ) (period T : ℕ)
    (hperiod_pos : 0 < period)
    (hT : 2 * period ≤ T)
    (hcmean_nonneg : 0 ≤ cmean)
    (hlower : ∀ k : ℕ, k < T / period → cmean ≤ |signal (k * period)|) :
    lambda ^ 2 * cmean ^ 2 * ((1 : ℝ) / (2 * (period : ℝ))) ≤
      ((T : ℝ)⁻¹) *
        Finset.sum (Finset.range T) (fun t =>
          lambda ^ 2 * |signal t| ^ 2) := by
  classical
  rcases
      block_boundary_positive_density_subset_source period T hperiod_pos hT with
    ⟨S, hS_subset, hcard_lower, hS_mem⟩
  have hT_pos : 0 < T := by
    have htwo_period_pos : 0 < 2 * period := by omega
    exact lt_of_lt_of_le htwo_period_pos hT
  exact
    average_iterate_mean_square_floor_of_positive_density_abs_lower_source
      (signal := signal) (lambda := lambda) (cmean := cmean)
      (density := (1 : ℝ) / (2 * (period : ℝ))) (T := T) (S := S)
      hT_pos hcmean_nonneg (by positivity) hS_subset hcard_lower
      (by
        intro t ht
        rcases hS_mem t ht with ⟨k, hk, rfl⟩
        exact hlower k hk)

/-- Bounded-scaled block-boundary persistence feeds the Appendix C.3
mean-square floor.

This is the Part002-visible source/coarser route interface: the spectral
block-boundary supplier only has to prove a uniform absolute lower bound at
complete-period block starts.  The finite positive-density counting endpoint
then converts it to the averaged squared-mean floor without using the retired
all-raw upper-half route. -/
theorem bounded_scaled_stepsize_mean_square_floor_of_block_boundary_abs_lower_source
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (oracle : OracleNoiseProcess Ω Node ℝ)
    (hlambda_pos : 0 < lambda)
    (hblock :
      ∀ M : ℝ, 0 ≤ M →
        ∃ cmean alpha0 T0, 0 < cmean ∧ 0 < alpha0 ∧
          ∀ T : ℕ, ∀ alpha : ℝ, T0 ≤ T → 0 ≤ alpha →
            alpha ≤ alpha0 → alpha * (T : ℝ) ≤ M →
              ∀ k : ℕ, k < T / quad.period →
                cmean ≤
                  |∫ ω,
                    (quad.withStepsize alpha).averageIterate
                      (oracle.noise ω) (k * quad.period) ∂μ|) :
    BoundedScaledStepsizeMeanSquareFloorStatement
      (Node := Node) quad lambda μ oracle := by
  classical
  intro M hM_nonneg
  rcases hblock M hM_nonneg with
    ⟨cmean, alpha0, Tblock, hcmean_pos, halpha0_pos, hblock_lower⟩
  let density : ℝ := (1 : ℝ) / (2 * (quad.period : ℝ))
  let c : ℝ := lambda ^ 2 * cmean ^ 2 * density
  let T0 : ℕ := max Tblock (2 * quad.period)
  have hdensity_pos : 0 < density := by
    dsimp [density]
    have hperiod_pos : 0 < (quad.period : ℝ) := by
      exact_mod_cast quad.period_pos
    positivity
  have hc_pos : 0 < c := by
    have hlambda_sq_pos : 0 < lambda ^ 2 :=
      sq_pos_of_ne_zero (ne_of_gt hlambda_pos)
    have hcmean_sq_pos : 0 < cmean ^ 2 :=
      sq_pos_of_ne_zero (ne_of_gt hcmean_pos)
    dsimp [c]
    positivity
  refine ⟨c, alpha0, T0, hc_pos, halpha0_pos, ?_⟩
  intro T alpha hT halpha_nonneg halpha_le hscaled
  have hTblock : Tblock ≤ T := le_trans (Nat.le_max_left Tblock _) hT
  have hT_period : 2 * quad.period ≤ T :=
    le_trans (Nat.le_max_right Tblock _) hT
  simpa [c, density] using
    average_iterate_mean_square_floor_of_block_boundary_abs_lower
      (signal := fun t : ℕ =>
        ∫ ω,
          (quad.withStepsize alpha).averageIterate
            (oracle.noise ω) t ∂μ)
      (lambda := lambda) (cmean := cmean) (period := quad.period)
      (T := T) quad.period_pos hT_period hcmean_pos.le
      (hblock_lower T alpha hTblock halpha_nonneg halpha_le hscaled)

/-- Named source/coarser Appendix C.3 route from block-boundary persistence to
the bounded-scaled mean-square floor.

This is the Part002-visible replacement interface for the retired all-raw
upper-half route.  It consumes the block-boundary persistence statement above
and only uses the finite positive-density counting endpoint. -/
theorem bounded_scaled_stepsize_mean_square_floor_of_block_boundary_statement_source
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (oracle : OracleNoiseProcess Ω Node ℝ)
    (hlambda_pos : 0 < lambda)
    (hblock :
      BlockBoundaryAbsMeanPersistenceStatement
        (Node := Node) quad lambda μ oracle) :
    BoundedScaledStepsizeMeanSquareFloorStatement
      (Node := Node) quad lambda μ oracle := by
  classical
  exact
    bounded_scaled_stepsize_mean_square_floor_of_block_boundary_abs_lower_source
      (Node := Node) quad lambda μ oracle hlambda_pos
      (by
        simpa [BlockBoundaryAbsMeanPersistenceStatement] using hblock)

/-- Exact-shape source/coarser Appendix C.3 mean-square floor.

This is the public Part002 entrypoint with the name and conclusion shape
requested by the Phase 2b audit.  It is proved from block-boundary
persistence through the finite positive-density counting endpoint above, and
therefore does not route through the noncurrent all-raw upper-half supplier. -/
theorem quadratic_restricted_block_boundary_mean_square_floor_of_bounded_scaled_stepsize_source
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (oracle : OracleNoiseProcess Ω Node ℝ)
    (hlambda_pos : 0 < lambda)
    (hblock :
      BlockBoundaryAbsMeanPersistenceStatement
        (Node := Node) quad lambda μ oracle)
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
    bounded_scaled_stepsize_mean_square_floor_of_block_boundary_statement_source
      (Node := Node) quad lambda μ oracle hlambda_pos hblock M hM_nonneg

/-- Positive-density Appendix C.3 persistence feeds the bounded-scaled
mean-square floor.

This is the finite-subset source interface requested by the audit.  It is
strictly coarser than block-boundary persistence and uses only the proven
positive-density counting endpoint, not the retired all-raw upper-half route. -/
theorem bounded_scaled_stepsize_mean_square_floor_of_positive_density_statement_source
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (oracle : OracleNoiseProcess Ω Node ℝ)
    (hlambda_pos : 0 < lambda)
    (hpd :
      PositiveDensityAbsMeanPersistenceStatement
        (Node := Node) quad lambda μ oracle) :
    BoundedScaledStepsizeMeanSquareFloorStatement
      (Node := Node) quad lambda μ oracle := by
  classical
  intro M hM_nonneg
  rcases hpd M hM_nonneg with
    ⟨cmean, density, alpha0, Tpd, hcmean_pos, hdensity_pos,
      halpha0_pos, hpd_floor⟩
  let c : ℝ := lambda ^ 2 * cmean ^ 2 * density
  let T0 : ℕ := max Tpd 1
  have hc_pos : 0 < c := by
    have hlambda_sq_pos : 0 < lambda ^ 2 :=
      sq_pos_of_ne_zero (ne_of_gt hlambda_pos)
    have hcmean_sq_pos : 0 < cmean ^ 2 :=
      sq_pos_of_ne_zero (ne_of_gt hcmean_pos)
    dsimp [c]
    positivity
  refine ⟨c, alpha0, T0, hc_pos, halpha0_pos, ?_⟩
  intro T alpha hT halpha_nonneg halpha_le hscaled
  have hTpd : Tpd ≤ T := le_trans (Nat.le_max_left Tpd 1) hT
  have hT_one : 1 ≤ T := le_trans (Nat.le_max_right Tpd 1) hT
  have hT_pos : 0 < T := lt_of_lt_of_le (by norm_num) hT_one
  rcases hpd_floor T alpha hTpd halpha_nonneg halpha_le hscaled with
    ⟨S, hS_subset, hcard_lower, hlower⟩
  simpa [c] using
    average_iterate_mean_square_floor_of_positive_density_abs_lower_source
      (signal := fun t : ℕ =>
        ∫ ω,
          (quad.withStepsize alpha).averageIterate
            (oracle.noise ω) t ∂μ)
      (lambda := lambda) (cmean := cmean) (density := density)
      (T := T) (S := S) hT_pos hcmean_pos.le hdensity_pos.le
      hS_subset hcard_lower hlower

/-- The square of the absolute value of a real `L²` process is integrable. -/
private theorem c3_real_abs_sq_integrable_of_memLp_two
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    Integrable (fun ω => |f ω| ^ 2) μ := by
  simpa [Real.norm_eq_abs] using
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf

/-- In a homogeneous one-dimensional quadratic instance, every component
gradient is the scalar map `x ↦ lambda*x`. -/
private theorem c3_homogeneousQuadratic_componentGradient_eq_linear
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

/-- The finite-average gradient of a homogeneous one-dimensional quadratic
instance is also `x ↦ lambda*x`. -/
private theorem c3_homogeneousQuadratic_averageGradient_eq_linear
    (quad : Setup Node ℝ) (lambda : ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda) :
    ∀ x : ℝ, quad.averageGradient x = lambda * x := by
  intro x
  have hcomp :=
    c3_homogeneousQuadratic_componentGradient_eq_linear
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

/-- Source-neutral Jensen endpoint for Appendix C.3 step 3.

If the squared mean of the arithmetic average has a finite-horizon lower
floor, then the true quadratic stationarity functional has the same floor.
The proof uses the homogeneous identity `∇f(\bar x)=lambda*\bar x` and the
probability-space inequality `(E Z)^2 <= E Z^2` at each time. -/
private theorem c3_stationarity_functional_floor_of_average_iterate_mean_square
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
    c3_homogeneousQuadratic_averageGradient_eq_linear
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
      simpa [sq_abs] using
        c3_real_abs_sq_integrable_of_memLp_two hactual_mem
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

/-- Source/coarser Appendix C.3 Jensen bridge.

Any bounded-scaled-stepsize mean-square floor for the arithmetic averages
immediately gives the corresponding floor for the quadratic stationarity
functional.  This is the upstream bridge that the block-boundary or
positive-density source supplier should feed; it does not mention the retired
all-raw upper-half route. -/
theorem bounded_scaled_stepsize_stationarity_floor_of_mean_square_floor_source
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (hmean_floor :
      BoundedScaledStepsizeMeanSquareFloorStatement
        (Node := Node) quad lambda μ oracle) :
    BoundedScaledStepsizeStationarityFloorStatement
      (Node := Node) quad lambda μ oracle := by
  classical
  intro M hM_nonneg
  rcases hmean_floor M hM_nonneg with
    ⟨c, alpha0, T0, hc_pos, halpha0_pos, hfloor⟩
  refine ⟨c, alpha0, T0, hc_pos, halpha0_pos, ?_⟩
  intro T alpha hT halpha_nonneg halpha_le hscaled
  exact
    c3_stationarity_functional_floor_of_average_iterate_mean_square
      (Node := Node) quad lambda μ oracle hquad hnoise T alpha c
      (hfloor T alpha hT halpha_nonneg halpha_le hscaled)

/-- Source/coarser Appendix C.3 block-boundary route, composed through the
Jensen stationarity endpoint.

This is the complete Part002-visible consumer path requested by the audit:
block-boundary absolute mean persistence implies the bounded-scaled
stationarity floor, with no dependency on the retired all-raw upper-half
supplier. -/
theorem bounded_scaled_stepsize_stationarity_floor_of_block_boundary_abs_lower_source
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (hblock :
      ∀ M : ℝ, 0 ≤ M →
        ∃ cmean alpha0 T0, 0 < cmean ∧ 0 < alpha0 ∧
          ∀ T : ℕ, ∀ alpha : ℝ, T0 ≤ T → 0 ≤ alpha →
            alpha ≤ alpha0 → alpha * (T : ℝ) ≤ M →
              ∀ k : ℕ, k < T / quad.period →
                cmean ≤
                  |∫ ω,
                    (quad.withStepsize alpha).averageIterate
                      (oracle.noise ω) (k * quad.period) ∂μ|) :
    BoundedScaledStepsizeStationarityFloorStatement
      (Node := Node) quad lambda μ oracle := by
  exact
    bounded_scaled_stepsize_stationarity_floor_of_mean_square_floor_source
      (Node := Node) quad lambda μ oracle hquad hnoise
      (bounded_scaled_stepsize_mean_square_floor_of_block_boundary_abs_lower_source
        (Node := Node) quad lambda μ oracle hquad.1 hblock)

/-- Named source/coarser Appendix C.3 route through the Jensen stationarity
endpoint.

This theorem is the compiled Part002 attempt at the arbiter-designated
replacement path: block-boundary persistence implies the stationarity floor
without routing through the noncurrent all-raw upper-half helper. -/
theorem bounded_scaled_stepsize_stationarity_floor_of_block_boundary_statement_source
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (hblock :
      BlockBoundaryAbsMeanPersistenceStatement
        (Node := Node) quad lambda μ oracle) :
    BoundedScaledStepsizeStationarityFloorStatement
      (Node := Node) quad lambda μ oracle := by
  exact
    bounded_scaled_stepsize_stationarity_floor_of_mean_square_floor_source
      (Node := Node) quad lambda μ oracle hquad hnoise
      (bounded_scaled_stepsize_mean_square_floor_of_positive_density_statement_source
        (Node := Node) quad lambda μ oracle hquad.1
        (positiveDensityAbsMeanPersistence_of_blockBoundaryAbsMeanPersistence_source
          (Node := Node) quad lambda μ oracle hblock))

/-- Positive-density Appendix C.3 persistence, composed through the Jensen
stationarity endpoint.

This theorem is the exact coarser source-route attempt: a positive-density
mean persistence supplier implies the bounded-scaled stationarity floor
without using the noncurrent all-raw upper-half helper. -/
theorem bounded_scaled_stepsize_stationarity_floor_of_positive_density_statement_source
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (hpd :
      PositiveDensityAbsMeanPersistenceStatement
        (Node := Node) quad lambda μ oracle) :
    BoundedScaledStepsizeStationarityFloorStatement
      (Node := Node) quad lambda μ oracle := by
  exact
    bounded_scaled_stepsize_stationarity_floor_of_mean_square_floor_source
      (Node := Node) quad lambda μ oracle hquad hnoise
      (bounded_scaled_stepsize_mean_square_floor_of_positive_density_statement_source
        (Node := Node) quad lambda μ oracle hquad.1 hpd)

/-- Exact-shape source/coarser Appendix C.3 slow floor.

This is the Part002-visible endpoint that a block-boundary spectral
persistence proof should feed.  It has the same pointwise lower-floor shape as
the downstream C.3 slow-floor consumer, but its only source-specific premise is
the block-boundary persistence statement rather than the retired all-raw
upper-half route. -/
theorem quadraticLowerBoundStationarityFunctional_slow_mode_floor_of_block_boundary_statement_source
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (hblock :
      BlockBoundaryAbsMeanPersistenceStatement
        (Node := Node) quad lambda μ oracle)
    (M : ℝ) (hM_nonneg : 0 ≤ M) :
    ∃ c alpha0 T0, 0 < c ∧ 0 < alpha0 ∧
      ∀ T : ℕ, ∀ alpha : ℝ, T0 ≤ T → 0 ≤ alpha →
        alpha ≤ alpha0 → alpha * (T : ℝ) ≤ M →
          c ≤ quad.quadraticLowerBoundStationarityFunctional μ oracle T alpha := by
  exact
    bounded_scaled_stepsize_stationarity_floor_of_block_boundary_statement_source
      (Node := Node) quad lambda μ oracle hquad hnoise hblock M hM_nonneg

/-
Phase 2b dependency certificate for Theorem 3.1.

The source proof of `NoNetworkIndependentDominantConstant` consumes the
Appendix C.3 trichotomy and Theorem 8.1 matching expansion.  Those declarations
are intentionally downstream in `Part003`, while this module is imported by
`Part003`; importing or calling them here would create a cycle.  The public
theorem is therefore placed downstream in `Part003`.  The guarded checks below
keep the old upstream obstruction typed without adding an assumption-carrying
wrapper around the matching expansion.

The Phase 2b audit also retired the old all-raw upper-half route in favor of
the block-boundary/positive-density supplier.  That replacement is likewise
downstream and private in `Part003`; the active theorem cannot consume it from
this module.  The additional guarded checks are the same-interface obstruction
for this Part002 boundary, not a replacement proof route.

The guarded example after the name checks is intentionally stated at the
replacement supplier's granularity.  It records the exact Part002-local call
that would discharge the Appendix C.3 source floor if the downstream private
supplier were visible here.  The failure is therefore a typed module-order /
visibility obstruction for the source/coarser interface, not evidence for
reactivating the noncurrent all-raw upper-half route.

This module now exposes the source-neutral positive-density counting endpoint
`average_iterate_mean_square_floor_of_positive_density_abs_lower_source`.
It also exposes the named replacement interface
`BlockBoundaryAbsMeanPersistenceStatement` and the compiled bridge
`bounded_scaled_stepsize_stationarity_floor_of_block_boundary_statement_source`.
The downstream theorem can additionally see the spectral proof of
`BlockBoundaryAbsMeanPersistenceStatement` and the matching lower-bound route.
-/
#check average_iterate_mean_square_floor_of_positive_density_abs_lower_source
#check BlockBoundaryAbsMeanPersistenceStatement
#check positiveDensityAbsMeanPersistence_of_blockBoundaryAbsMeanPersistence_source
#check bounded_scaled_stepsize_mean_square_floor_of_block_boundary_statement_source
#check quadratic_restricted_block_boundary_mean_square_floor_of_bounded_scaled_stepsize_source
#check bounded_scaled_stepsize_stationarity_floor_of_block_boundary_statement_source
#check quadraticLowerBoundStationarityFunctional_slow_mode_floor_of_block_boundary_statement_source

/--
error: Unknown identifier `quadratic_restricted_block_boundary_mean_abs_lower_of_source_components`
-/
#guard_msgs in
#check quadratic_restricted_block_boundary_mean_abs_lower_of_source_components

/--
error: Unknown identifier `quadratic_restricted_block_boundary_mean_abs_lower_of_source_components`
-/
#guard_msgs in
example
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle) :
    BlockBoundaryAbsMeanPersistenceStatement
      (Node := Node) quad lambda μ oracle := by
  intro M hM_nonneg
  exact
    quadratic_restricted_block_boundary_mean_abs_lower_of_source_components
      (Node := Node) quad lambda μ oracle hquad hnoise M hM_nonneg

/--
error: Unknown identifier `MatchingQuadraticLowerBound`
-/
#guard_msgs in
#check MatchingQuadraticLowerBound

/--
error: Unknown identifier `AllStepsizeTrichotomyForQuadraticLowerBound`
-/
#guard_msgs in
#check AllStepsizeTrichotomyForQuadraticLowerBound

/--
error: Unknown identifier `quadratic_restricted_block_boundary_mean_square_floor_of_bounded_scaled_stepsize`
-/
#guard_msgs in
#check quadratic_restricted_block_boundary_mean_square_floor_of_bounded_scaled_stepsize

/--
error: Unknown identifier `average_iterate_mean_square_floor_of_positive_density_abs_lower`
-/
#guard_msgs in
#check average_iterate_mean_square_floor_of_positive_density_abs_lower

/--
error: Unknown identifier `quadratic_restricted_positive_density_mean_abs_lower_of_bounded_scaled_stepsize`
-/
#guard_msgs in
#check quadratic_restricted_positive_density_mean_abs_lower_of_bounded_scaled_stepsize

/--
error: Unknown identifier `quadratic_restricted_mean_persistence_floor_of_bounded_scaled_stepsize`
-/
#guard_msgs in
#check quadratic_restricted_mean_persistence_floor_of_bounded_scaled_stepsize

/--
error: Unknown identifier `stationarity_functional_floor_of_average_iterate_mean_square`
-/
#guard_msgs in
#check stationarity_functional_floor_of_average_iterate_mean_square

/--
error: Unknown identifier `quadraticLowerBoundStationarityFunctional_slow_mode_floor_of_bounded_scaled_stepsize`
-/
#guard_msgs in
#check quadraticLowerBoundStationarityFunctional_slow_mode_floor_of_bounded_scaled_stepsize

/--
error: Unknown identifier `quadratic_restricted_block_boundary_mean_square_floor_of_bounded_scaled_stepsize`
-/
#guard_msgs in
example
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (M : ℝ) (hM_nonneg : 0 ≤ M) :
    BoundedScaledStepsizeMeanSquareFloorStatement
      (Node := Node) quad lambda μ oracle := by
  intro M hM_nonneg
  exact
    quadratic_restricted_block_boundary_mean_square_floor_of_bounded_scaled_stepsize
      (Node := Node) quad lambda μ oracle hquad hnoise M hM_nonneg

/--
error: Unknown identifier `quadraticLowerBoundStationarityFunctional_slow_mode_floor_of_bounded_scaled_stepsize`
-/
#guard_msgs in
example
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (hslow : QuadraticSlowComparisonStatement (Node := Node) quad lambda μ oracle)
    (M : ℝ) (hM_nonneg : 0 ≤ M) :
    BoundedScaledStepsizeStationarityFloorStatement
      (Node := Node) quad lambda μ oracle := by
  intro M hM_nonneg
  exact
    quadraticLowerBoundStationarityFunctional_slow_mode_floor_of_bounded_scaled_stepsize
      (Node := Node) quad lambda μ oracle hquad hnoise hslow M hM_nonneg

/-- Theorem 3.3: a predictable feedback choice of time-varying matrices can
force a non-vanishing stationarity lower bound for every constant stepsize. -/
noncomputable def canonicalHalfRademacherMarginal : Measure Bool :=
  SOptLib.finiteBlockIndexLaw (fun _ : Bool => 1 / 2)
    (by intro b; norm_num) (by norm_num [Fintype.sum_bool])

noncomputable instance canonicalHalfRademacherMarginal_probability :
    IsProbabilityMeasure canonicalHalfRademacherMarginal := by
  unfold canonicalHalfRademacherMarginal
  exact SOptLib.finiteBlockIndexLaw_isProbabilityMeasure
    (fun _ : Bool => 1 / 2) (by intro b; norm_num)
      (by norm_num [Fintype.sum_bool])

noncomputable def canonicalHalfRademacherMeasure :
    Measure (ℕ → Bool) :=
  SOptLib.iidStreamLaw canonicalHalfRademacherMarginal

noncomputable instance canonicalHalfRademacherMeasure_probability :
    IsProbabilityMeasure canonicalHalfRademacherMeasure := by
  unfold canonicalHalfRademacherMeasure
  exact SOptLib.iidStreamLaw_isProbabilityMeasure
    canonicalHalfRademacherMarginal

noncomputable def canonicalHalfRademacherNoise :
    (ℕ → Bool) → ℕ → ℝ :=
  fun ω t => if ω t then 1 / 2 else -(1 / 2)

theorem canonicalHalfRademacherNoise_spec :
    HalfRademacherNoise canonicalHalfRademacherMeasure
      canonicalHalfRademacherNoise := by
  classical
  constructor
  · have hindepEval :=
      SOptLib.iidStreamLaw_iIndepFun_eval canonicalHalfRademacherMarginal
    have hhalfMeas :
        Measurable (fun b : Bool => if b then (1 / 2 : ℝ) else -(1 / 2)) :=
      measurable_of_finite _
    simpa [canonicalHalfRademacherMeasure, canonicalHalfRademacherNoise,
      Function.comp_def] using
      hindepEval.comp
        (fun _t => fun b : Bool => if b then (1 / 2 : ℝ) else -(1 / 2))
        (fun _t => hhalfMeas)
  · intro t
    have hmap := SOptLib.iidStreamLaw_map_eval
      canonicalHalfRademacherMarginal t
    have heval : Measurable (fun ω : ℕ → Bool => ω t) :=
      measurable_pi_apply t
    have htrueMeasure :
        canonicalHalfRademacherMeasure
            ((fun ω : ℕ → Bool => ω t) ⁻¹' ({true} : Set Bool)) =
          canonicalHalfRademacherMarginal ({true} : Set Bool) := by
      exact measure_preimage_singleton_eq_of_map_eq true heval.aemeasurable
        (by simpa [canonicalHalfRademacherMeasure] using hmap)
    have hfalseMeasure :
        canonicalHalfRademacherMeasure
            ((fun ω : ℕ → Bool => ω t) ⁻¹' ({false} : Set Bool)) =
          canonicalHalfRademacherMarginal ({false} : Set Bool) := by
      exact measure_preimage_singleton_eq_of_map_eq false heval.aemeasurable
        (by simpa [canonicalHalfRademacherMeasure] using hmap)
    have htrueSet :
        {ω : ℕ → Bool | canonicalHalfRademacherNoise ω t = 1 / 2} =
          (fun ω : ℕ → Bool => ω t) ⁻¹' ({true} : Set Bool) := by
      ext ω
      cases h : ω t <;> simp [canonicalHalfRademacherNoise, h] <;> norm_num
    have hfalseSet :
        {ω : ℕ → Bool | canonicalHalfRademacherNoise ω t = -(1 / 2)} =
          (fun ω : ℕ → Bool => ω t) ⁻¹' ({false} : Set Bool) := by
      ext ω
      cases h : ω t <;> simp [canonicalHalfRademacherNoise, h] <;> norm_num
    constructor
    · rw [htrueSet, Measure.real_def, htrueMeasure]
      simp [canonicalHalfRademacherMarginal,
        SOptLib.finiteBlockIndexLaw_singleton]
    · rw [hfalseSet, Measure.real_def, hfalseMeasure]
      simp [canonicalHalfRademacherMarginal,
        SOptLib.finiteBlockIndexLaw_singleton]

theorem predictableFeedbackScalarTrajectory_zero_stepsize_mean
    (halfNoise : ℕ → ℝ) (t : ℕ) :
    (predictableFeedbackScalarTrajectory halfNoise 0 t).mean = 1 ∧
      (predictableFeedbackScalarTrajectory halfNoise 0 t).disagreement = 0 := by
  induction t with
  | zero =>
      simp [predictableFeedbackScalarTrajectory,
        SOptLib.recursiveIterateProcess, predictableFeedbackScalarInitial]
  | succ t ih =>
      rcases ih with ⟨hmean, hdis⟩
      change
        (predictableFeedbackScalarStep halfNoise 0 t
            (predictableFeedbackScalarTrajectory halfNoise 0 t)).mean = 1 ∧
          (predictableFeedbackScalarStep halfNoise 0 t
            (predictableFeedbackScalarTrajectory halfNoise 0 t)).disagreement = 0
      simp [predictableFeedbackScalarStep, hmean, hdis]

theorem predictableFeedbackScalar_zero_stepsize_second_moment_lower
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (halfNoise : Ω → ℕ → ℝ) (t : ℕ) :
    (1 / 64 : ℝ) ≤
      ∫ ω, |(predictableFeedbackScalarTrajectory
        (fun k => halfNoise ω k) 0 t).mean| ^ 2 ∂μ := by
  have hmean : ∀ ω,
      (predictableFeedbackScalarTrajectory
        (fun k => halfNoise ω k) 0 t).mean = 1 := by
    intro ω
    exact (predictableFeedbackScalarTrajectory_zero_stepsize_mean
      (fun k => halfNoise ω k) t).1
  simp_rw [hmean]
  norm_num

theorem canonical_predictableFeedbackScalar_prefix_regular
    (alpha : ℝ) (t : ℕ) :
    let sample : ℕ → (ℕ → Bool) → Bool := fun j ω => ω j
    let hsample : ∀ j, Measurable (sample j) :=
      fun j => measurable_pi_apply j
    let past := fun n => (SOptLib.filtration sample hsample).seq n
    let process := fun n ω =>
      predictableFeedbackScalarTrajectory
        (fun k => canonicalHalfRademacherNoise ω k) alpha n
    @Measurable (ℕ → Bool) PredictableFeedbackScalarState
        (past t) ⊤ (process t) ∧
      (Set.range (process t)).Finite := by
  classical
  dsimp only
  let sample : ℕ → (ℕ → Bool) → Bool := fun j ω => ω j
  let hsample : ∀ j, Measurable (sample j) :=
    fun j => measurable_pi_apply j
  let past := fun n => (SOptLib.filtration sample hsample).seq n
  let process := fun n ω =>
    predictableFeedbackScalarTrajectory
      (fun k => canonicalHalfRademacherNoise ω k) alpha n
  let driver : ℕ → (ℕ → Bool) → Bool := fun j ω => ω j
  let step : ℕ → PredictableFeedbackScalarState → Bool →
      PredictableFeedbackScalarState := fun j state b =>
    predictableFeedbackScalarStep
      (fun _k => if b then 1 / 2 else -(1 / 2)) alpha j state
  letI : MeasurableSpace PredictableFeedbackScalarState := ⊤
  have hregular :=
    SOptLib.recursive_process_measurable_finite_range_wrt_history
      (past t) process driver step t t
      (by
        simpa [process, predictableFeedbackScalarTrajectory,
          SOptLib.recursiveIterateProcess] using
            (measurable_const : Measurable[past t]
              (fun _ω : ℕ → Bool => predictableFeedbackScalarInitial)))
      (by
        simpa [process, predictableFeedbackScalarTrajectory,
          SOptLib.recursiveIterateProcess] using
            (Set.finite_range_const :
              (Set.range (fun _ω : ℕ → Bool =>
                predictableFeedbackScalarInitial)).Finite))
      (by
        intro j hj
        exact SOptLib.measurable_sample_of_lt_prefixFiltration sample hsample
          (by omega))
      (by
        intro j hj
        exact (Set.finite_univ : (Set.univ : Set Bool).Finite).subset
          (Set.subset_univ _))
      (by
        intro j hj ω
        simp only [process, driver, step]
        change
          predictableFeedbackScalarStep
              (fun k => canonicalHalfRademacherNoise ω k) alpha j
                (predictableFeedbackScalarTrajectory
                  (fun k => canonicalHalfRademacherNoise ω k) alpha j) =
            predictableFeedbackScalarStep
              (fun _k => if ω j then 1 / 2 else -(1 / 2)) alpha j
                (predictableFeedbackScalarTrajectory
                  (fun k => canonicalHalfRademacherNoise ω k) alpha j)
        simp [predictableFeedbackScalarStep, canonicalHalfRademacherNoise])
      (le_refl t)
  simpa [past, process] using hregular

/-- A fresh Bool coordinate can be averaged explicitly against the canonical
iid stream when the other argument is the strict-prefix scalar state. -/
theorem canonical_predictable_feedback_fresh_bool_integral
    (alpha : ℝ) (s : ℕ)
    (F : PredictableFeedbackScalarState → Bool → ℝ) :
    (∫ ω : ℕ → Bool,
        F (predictableFeedbackScalarTrajectory
          (fun k => canonicalHalfRademacherNoise ω k) alpha s) (ω s)
          ∂canonicalHalfRademacherMeasure) =
      ∫ ω : ℕ → Bool,
        (F (predictableFeedbackScalarTrajectory
              (fun k => canonicalHalfRademacherNoise ω k) alpha s) false +
            F (predictableFeedbackScalarTrajectory
              (fun k => canonicalHalfRademacherNoise ω k) alpha s) true) / 2
          ∂canonicalHalfRademacherMeasure := by
  classical
  let sample : ℕ → (ℕ → Bool) → Bool := fun j ω => ω j
  let hsample : ∀ j, Measurable (sample j) :=
    fun j => measurable_pi_apply j
  let state : (ℕ → Bool) → PredictableFeedbackScalarState := fun ω =>
    predictableFeedbackScalarTrajectory
      (fun k => canonicalHalfRademacherNoise ω k) alpha s
  letI : MeasurableSpace PredictableFeedbackScalarState := ⊤
  have hregular :=
    canonical_predictableFeedbackScalar_prefix_regular alpha s
  have hstate_past :
      Measurable[(SOptLib.filtration sample hsample).seq s] state := by
    simpa [sample, hsample, state] using hregular.1
  have hstate_fin : (Set.range state).Finite := by
    simpa [state] using hregular.2
  have hstate : Measurable state :=
    hstate_past.of_measurableSpace_le
      ((SOptLib.filtration sample hsample).le' s)
  have hiid : iIndepFun sample canonicalHalfRademacherMeasure := by
    simpa [sample, canonicalHalfRademacherMeasure] using
      SOptLib.iidStreamLaw_iIndepFun_eval canonicalHalfRademacherMarginal
  have hindep : IndepFun state (fun ω : ℕ → Bool => ω s)
      canonicalHalfRademacherMeasure := by
    apply ProbabilityTheory.iIndepFun.indepFun_prefixMeasurable_future
      sample hsample hiid
    · simpa [SOptLib.filtration_seq] using hstate_past
    · exact le_rfl
  have hidx : Measurable (fun ω : ℕ → Bool => ω s) :=
    measurable_pi_apply s
  have huniform : ∀ b : Bool,
      (Measure.map (fun ω : ℕ → Bool => ω s)
        canonicalHalfRademacherMeasure).real ({b} : Set Bool) =
          (Fintype.card Bool : ℝ)⁻¹ := by
    intro b
    have hmap := SOptLib.iidStreamLaw_map_eval
      canonicalHalfRademacherMarginal s
    rw [show Measure.map (fun ω : ℕ → Bool => ω s)
        canonicalHalfRademacherMeasure =
          canonicalHalfRademacherMarginal by
      simpa [canonicalHalfRademacherMeasure] using hmap]
    simp [canonicalHalfRademacherMarginal,
      SOptLib.finiteBlockIndexLaw_singleton, Measure.real_def]
  have hkernel :
      Measurable (fun q : PredictableFeedbackScalarState × Bool =>
        F q.1 q.2) := by
    refine measurable_fintype_dispatch
      (idx := fun q : PredictableFeedbackScalarState × Bool => q.2)
      (f := fun b (q : PredictableFeedbackScalarState × Bool) => F q.1 b)
      measurable_snd ?_
    intro b
    exact (measurable_from_top : Measurable fun x => F x b).comp
      measurable_fst
  have hfiber : ∀ b : Bool,
      Integrable (fun ω : ℕ → Bool => F (state ω) b)
        canonicalHalfRademacherMeasure := by
    intro b
    apply integrable_of_finiteRange_factor hstate hstate_fin
    intro ω ω' hEq
    rw [hEq]
  have hbridge :=
    SOptLib.integral_comp_indep_finite_uniform_eq_integral_inv_card_sum
      canonicalHalfRademacherMeasure (fun ω : ℕ → Bool => ω s)
        state F hstate hidx hindep huniform hkernel hfiber
  rw [hbridge]
  apply integral_congr_ae
  filter_upwards [] with ω
  norm_num [Fintype.sum_bool]
  ring

/-- Every positive-time disagreement retains at least half the stepsize in
expected absolute value under the canonical fresh half-Rademacher sample. -/
theorem canonical_expected_abs_disagreement_ge
    (alpha : ℝ) (u : ℕ) (halpha : 0 ≤ alpha) (hu : 1 ≤ u) :
    alpha / 2 ≤
      ∫ ω : ℕ → Bool,
        |(predictableFeedbackScalarTrajectory
          (fun k => canonicalHalfRademacherNoise ω k) alpha u).disagreement|
          ∂canonicalHalfRademacherMeasure := by
  classical
  obtain ⟨s, rfl⟩ : ∃ s, u = s + 1 := by
    exact Nat.exists_eq_succ_of_ne_zero (by omega)
  let state : (ℕ → Bool) → PredictableFeedbackScalarState := fun ω =>
    predictableFeedbackScalarTrajectory
      (fun k => canonicalHalfRademacherNoise ω k) alpha s
  let F : PredictableFeedbackScalarState → Bool → ℝ := fun q b =>
    |(predictableFeedbackScalarStep
      (fun _k => if b then 1 / 2 else -(1 / 2)) alpha s q).disagreement|
  have hfresh := canonical_predictable_feedback_fresh_bool_integral alpha s F
  have hselected :
      (∫ ω : ℕ → Bool,
          |(predictableFeedbackScalarTrajectory
            (fun k => canonicalHalfRademacherNoise ω k) alpha
              (s + 1)).disagreement| ∂canonicalHalfRademacherMeasure) =
        ∫ ω : ℕ → Bool, F (state ω) (ω s)
          ∂canonicalHalfRademacherMeasure := by
    apply integral_congr_ae
    filter_upwards [] with ω
    change
      |(predictableFeedbackScalarStep
        (fun k => canonicalHalfRademacherNoise ω k) alpha s
          (state ω)).disagreement| = F (state ω) (ω s)
    simp [F, predictableFeedbackScalarStep, canonicalHalfRademacherNoise]
  rw [hselected, hfresh]
  have htwoPoint : ∀ A : ℝ,
      alpha / 2 ≤ (|A + alpha / 2| + |A - alpha / 2|) / 2 := by
    intro A
    have htri := abs_sub_le (A + alpha / 2) 0 (A - alpha / 2)
    simp only [sub_zero, zero_sub, abs_neg] at htri
    rw [show (A + alpha / 2) - (A - alpha / 2) = alpha by ring,
      abs_of_nonneg halpha] at htri
    linarith
  have hpoint : ∀ ω : ℕ → Bool,
      alpha / 2 ≤ (F (state ω) false + F (state ω) true) / 2 := by
    intro ω
    by_cases hs : s = 0
    · subst s
      change alpha / 2 ≤
        (|-alpha * (-(1 / 2))| + |-alpha * (1 / 2)|) / 2
      rw [show -alpha * (-(1 / 2)) = alpha / 2 by ring,
        show -alpha * (1 / 2) = -alpha / 2 by ring,
        abs_of_nonneg (div_nonneg halpha (by norm_num)),
        abs_of_nonpos
          (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr halpha)
            (by norm_num))]
      linarith
    · let A : ℝ :=
        -alpha * ((state ω).disagreement - (state ω).previousDisagreement) +
          alpha * (state ω).previousHalfNoise
      calc
        alpha / 2 ≤ (|A + alpha / 2| + |A - alpha / 2|) / 2 :=
          htwoPoint A
        _ = (F (state ω) false + F (state ω) true) / 2 := by
          simp only [F, predictableFeedbackScalarStep, hs, if_false]
          congr 2 <;> apply congrArg abs <;> simp only [A] <;> norm_num <;> ring
  letI : MeasurableSpace PredictableFeedbackScalarState := ⊤
  let sample : ℕ → (ℕ → Bool) → Bool := fun j ω => ω j
  let hsample : ∀ j, Measurable (sample j) :=
    fun j => measurable_pi_apply j
  have hregular :=
    canonical_predictableFeedbackScalar_prefix_regular alpha s
  have hstate_past :
      Measurable[(SOptLib.filtration sample hsample).seq s] state := by
    simpa [sample, hsample, state] using hregular.1
  have hstate_fin : (Set.range state).Finite := by
    simpa [state] using hregular.2
  have hstate : Measurable state :=
    hstate_past.of_measurableSpace_le
      ((SOptLib.filtration sample hsample).le' s)
  have hfiber : ∀ b : Bool,
      Integrable (fun ω : ℕ → Bool => F (state ω) b)
        canonicalHalfRademacherMeasure := by
    intro b
    apply integrable_of_finiteRange_factor hstate hstate_fin
    intro ω ω' hEq
    rw [hEq]
  have havg : Integrable
      (fun ω : ℕ → Bool => (F (state ω) false + F (state ω) true) / 2)
      canonicalHalfRademacherMeasure :=
    ((hfiber false).add (hfiber true)).div_const 2
  have hmono := integral_mono
    (integrable_const (alpha / 2)) havg hpoint
  simpa using hmono

/-- The canonical scalar mean obeys the exact integrated recurrence obtained
by averaging the fresh half-Rademacher coordinate. -/
theorem canonical_expected_mean_succ
    (alpha : ℝ) (s : ℕ) :
    (∫ ω : ℕ → Bool,
        (predictableFeedbackScalarTrajectory
          (fun k => canonicalHalfRademacherNoise ω k) alpha
            (s + 1)).mean ∂canonicalHalfRademacherMeasure) =
      (1 - alpha) *
          ∫ ω : ℕ → Bool,
            (predictableFeedbackScalarTrajectory
              (fun k => canonicalHalfRademacherNoise ω k) alpha s).mean
              ∂canonicalHalfRademacherMeasure +
        (1 / 2) *
          ∫ ω : ℕ → Bool,
            |(predictableFeedbackScalarTrajectory
              (fun k => canonicalHalfRademacherNoise ω k) alpha s).disagreement|
              ∂canonicalHalfRademacherMeasure := by
  classical
  let state : (ℕ → Bool) → PredictableFeedbackScalarState := fun ω =>
    predictableFeedbackScalarTrajectory
      (fun k => canonicalHalfRademacherNoise ω k) alpha s
  let F : PredictableFeedbackScalarState → Bool → ℝ := fun q b =>
    (predictableFeedbackScalarStep
      (fun _k => if b then 1 / 2 else -(1 / 2)) alpha s q).mean
  have hfresh := canonical_predictable_feedback_fresh_bool_integral alpha s F
  have hselected :
      (∫ ω : ℕ → Bool,
          (predictableFeedbackScalarTrajectory
            (fun k => canonicalHalfRademacherNoise ω k) alpha
              (s + 1)).mean ∂canonicalHalfRademacherMeasure) =
        ∫ ω : ℕ → Bool, F (state ω) (ω s)
          ∂canonicalHalfRademacherMeasure := by
    apply integral_congr_ae
    filter_upwards [] with ω
    change
      (predictableFeedbackScalarStep
        (fun k => canonicalHalfRademacherNoise ω k) alpha s
          (state ω)).mean = F (state ω) (ω s)
    simp [F, predictableFeedbackScalarStep, canonicalHalfRademacherNoise]
  rw [hselected, hfresh]
  have havgPoint : ∀ ω : ℕ → Bool,
      (F (state ω) false + F (state ω) true) / 2 =
        (1 - alpha) * (state ω).mean + |(state ω).disagreement| / 2 := by
    intro ω
    simp [F, predictableFeedbackScalarStep]
  have havgIntegral :
      (∫ ω : ℕ → Bool, (F (state ω) false + F (state ω) true) / 2
          ∂canonicalHalfRademacherMeasure) =
        ∫ ω : ℕ → Bool,
          (1 - alpha) * (state ω).mean + |(state ω).disagreement| / 2
            ∂canonicalHalfRademacherMeasure := by
    apply integral_congr_ae
    filter_upwards [] with ω
    exact havgPoint ω
  rw [havgIntegral]
  letI : MeasurableSpace PredictableFeedbackScalarState := ⊤
  let sample : ℕ → (ℕ → Bool) → Bool := fun j ω => ω j
  let hsample : ∀ j, Measurable (sample j) :=
    fun j => measurable_pi_apply j
  have hregular :=
    canonical_predictableFeedbackScalar_prefix_regular alpha s
  have hstate_past :
      Measurable[(SOptLib.filtration sample hsample).seq s] state := by
    simpa [sample, hsample, state] using hregular.1
  have hstate_fin : (Set.range state).Finite := by
    simpa [state] using hregular.2
  have hstate : Measurable state :=
    hstate_past.of_measurableSpace_le
      ((SOptLib.filtration sample hsample).le' s)
  have hmeanInt : Integrable (fun ω : ℕ → Bool => (state ω).mean)
      canonicalHalfRademacherMeasure := by
    apply integrable_of_finiteRange_factor hstate hstate_fin
    intro ω ω' hEq
    rw [hEq]
  have hdisInt : Integrable
      (fun ω : ℕ → Bool => |(state ω).disagreement|)
      canonicalHalfRademacherMeasure := by
    apply integrable_of_finiteRange_factor hstate hstate_fin
    intro ω ω' hEq
    rw [hEq]
  rw [MeasureTheory.integral_add (hmeanInt.const_mul (1 - alpha))
    (hdisInt.div_const 2), MeasureTheory.integral_const_mul,
    MeasureTheory.integral_div]
  simp only [state]
  ring

/-- In the source small-stepsize regime, the exact mean recurrence and the
fresh-noise disagreement floor yield the geometric lower expansion. -/
theorem canonical_small_stepsize_expected_mean_lower
    (alpha : ℝ) (t : ℕ) (halpha_pos : 0 < alpha)
    (halpha_small : alpha ≤ 1) (ht : 1 ≤ t) :
    (1 - alpha) ^ t +
        (1 / 4) * (1 - (1 - alpha) ^ (t - 1)) ≤
      ∫ ω : ℕ → Bool,
        (predictableFeedbackScalarTrajectory
          (fun k => canonicalHalfRademacherNoise ω k) alpha t).mean
          ∂canonicalHalfRademacherMeasure := by
  have halpha : 0 ≤ alpha := halpha_pos.le
  have hq : 0 ≤ 1 - alpha := sub_nonneg.mpr halpha_small
  induction t, ht using Nat.le_induction with
  | base =>
      have hrec := canonical_expected_mean_succ alpha 0
      simpa [predictableFeedbackScalarTrajectory,
        SOptLib.recursiveIterateProcess, predictableFeedbackScalarInitial]
        using hrec.ge
  | succ t ht ih =>
      have hrec := canonical_expected_mean_succ alpha t
      have hdis := canonical_expected_abs_disagreement_ge alpha t halpha ht
      have hmul := mul_le_mul_of_nonneg_left ih hq
      have hpow : (1 - alpha) ^ t =
          (1 - alpha) * (1 - alpha) ^ (t - 1) := by
        calc
          (1 - alpha) ^ t = (1 - alpha) ^ (t - 1 + 1) := by
            rw [Nat.sub_add_cancel ht]
          _ = (1 - alpha) * (1 - alpha) ^ (t - 1) := by
            rw [pow_succ]
            ring
      rw [hrec]
      calc
        (1 - alpha) ^ (t + 1) +
              (1 / 4) * (1 - (1 - alpha) ^ (t + 1 - 1)) =
            (1 - alpha) *
                ((1 - alpha) ^ t +
                  (1 / 4) * (1 - (1 - alpha) ^ (t - 1))) +
              (1 / 2) * (alpha / 2) := by
                rw [Nat.add_sub_cancel]
                rw [pow_succ, hpow]
                ring
        _ ≤ (1 - alpha) *
              (∫ ω : ℕ → Bool,
                (predictableFeedbackScalarTrajectory
                  (fun k => canonicalHalfRademacherNoise ω k) alpha t).mean
                  ∂canonicalHalfRademacherMeasure) +
            (1 / 2) *
              (∫ ω : ℕ → Bool,
                |(predictableFeedbackScalarTrajectory
                  (fun k => canonicalHalfRademacherNoise ω k) alpha t).disagreement|
                  ∂canonicalHalfRademacherMeasure) := by
                exact add_le_add hmul
                  (mul_le_mul_of_nonneg_left hdis (by norm_num))

/-- In the large-stepsize regime, the fresh half-Rademacher term alone gives
the source conditional-variance lower bound for the scalar mean. -/
theorem canonical_large_stepsize_second_moment_lower
    (alpha : ℝ) (t : ℕ) (halpha_large : 1 < alpha) (ht : 1 ≤ t) :
    alpha ^ 2 / 4 ≤
      ∫ ω : ℕ → Bool,
        (predictableFeedbackScalarTrajectory
          (fun k => canonicalHalfRademacherNoise ω k) alpha t).mean ^ 2
          ∂canonicalHalfRademacherMeasure := by
  classical
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := by
    exact Nat.exists_eq_succ_of_ne_zero (by omega)
  let state : (ℕ → Bool) → PredictableFeedbackScalarState := fun ω =>
    predictableFeedbackScalarTrajectory
      (fun k => canonicalHalfRademacherNoise ω k) alpha s
  let F : PredictableFeedbackScalarState → Bool → ℝ := fun q b =>
    (predictableFeedbackScalarStep
      (fun _k => if b then 1 / 2 else -(1 / 2)) alpha s q).mean ^ 2
  have hfresh := canonical_predictable_feedback_fresh_bool_integral alpha s F
  have hselected :
      (∫ ω : ℕ → Bool,
          (predictableFeedbackScalarTrajectory
            (fun k => canonicalHalfRademacherNoise ω k) alpha
              (s + 1)).mean ^ 2 ∂canonicalHalfRademacherMeasure) =
        ∫ ω : ℕ → Bool, F (state ω) (ω s)
          ∂canonicalHalfRademacherMeasure := by
    apply integral_congr_ae
    filter_upwards [] with ω
    change
      (predictableFeedbackScalarStep
        (fun k => canonicalHalfRademacherNoise ω k) alpha s
          (state ω)).mean ^ 2 = F (state ω) (ω s)
    simp [F, predictableFeedbackScalarStep, canonicalHalfRademacherNoise]
  rw [hselected, hfresh]
  have hpoint : ∀ ω : ℕ → Bool,
      alpha ^ 2 / 4 ≤ (F (state ω) false + F (state ω) true) / 2 := by
    intro ω
    let A := (1 - alpha) * (state ω).mean +
      |(state ω).disagreement| / 2
    calc
      alpha ^ 2 / 4 ≤ A ^ 2 + alpha ^ 2 / 4 := by
        nlinarith [sq_nonneg A]
      _ = (F (state ω) false + F (state ω) true) / 2 := by
        simp [F, predictableFeedbackScalarStep, A]
        ring
  letI : MeasurableSpace PredictableFeedbackScalarState := ⊤
  let sample : ℕ → (ℕ → Bool) → Bool := fun j ω => ω j
  let hsample : ∀ j, Measurable (sample j) :=
    fun j => measurable_pi_apply j
  have hregular :=
    canonical_predictableFeedbackScalar_prefix_regular alpha s
  have hstate_past :
      Measurable[(SOptLib.filtration sample hsample).seq s] state := by
    simpa [sample, hsample, state] using hregular.1
  have hstate_fin : (Set.range state).Finite := by
    simpa [state] using hregular.2
  have hstate : Measurable state :=
    hstate_past.of_measurableSpace_le
      ((SOptLib.filtration sample hsample).le' s)
  have hfiber : ∀ b : Bool,
      Integrable (fun ω : ℕ → Bool => F (state ω) b)
        canonicalHalfRademacherMeasure := by
    intro b
    apply integrable_of_finiteRange_factor hstate hstate_fin
    intro ω ω' hEq
    rw [hEq]
  have havg : Integrable
      (fun ω : ℕ → Bool => (F (state ω) false + F (state ω) true) / 2)
      canonicalHalfRademacherMeasure :=
    ((hfiber false).add (hfiber true)).div_const 2
  have hmono := integral_mono
    (integrable_const (alpha ^ 2 / 4)) havg hpoint
  simpa using hmono

theorem predictable_feedback_horizon_average_lower
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (halfNoise : Ω → ℕ → ℝ) (T : ℕ) (alpha : ℝ)
    (hT : 3 ≤ T)
    (hmoment : ∀ t : ℕ, 2 ≤ t →
      (1 / 64 : ℝ) ≤
        ∫ ω, |(predictableFeedbackScalarTrajectory
          (fun k => halfNoise ω k) alpha t).mean| ^ 2 ∂μ) :
    ((T : ℝ) - 2) / (64 * (T : ℝ)) ≤
      predictableFeedbackStationarityAverage μ halfNoise T alpha := by
  let F : ℕ → ℝ := fun t =>
    ∫ ω, |(predictableFeedbackScalarTrajectory
      (fun k => halfNoise ω k) alpha t).mean| ^ 2 ∂μ
  have hF_nonneg : ∀ t, 0 ≤ F t := by
    intro t
    exact integral_nonneg (fun ω => sq_nonneg _)
  have hsum : ∀ n : ℕ, 2 ≤ n →
      ((n : ℝ) - 2) / 64 ≤ ∑ t ∈ Finset.range n, F t := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
        norm_num
        exact Finset.sum_nonneg (fun i _hi => hF_nonneg i)
    | succ n hn ih =>
        rw [Finset.sum_range_succ]
        have hnew : (1 / 64 : ℝ) ≤ F n := by
          simpa [F] using hmoment n hn
        push_cast
        nlinarith
  have hTpos : (0 : ℝ) < T := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) hT)
  unfold predictableFeedbackStationarityAverage
  change ((T : ℝ) - 2) / (64 * (T : ℝ)) ≤
    (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, F t
  calc
    ((T : ℝ) - 2) / (64 * (T : ℝ)) =
        (T : ℝ)⁻¹ * (((T : ℝ) - 2) / 64) := by
          field_simp
          <;> ring
    _ ≤ (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, F t :=
      mul_le_mul_of_nonneg_left (hsum T (le_trans (by norm_num) hT))
        (inv_nonneg.mpr hTpos.le)

theorem PredictableFeedbackNonconvergence :
    PredictableFeedbackCounterexample := by
  unfold PredictableFeedbackCounterexample
  refine ⟨?_, ?_⟩
  · simp [PredictableFeedbackConcreteProblem,
      predictableFeedbackQuadraticObjective, predictableFeedbackInitialPoint]
  · refine ⟨ℕ → Bool, inferInstance, ?_⟩
    refine ⟨canonicalHalfRademacherMeasure, inferInstance, ?_⟩
    refine ⟨canonicalHalfRademacherNoise,
      canonicalHalfRademacherNoise_spec, ?_, ?_⟩
    · intro t history
      by_cases hsign : 0 ≤ twoNodeDisagreement (history t)
      · refine ⟨⟨0, by decide⟩, ?_⟩
        simp [signPredictableFeedbackRule, predictableFeedbackMatrixSet, hsign]
      · refine ⟨⟨1, by decide⟩, ?_⟩
        simp [signPredictableFeedbackRule, predictableFeedbackMatrixSet, hsign]
    · intro T hT alpha halpha
      rw [predictableFeedbackAlgorithmStationarity_eq_scalar]
      apply predictable_feedback_horizon_average_lower
        canonicalHalfRademacherMeasure canonicalHalfRademacherNoise T alpha hT
      intro t ht
      by_cases halpha_zero : alpha = 0
      · subst alpha
        exact predictableFeedbackScalar_zero_stepsize_second_moment_lower
          canonicalHalfRademacherMeasure canonicalHalfRademacherNoise t
      · have halpha_pos : 0 < alpha := lt_of_le_of_ne halpha (Ne.symm halpha_zero)
        by_cases hsmall : alpha ≤ 1
        · let q : ℝ := 1 - alpha
          have hq0 : 0 ≤ q := by
            dsimp [q]
            linarith
          have hq1 : q ≤ 1 := by
            dsimp [q]
            linarith
          have htPred : 1 ≤ t - 1 := by omega
          obtain ⟨n, hn⟩ : ∃ n, t - 1 = n + 1 := by
            exact Nat.exists_eq_succ_of_ne_zero (by omega)
          have hpowN_le_one : q ^ n ≤ 1 :=
            pow_le_one₀ hq0 hq1
          have hx_le_q : q ^ (t - 1) ≤ q := by
            rw [hn, pow_succ]
            nlinarith [mul_le_mul_of_nonneg_right hpowN_le_one hq0]
          have hx0 : 0 ≤ q ^ (t - 1) := pow_nonneg hq0 _
          have hpowT : q ^ t = q * q ^ (t - 1) := by
            calc
              q ^ t = q ^ (t - 1 + 1) := by
                rw [Nat.sub_add_cancel (le_trans (by norm_num) ht)]
              _ = q * q ^ (t - 1) := by
                rw [pow_succ]
                ring
          have hscalar : (1 / 8 : ℝ) ≤
              q ^ t + (1 / 4) * (1 - q ^ (t - 1)) := by
            rw [hpowT]
            by_cases hquarter : (1 / 4 : ℝ) ≤ q
            · have hprod : 0 ≤ q ^ (t - 1) * (q - 1 / 4) :=
                mul_nonneg hx0 (sub_nonneg.mpr hquarter)
              nlinarith
            · have hqquarter : q < (1 / 4 : ℝ) := lt_of_not_ge hquarter
              have hxquarter : q ^ (t - 1) ≤ (1 / 4 : ℝ) :=
                le_trans hx_le_q hqquarter.le
              have hprod : 0 ≤ q * q ^ (t - 1) := mul_nonneg hq0 hx0
              nlinarith
          have hmeanExpansion :=
            canonical_small_stepsize_expected_mean_lower alpha t
              halpha_pos hsmall (le_trans (by norm_num) ht)
          have hmean : (1 / 8 : ℝ) ≤
              ∫ ω : ℕ → Bool,
                (predictableFeedbackScalarTrajectory
                  (fun k => canonicalHalfRademacherNoise ω k) alpha t).mean
                  ∂canonicalHalfRademacherMeasure := by
            exact le_trans hscalar (by simpa [q] using hmeanExpansion)
          let state : (ℕ → Bool) → PredictableFeedbackScalarState := fun ω =>
            predictableFeedbackScalarTrajectory
              (fun k => canonicalHalfRademacherNoise ω k) alpha t
          letI : MeasurableSpace PredictableFeedbackScalarState := ⊤
          let sample : ℕ → (ℕ → Bool) → Bool := fun j ω => ω j
          let hsample : ∀ j, Measurable (sample j) :=
            fun j => measurable_pi_apply j
          have hregular :=
            canonical_predictableFeedbackScalar_prefix_regular alpha t
          have hstate_past :
              Measurable[(SOptLib.filtration sample hsample).seq t] state := by
            simpa [sample, hsample, state] using hregular.1
          have hstate_fin : (Set.range state).Finite := by
            simpa [state] using hregular.2
          have hstate : Measurable state :=
            hstate_past.of_measurableSpace_le
              ((SOptLib.filtration sample hsample).le' t)
          have hmeanMeas : Measurable (fun ω : ℕ → Bool => (state ω).mean) :=
            (measurable_from_top : Measurable
              fun q : PredictableFeedbackScalarState => q.mean).comp hstate
          have hmeanSqInt : Integrable
              (fun ω : ℕ → Bool => (state ω).mean ^ 2)
              canonicalHalfRademacherMeasure := by
            apply integrable_of_finiteRange_factor hstate hstate_fin
            intro ω ω' hEq
            rw [hEq]
          have hjensen := sq_integral_le_integral_sq
            hmeanMeas.aestronglyMeasurable hmeanSqInt
          have hmeanSq : (1 / 64 : ℝ) ≤
              (∫ ω : ℕ → Bool, (state ω).mean
                ∂canonicalHalfRademacherMeasure) ^ 2 := by
            have hmeanState : (1 / 8 : ℝ) ≤
                ∫ ω : ℕ → Bool, (state ω).mean
                  ∂canonicalHalfRademacherMeasure := by
              simpa [state] using hmean
            nlinarith [sq_nonneg
              ((∫ ω : ℕ → Bool, (state ω).mean
                ∂canonicalHalfRademacherMeasure) - 1 / 8)]
          have hsecond : (1 / 64 : ℝ) ≤
              ∫ ω : ℕ → Bool, (state ω).mean ^ 2
                ∂canonicalHalfRademacherMeasure :=
            le_trans hmeanSq hjensen
          simpa [state, sq_abs] using hsecond
        · have hlarge : 1 < alpha := lt_of_not_ge hsmall
          have hlargeMoment :=
            canonical_large_stepsize_second_moment_lower alpha t hlarge
              (le_trans (by norm_num) ht)
          have hconstant : (1 / 64 : ℝ) ≤ alpha ^ 2 / 4 := by
            nlinarith [sq_nonneg (alpha - 1)]
          exact le_trans hconstant (by simpa [sq_abs] using hlargeMoment)

/-- Theorem 3.4: there is no uniform heterogeneity residual depending only on
the listed aggregate network and problem parameters. -/
theorem NoUniformHeterogeneityResidual :
    ¬ UniformHeterogeneityFreeResidualRuleExists := by
  rintro ⟨C, residual, stepsize, threshold, hresidual, huniform⟩
  have hsmall : ∀ᶠ T : ℕ in Filter.atTop,
      Real.sqrt (T : ℝ) *
          heterogeneousQuadraticResidualAtSourceTuple residual T < 1 :=
    (tendsto_order.1 hresidual).2 1 (by norm_num)
  have hlarge : ∀ᶠ T : ℕ in Filter.atTop,
      max 3 (heterogeneousQuadraticThresholdAtSourceTuple threshold) ≤ T :=
    Filter.eventually_ge_atTop _
  obtain ⟨T, hscaled, hTlarge⟩ := (hsmall.and hlarge).exists
  have hT3 : 3 ≤ T := le_trans (Nat.le_max_left _ _) hTlarge
  have hthreshold :
      heterogeneousQuadraticThresholdAtSourceTuple threshold ≤ T :=
    le_trans (Nat.le_max_right _ _) hTlarge
  let alphaT := heterogeneousQuadraticStepsizeAtSourceTuple stepsize T
  let B := heterogeneousQuadraticResidualAtSourceTuple residual T
  have hspec := huniform T hthreshold
  change 0 ≤ alphaT ∧
    ∀ H : ℝ,
      heterogeneousQuadraticStationarityAverage T alphaT H ≤
        heterogeneityFreeLinearSpeedupBound C residual
          heterogeneousQuadraticAggregatePeriod
          heterogeneousQuadraticAggregateMinWeight
          heterogeneousQuadraticAggregateMixingGap
          heterogeneousQuadraticAggregateGain
          heterogeneousQuadraticAggregateInfluenceSecondMoment
          heterogeneousQuadraticAggregateNodeCount
          heterogeneousQuadraticAggregateSmoothness
          heterogeneousQuadraticAggregateDelta
          heterogeneousQuadraticAggregateNoiseLevel T at hspec
  rcases hspec with ⟨halpha_nonneg, hallH⟩
  have hupper : ∀ H : ℝ,
      heterogeneousQuadraticStationarityAverage T alphaT H ≤ B := by
    intro H
    simpa [heterogeneityFreeLinearSpeedupBound,
      heterogeneousQuadraticAggregateNoiseLevel, B] using hallH H
  have hstation_nonneg :
      0 ≤ heterogeneousQuadraticStationarityAverage T alphaT 0 := by
    unfold heterogeneousQuadraticStationarityAverage
    positivity
  have hB_nonneg : 0 ≤ B := le_trans hstation_nonneg (hupper 0)
  change Real.sqrt (T : ℝ) * B < 1 at hscaled
  have hToneNat : 1 ≤ T := le_trans (by omega : 1 ≤ 3) hT3
  have hTone : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hToneNat
  have hsqrt_one : 1 ≤ Real.sqrt (T : ℝ) := Real.one_le_sqrt.mpr hTone
  have hB_lt_one : B < 1 := by nlinarith
  have hTpos : 0 < (T : ℝ) := lt_of_lt_of_le (by norm_num) hTone
  have hT_ne : (T : ℝ) ≠ 0 := ne_of_gt hTpos
  rcases halpha_nonneg.eq_or_lt with halpha_zero | halpha_pos
  · have hupper_zero := hupper 0
    rw [← halpha_zero] at hupper_zero
    have hzero : heterogeneousQuadraticStationarityAverage T 0 0 = 1 := by
      unfold heterogeneousQuadraticStationarityAverage
      simp_rw [heterogeneous_quadratic_average_iterate_zero_stepsize]
      simp [hT_ne]
    linarith
  · obtain ⟨H, hH⟩ :=
      exists_heterogeneity_two_step_exceeds T alphaT B hTpos halpha_pos
    have htwo := heterogeneous_quadratic_stationarity_average_ge_two_step
      T alphaT H hT3
    exact (not_lt_of_ge (hupper H)) (lt_of_lt_of_le hH htwo)

/-- Lemma A.1: spectral decomposition surface for the analytic periodic
linearization used in the counterexample analysis. -/
theorem exists_unit_spectral_separating_circle
    (A0 : NodeMatrix Node) (r0 : ℝ) (right left : RowVector Node)
    (hspectrum :
      SimpleIsolatedUnitEigenvalueStableSpectrum
        (Node := Node) A0 r0 right left) :
    ∃ radius : ℝ, 0 < radius ∧
      ∀ z : ℂ, ‖z - 1‖ = radius →
        ¬ IsComplexRightEigenvalue (Node := Node) A0 z := by
  rcases hspectrum with
    ⟨hr0_nonneg, hr0_lt_one, hright, hleft, hnormalized,
      halgebraic, hstable⟩
  refine ⟨(1 - r0) / 2, by linarith, ?_⟩
  intro z hz heigen
  have hz_ne_one : z ≠ (1 : ℂ) := by
    intro hzone
    subst z
    norm_num at hz
    linarith
  have hznorm : ‖z‖ ≤ r0 := hstable z heigen hz_ne_one
  have htriangle : (1 : ℝ) ≤ ‖z‖ + ‖z - 1‖ := by
    have h := norm_sub_le z (z - 1)
    convert h using 1 <;> norm_num <;> ring
  rw [hz] at htriangle
  linarith

end Setup
end Algorithms.Unverified.TimeVaryingPushPull
