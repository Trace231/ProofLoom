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
import Algorithms.Unverified.TimeVaryingPushPull.Part003.Part005

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

/-- Projected period-input finite-Duhamel unroll.

This is the exact vector form needed before pairing with the primal-average
row and comparing the resulting deterministic noise rows with the scalar block
innovation coefficients. -/
theorem quadratic_restricted_projected_period_input_vector_unroll
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (i0 : Node)
    (P : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (noise : NoisePath Node ℝ) (k : ℕ) :
    let Idx := Sum Node {i : Node // i ≠ i0}
    let step : ℕ → NodeMatrix Idx := fun t =>
      quadraticRestrictedOneStepMatrix (Node := Node)
        quad lambda alpha i0 t
    matrixMulVector (Node := Idx) (P alpha)
        (quadraticRestrictedPeriodNoiseInnovationCoord
          (Node := Node) quad lambda alpha i0 noise k) =
      (Finset.range quad.period).sum fun r =>
        matrixMulVector (Node := Idx) (P alpha)
          (matrixMulVector (Node := Idx)
            (consecutiveProduct (Node := Idx) step
              (k * quad.period + r + 1) (quad.period - 1 - r))
            (quadraticRestrictedNoiseInnovationCoord
              (Node := Node) quad alpha i0 noise (k * quad.period + r))) := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  let step : ℕ → NodeMatrix Idx := fun t =>
    quadraticRestrictedOneStepMatrix (Node := Node)
      quad lambda alpha i0 t
  have hunroll :=
    quadraticRestrictedConsecutiveNoiseInnovationCoord_eq_finset_sum
      (Node := Node) quad lambda alpha i0 noise (k * quad.period) quad.period
  have hmul :=
    matrixMulVector_finset_sum_local
      (Node := Idx) (P alpha) (Finset.range quad.period)
      (fun r =>
        matrixMulVector (Node := Idx)
          (consecutiveProduct (Node := Idx) step
            (k * quad.period + r + 1) (quad.period - 1 - r))
          (quadraticRestrictedNoiseInnovationCoord
            (Node := Node) quad alpha i0 noise (k * quad.period + r)))
  rw [quadraticRestrictedPeriodNoiseInnovationCoord]
  rw [hunroll]
  exact hmul

/-- Scalar-output form of the projected period-input finite-Duhamel unroll. -/
theorem quadratic_restricted_projected_period_input_output_unroll
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (i0 : Node)
    (P : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (noise : NoisePath Node ℝ) (k : ℕ) :
    let Idx := Sum Node {i : Node // i ≠ i0}
    let step : ℕ → NodeMatrix Idx := fun t =>
      quadraticRestrictedOneStepMatrix (Node := Node)
        quad lambda alpha i0 t
    quadraticRestrictedPrimalAverageOutput (Node := Node) i0
        (matrixMulVector (Node := Idx) (P alpha)
          (quadraticRestrictedPeriodNoiseInnovationCoord
            (Node := Node) quad lambda alpha i0 noise k)) =
      (Finset.range quad.period).sum fun r =>
        quadraticRestrictedPrimalAverageOutput (Node := Node) i0
          (matrixMulVector (Node := Idx) (P alpha)
            (matrixMulVector (Node := Idx)
              (consecutiveProduct (Node := Idx) step
                (k * quad.period + r + 1) (quad.period - 1 - r))
              (quadraticRestrictedNoiseInnovationCoord
                (Node := Node) quad alpha i0 noise (k * quad.period + r)))) := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  let step : ℕ → NodeMatrix Idx := fun t =>
    quadraticRestrictedOneStepMatrix (Node := Node)
      quad lambda alpha i0 t
  have hv :
      matrixMulVector (Node := Idx) (P alpha)
          (quadraticRestrictedPeriodNoiseInnovationCoord
            (Node := Node) quad lambda alpha i0 noise k) =
        (Finset.range quad.period).sum fun r =>
          matrixMulVector (Node := Idx) (P alpha)
            (matrixMulVector (Node := Idx)
              (consecutiveProduct (Node := Idx) step
                (k * quad.period + r + 1) (quad.period - 1 - r))
              (quadraticRestrictedNoiseInnovationCoord
                (Node := Node) quad alpha i0 noise (k * quad.period + r))) := by
    simpa [Idx, step] using
      quadratic_restricted_projected_period_input_vector_unroll
        (Node := Node) quad lambda alpha i0 P noise k
  change
    quadraticRestrictedPrimalAverageOutput (Node := Node) i0
        (matrixMulVector (Node := Idx) (P alpha)
          (quadraticRestrictedPeriodNoiseInnovationCoord
            (Node := Node) quad lambda alpha i0 noise k)) =
      (Finset.range quad.period).sum fun r =>
        quadraticRestrictedPrimalAverageOutput (Node := Node) i0
          (matrixMulVector (Node := Idx) (P alpha)
            (matrixMulVector (Node := Idx)
              (consecutiveProduct (Node := Idx) step
                (k * quad.period + r + 1) (quad.period - 1 - r))
              (quadraticRestrictedNoiseInnovationCoord
                (Node := Node) quad alpha i0 noise (k * quad.period + r))))
  rw [hv]
  exact
    quadraticRestrictedPrimalAverageOutput_finset_sum
      (Node := Node) i0 (Finset.range quad.period)
      (fun r =>
        matrixMulVector (Node := Idx) (P alpha)
          (matrixMulVector (Node := Idx)
            (consecutiveProduct (Node := Idx) step
              (k * quad.period + r + 1) (quad.period - 1 - r))
            (quadraticRestrictedNoiseInnovationCoord
              (Node := Node) quad alpha i0 noise (k * quad.period + r))))

/-- Row-vector representative of the restricted primal-average output. -/
noncomputable def quadraticRestrictedPrimalAverageRow
    (i0 : Node) : RowVector (Sum Node {i : Node // i ≠ i0}) :=
  fun a =>
    match a with
    | Sum.inl _ => (nodeCount (Node := Node) : ℝ)⁻¹
    | Sum.inr _ => 0

/-- At the base point, the rank-one slow projection turns the restricted
arithmetic-average row into the normalized Perron-left row. -/
theorem quadraticRestrictedPrimalAverageRow_mul_rankOneProjection_eq_left
    (i0 : Node)
    (right left : RowVector (Sum Node {i : Node // i ≠ i0}))
    (P : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (hP0 :
      P 0 = (fun i j : Sum Node {i : Node // i ≠ i0} => right i * left j))
    (hright_top : ∀ i : Node, right (Sum.inl i) = 1) :
    rowMulMatrix (Node := Sum Node {i : Node // i ≠ i0})
        (quadraticRestrictedPrimalAverageRow (Node := Node) i0) (P 0) =
      left := by
  classical
  funext a
  simp [rowMulMatrix, quadraticRestrictedPrimalAverageRow, hP0,
    Fintype.sum_sum_type, hright_top, Finset.sum_const, nodeCount,
    nodeCount_real_ne_zero (Node := Node), nsmul_eq_mul]

theorem weightedState_restrictedStateToCoord_of_top_bottom
    (i0 : Node) (w : RowVector (Sum Node {i : Node // i ≠ i0}))
    (v : RowVector Node) (S : State Node ℝ × ZeroSumState Node ℝ)
    (htop : ∀ i : Node, w (Sum.inl i) = v i)
    (hbottom : ∀ j : {i : Node // i ≠ i0}, w (Sum.inr j) = 0) :
    weightedState (Node := Sum Node {i : Node // i ≠ i0}) (E := ℝ)
        w (restrictedStateToCoord (Node := Node) i0 S) =
      weightedState (Node := Node) (E := ℝ) v S.1 := by
  classical
  unfold weightedState restrictedStateToCoord
  rw [Fintype.sum_sum_type]
  have hbottom_sum :
      (∑ j : {i : Node // i ≠ i0}, w (Sum.inr j) • S.2.1 j.1) = 0 := by
    apply Finset.sum_eq_zero
    intro j _hj
    simp [hbottom j]
  rw [hbottom_sum]
  have htop_sum :
      (∑ i : Node, w (Sum.inl i) • S.1 i) =
        ∑ i : Node, v i • S.1 i := by
    apply Finset.sum_congr rfl
    intro i _hi
    rw [htop i]
  rw [htop_sum]
  simp

/-- The alpha-zero projected average row is the source Perron-left functional
at every block endpoint when applied to restricted coordinates.

This is the base-row part of the Appendix C.1 spectral-left/corrected-lift
first variation: after the rank-one base projection is unpacked, the projected
restricted row has Perron-left top coordinates and zero tracker coordinates. -/
theorem quadraticRestrictedPrimalAverageProjectedRow_alpha_zero_weighted_eq_endpoint_perron
    (quad : Setup Node ℝ) (i0 : Node)
    (right left : RowVector (Sum Node {i : Node // i ≠ i0}))
    (P : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (hP0 :
      P 0 = (fun i j : Sum Node {i : Node // i ≠ i0} => right i * left j))
    (hright_top : ∀ i : Node, right (Sum.inl i) = 1)
    (hleft_top : ∀ i : Node, left (Sum.inl i) = quad.perronLeft 0 i)
    (hleft_bottom : ∀ j : {i : Node // i ≠ i0}, left (Sum.inr j) = 0)
    (k : ℕ) (S : State Node ℝ × ZeroSumState Node ℝ) :
    weightedState (Node := Sum Node {i : Node // i ≠ i0}) (E := ℝ)
        (rowMulMatrix (Node := Sum Node {i : Node // i ≠ i0})
          (quadraticRestrictedPrimalAverageRow (Node := Node) i0) (P 0))
        (restrictedStateToCoord (Node := Node) i0 S) =
      weightedState (Node := Node) (E := ℝ)
        (quad.perronLeft (quad.blockStart (k + 1))) S.1 := by
  classical
  let rowP : RowVector (Sum Node {i : Node // i ≠ i0}) :=
    rowMulMatrix (Node := Sum Node {i : Node // i ≠ i0})
      (quadraticRestrictedPrimalAverageRow (Node := Node) i0) (P 0)
  have hrowP :
      rowP = left := by
    simpa [rowP] using
      quadraticRestrictedPrimalAverageRow_mul_rankOneProjection_eq_left
        (Node := Node) i0 right left P hP0 hright_top
  have hperron_block :
      quad.perronLeft (quad.blockStart (k + 1)) = quad.perronLeft 0 := by
    simpa using quad.perronLeft_blockStart_add (k + 1) 0
  have htop :
      ∀ i : Node, rowP (Sum.inl i) =
        quad.perronLeft (quad.blockStart (k + 1)) i := by
    intro i
    rw [hrowP, hperron_block, hleft_top i]
  have hbottom :
      ∀ j : {i : Node // i ≠ i0}, rowP (Sum.inr j) = 0 := by
    intro j
    rw [hrowP, hleft_bottom j]
  simpa [rowP] using
    weightedState_restrictedStateToCoord_of_top_bottom
      (Node := Node) i0 rowP (quad.perronLeft (quad.blockStart (k + 1)))
      S htop hbottom

/-- The row-derivative/corrected-lift functional is invariant under one
alpha-zero tracker period.

This is the next source-specific bridge for Appendix C.1: differentiating the
moving projected left eigenrow and inserting the period-matrix derivative
transport shows that `rowDeriv + correctedLift` is unchanged by the tracker
period map at `alpha = 0`. -/
theorem quadraticRestrictedProjectedRowDeriv_correctedLift_tracker_period_invariant
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (left : RowVector (Sum Node {i : Node // i ≠ i0}))
    (P : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (gamma : ℝ → ℝ)
    (Aderiv : NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (gammaDeriv : ℝ)
    (rowDeriv : RowVector (Sum Node {i : Node // i ≠ i0}))
    (hleft_top : ∀ i : Node, left (Sum.inl i) = quad.perronLeft 0 i)
    (hleft_bottom : ∀ j : {i : Node // i ≠ i0}, left (Sum.inr j) = 0)
    (hrow :
      HasDerivAt
        (fun alpha : ℝ =>
          rowMulMatrix (Node := Sum Node {i : Node // i ≠ i0})
            (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
            (P alpha))
        rowDeriv 0)
    (hAderiv :
      HasDerivAt
        (fun alpha : ℝ =>
          quadraticRestrictedPeriodMatrix (Node := Node)
            quad lambda alpha i0)
        Aderiv 0)
    (hgammaDeriv : HasDerivAt gamma gammaDeriv 0)
    (hgamma0 : gamma 0 = 1)
    (heigen : ∀ᶠ alpha : ℝ in 𝓝 0,
      rowMulMatrix (Node := Sum Node {i : Node // i ≠ i0})
          (rowMulMatrix (Node := Sum Node {i : Node // i ≠ i0})
            (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
            (P alpha))
          (quadraticRestrictedPeriodMatrix (Node := Node)
            quad lambda alpha i0) =
        gamma alpha •
          rowMulMatrix (Node := Sum Node {i : Node // i ≠ i0})
            (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
            (P alpha))
    (hrow0_eq_left :
      rowMulMatrix (Node := Sum Node {i : Node // i ≠ i0})
        (quadraticRestrictedPrimalAverageRow (Node := Node) i0) (P 0) =
        left)
    (W : ZeroSumState Node ℝ) :
    let Wnext : ZeroSumState Node ℝ :=
      (quadraticRestrictedHomogeneousOrbit (Node := Node)
        quad lambda 0 0 quad.period
        ((fun _ : Node => (0 : ℝ)), W)).2
    weightedState (Node := Sum Node {i : Node // i ≠ i0}) (E := ℝ)
        rowDeriv
        (restrictedStateToCoord (Node := Node) i0
          ((fun _ : Node => (0 : ℝ)), Wnext)) +
      quad.correctedLift 0 Wnext =
        weightedState (Node := Sum Node {i : Node // i ≠ i0}) (E := ℝ)
          rowDeriv
          (restrictedStateToCoord (Node := Node) i0
            ((fun _ : Node => (0 : ℝ)), W)) +
        quad.correctedLift 0 W := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  let row : ℝ → RowVector Idx := fun alpha =>
    rowMulMatrix (Node := Idx)
      (quadraticRestrictedPrimalAverageRow (Node := Node) i0) (P alpha)
  let S0 : State Node ℝ × ZeroSumState Node ℝ :=
    ((fun _ : Node => (0 : ℝ)), W)
  let Wnext : ZeroSumState Node ℝ :=
    (quadraticRestrictedHomogeneousOrbit (Node := Node)
      quad lambda 0 0 quad.period S0).2
  let z : RowVector Idx := restrictedStateToCoord (Node := Node) i0 S0
  have hleft_eq :
      left =
        (fun a : Idx =>
          match a with
          | Sum.inl i => quad.perronLeft 0 i
          | Sum.inr _ => 0) := by
    funext a
    cases a with
    | inl i => exact hleft_top i
    | inr j => exact hleft_bottom j
  have hrow' : HasDerivAt row rowDeriv 0 := by
    simpa [row, Idx] using hrow
  have heigen' : ∀ᶠ alpha : ℝ in 𝓝 0,
      rowMulMatrix (Node := Idx) (row alpha)
          (quadraticRestrictedPeriodMatrix (Node := Node)
            quad lambda alpha i0) =
        gamma alpha • row alpha := by
    simpa [row, Idx] using heigen
  have hderiv_pair :=
    weightedState_left_eigenrow_derivative_pairing
      (Node := Idx)
      (fun alpha : ℝ =>
        quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda alpha i0)
      gamma row Aderiv gammaDeriv rowDeriv hAderiv hgammaDeriv hrow'
      hgamma0 heigen' z
  have horbit_top :
      (quadraticRestrictedHomogeneousOrbit (Node := Node)
        quad lambda 0 0 quad.period S0).1 =
        fun _ : Node => (0 : ℝ) := by
    have horbit :=
      quadraticRestrictedHomogeneousOrbit_alpha_zero_tracker_only
        (Node := Node) quad lambda 0 quad.period W
    simpa [S0] using congrArg Prod.fst horbit
  have hA0z :
      matrixMulVector (Node := Idx)
          (quadraticRestrictedPeriodMatrix (Node := Node)
            quad lambda 0 i0) z =
        restrictedStateToCoord (Node := Node) i0
          ((fun _ : Node => (0 : ℝ)), Wnext) := by
    change
      matrixMulVector (Node := Idx)
          (quadraticRestrictedPeriodMatrix (Node := Node)
            quad lambda 0 i0)
          (restrictedStateToCoord (Node := Node) i0 S0) =
        restrictedStateToCoord (Node := Node) i0
          ((fun _ : Node => (0 : ℝ)), Wnext)
    rw [quadraticRestrictedPeriodMatrix_represents_period]
    congr 1
    exact Prod.ext horbit_top rfl
  have hrow0_zero :
      weightedState (Node := Idx) (E := ℝ) (row 0) z = 0 := by
    change
      weightedState (Node := Idx) (E := ℝ)
          (rowMulMatrix (Node := Idx)
            (quadraticRestrictedPrimalAverageRow (Node := Node) i0) (P 0))
          (restrictedStateToCoord (Node := Node) i0 S0) = 0
    rw [hrow0_eq_left]
    unfold weightedState
    dsimp [S0, restrictedStateToCoord]
    rw [Fintype.sum_sum_type]
    have htop :
        (∑ i : Node, left (Sum.inl i) * (0 : ℝ)) = 0 := by
      simp
    have hbottom :
        (∑ j : {i : Node // i ≠ i0},
          left (Sum.inr j) * W.1 j.1) = 0 := by
      apply Finset.sum_eq_zero
      intro j _hj
      simp [hleft_bottom j]
    rw [htop, hbottom]
    ring
  have hmatrix_pair :
      weightedState (Node := Idx) (E := ℝ) (row 0)
          (matrixMulVector (Node := Idx) Aderiv z) =
        quad.correctedLift quad.period Wnext - quad.correctedLift 0 W := by
    have hperiod :=
      quadraticRestrictedPeriodMatrix_deriv_tracker_pairing_eq_correctedLift_difference
        (Node := Node) quad lambda i0 Aderiv hAderiv W
    change
      weightedState (Node := Idx) (E := ℝ)
          (rowMulMatrix (Node := Idx)
            (quadraticRestrictedPrimalAverageRow (Node := Node) i0) (P 0))
          (matrixMulVector (Node := Idx) Aderiv
            (restrictedStateToCoord (Node := Node) i0 S0)) =
        quad.correctedLift quad.period Wnext - quad.correctedLift 0 W
    rw [hrow0_eq_left, hleft_eq]
    simpa [Idx, S0, Wnext, rowDot, weightedState] using hperiod
  have hcorr_period :
      quad.correctedLift quad.period Wnext = quad.correctedLift 0 Wnext := by
    simpa [Setup.blockStart] using
      quad.correctedLift_blockStart 1 Wnext
  rw [hA0z, hmatrix_pair, hrow0_zero, hcorr_period] at hderiv_pair
  dsimp [Wnext, S0] at hderiv_pair ⊢
  nlinarith

/-- A tracker-period invariant row-derivative/corrected-lift functional must
vanish on the zero-sum tracker subspace.

The proof is the source C.1 contraction argument at the functional level:
iterate the invariant through alpha-zero pull periods, bound the row part and
the corrected lift by the Frobenius norm of the tracker state, and let the
geometrically contracted tail go to zero. -/
theorem quadraticRestrictedTrackerInvariantFunctional_eq_zero
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (rowDeriv : RowVector (Sum Node {i : Node // i ≠ i0}))
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
    (hinv :
      ∀ W : ZeroSumState Node ℝ,
        let Wnext : ZeroSumState Node ℝ :=
          (quadraticRestrictedHomogeneousOrbit (Node := Node)
            quad lambda 0 0 quad.period
            ((fun _ : Node => (0 : ℝ)), W)).2
        weightedState
            (Node := Sum Node {i : Node // i ≠ i0}) (E := ℝ)
            rowDeriv
            (restrictedStateToCoord (Node := Node) i0
              ((fun _ : Node => (0 : ℝ)), Wnext)) +
          quad.correctedLift 0 Wnext =
            weightedState
              (Node := Sum Node {i : Node // i ≠ i0}) (E := ℝ)
              rowDeriv
              (restrictedStateToCoord (Node := Node) i0
                ((fun _ : Node => (0 : ℝ)), W)) +
            quad.correctedLift 0 W)
    (W : ZeroSumState Node ℝ) :
    weightedState
        (Node := Sum Node {i : Node // i ≠ i0}) (E := ℝ)
        rowDeriv
        (restrictedStateToCoord (Node := Node) i0
          ((fun _ : Node => (0 : ℝ)), W)) +
      quad.correctedLift 0 W = 0 := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  let Phi : ZeroSumState Node ℝ → ℝ := fun V =>
    weightedState (Node := Idx) (E := ℝ) rowDeriv
        (restrictedStateToCoord (Node := Node) i0
          ((fun _ : Node => (0 : ℝ)), V)) +
      quad.correctedLift 0 V
  let Witer : ℕ → ZeroSumState Node ℝ := fun m =>
    ⟨leftMul (Node := Node) (E := ℝ)
        (quad.pullLiftProduct 0 (m * quad.period)) W.1,
      quad.pullLiftProduct_leftMul_zeroSum 0 (m * quad.period) W⟩
  have hWiter_zero : Witer 0 = W := by
    apply Subtype.ext
    funext i
    simp [Witer, pullLiftProduct, leftMul, identityMatrix]
  have hWiter_succ :
      ∀ m : ℕ,
        (quadraticRestrictedHomogeneousOrbit (Node := Node)
            quad lambda 0 0 quad.period
            ((fun _ : Node => (0 : ℝ)), Witer m)).2 =
          Witer (m + 1) := by
    intro m
    have horbit :=
      quadraticRestrictedHomogeneousOrbit_alpha_zero_tracker_only
        (Node := Node) quad lambda 0 quad.period (Witer m)
    apply Subtype.ext
    funext i
    have hprod :
        leftMul (Node := Node) (E := ℝ)
            (quad.pullLiftProduct 0 ((m + 1) * quad.period)) W.1 =
          leftMul (Node := Node) (E := ℝ)
            (quad.pullLiftProduct 0 quad.period)
            (leftMul (Node := Node) (E := ℝ)
              (quad.pullLiftProduct 0 (m * quad.period)) W.1) := by
      calc
        leftMul (Node := Node) (E := ℝ)
            (quad.pullLiftProduct 0 ((m + 1) * quad.period)) W.1 =
          leftMul (Node := Node) (E := ℝ)
            (quad.pullLiftProduct 0 (m * quad.period + quad.period)) W.1 := by
              rw [Nat.succ_mul]
        _ =
          leftMul (Node := Node) (E := ℝ)
            (matrixMul (Node := Node)
              (quad.pullLiftProduct (0 + m * quad.period) quad.period)
              (quad.pullLiftProduct 0 (m * quad.period))) W.1 := by
              rw [quad.pullLiftProduct_add]
        _ =
          leftMul (Node := Node) (E := ℝ)
            (quad.pullLiftProduct (m * quad.period) quad.period)
            (leftMul (Node := Node) (E := ℝ)
              (quad.pullLiftProduct 0 (m * quad.period)) W.1) := by
              rw [leftMul_matrixMul]
              simp
        _ =
          leftMul (Node := Node) (E := ℝ)
            (quad.pullLiftProduct 0 quad.period)
            (leftMul (Node := Node) (E := ℝ)
              (quad.pullLiftProduct 0 (m * quad.period)) W.1) := by
              rw [pullLiftProduct_periodic_start_mul]
    have hcoord := congrArg (fun S : State Node ℝ × ZeroSumState Node ℝ => S.2.1 i) horbit
    simpa [Witer, hprod] using hcoord
  have hPhi_iter : ∀ m : ℕ, Phi (Witer m) = Phi W := by
    intro m
    induction m with
    | zero =>
        simpa [hWiter_zero]
    | succ m ih =>
        have hstep := hinv (Witer m)
        have hs := hWiter_succ m
        have hstep' : Phi (Witer (m + 1)) = Phi (Witer m) := by
          simpa [Phi, Idx, hs] using hstep
        exact hstep'.trans ih
  let rowMass : ℝ := ∑ a : Idx, |rowDeriv a|
  let opNorm : ℝ := quad.correctedLiftOperatorNorm 0
  let Cfun : ℝ := rowMass + opNorm
  have hrowMass_nonneg : 0 ≤ rowMass := by
    dsimp [rowMass]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hop_nonneg : 0 ≤ opNorm := by
    dsimp [opNorm]
    exact (quad.correctedLiftOperatorNorm_spec 0).1
  have hCfun_nonneg : 0 ≤ Cfun := by
    dsimp [Cfun]
    exact add_nonneg hrowMass_nonneg hop_nonneg
  have hPhi_bound :
      ∀ V : ZeroSumState Node ℝ,
        ‖Phi V‖ ≤
          Cfun * stateFrobeniusNorm (Node := Node) (E := ℝ) V.1 := by
    intro V
    let z : RowVector Idx :=
      restrictedStateToCoord (Node := Node) i0
        ((fun _ : Node => (0 : ℝ)), V)
    have hrow :
        ‖weightedState (Node := Idx) (E := ℝ) rowDeriv z‖ ≤
          rowMass * stateFrobeniusNorm (Node := Node) (E := ℝ) V.1 := by
      calc
        ‖weightedState (Node := Idx) (E := ℝ) rowDeriv z‖ =
            ‖∑ a : Idx, rowDeriv a • z a‖ := rfl
        _ ≤ ∑ a : Idx, ‖rowDeriv a • z a‖ := norm_sum_le _ _
        _ ≤ ∑ a : Idx,
              |rowDeriv a| *
                stateFrobeniusNorm (Node := Node) (E := ℝ) V.1 := by
              apply Finset.sum_le_sum
              intro a _ha
              rw [norm_smul, Real.norm_eq_abs]
              apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
              cases a with
              | inl i =>
                  simp [z, restrictedStateToCoord, stateFrobeniusNorm]
              | inr j =>
                  simpa [z, restrictedStateToCoord] using
                    norm_apply_le_stateFrobeniusNorm
                      (Node := Node) (E := ℝ) V.1 j.1
        _ = rowMass * stateFrobeniusNorm (Node := Node) (E := ℝ) V.1 := by
              rw [Finset.sum_mul]
    have hcorr :
        ‖quad.correctedLift 0 V‖ ≤
          opNorm * stateFrobeniusNorm (Node := Node) (E := ℝ) V.1 := by
      dsimp [opNorm]
      exact (quad.correctedLiftOperatorNorm_spec 0).2 V
    calc
      ‖Phi V‖ ≤
          ‖weightedState (Node := Idx) (E := ℝ) rowDeriv
              (restrictedStateToCoord (Node := Node) i0
                ((fun _ : Node => (0 : ℝ)), V))‖ +
            ‖quad.correctedLift 0 V‖ := by
              simpa [Phi, z] using
                norm_add_le
                  (weightedState (Node := Idx) (E := ℝ) rowDeriv z)
                  (quad.correctedLift 0 V)
      _ ≤
          rowMass * stateFrobeniusNorm (Node := Node) (E := ℝ) V.1 +
            opNorm * stateFrobeniusNorm (Node := Node) (E := ℝ) V.1 :=
              add_le_add hrow hcorr
      _ =
          Cfun * stateFrobeniusNorm (Node := Node) (E := ℝ) V.1 := by
            ring
  let Wnorm : ℝ := stateFrobeniusNorm (Node := Node) (E := ℝ) W.1
  have hWnorm_nonneg : 0 ≤ Wnorm := by
    dsimp [Wnorm]
    exact Real.sqrt_nonneg _
  have hcol_nonneg : 0 ≤ quad.columnContractionConstant := by
    dsimp [Setup.columnContractionConstant]
    exact div_nonneg (Real.sqrt_nonneg _) quad.contractionDelta_pos.le
  have hM_nonneg :
      0 ≤ Cfun * quad.columnContractionConstant * Wnorm := by
    exact mul_nonneg (mul_nonneg hCfun_nonneg hcol_nonneg) hWnorm_nonneg
  have hq_nonneg : 0 ≤ quad.contractionRate ^ quad.period :=
    pow_nonneg hstable.1 quad.period
  have hq_lt_one : quad.contractionRate ^ quad.period < 1 := by
    exact pow_lt_one₀ hstable.1 hstable.2.1
      (Nat.ne_of_gt quad.period_pos)
  have htail :
      ∀ N : ℕ,
        ‖((Phi W : ℝ) : ℂ)‖ ≤
          (1 : ℝ) *
            ((Cfun * quad.columnContractionConstant * Wnorm) *
              (quad.contractionRate ^ quad.period) ^ (N + 1)) := by
    intro N
    have hcontract :=
      hstable.2.2.1 0 ((N + 1) * quad.period) W
    have hcontract' :
        stateFrobeniusNorm (Node := Node) (E := ℝ) (Witer (N + 1)).1 ≤
          quad.columnContractionConstant *
            quad.contractionRate ^ ((N + 1) * quad.period) * Wnorm := by
      simpa [Witer, Wnorm] using hcontract
    have hbound_iter := hPhi_bound (Witer (N + 1))
    have hbound_real :
        ‖Phi W‖ ≤
          Cfun *
            (quad.columnContractionConstant *
              quad.contractionRate ^ ((N + 1) * quad.period) * Wnorm) := by
      calc
        ‖Phi W‖ = ‖Phi (Witer (N + 1))‖ := by
          rw [hPhi_iter (N + 1)]
        _ ≤
          Cfun * stateFrobeniusNorm (Node := Node) (E := ℝ)
            (Witer (N + 1)).1 := hbound_iter
        _ ≤
          Cfun *
            (quad.columnContractionConstant *
              quad.contractionRate ^ ((N + 1) * quad.period) * Wnorm) :=
            mul_le_mul_of_nonneg_left hcontract' hCfun_nonneg
    have hpow :
        quad.contractionRate ^ ((N + 1) * quad.period) =
          (quad.contractionRate ^ quad.period) ^ (N + 1) := by
      rw [Nat.mul_comm, pow_mul]
    have hnorm_cast : ‖((Phi W : ℝ) : ℂ)‖ = ‖Phi W‖ := by
      simp
    calc
      ‖((Phi W : ℝ) : ℂ)‖ = ‖Phi W‖ := hnorm_cast
      _ ≤
          Cfun *
            (quad.columnContractionConstant *
              quad.contractionRate ^ ((N + 1) * quad.period) * Wnorm) :=
          hbound_real
      _ =
          (1 : ℝ) *
            ((Cfun * quad.columnContractionConstant * Wnorm) *
              (quad.contractionRate ^ quad.period) ^ (N + 1)) := by
          rw [hpow]
          ring
  have hcomplex_zero :
      ((Phi W : ℝ) : ℂ) = 0 :=
    zero_center_norm_le_geometric_tail_for_all_N_forces_eq_zero
      (R := (1 : ℝ))
      (M := Cfun * quad.columnContractionConstant * Wnorm)
      (q := quad.contractionRate ^ quad.period)
      (D := ((Phi W : ℝ) : ℂ))
      zero_lt_one hM_nonneg hq_nonneg hq_lt_one htail
  have hreal_zero : Phi W = 0 := Complex.ofReal_eq_zero.mp hcomplex_zero
  simpa [Phi, Idx] using hreal_zero

/-- The projected arithmetic-average row is a left eigenrow of the current
restricted period matrix on the Riesz slow branch.

This is the algebraic half of the Appendix C.1 "spectral left coordinate"
bridge: the moving row is not an arbitrary analytic row, but the row obtained
by left-multiplying the slow Riesz projection.  The remaining first-variation
leaf is to identify the derivative of this left eigenrow on tracker
directions with the corrected lift. -/
theorem quadraticRestrictedPrimalAverageProjectedRow_left_eigen
    (i0 : Node) (gamma : ℝ)
    (A P : NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (hRiesz :
      IsRieszProjectionAtEigenvalue
        (Node := Sum Node {i : Node // i ≠ i0}) A gamma P) :
    rowMulMatrix (Node := Sum Node {i : Node // i ≠ i0})
        (rowMulMatrix (Node := Sum Node {i : Node // i ≠ i0})
          (quadraticRestrictedPrimalAverageRow (Node := Node) i0) P) A =
      gamma •
        rowMulMatrix (Node := Sum Node {i : Node // i ≠ i0})
          (quadraticRestrictedPrimalAverageRow (Node := Node) i0) P := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  have hPA : matrixMul (Node := Idx) P A = gamma • P :=
    IsRieszProjectionAtEigenvalue.matrix_mul_right
      (Node := Idx) hRiesz
  calc
    rowMulMatrix (Node := Idx)
        (rowMulMatrix (Node := Idx)
          (quadraticRestrictedPrimalAverageRow (Node := Node) i0) P) A =
      rowMulMatrix (Node := Idx)
        (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
        (matrixMul (Node := Idx) P A) := by
        rw [rowMulMatrix_matrixMul]
    _ =
      rowMulMatrix (Node := Idx)
        (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
        (gamma • P) := by
        rw [hPA]
    _ =
      gamma •
        rowMulMatrix (Node := Idx)
          (quadraticRestrictedPrimalAverageRow (Node := Node) i0) P := by
        funext a
        unfold rowMulMatrix
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _hb
        ring

/-- Left-multiplying an analytic matrix path by a fixed row preserves the
derivative at the source expansion point.  This isolates the calculus part of
the moving projected-average-row first variation. -/
theorem rowMulMatrix_const_hasDerivAt
    (row : RowVector Node) (P : ℝ → NodeMatrix Node)
    (Pderiv : NodeMatrix Node)
    (hP : HasDerivAt P Pderiv 0) :
    HasDerivAt
      (fun alpha : ℝ => rowMulMatrix (Node := Node) row (P alpha))
      (rowMulMatrix (Node := Node) row Pderiv) 0 := by
  classical
  rw [hasDerivAt_pi]
  intro j
  unfold rowMulMatrix
  apply HasDerivAt.fun_sum
  intro i _hi
  have hPij :
      HasDerivAt (fun alpha : ℝ => P alpha i j) (Pderiv i j) 0 := by
    have hi :=
      (hasFDerivAt_apply (𝕜 := ℝ) i (P 0)).comp 0 hP.hasFDerivAt
    have hij :=
      (hasFDerivAt_apply (𝕜 := ℝ) j (P 0 i)).comp 0 hi
    convert hij.hasDerivAt using 1 <;>
      simp [Function.comp_def, ContinuousLinearMap.one_apply]
  exact hPij.const_mul (row i)

/-- The moving projected arithmetic-average row supplied by the periodic
spectral splitting has a derivative at zero.

This does not identify the derivative with the corrected lift; it exposes the
actual derivative object that the Appendix C.1 Poisson/eigenrow first-variation
calculation must evaluate. -/
theorem quadraticRestrictedPrimalAverageProjectedRow_hasDerivAt_zero
    (i0 : Node) (r0 alpha0 theta K : ℝ)
    (right left : RowVector (Sum Node {i : Node // i ≠ i0}))
    (gamma : ℝ → ℝ)
    (A P F : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (hsplitting :
      PeriodicSpectralSplitting
        (Node := Sum Node {i : Node // i ≠ i0})
        A r0 alpha0 theta K right left gamma P F) :
    ∃ rowDeriv : RowVector (Sum Node {i : Node // i ≠ i0}),
      HasDerivAt
        (fun alpha : ℝ =>
          rowMulMatrix (Node := Sum Node {i : Node // i ≠ i0})
            (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
            (P alpha))
        rowDeriv 0 := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  rcases hsplitting with
    ⟨halpha0_pos, _hr0theta, _htheta_lt_one, _hK_nonneg, _hgamma0,
      _hgamma_analytic, hP_analytic, _hderiv, _hlocal⟩
  have hP0_analytic : AnalyticAt ℝ P 0 :=
    hP_analytic 0 (by simpa using halpha0_pos)
  let Pderiv : NodeMatrix Idx := (fderiv ℝ P 0) 1
  refine
    ⟨rowMulMatrix (Node := Idx)
        (quadraticRestrictedPrimalAverageRow (Node := Node) i0) Pderiv, ?_⟩
  exact
    rowMulMatrix_const_hasDerivAt
      (Node := Idx)
      (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
      P Pderiv hP0_analytic.differentiableAt.hasDerivAt

/-- The restricted primal-average output is the weighted row action of its
canonical average row. -/
theorem quadraticRestrictedPrimalAverageOutput_eq_weightedState
    (i0 : Node) (z : RowVector (Sum Node {i : Node // i ≠ i0})) :
    quadraticRestrictedPrimalAverageOutput (Node := Node) i0 z =
      weightedState (Node := Sum Node {i : Node // i ≠ i0}) (E := ℝ)
        (quadraticRestrictedPrimalAverageRow (Node := Node) i0) z := by
  classical
  unfold quadraticRestrictedPrimalAverageOutput
  unfold weightedState quadraticRestrictedPrimalAverageRow
  rw [Fintype.sum_sum_type]
  simp [smul_eq_mul, Finset.mul_sum]

/-- Applying any restricted row to the one-step C.1 noise channel gives a
deterministic weighted node-noise row. -/
theorem weightedState_quadraticRestrictedNoiseInnovationCoord
    (quad : Setup Node ℝ) (alpha : ℝ) (i0 : Node)
    (noise : NoisePath Node ℝ) (t : ℕ)
    (w : RowVector (Sum Node {i : Node // i ≠ i0})) :
    weightedState (Node := Sum Node {i : Node // i ≠ i0}) (E := ℝ) w
        (quadraticRestrictedNoiseInnovationCoord
          (Node := Node) quad alpha i0 noise t) =
      weightedState (Node := Node) (E := ℝ)
        (fun j : Node =>
          ∑ a : Sum Node {i : Node // i ≠ i0},
            w a *
              quadraticRestrictedNoiseInnovationCoeff
                (Node := Node) quad alpha i0 t a j)
        (noise t) := by
  classical
  unfold weightedState
  simp only [quadraticRestrictedNoiseInnovationCoord_eq_weightedCoeff,
    weightedState, Finset.smul_sum, smul_eq_mul]
  calc
    (∑ x : Sum Node {i : Node // i ≠ i0},
        w x *
          ∑ x_1 : Node,
            quadraticRestrictedNoiseInnovationCoeff
              (Node := Node) quad alpha i0 t x x_1 * noise t x_1) =
      ∑ x : Sum Node {i : Node // i ≠ i0},
        ∑ x_1 : Node,
          w x *
            (quadraticRestrictedNoiseInnovationCoeff
              (Node := Node) quad alpha i0 t x x_1 * noise t x_1) := by
        apply Finset.sum_congr rfl
        intro a _ha
        rw [Finset.mul_sum]
    _ =
      ∑ x_1 : Node,
        ∑ x : Sum Node {i : Node // i ≠ i0},
          w x *
            (quadraticRestrictedNoiseInnovationCoeff
              (Node := Node) quad alpha i0 t x x_1 * noise t x_1) := by
        rw [Finset.sum_comm]
    _ =
      ∑ x : Node,
        (∑ a : Sum Node {i : Node // i ≠ i0},
          w a *
            quadraticRestrictedNoiseInnovationCoeff
              (Node := Node) quad alpha i0 t a x) *
          noise t x := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _ha
        ring

/-- Each deterministic one-step restricted noise coefficient is analytic in
the stepsize. -/
theorem quadraticRestrictedNoiseInnovationCoeff_analyticAt
    (quad : Setup Node ℝ) (i0 : Node) (t : ℕ)
    (a : Sum Node {i : Node // i ≠ i0}) (j : Node)
    (alphaBase : ℝ) :
    AnalyticAt ℝ
      (fun alpha : ℝ =>
        quadraticRestrictedNoiseInnovationCoeff
          (Node := Node) quad alpha i0 t a j) alphaBase := by
  classical
  cases a with
  | inl i =>
      by_cases hij : i = j
      · simp [quadraticRestrictedNoiseInnovationCoeff, hij]
        fun_prop
      · simp [quadraticRestrictedNoiseInnovationCoeff, hij]
        fun_prop
  | inr i =>
      simp [quadraticRestrictedNoiseInnovationCoeff]
      fun_prop

/-- Deterministic node-noise row produced by one phase of the projected
restricted period input after pairing with the primal-average output. -/
noncomputable def quadraticRestrictedProjectedPeriodInputCoeff
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (i0 : Node)
    (P : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (k r : ℕ) : RowVector Node :=
  let Idx := Sum Node {i : Node // i ≠ i0}
  let step : ℕ → NodeMatrix Idx := fun t =>
    quadraticRestrictedOneStepMatrix (Node := Node)
      quad lambda alpha i0 t
  let B : NodeMatrix Idx :=
    consecutiveProduct (Node := Idx) step
      (k * quad.period + r + 1) (quad.period - 1 - r)
  let row : RowVector Idx :=
    rowMulMatrix (Node := Idx)
      (rowMulMatrix (Node := Idx)
        (quadraticRestrictedPrimalAverageRow (Node := Node) i0) (P alpha)) B
  fun j : Node =>
    ∑ a : Idx,
      row a *
        quadraticRestrictedNoiseInnovationCoeff
          (Node := Node) quad alpha i0 (k * quad.period + r) a j

/-- The projected period-input coefficient row is block-periodic.  Hence the
fixed-block coefficient and `L²` estimates can be upgraded through the finite
set of within-period phases instead of carrying constants depending on `k`. -/
theorem quadraticRestrictedProjectedPeriodInputCoeff_block_eq_zero
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (i0 : Node)
    (P : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (k r : ℕ) :
    quadraticRestrictedProjectedPeriodInputCoeff
        (Node := Node) quad lambda alpha i0 P k r =
      quadraticRestrictedProjectedPeriodInputCoeff
        (Node := Node) quad lambda alpha i0 P 0 r := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  let step : ℕ → NodeMatrix Idx := fun t =>
    quadraticRestrictedOneStepMatrix (Node := Node)
      quad lambda alpha i0 t
  have hstart :
      k * quad.period + r + 1 = quad.blockStart k + (r + 1) := by
    simp [Setup.blockStart]
    omega
  have hstart0 : 0 * quad.period + r + 1 = r + 1 := by omega
  have hB :
      consecutiveProduct (Node := Idx) step
          (k * quad.period + r + 1) (quad.period - 1 - r) =
        consecutiveProduct (Node := Idx) step
          (r + 1) (quad.period - 1 - r) := by
    calc
      consecutiveProduct (Node := Idx) step
          (k * quad.period + r + 1) (quad.period - 1 - r) =
        consecutiveProduct (Node := Idx) step
          (quad.blockStart k + (r + 1)) (quad.period - 1 - r) := by
            rw [hstart]
      _ =
        consecutiveProduct (Node := Idx) step
          (r + 1) (quad.period - 1 - r) := by
            simpa [Idx, step] using
              quadraticRestrictedConsecutiveProduct_blockStart_add
                (Node := Node) quad lambda alpha i0 k (r + 1)
                (quad.period - 1 - r)
  have hcoeff :
      ∀ a : Idx,
        quadraticRestrictedNoiseInnovationCoeff
            (Node := Node) quad alpha i0 (k * quad.period + r) a =
          quadraticRestrictedNoiseInnovationCoeff
            (Node := Node) quad alpha i0 r a := by
    intro a
    have h :=
      quadraticRestrictedNoiseInnovationCoeff_blockStart_add
        (Node := Node) quad alpha i0 k r a
    simpa [Setup.blockStart] using h
  funext j
  simp [quadraticRestrictedProjectedPeriodInputCoeff, Idx, step, hB,
    hcoeff, hstart0]

/-- Coefficient-row form of a projected period-input phase.  This is the
deterministic row gateway for the Appendix C.1 step-6 noise comparison. -/
theorem quadratic_restricted_projected_period_input_coeff_row
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (i0 : Node)
    (P : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (noise : NoisePath Node ℝ) (k r : ℕ) :
    let Idx := Sum Node {i : Node // i ≠ i0}
    let step : ℕ → NodeMatrix Idx := fun t =>
      quadraticRestrictedOneStepMatrix (Node := Node)
        quad lambda alpha i0 t
    quadraticRestrictedPrimalAverageOutput (Node := Node) i0
        (matrixMulVector (Node := Idx) (P alpha)
          (matrixMulVector (Node := Idx)
            (consecutiveProduct (Node := Idx) step
              (k * quad.period + r + 1) (quad.period - 1 - r))
            (quadraticRestrictedNoiseInnovationCoord
              (Node := Node) quad alpha i0 noise (k * quad.period + r)))) =
      weightedState (Node := Node) (E := ℝ)
        (quadraticRestrictedProjectedPeriodInputCoeff
          (Node := Node) quad lambda alpha i0 P k r)
        (noise (k * quad.period + r)) := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  let step : ℕ → NodeMatrix Idx := fun t =>
    quadraticRestrictedOneStepMatrix (Node := Node)
      quad lambda alpha i0 t
  let B : NodeMatrix Idx :=
    consecutiveProduct (Node := Idx) step
      (k * quad.period + r + 1) (quad.period - 1 - r)
  let xi : RowVector Idx :=
    quadraticRestrictedNoiseInnovationCoord
      (Node := Node) quad alpha i0 noise (k * quad.period + r)
  let row0 : RowVector Idx :=
    quadraticRestrictedPrimalAverageRow (Node := Node) i0
  let rowP : RowVector Idx := rowMulMatrix (Node := Idx) row0 (P alpha)
  let rowPB : RowVector Idx := rowMulMatrix (Node := Idx) rowP B
  calc
    quadraticRestrictedPrimalAverageOutput (Node := Node) i0
        (matrixMulVector (Node := Idx) (P alpha)
          (matrixMulVector (Node := Idx) B xi)) =
      weightedState (Node := Idx) (E := ℝ) row0
        (matrixMulVector (Node := Idx) (P alpha)
          (matrixMulVector (Node := Idx) B xi)) := by
        rw [quadraticRestrictedPrimalAverageOutput_eq_weightedState]
    _ =
      weightedState (Node := Idx) (E := ℝ) rowP
        (matrixMulVector (Node := Idx) B xi) := by
        simpa [rowP, leftMul, matrixMulVector] using
          (weightedState_rowMulMatrix (Node := Idx) (E := ℝ)
            row0 (P alpha) (matrixMulVector (Node := Idx) B xi)).symm
    _ =
      weightedState (Node := Idx) (E := ℝ) rowPB xi := by
        simpa [rowPB, leftMul, matrixMulVector] using
          (weightedState_rowMulMatrix (Node := Idx) (E := ℝ)
            rowP B xi).symm
    _ =
      weightedState (Node := Node) (E := ℝ)
        (quadraticRestrictedProjectedPeriodInputCoeff
          (Node := Node) quad lambda alpha i0 P k r)
        (noise (k * quad.period + r)) := by
        simpa [Idx, step, B, xi, row0, rowP, rowPB,
          quadraticRestrictedProjectedPeriodInputCoeff] using
          weightedState_quadraticRestrictedNoiseInnovationCoord
            (Node := Node) quad alpha i0 noise (k * quad.period + r) rowPB

/-- Coefficient-row finite-sum unroll for the whole projected period input. -/
theorem quadratic_restricted_projected_period_input_coeff_row_unroll
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (i0 : Node)
    (P : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (noise : NoisePath Node ℝ) (k : ℕ) :
    quadraticRestrictedPrimalAverageOutput (Node := Node) i0
        (matrixMulVector (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
          (quadraticRestrictedPeriodNoiseInnovationCoord
            (Node := Node) quad lambda alpha i0 noise k)) =
      (Finset.range quad.period).sum fun r =>
        weightedState (Node := Node) (E := ℝ)
          (quadraticRestrictedProjectedPeriodInputCoeff
            (Node := Node) quad lambda alpha i0 P k r)
          (noise (k * quad.period + r)) := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  let step : ℕ → NodeMatrix Idx := fun t =>
    quadraticRestrictedOneStepMatrix (Node := Node)
      quad lambda alpha i0 t
  rw [quadratic_restricted_projected_period_input_output_unroll
    (Node := Node) quad lambda alpha i0 P noise k]
  apply Finset.sum_congr rfl
  intro r _hr
  simpa [Idx, step] using
    quadratic_restricted_projected_period_input_coeff_row
      (Node := Node) quad lambda alpha i0 P noise k r

/-- A single node-noise coefficient row is exactly the restricted coordinate
vector of the corresponding deterministic unit-noise injection. -/
theorem quadraticRestrictedNoiseInnovationCoeff_unit_coord
    [DecidableEq Node]
    (quad : Setup Node ℝ) (alpha : ℝ) (i0 : Node) (t : ℕ) (j : Node) :
    (fun a : Sum Node {i : Node // i ≠ i0} =>
        quadraticRestrictedNoiseInnovationCoeff
          (Node := Node) quad alpha i0 t a j) =
      restrictedStateToCoord (Node := Node) i0
        (fun i : Node => -alpha * if i = j then (1 : ℝ) else 0,
          quad.pullColumnInnovation t j) := by
  classical
  funext a
  cases a with
  | inl i =>
      simp [quadraticRestrictedNoiseInnovationCoeff, restrictedStateToCoord]
  | inr i =>
      simp [quadraticRestrictedNoiseInnovationCoeff, restrictedStateToCoord,
        pullColumnInnovation]

/-- Propagating the deterministic unit-noise coefficient row through a finite
restricted product gives the restricted coordinates of the propagated
homogeneous unit-noise orbit. -/
theorem quadraticRestrictedUnitNoiseCoeff_consecutiveProduct_eq_orbit_coord
    [DecidableEq Node]
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (i0 : Node)
    (t n : ℕ) (j : Node) :
    matrixMulVector
        (Node := Sum Node {i : Node // i ≠ i0})
        (consecutiveProduct (Node := Sum Node {i : Node // i ≠ i0})
          (fun s => quadraticRestrictedOneStepMatrix
            (Node := Node) quad lambda alpha i0 s) (t + 1) n)
        (fun a : Sum Node {i : Node // i ≠ i0} =>
          quadraticRestrictedNoiseInnovationCoeff
            (Node := Node) quad alpha i0 t a j) =
      restrictedStateToCoord (Node := Node) i0
        (quadraticRestrictedHomogeneousOrbit (Node := Node)
          quad lambda alpha (t + 1) n
          (fun i : Node => -alpha * if i = j then (1 : ℝ) else 0,
            quad.pullColumnInnovation t j)) := by
  classical
  let Snoise : State Node ℝ × ZeroSumState Node ℝ :=
    (fun i : Node => -alpha * if i = j then (1 : ℝ) else 0,
      quad.pullColumnInnovation t j)
  have hcoeff :
      (fun a : Sum Node {i : Node // i ≠ i0} =>
          quadraticRestrictedNoiseInnovationCoeff
            (Node := Node) quad alpha i0 t a j) =
        restrictedStateToCoord (Node := Node) i0 Snoise := by
    simpa [Snoise] using
      quadraticRestrictedNoiseInnovationCoeff_unit_coord
        (Node := Node) quad alpha i0 t j
  rw [hcoeff]
  simpa [Snoise] using
    quadraticRestrictedConsecutiveProduct_represents_orbit
      (Node := Node) quad lambda alpha i0 (t + 1) n Snoise

/-- Corrected-functional derivative for the exact block/phase unit-noise orbit
used by the projected period-input row.

This is the source Appendix C.1 coefficient derivative before the final
Riesz-projection transfer: the propagated deterministic phase-noise channel has
corrected slow functional derivative `-b_{kp+r}(j)` at the base point. -/
theorem quadraticRestrictedPeriodPhaseUnitNoise_correctedFunctional_hasDerivAt_zero
    [DecidableEq Node]
    (quad : Setup Node ℝ) (lambda : ℝ) (k r : ℕ) (j : Node) :
    HasDerivAt
      (fun alpha : ℝ =>
        let t : ℕ := quad.blockStart k + r
        let n : ℕ := quad.period - 1 - r
        let Snoise : State Node ℝ × ZeroSumState Node ℝ :=
          (fun i : Node => -alpha * if i = j then (1 : ℝ) else 0,
            quad.pullColumnInnovation t j)
        let Sout :=
          quadraticRestrictedHomogeneousOrbit (Node := Node)
            quad lambda alpha (t + 1) n Snoise
        weightedState (Node := Node) (E := ℝ) (quad.perronLeft (t + 1 + n))
            Sout.1 -
          alpha * quad.correctedLift (t + 1 + n) Sout.2)
      (-(quad.influence (quad.blockStart k + r) j)) 0 := by
  classical
  simpa using
    quadraticRestrictedUnitNoise_correctedFunctional_propagated_hasDerivAt
      (Node := Node) quad lambda (quad.blockStart k + r)
      (quad.period - 1 - r) j

/-- Projected period-input phase coefficient as the moving projected average
row paired with the propagated deterministic unit-noise orbit.

This closes the coordinate side of the Riesz/corrected-functional transfer:
the remaining source leaf is now exactly the first-order identification of
`rowAvg * P(alpha)` on this orbit with the corrected slow functional. -/
theorem quadraticRestrictedProjectedPeriodInputCoeff_eq_projected_orbit_pairing
    [DecidableEq Node]
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (i0 : Node)
    (P : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (k r : ℕ) (j : Node) :
    quadraticRestrictedProjectedPeriodInputCoeff
        (Node := Node) quad lambda alpha i0 P k r j =
      weightedState (Node := Sum Node {i : Node // i ≠ i0}) (E := ℝ)
        (rowMulMatrix (Node := Sum Node {i : Node // i ≠ i0})
          (quadraticRestrictedPrimalAverageRow (Node := Node) i0) (P alpha))
        (restrictedStateToCoord (Node := Node) i0
          (quadraticRestrictedHomogeneousOrbit (Node := Node)
            quad lambda alpha (k * quad.period + r + 1)
            (quad.period - 1 - r)
            (fun i : Node => -alpha * if i = j then (1 : ℝ) else 0,
              quad.pullColumnInnovation (k * quad.period + r) j))) := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  let step : ℕ → NodeMatrix Idx := fun t =>
    quadraticRestrictedOneStepMatrix (Node := Node)
      quad lambda alpha i0 t
  let B : NodeMatrix Idx :=
    consecutiveProduct (Node := Idx) step
      (k * quad.period + r + 1) (quad.period - 1 - r)
  let coeff : RowVector Idx := fun a : Idx =>
    quadraticRestrictedNoiseInnovationCoeff
      (Node := Node) quad alpha i0 (k * quad.period + r) a j
  let rowP : RowVector Idx :=
    rowMulMatrix (Node := Idx)
      (quadraticRestrictedPrimalAverageRow (Node := Node) i0) (P alpha)
  have horbit :
      matrixMulVector (Node := Idx) B coeff =
        restrictedStateToCoord (Node := Node) i0
          (quadraticRestrictedHomogeneousOrbit (Node := Node)
            quad lambda alpha (k * quad.period + r + 1)
            (quad.period - 1 - r)
            (fun i : Node => -alpha * if i = j then (1 : ℝ) else 0,
              quad.pullColumnInnovation (k * quad.period + r) j)) := by
    simpa [Idx, step, B, coeff] using
      quadraticRestrictedUnitNoiseCoeff_consecutiveProduct_eq_orbit_coord
        (Node := Node) quad lambda alpha i0 (k * quad.period + r)
        (quad.period - 1 - r) j
  have hpair :
      weightedState (Node := Idx) (E := ℝ)
          (rowMulMatrix (Node := Idx) rowP B) coeff =
        weightedState (Node := Idx) (E := ℝ) rowP
          (matrixMulVector (Node := Idx) B coeff) := by
    simpa [leftMul, matrixMulVector] using
      (weightedState_rowMulMatrix (Node := Idx) (E := ℝ) rowP B coeff)
  calc
    quadraticRestrictedProjectedPeriodInputCoeff
        (Node := Node) quad lambda alpha i0 P k r j =
      weightedState (Node := Idx) (E := ℝ)
        (rowMulMatrix (Node := Idx) rowP B) coeff := by
        simp [quadraticRestrictedProjectedPeriodInputCoeff, Idx, step, B,
          coeff, rowP, weightedState, smul_eq_mul]
    _ =
      weightedState (Node := Idx) (E := ℝ) rowP
        (matrixMulVector (Node := Idx) B coeff) := hpair
    _ =
      weightedState (Node := Idx) (E := ℝ) rowP
        (restrictedStateToCoord (Node := Node) i0
          (quadraticRestrictedHomogeneousOrbit (Node := Node)
            quad lambda alpha (k * quad.period + r + 1)
            (quad.period - 1 - r)
            (fun i : Node => -alpha * if i = j then (1 : ℝ) else 0,
              quad.pullColumnInnovation (k * quad.period + r) j))) := by
        rw [horbit]

theorem weightedState_row_sub_hasDerivAt_zero_of_continuousAt
    (row : ℝ → RowVector Node) (rowDeriv : RowVector Node)
    (z : ℝ → RowVector Node)
    (hrow : HasDerivAt row rowDeriv 0)
    (hz : ContinuousAt z 0) :
    HasDerivAt
      (fun alpha : ℝ =>
        weightedState (Node := Node) (E := ℝ)
          (fun i : Node => row alpha i - row 0 i) (z alpha))
      (weightedState (Node := Node) (E := ℝ) rowDeriv (z 0)) 0 := by
  classical
  unfold weightedState
  apply HasDerivAt.fun_sum
  intro i _hi
  have hrow_i :
      HasDerivAt (fun alpha : ℝ => row alpha i) (rowDeriv i) 0 := by
    have hi :=
      (hasFDerivAt_apply (𝕜 := ℝ) i (row 0)).comp 0 hrow.hasFDerivAt
    convert hi.hasDerivAt using 1 <;>
      simp [Function.comp_def, ContinuousLinearMap.one_apply]
  have hrow_sub_i :
      HasDerivAt (fun alpha : ℝ => row alpha i - row 0 i)
        (rowDeriv i) 0 := by
    simpa using hrow_i.sub_const (row 0 i)
  have hrow_sub_zero_i :
      row 0 i - row 0 i = 0 := by ring
  have hz_i : ContinuousAt (fun alpha : ℝ => z alpha i) 0 :=
    (continuous_apply i).continuousAt.comp hz
  simpa [smul_eq_mul] using
    hasDerivAt_mul_of_hasDerivAt_zero_left_continuousAt
      hrow_sub_i hrow_sub_zero_i hz_i

/-- Calculus transfer for Appendix C.1's projected-row/corrected-functional
first variation.

After the alpha-zero projected row has been identified with the endpoint
Perron functional, the only remaining non-calculus input is the value of the
spectral row derivative on the alpha-zero tracker orbit.  This helper turns
that value into the exact `hfirst` premise required by the coefficient
derivative transfer. -/
theorem quadraticRestrictedProjectedCorrected_firstVariation_of_rowDeriv_value
    [DecidableEq Node]
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (P : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (rowDeriv : RowVector (Sum Node {i : Node // i ≠ i0}))
    (k r : ℕ) (j : Node) (hr : r < quad.period)
    (hrow :
      HasDerivAt
        (fun alpha : ℝ =>
          rowMulMatrix (Node := Sum Node {i : Node // i ≠ i0})
            (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
            (P alpha))
        rowDeriv 0)
    (hrow0_endpoint :
      ∀ S : State Node ℝ × ZeroSumState Node ℝ,
        weightedState (Node := Sum Node {i : Node // i ≠ i0}) (E := ℝ)
            (rowMulMatrix (Node := Sum Node {i : Node // i ≠ i0})
              (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
              (P 0))
            (restrictedStateToCoord (Node := Node) i0 S) =
          weightedState (Node := Node) (E := ℝ)
            (quad.perronLeft (quad.blockStart (k + 1))) S.1)
    (hrowDeriv_value :
      let t : ℕ := quad.blockStart k + r
      let n : ℕ := quad.period - 1 - r
      let Snoise0 : State Node ℝ × ZeroSumState Node ℝ :=
        (fun _ : Node => 0, quad.pullColumnInnovation t j)
      let Sout0 :=
        quadraticRestrictedHomogeneousOrbit (Node := Node)
          quad lambda 0 (t + 1) n Snoise0
      weightedState (Node := Sum Node {i : Node // i ≠ i0}) (E := ℝ)
          rowDeriv (restrictedStateToCoord (Node := Node) i0 Sout0) +
        quad.correctedLift (t + 1 + n) Sout0.2 = 0) :
    HasDerivAt
      (fun alpha : ℝ =>
        weightedState (Node := Sum Node {i : Node // i ≠ i0}) (E := ℝ)
          (rowMulMatrix (Node := Sum Node {i : Node // i ≠ i0})
            (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
            (P alpha))
          (restrictedStateToCoord (Node := Node) i0
            (quadraticRestrictedHomogeneousOrbit (Node := Node)
              quad lambda alpha (k * quad.period + r + 1)
              (quad.period - 1 - r)
              (fun i : Node => -alpha * if i = j then (1 : ℝ) else 0,
                quad.pullColumnInnovation (k * quad.period + r) j))) -
          (let t : ℕ := quad.blockStart k + r
           let n : ℕ := quad.period - 1 - r
           let Snoise : State Node ℝ × ZeroSumState Node ℝ :=
            (fun i : Node => -alpha * if i = j then (1 : ℝ) else 0,
              quad.pullColumnInnovation t j)
           let Sout :=
            quadraticRestrictedHomogeneousOrbit (Node := Node)
              quad lambda alpha (t + 1) n Snoise
           weightedState (Node := Node) (E := ℝ)
              (quad.perronLeft (t + 1 + n)) Sout.1 -
            alpha * quad.correctedLift (t + 1 + n) Sout.2))
      0 0 := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  let t : ℕ := quad.blockStart k + r
  let n : ℕ := quad.period - 1 - r
  let row : ℝ → RowVector Idx := fun alpha =>
    rowMulMatrix (Node := Idx)
      (quadraticRestrictedPrimalAverageRow (Node := Node) i0) (P alpha)
  let Snoise : ℝ → State Node ℝ × ZeroSumState Node ℝ := fun alpha =>
    (fun i : Node => -alpha * if i = j then (1 : ℝ) else 0,
      quad.pullColumnInnovation t j)
  let Sout : ℝ → State Node ℝ × ZeroSumState Node ℝ := fun alpha =>
    quadraticRestrictedHomogeneousOrbit (Node := Node)
      quad lambda alpha (t + 1) n (Snoise alpha)
  let z : ℝ → RowVector Idx := fun alpha =>
    restrictedStateToCoord (Node := Node) i0 (Sout alpha)
  let corr : ℝ → ℝ := fun alpha =>
    quad.correctedLift (t + 1 + n) (Sout alpha).2
  have ht_eq : t = k * quad.period + r := by
    simp [t, Setup.blockStart]
  have hstart_eq : t + 1 = k * quad.period + r + 1 := by
    rw [ht_eq]
  have hendpoint_time : t + 1 + n = quad.blockStart (k + 1) := by
    have hr_succ : r + 1 ≤ quad.period := Nat.succ_le_of_lt hr
    have hn_alt : n = quad.period - (r + 1) := by
      dsimp [n]
      rw [Nat.sub_sub, Nat.add_comm]
    have hcancel : r + 1 + n = quad.period := by
      rw [hn_alt]
      exact Nat.add_sub_of_le hr_succ
    calc
      t + 1 + n = k * quad.period + r + 1 + n := by rw [ht_eq]
      _ = k * quad.period + (r + 1 + n) := by omega
      _ = k * quad.period + quad.period := by rw [hcancel]
      _ = (k + 1) * quad.period := by
        exact (Nat.succ_mul k quad.period).symm
      _ = quad.blockStart (k + 1) := by rfl
  have hSnoise_cont : Continuous Snoise := by
    have htop : Continuous (fun alpha : ℝ =>
        fun i : Node => -alpha * if i = j then (1 : ℝ) else 0) := by
      apply continuous_pi
      intro i
      exact continuous_id.neg.mul
        (continuous_const : Continuous
          (fun _alpha : ℝ => if i = j then (1 : ℝ) else 0))
    exact htop.prodMk continuous_const
  have hSout_cont : Continuous Sout := by
    simpa [Sout] using
      quadraticRestrictedHomogeneousOrbit_continuous_alpha_of_continuous_initial
        (Node := Node) quad lambda (t + 1) n Snoise hSnoise_cont
  have hz_cont : ContinuousAt z 0 := by
    have hz_global : Continuous z := by
      apply continuous_pi
      intro a
      cases a with
      | inl i =>
          exact (continuous_apply i).comp hSout_cont.fst
      | inr i =>
          exact (continuous_apply i.1).comp
            (continuous_subtype_val.comp hSout_cont.snd)
    exact hz_global.continuousAt
  have hcorr_cont : ContinuousAt corr 0 := by
    obtain ⟨Kcorr, hcorr⟩ :=
      quad.correctedLift_exists_lipschitz (t + 1 + n)
    exact (hcorr.continuous.comp hSout_cont.snd).continuousAt
  have hrow' : HasDerivAt row rowDeriv 0 := by
    simpa [row, Idx] using hrow
  have hrow_sub :
      HasDerivAt
        (fun alpha : ℝ =>
          weightedState (Node := Idx) (E := ℝ)
            (fun a : Idx => row alpha a - row 0 a) (z alpha))
        (weightedState (Node := Idx) (E := ℝ) rowDeriv (z 0)) 0 :=
    weightedState_row_sub_hasDerivAt_zero_of_continuousAt
      (Node := Idx) row rowDeriv z hrow' hz_cont
  have hcorr_term :
      HasDerivAt (fun alpha : ℝ => alpha * corr alpha) (corr 0) 0 :=
    hasDerivAt_id_mul_of_continuousAt_zero corr hcorr_cont
  have hsum :
      HasDerivAt
        (fun alpha : ℝ =>
          weightedState (Node := Idx) (E := ℝ)
            (fun a : Idx => row alpha a - row 0 a) (z alpha) +
            alpha * corr alpha)
        (weightedState (Node := Idx) (E := ℝ) rowDeriv (z 0) + corr 0) 0 :=
    hrow_sub.add hcorr_term
  have hSnoise0 :
      Snoise 0 =
        (fun _ : Node => 0, quad.pullColumnInnovation t j) := by
    ext i <;> simp [Snoise]
  have hderiv_zero :
      weightedState (Node := Idx) (E := ℝ) rowDeriv (z 0) + corr 0 = 0 := by
    simpa [z, corr, Sout, hSnoise0, t, n, Idx] using hrowDeriv_value
  have hsum_zero :
      HasDerivAt
        (fun alpha : ℝ =>
          weightedState (Node := Idx) (E := ℝ)
            (fun a : Idx => row alpha a - row 0 a) (z alpha) +
            alpha * corr alpha)
        0 0 := by
    simpa [hderiv_zero] using hsum
  convert hsum_zero using 1
  · funext alpha
    dsimp [row, z, corr, Sout, Snoise, t, n, Idx]
    rw [← hstart_eq]
    have hendpoint :
        weightedState (Node := Idx) (E := ℝ)
            (rowMulMatrix (Node := Idx)
              (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
              (P 0))
            (restrictedStateToCoord (Node := Node) i0
              (quadraticRestrictedHomogeneousOrbit (Node := Node)
                quad lambda alpha (t + 1) n
                (fun i : Node => -alpha *
                  if i = j then (1 : ℝ) else 0,
                  quad.pullColumnInnovation t j))) =
          weightedState (Node := Node) (E := ℝ)
            (quad.perronLeft (t + 1 + n))
            (quadraticRestrictedHomogeneousOrbit (Node := Node)
                quad lambda alpha (t + 1) n
                (fun i : Node => -alpha *
                  if i = j then (1 : ℝ) else 0,
                  quad.pullColumnInnovation t j)).1 := by
      have hper :
          quad.perronLeft (quad.blockStart (k + 1)) =
            quad.perronLeft (t + 1 + n) := by
        rw [hendpoint_time]
      rw [← hper]
      exact hrow0_endpoint
        (quadraticRestrictedHomogeneousOrbit (Node := Node)
          quad lambda alpha (t + 1) n
          (fun i : Node => -alpha * if i = j then (1 : ℝ) else 0,
            quad.pullColumnInnovation t j))
    rw [← hendpoint]
    unfold weightedState
    simp only [smul_eq_mul, t, n, Setup.blockStart]
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    ring

/-- Transfer from the source spectral-left first variation to the projected
phase-noise coefficient derivative.

The only non-calculus input is the first-order Riesz-row identification:
on the propagated phase-noise orbit, the difference between the moving
projected average row and the corrected slow functional has zero derivative at
the source expansion point.  The corrected-functional derivative and the
projected-orbit pairing then give the coefficient derivative required by
Appendix C.1. -/
theorem quadraticRestrictedProjectedPeriodInputCoeff_hasDerivAt_zero_of_projected_corrected_firstVariation
    [DecidableEq Node]
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (P : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (k r : ℕ) (j : Node)
    (hfirst :
      HasDerivAt
        (fun alpha : ℝ =>
          weightedState (Node := Sum Node {i : Node // i ≠ i0}) (E := ℝ)
            (rowMulMatrix (Node := Sum Node {i : Node // i ≠ i0})
              (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
              (P alpha))
            (restrictedStateToCoord (Node := Node) i0
              (quadraticRestrictedHomogeneousOrbit (Node := Node)
                quad lambda alpha (k * quad.period + r + 1)
                (quad.period - 1 - r)
                (fun i : Node => -alpha * if i = j then (1 : ℝ) else 0,
                  quad.pullColumnInnovation (k * quad.period + r) j))) -
            (let t : ℕ := quad.blockStart k + r
             let n : ℕ := quad.period - 1 - r
             let Snoise : State Node ℝ × ZeroSumState Node ℝ :=
              (fun i : Node => -alpha * if i = j then (1 : ℝ) else 0,
                quad.pullColumnInnovation t j)
             let Sout :=
              quadraticRestrictedHomogeneousOrbit (Node := Node)
                quad lambda alpha (t + 1) n Snoise
             weightedState (Node := Node) (E := ℝ)
                (quad.perronLeft (t + 1 + n)) Sout.1 -
              alpha * quad.correctedLift (t + 1 + n) Sout.2))
        0 0) :
    HasDerivAt
      (fun alpha : ℝ =>
        quadraticRestrictedProjectedPeriodInputCoeff
          (Node := Node) quad lambda alpha i0 P k r j)
      (-(quad.influence (quad.blockStart k + r) j)) 0 := by
  classical
  let paired : ℝ → ℝ := fun alpha =>
    weightedState (Node := Sum Node {i : Node // i ≠ i0}) (E := ℝ)
      (rowMulMatrix (Node := Sum Node {i : Node // i ≠ i0})
        (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
        (P alpha))
      (restrictedStateToCoord (Node := Node) i0
        (quadraticRestrictedHomogeneousOrbit (Node := Node)
          quad lambda alpha (k * quad.period + r + 1)
          (quad.period - 1 - r)
          (fun i : Node => -alpha * if i = j then (1 : ℝ) else 0,
            quad.pullColumnInnovation (k * quad.period + r) j)))
  let corrected : ℝ → ℝ := fun alpha =>
    let t : ℕ := quad.blockStart k + r
    let n : ℕ := quad.period - 1 - r
    let Snoise : State Node ℝ × ZeroSumState Node ℝ :=
      (fun i : Node => -alpha * if i = j then (1 : ℝ) else 0,
        quad.pullColumnInnovation t j)
    let Sout :=
      quadraticRestrictedHomogeneousOrbit (Node := Node)
        quad lambda alpha (t + 1) n Snoise
    weightedState (Node := Node) (E := ℝ)
        (quad.perronLeft (t + 1 + n)) Sout.1 -
      alpha * quad.correctedLift (t + 1 + n) Sout.2
  have hfirst' :
      HasDerivAt (fun alpha : ℝ => paired alpha - corrected alpha) 0 0 := by
    simpa [paired, corrected] using hfirst
  have hcorrected :
      HasDerivAt corrected (-(quad.influence (quad.blockStart k + r) j)) 0 := by
    simpa [corrected] using
      quadraticRestrictedPeriodPhaseUnitNoise_correctedFunctional_hasDerivAt_zero
        (Node := Node) quad lambda k r j
  have hpaired :
      HasDerivAt paired (-(quad.influence (quad.blockStart k + r) j)) 0 := by
    have hsum := hfirst'.add hcorrected
    convert hsum using 1
    · funext alpha
      dsimp [paired, corrected]
      ring
    · ring
  convert hpaired using 1
  funext alpha
  simpa [paired] using
    (quadraticRestrictedProjectedPeriodInputCoeff_eq_projected_orbit_pairing
      (Node := Node) quad lambda alpha i0 P k r j)

/-- Source-derived projected phase-noise coefficient derivative for Appendix
C.1.

This packages the complete first-variation route rather than exposing the
intermediate `hfirst` premise: the spectral splitting supplies the derivative
of the projected average row, the alpha-zero rank-one row identifies the
endpoint Perron functional, and the corrected-lift invariant evaluates the
row derivative on the phase-noise tracker orbit. -/
theorem quadraticRestrictedProjectedPeriodInputCoeff_hasDerivAt_zero
    [DecidableEq Node]
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (r0 alpha0 theta K : ℝ)
    (right left : RowVector (Sum Node {i : Node // i ≠ i0}))
    (gamma : ℝ → ℝ)
    (P F : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (hsplitting :
      PeriodicSpectralSplitting
        (Node := Sum Node {i : Node // i ≠ i0})
        (fun alpha : ℝ =>
          quadraticRestrictedPeriodMatrix (Node := Node)
            quad lambda alpha i0)
        r0 alpha0 theta K right left gamma P F)
    (hP0 :
      P 0 = (fun i j : Sum Node {i : Node // i ≠ i0} => right i * left j))
    (hright_top : ∀ i : Node, right (Sum.inl i) = 1)
    (hleft_top : ∀ i : Node, left (Sum.inl i) = quad.perronLeft 0 i)
    (hleft_bottom : ∀ j : {i : Node // i ≠ i0}, left (Sum.inr j) = 0)
    (k r : ℕ) (hr : r < quad.period) (j : Node) :
    HasDerivAt
      (fun alpha : ℝ =>
        quadraticRestrictedProjectedPeriodInputCoeff
          (Node := Node) quad lambda alpha i0 P k r j)
      (-(quad.influence (quad.blockStart k + r) j)) 0 := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  have hrestricted_splitting_at :
      ∀ alpha : ℝ, |alpha| ≤ alpha0 →
        IsRieszProjectionAtEigenvalue
            (Node := Idx)
            (quadraticRestrictedPeriodMatrix (Node := Node)
              quad lambda alpha i0)
            (gamma alpha) (P alpha) ∧
          quadraticRestrictedPeriodMatrix (Node := Node)
              quad lambda alpha i0 =
            matrixAdd (Node := Idx)
              ((gamma alpha) • P alpha) (F alpha) ∧
            matrixMul (Node := Idx) (P alpha) (F alpha) = 0 ∧
              matrixMul (Node := Idx) (F alpha) (P alpha) = 0 ∧
                ∀ j : ℕ,
                  matrixEuclideanOperatorNorm (Node := Idx)
                      (matrixPower (Node := Idx) (F alpha) j) ≤
                    K * theta ^ j := by
    intro alpha halpha
    exact hsplitting.2.2.2.2.2.2.2.2 alpha halpha
  have hprojected_average_row_left_eigen :
      ∀ alpha : ℝ, |alpha| ≤ alpha0 →
        rowMulMatrix
            (Node := Idx)
            (rowMulMatrix
              (Node := Idx)
              (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
              (P alpha))
            (quadraticRestrictedPeriodMatrix (Node := Node)
              quad lambda alpha i0) =
          gamma alpha •
            rowMulMatrix
              (Node := Idx)
              (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
              (P alpha) := by
    intro alpha halpha_abs
    exact
      quadraticRestrictedPrimalAverageProjectedRow_left_eigen
        (Node := Node) i0 (gamma alpha)
        (quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda alpha i0)
        (P alpha)
        (hrestricted_splitting_at alpha halpha_abs).1
  have hprojected_average_row_left_eigen_eventually :
      ∀ᶠ alpha : ℝ in 𝓝 0,
        rowMulMatrix
            (Node := Idx)
            (rowMulMatrix
              (Node := Idx)
              (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
              (P alpha))
            (quadraticRestrictedPeriodMatrix (Node := Node)
              quad lambda alpha i0) =
          gamma alpha •
            rowMulMatrix
              (Node := Idx)
              (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
              (P alpha) := by
    have halpha0_pos : 0 < alpha0 := hsplitting.1
    have hsmall :
        ∀ᶠ alpha : ℝ in 𝓝 0, |alpha| ≤ alpha0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) halpha0_pos]
        with alpha hdist
      have hlt : |alpha| < alpha0 := by
        simpa [Real.dist_eq] using hdist
      exact le_of_lt hlt
    filter_upwards [hsmall] with alpha halpha
    exact hprojected_average_row_left_eigen alpha halpha
  have hprojected_average_row_alpha_zero_endpoint_perron :
      ∀ k : ℕ, ∀ S : State Node ℝ × ZeroSumState Node ℝ,
        weightedState (Node := Idx) (E := ℝ)
            (rowMulMatrix (Node := Idx)
              (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
              (P 0))
            (restrictedStateToCoord (Node := Node) i0 S) =
          weightedState (Node := Node) (E := ℝ)
            (quad.perronLeft (quad.blockStart (k + 1))) S.1 := by
    intro k S
    exact
      quadraticRestrictedPrimalAverageProjectedRow_alpha_zero_weighted_eq_endpoint_perron
        (Node := Node) quad i0 right left P hP0 hright_top hleft_top
        hleft_bottom k S
  have hprojected_average_row_hasDerivAt_zero :
      ∃ rowDeriv : RowVector Idx,
        HasDerivAt
          (fun alpha : ℝ =>
            rowMulMatrix (Node := Idx)
              (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
              (P alpha))
          rowDeriv 0 := by
    exact
      quadraticRestrictedPrimalAverageProjectedRow_hasDerivAt_zero
        (Node := Node) i0 r0 alpha0 theta K right left gamma
        (fun alpha : ℝ =>
          quadraticRestrictedPeriodMatrix (Node := Node)
            quad lambda alpha i0)
        P F hsplitting
  have hrestricted_all_lengths_stable_blocks :
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
    exact quadratic_restricted_all_lengths_stable_blocks (Node := Node) quad
  have hprojected_rowDeriv_correctedLift_tracker_period_invariant :
      ∀ rowDeriv : RowVector Idx,
        HasDerivAt
          (fun alpha : ℝ =>
            rowMulMatrix (Node := Idx)
              (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
              (P alpha))
          rowDeriv 0 →
        ∀ Aderiv : NodeMatrix Idx,
          HasDerivAt
            (fun alpha : ℝ =>
              quadraticRestrictedPeriodMatrix (Node := Node)
                quad lambda alpha i0)
            Aderiv 0 →
        ∀ gammaDeriv : ℝ,
          HasDerivAt gamma gammaDeriv 0 →
        ∀ W : ZeroSumState Node ℝ,
          let Wnext : ZeroSumState Node ℝ :=
            (quadraticRestrictedHomogeneousOrbit (Node := Node)
              quad lambda 0 0 quad.period
              ((fun _ : Node => (0 : ℝ)), W)).2
          weightedState
              (Node := Idx) (E := ℝ)
              rowDeriv
              (restrictedStateToCoord (Node := Node) i0
                ((fun _ : Node => (0 : ℝ)), Wnext)) +
            quad.correctedLift 0 Wnext =
              weightedState
                (Node := Idx) (E := ℝ)
                rowDeriv
                (restrictedStateToCoord (Node := Node) i0
                  ((fun _ : Node => (0 : ℝ)), W)) +
              quad.correctedLift 0 W := by
    intro rowDeriv hrow Aderiv hAderiv gammaDeriv hgammaDeriv W
    have hgamma0 : gamma 0 = 1 := hsplitting.2.2.2.2.1
    have hrow0_eq_left :
        rowMulMatrix
            (Node := Idx)
            (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
            (P 0) =
          left := by
      simpa [Idx] using
        quadraticRestrictedPrimalAverageRow_mul_rankOneProjection_eq_left
          (Node := Node) i0 right left P hP0 hright_top
    exact
      quadraticRestrictedProjectedRowDeriv_correctedLift_tracker_period_invariant
        (Node := Node) quad lambda i0 left P gamma Aderiv gammaDeriv
        rowDeriv hleft_top hleft_bottom hrow hAderiv hgammaDeriv hgamma0
        hprojected_average_row_left_eigen_eventually hrow0_eq_left W
  have hprojected_rowDeriv_correctedLift_tracker_zero :
      ∀ rowDeriv : RowVector Idx,
        HasDerivAt
          (fun alpha : ℝ =>
            rowMulMatrix (Node := Idx)
              (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
              (P alpha))
          rowDeriv 0 →
        ∀ W : ZeroSumState Node ℝ,
          weightedState
              (Node := Idx) (E := ℝ)
              rowDeriv
              (restrictedStateToCoord (Node := Node) i0
                ((fun _ : Node => (0 : ℝ)), W)) +
            quad.correctedLift 0 W = 0 := by
    intro rowDeriv hrow W
    rcases hsplitting.2.2.2.2.2.2.2.1 with
      ⟨Aderiv, hAderiv, hgammaDeriv⟩
    exact
      quadraticRestrictedTrackerInvariantFunctional_eq_zero
        (Node := Node) quad lambda i0 rowDeriv
        hrestricted_all_lengths_stable_blocks
        (hprojected_rowDeriv_correctedLift_tracker_period_invariant
          rowDeriv hrow Aderiv hAderiv
          (rowDot (Node := Idx) left
            (matrixMulVector (Node := Idx) Aderiv right))
          hgammaDeriv)
        W
  have hprojected_rowDeriv_value_zero :
      ∀ rowDeriv : RowVector Idx,
        HasDerivAt
          (fun alpha : ℝ =>
            rowMulMatrix (Node := Idx)
              (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
              (P alpha))
          rowDeriv 0 →
        ∀ k r : ℕ, r < quad.period → ∀ j : Node,
          let t : ℕ := quad.blockStart k + r
          let n : ℕ := quad.period - 1 - r
          let Snoise0 : State Node ℝ × ZeroSumState Node ℝ :=
            (fun _ : Node => 0, quad.pullColumnInnovation t j)
          let Sout0 :=
            quadraticRestrictedHomogeneousOrbit (Node := Node)
              quad lambda 0 (t + 1) n Snoise0
          weightedState
              (Node := Idx) (E := ℝ)
              rowDeriv (restrictedStateToCoord (Node := Node) i0 Sout0) +
            quad.correctedLift (t + 1 + n) Sout0.2 = 0 := by
    intro rowDeriv hrow k r hr j
    let t : ℕ := quad.blockStart k + r
    let n : ℕ := quad.period - 1 - r
    let Snoise0 : State Node ℝ × ZeroSumState Node ℝ :=
      (fun _ : Node => 0, quad.pullColumnInnovation t j)
    let Sout0 : State Node ℝ × ZeroSumState Node ℝ :=
      quadraticRestrictedHomogeneousOrbit (Node := Node)
        quad lambda 0 (t + 1) n Snoise0
    have hSout_top : Sout0.1 = fun _ : Node => (0 : ℝ) := by
      have horbit :=
        quadraticRestrictedHomogeneousOrbit_alpha_zero_tracker_only
          (Node := Node) quad lambda (t + 1) n
          (quad.pullColumnInnovation t j)
      simpa [Sout0, Snoise0] using congrArg Prod.fst horbit
    have hSout_eq : Sout0 = ((fun _ : Node => (0 : ℝ)), Sout0.2) := by
      exact Prod.ext hSout_top rfl
    have ht_eq : t = k * quad.period + r := by
      simp [t, Setup.blockStart]
    have hendpoint_time : t + 1 + n = quad.blockStart (k + 1) := by
      have hr_succ : r + 1 ≤ quad.period := Nat.succ_le_of_lt hr
      have hn_alt : n = quad.period - (r + 1) := by
        dsimp [n]
        rw [Nat.sub_sub, Nat.add_comm]
      have hcancel : r + 1 + n = quad.period := by
        rw [hn_alt]
        exact Nat.add_sub_of_le hr_succ
      calc
        t + 1 + n = k * quad.period + r + 1 + n := by rw [ht_eq]
        _ = k * quad.period + (r + 1 + n) := by omega
        _ = k * quad.period + quad.period := by rw [hcancel]
        _ = (k + 1) * quad.period := by
          exact (Nat.succ_mul k quad.period).symm
        _ = quad.blockStart (k + 1) := by rfl
    have hzero :=
      hprojected_rowDeriv_correctedLift_tracker_zero rowDeriv hrow Sout0.2
    have hcorr_time :
        quad.correctedLift (t + 1 + n) Sout0.2 =
          quad.correctedLift 0 Sout0.2 := by
      rw [hendpoint_time]
      simpa [Setup.blockStart] using
        quad.correctedLift_blockStart (k + 1) Sout0.2
    change
      weightedState
          (Node := Idx) (E := ℝ)
          rowDeriv (restrictedStateToCoord (Node := Node) i0 Sout0) +
        quad.correctedLift (t + 1 + n) Sout0.2 = 0
    rw [hSout_eq, hcorr_time]
    exact hzero
  have hprojected_corrected_firstVariation :
      HasDerivAt
        (fun alpha : ℝ =>
          weightedState
            (Node := Idx) (E := ℝ)
            (rowMulMatrix (Node := Idx)
              (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
              (P alpha))
            (restrictedStateToCoord (Node := Node) i0
              (quadraticRestrictedHomogeneousOrbit (Node := Node)
                quad lambda alpha (k * quad.period + r + 1)
                (quad.period - 1 - r)
                (fun i : Node =>
                  -alpha * if i = j then (1 : ℝ) else 0,
                  quad.pullColumnInnovation
                    (k * quad.period + r) j))) -
            (let t : ℕ := quad.blockStart k + r
             let n : ℕ := quad.period - 1 - r
             let Snoise : State Node ℝ × ZeroSumState Node ℝ :=
              (fun i : Node => -alpha * if i = j then (1 : ℝ) else 0,
                quad.pullColumnInnovation t j)
             let Sout :=
              quadraticRestrictedHomogeneousOrbit (Node := Node)
                quad lambda alpha (t + 1) n Snoise
             weightedState (Node := Node) (E := ℝ)
                (quad.perronLeft (t + 1 + n)) Sout.1 -
              alpha * quad.correctedLift (t + 1 + n) Sout.2))
        0 0 := by
    rcases hprojected_average_row_hasDerivAt_zero with ⟨rowDeriv, hrow⟩
    exact
      quadraticRestrictedProjectedCorrected_firstVariation_of_rowDeriv_value
        (Node := Node) quad lambda i0 P rowDeriv k r j hr hrow
        (fun S => hprojected_average_row_alpha_zero_endpoint_perron k S)
        (hprojected_rowDeriv_value_zero rowDeriv hrow k r hr j)
  exact
    quadraticRestrictedProjectedPeriodInputCoeff_hasDerivAt_zero_of_projected_corrected_firstVariation
      (Node := Node) quad lambda i0 P k r j
      hprojected_corrected_firstVariation

/-- The projected period-input coefficient row is analytic at the source
expansion point.  This is the analytic half of the Appendix C.1 row matching;
the remaining hard source leaf is identifying its first derivative with the
scalar phase-noise coefficient. -/
theorem quadraticRestrictedProjectedPeriodInputCoeff_analyticAt_zero
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
    (k r : ℕ) (j : Node) :
    AnalyticAt ℝ
      (fun alpha : ℝ =>
        quadraticRestrictedProjectedPeriodInputCoeff
          (Node := Node) quad lambda alpha i0 P k r j) 0 := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  rcases hsplitting with
    ⟨halpha0_pos, _hr0theta, _htheta_lt_one, _hK_nonneg, _hgamma0,
      _hgamma_analytic, hP_analytic, _hderiv, _hlocal⟩
  have hP0_analytic : AnalyticAt ℝ P 0 := by
    exact hP_analytic 0 (by simpa using halpha0_pos)
  have hB_analytic :
      AnalyticAt ℝ
        (fun alpha : ℝ =>
          consecutiveProduct (Node := Idx)
            (fun t => quadraticRestrictedOneStepMatrix
              (Node := Node) quad lambda alpha i0 t)
            (k * quad.period + r + 1) (quad.period - 1 - r)) 0 := by
    simpa [Idx] using
      quadraticRestrictedConsecutiveProduct_analyticAt_start
        (Node := Node) quad lambda i0 0 (k * quad.period + r + 1)
        (quad.period - 1 - r)
  unfold quadraticRestrictedProjectedPeriodInputCoeff
  apply Finset.analyticAt_fun_sum
  intro a _ha
  apply AnalyticAt.mul
  · unfold rowMulMatrix
    apply Finset.analyticAt_fun_sum
    intro b _hb
    apply AnalyticAt.mul
    · apply Finset.analyticAt_fun_sum
      intro c _hc
      have hPcb :
          AnalyticAt ℝ (fun alpha : ℝ => P alpha c b) 0 :=
        analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hP0_analytic c) b
      exact analyticAt_const.mul hPcb
    · exact analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hB_analytic b) a
  · exact
      quadraticRestrictedNoiseInnovationCoeff_analyticAt
        (Node := Node) quad i0 (k * quad.period + r) a j 0

/-- Each projected phase-input coefficient vanishes at `alpha = 0`.

At zero stepsize the one-step noise channel has no primal component, and the
alpha-zero restricted homogeneous product cannot transport tracker coordinates
back into primal coordinates.  Since `P(0)` has zero bottom row against the
source-normalized left vector, the average of a single propagated phase input is
zero before the first-order coefficient is read. -/
theorem quadraticRestrictedProjectedPeriodInputCoeff_alpha_zero
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (right left : RowVector (Sum Node {i : Node // i ≠ i0}))
    (P : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (hP0 :
      P 0 = (fun i j : Sum Node {i : Node // i ≠ i0} => right i * left j))
    (hleft_bottom : ∀ j : {i : Node // i ≠ i0}, left (Sum.inr j) = 0)
    (k r : ℕ) (j : Node) :
    quadraticRestrictedProjectedPeriodInputCoeff
        (Node := Node) quad lambda 0 i0 P k r j = 0 := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  let step0 : ℕ → NodeMatrix Idx := fun t =>
    quadraticRestrictedOneStepMatrix (Node := Node)
      quad lambda 0 i0 t
  let B : NodeMatrix Idx :=
    consecutiveProduct (Node := Idx) step0
      (k * quad.period + r + 1) (quad.period - 1 - r)
  let row0 : RowVector Idx :=
    quadraticRestrictedPrimalAverageRow (Node := Node) i0
  let rowP : RowVector Idx := rowMulMatrix (Node := Idx) row0 (P 0)
  have hrowP_bottom : ∀ b : {i : Node // i ≠ i0}, rowP (Sum.inr b) = 0 := by
    intro b
    simp [rowP, rowMulMatrix, row0, quadraticRestrictedPrimalAverageRow,
      hP0, hleft_bottom]
  have hB_top_right :
      ∀ i : Node, ∀ b : {i : Node // i ≠ i0},
        B (Sum.inl i) (Sum.inr b) = 0 := by
    intro i b
    simpa [B, step0, Idx] using
      quadraticRestrictedConsecutiveProduct_alpha_zero_top_right
        (Node := Node) quad lambda i0 (k * quad.period + r + 1)
        (quad.period - 1 - r) i b
  have hrowPB_bottom :
      ∀ b : {i : Node // i ≠ i0},
        rowMulMatrix (Node := Idx) rowP B (Sum.inr b) = 0 := by
    intro b
    unfold rowMulMatrix
    rw [Fintype.sum_sum_type]
    have htop :
        (∑ i : Node, rowP (Sum.inl i) * B (Sum.inl i) (Sum.inr b)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _hi
      simp [hB_top_right i b]
    have hbottom :
        (∑ c : {i : Node // i ≠ i0},
          rowP (Sum.inr c) * B (Sum.inr c) (Sum.inr b)) = 0 := by
      apply Finset.sum_eq_zero
      intro c _hc
      simp [hrowP_bottom c]
    rw [htop, hbottom]
    ring
  unfold quadraticRestrictedProjectedPeriodInputCoeff
  apply Finset.sum_eq_zero
  intro a _ha
  cases a with
  | inl i =>
      simp [quadraticRestrictedNoiseInnovationCoeff]
  | inr b =>
      have hrow :
          rowMulMatrix
              (Node := Sum Node {i : Node // i ≠ i0})
              (rowMulMatrix
                (Node := Sum Node {i : Node // i ≠ i0})
                (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
                (P 0))
              (consecutiveProduct
                (Node := Sum Node {i : Node // i ≠ i0})
                (fun t =>
                  quadraticRestrictedOneStepMatrix
                    (Node := Node) quad lambda 0 i0 t)
                (k * quad.period + r + 1) (quad.period - 1 - r))
              (Sum.inr b) = 0 := by
        simpa [Idx, step0, B, row0, rowP] using hrowPB_bottom b
      rw [hrow]
      ring

/-- Scalar phase-input coefficient derivative at the Appendix C.1 base point.

The propagated scalar window coefficient is `1` at zero for every active phase,
so the explicit scalar row `-alpha A_r(alpha) b_{kp+r}` has first derivative
`-b_{kp+r}`. -/
theorem quadraticScalarPhaseInputCoeff_hasDerivAt_zero
    (quad : Setup Node ℝ) (lambda : ℝ) (k r : ℕ) (j : Node)
    (hr : r < quad.period) :
    HasDerivAt
      (fun alpha : ℝ =>
        -alpha *
          quadraticScalarWindowNoiseCoeff (Node := Node)
            quad lambda alpha (quad.blockStart k) quad.period r *
          quad.influence (quad.blockStart k + r) j)
      (-(quad.influence (quad.blockStart k + r) j)) 0 := by
  classical
  let coeff : ℝ → ℝ := fun alpha =>
    quadraticScalarWindowNoiseCoeff (Node := Node)
      quad lambda alpha (quad.blockStart k) quad.period r
  have hcoeff_cont : ContinuousAt coeff 0 :=
    (quadraticScalarWindowNoiseCoeff_continuous
      (Node := Node) quad lambda (quad.blockStart k)
      quad.period r).continuousAt
  have hcoeff_zero : coeff 0 = 1 := by
    exact
      quadraticScalarWindowNoiseCoeff_zero_of_lt
        (Node := Node) quad lambda (quad.blockStart k) quad.period r hr
  have hbase :
      HasDerivAt (fun alpha : ℝ => alpha * coeff alpha) 1 0 := by
    have hraw := hasDerivAt_id_mul_of_continuousAt_zero coeff hcoeff_cont
    convert hraw using 1
    exact hcoeff_zero.symm
  have hscaled :=
    hbase.mul_const (-(quad.influence (quad.blockStart k + r) j))
  convert hscaled using 1
  · funext alpha
    dsimp [coeff]
    ring
  · ring

/-- Analyticity of the explicit scalar phase-input coefficient row. -/
theorem quadraticScalarPhaseInputCoeff_analyticAt_zero
    (quad : Setup Node ℝ) (lambda : ℝ) (k r : ℕ) (j : Node) :
    AnalyticAt ℝ
      (fun alpha : ℝ =>
        -alpha *
          quadraticScalarWindowNoiseCoeff (Node := Node)
            quad lambda alpha (quad.blockStart k) quad.period r *
          quad.influence (quad.blockStart k + r) j) 0 := by
  classical
  have hcoeff :
      AnalyticAt ℝ
        (fun alpha : ℝ =>
          quadraticScalarWindowNoiseCoeff (Node := Node)
            quad lambda alpha (quad.blockStart k) quad.period r) 0 :=
    quadraticScalarWindowNoiseCoeff_analyticAt_zero
      (Node := Node) quad lambda (quad.blockStart k) quad.period r
  have hneg : AnalyticAt ℝ (fun alpha : ℝ => -alpha) 0 := by
    fun_prop
  exact (hneg.mul hcoeff).mul analyticAt_const

/-- Conditional Appendix C.1 row-error bridge.

Once the source-derived projected coefficient derivative is supplied, the
already-proved analyticity and alpha-zero cancellation give the desired
`O(alpha^2)` coefficient error against the scalar phase row. -/
theorem quadratic_restricted_projected_period_input_coeff_row_sub_scalar_isBigO_sq_of_hasDerivAt
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (right left : RowVector (Sum Node {i : Node // i ≠ i0}))
    (P : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (hP0 :
      P 0 = (fun i j : Sum Node {i : Node // i ≠ i0} => right i * left j))
    (hleft_bottom : ∀ j : {i : Node // i ≠ i0}, left (Sum.inr j) = 0)
    (k r : ℕ) (j : Node) (hr : r < quad.period)
    (hproj_analytic :
      AnalyticAt ℝ
        (fun alpha : ℝ =>
          quadraticRestrictedProjectedPeriodInputCoeff
            (Node := Node) quad lambda alpha i0 P k r j) 0)
    (hproj_deriv :
      HasDerivAt
        (fun alpha : ℝ =>
          quadraticRestrictedProjectedPeriodInputCoeff
            (Node := Node) quad lambda alpha i0 P k r j)
        (-(quad.influence (quad.blockStart k + r) j)) 0) :
    Asymptotics.IsBigO (nhds 0)
      (fun alpha : ℝ =>
        quadraticRestrictedProjectedPeriodInputCoeff
            (Node := Node) quad lambda alpha i0 P k r j -
          (-alpha *
            quadraticScalarWindowNoiseCoeff (Node := Node)
              quad lambda alpha (quad.blockStart k) quad.period r *
            quad.influence (quad.blockStart k + r) j))
      (fun alpha : ℝ => alpha ^ 2) := by
  classical
  let projected : ℝ → ℝ := fun alpha =>
    quadraticRestrictedProjectedPeriodInputCoeff
      (Node := Node) quad lambda alpha i0 P k r j
  let scalar : ℝ → ℝ := fun alpha =>
    -alpha *
      quadraticScalarWindowNoiseCoeff (Node := Node)
        quad lambda alpha (quad.blockStart k) quad.period r *
      quad.influence (quad.blockStart k + r) j
  have hprojected_zero : projected 0 = 0 := by
    simpa [projected] using
      quadraticRestrictedProjectedPeriodInputCoeff_alpha_zero
        (Node := Node) quad lambda i0 right left P hP0 hleft_bottom k r j
  have hprojected_O :
      Asymptotics.IsBigO (nhds 0)
        (fun alpha : ℝ =>
          projected alpha -
            (0 + alpha * (-(quad.influence (quad.blockStart k + r) j))))
        (fun alpha : ℝ => alpha ^ 2) := by
    exact
      analyticAt_scalar_first_order_remainder_isBigO_sq
        (by simpa [projected] using hproj_analytic)
        hprojected_zero
        (by simpa [projected] using hproj_deriv)
  have hscalar_zero : scalar 0 = 0 := by
    simp [scalar]
  have hscalar_deriv :
      HasDerivAt scalar (-(quad.influence (quad.blockStart k + r) j)) 0 := by
    simpa [scalar] using
      quadraticScalarPhaseInputCoeff_hasDerivAt_zero
        (Node := Node) quad lambda k r j hr
  have hscalar_O :
      Asymptotics.IsBigO (nhds 0)
        (fun alpha : ℝ =>
          scalar alpha -
            (0 + alpha * (-(quad.influence (quad.blockStart k + r) j))))
        (fun alpha : ℝ => alpha ^ 2) := by
    exact
      analyticAt_scalar_first_order_remainder_isBigO_sq
        (quadraticScalarPhaseInputCoeff_analyticAt_zero
          (Node := Node) quad lambda k r j)
        hscalar_zero hscalar_deriv
  have hdiff := hprojected_O.sub hscalar_O
  refine hdiff.congr ?_ (fun _ => rfl)
  intro alpha
  dsimp [projected, scalar]
  ring

/-- Alpha-zero cancellation for the projected slow period input against the
scalar block input.

Appendix C.1's step-6 coefficient comparison starts from this exact
cancellation: at `alpha = 0` the restricted period noise innovation has zero
primal block, while the scalar block innovation carries an explicit factor
`alpha`.  The remaining source leaf is the analytic first-order/coefficient
control upgrading this cancellation to an `O(alpha^2)` phase-input error. -/
theorem quadratic_restricted_projected_period_input_scalar_block_alpha_zero
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (right left : RowVector (Sum Node {i : Node // i ≠ i0}))
    (P : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (hP0 :
      P 0 = (fun i j : Sum Node {i : Node // i ≠ i0} => right i * left j))
    (hleft_bottom : ∀ j : {i : Node // i ≠ i0}, left (Sum.inr j) = 0)
    (noise : NoisePath Node ℝ) (k : ℕ) :
    quadraticRestrictedPrimalAverageOutput (Node := Node) i0
        (matrixMulVector (Node := Sum Node {i : Node // i ≠ i0}) (P 0)
          (quadraticRestrictedPeriodNoiseInnovationCoord
            (Node := Node) quad lambda 0 i0 noise k)) -
      quadraticScalarBlockNoiseInnovation (Node := Node)
        quad lambda 0 noise k = 0 := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  let xi : RowVector Idx :=
    quadraticRestrictedPeriodNoiseInnovationCoord
      (Node := Node) quad lambda 0 i0 noise k
  have hproj_zero :
      quadraticRestrictedPrimalAverageOutput (Node := Node) i0
          (matrixMulVector (Node := Idx) (P 0) xi) = 0 := by
    apply quadraticRestrictedPrimalAverageOutput_eq_zero_of_top_zero
      (Node := Node) i0
    intro i
    unfold matrixMulVector
    apply Finset.sum_eq_zero
    intro a _ha
    cases a with
    | inl j =>
        simp [Idx, xi, hP0,
          quadraticRestrictedPeriodNoiseInnovationCoord_alpha_zero_top]
    | inr j =>
        simp [Idx, xi, hP0, hleft_bottom]
  have hscalar_zero :
      quadraticScalarBlockNoiseInnovation (Node := Node)
        quad lambda 0 noise k = 0 := by
    rw [quadraticScalarBlockNoiseInnovation_eq_finset_sum]
    simp
  rw [hproj_zero, hscalar_zero]
  ring

/-- Exact diagonalization for a finite consecutive window of deterministic
weighted noise rows.

This is the stochastic aggregation layer needed after the projected/scalar
phase coefficient rows have been compared: the iid exact-variance contract
turns a finite within-period noise-row error into the sum of deterministic
row-norm squares, with all cross-time terms canceling. -/
theorem finite_consecutive_weightedNoise_sum_secondMoment_exact
    (quad : Setup Node ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (base n : ℕ) (w : ℕ → RowVector Node) :
    (∫ ω,
        |(Finset.range n).sum fun r =>
          weightedState (Node := Node) (E := ℝ) (w r)
            (oracle.noise ω (base + r))| ^ 2 ∂μ) =
      (Finset.range n).sum fun r =>
        rowNormSq (Node := Node) (w r) * quad.sigma ^ 2 := by
  classical
  let term : ℕ → Ω → ℝ := fun r ω =>
    weightedState (Node := Node) (E := ℝ) (w r)
      (oracle.noise ω (base + r))
  have horacle : quad.StochasticOracleAssumptions μ oracle := hnoise.1
  have hmem (r : ℕ) : MemLp (term r) 2 μ := by
    exact
      quad.weightedNoise_memLp_two μ oracle horacle (base + r) (w r)
  have hsq (r : ℕ) : Integrable (fun ω => ‖term r ω‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (hmem r).aestronglyMeasurable).1
      (hmem r)
  have hcross (r : ℕ) (_hr : r ∈ Finset.range n)
      (s : ℕ) (_hs : s ∈ Finset.range n) (hrs : r ≠ s) :
      (∫ ω, ⟪term r ω, term s ω⟫_ℝ ∂μ) = 0 := by
    rcases lt_or_gt_of_ne hrs with hrs_lt | hsr_lt
    · have hzero := quad.weightedNoise_crossTime_inner_integral_eq_zero
        μ oracle horacle (w r) (w s) (Nat.add_lt_add_left hrs_lt base)
      simpa [term] using hzero
    · have hzero := quad.weightedNoise_crossTime_inner_integral_eq_zero
        μ oracle horacle (w s) (w r) (Nat.add_lt_add_left hsr_lt base)
      simpa [term, real_inner_comm] using hzero
  have hdiag := integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero
    μ (Finset.range n) term
    (fun r _hr => (hmem r).aestronglyMeasurable)
    (fun r _hr => hsq r) hcross
  calc
    (∫ ω,
        |(Finset.range n).sum fun r =>
          weightedState (Node := Node) (E := ℝ) (w r)
            (oracle.noise ω (base + r))| ^ 2 ∂μ) =
        ∫ ω, ‖(Finset.range n).sum (fun r => term r ω)‖ ^ 2 ∂μ := by
      simp [term, Real.norm_eq_abs]
    _ = (Finset.range n).sum (fun r => ∫ ω, ‖term r ω‖ ^ 2 ∂μ) := hdiag
    _ =
        (Finset.range n).sum fun r =>
          rowNormSq (Node := Node) (w r) * quad.sigma ^ 2 := by
      apply Finset.sum_congr rfl
      intro r _hr
      have hrow :=
        sameTime_weightedNoise_secondMoment_eq_exact
          (Node := Node) quad μ oracle hnoise (base + r) (w r)
      calc
        (∫ ω, ‖term r ω‖ ^ 2 ∂μ) =
            ∫ ω,
              |weightedState (Node := Node) (E := ℝ) (w r)
                (oracle.noise ω (base + r))| ^ 2 ∂μ := by
              simp [term, Real.norm_eq_abs]
        _ = rowNormSq (Node := Node) (w r) * quad.sigma ^ 2 := hrow

/-- Exact second moment of the projected period-input/scalar-block
difference after both finite within-period noise rows are exposed.

This is the stochastic aggregation layer for Appendix C.1 step 6: the iid
exact-variance law diagonalizes the projected/scalar coefficient-row error
over the period window.  The remaining deterministic task is to prove that
each displayed coefficient row is `O(alpha^2)`. -/
theorem quadratic_restricted_projected_period_input_scalar_block_secondMoment_exact
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (i0 : Node)
    (P : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle) (k : ℕ) :
    (∫ ω,
        |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
            (matrixMulVector
              (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
              (quadraticRestrictedPeriodNoiseInnovationCoord
                (Node := Node) quad lambda alpha i0 (oracle.noise ω) k)) -
          quadraticScalarBlockNoiseInnovation (Node := Node)
            quad lambda alpha (oracle.noise ω) k| ^ 2 ∂μ) =
      (Finset.range quad.period).sum fun r =>
        rowNormSq (Node := Node)
          (fun j : Node =>
            quadraticRestrictedProjectedPeriodInputCoeff
                (Node := Node) quad lambda alpha i0 P k r j -
              (-alpha *
                quadraticScalarWindowNoiseCoeff (Node := Node)
                  quad lambda alpha (quad.blockStart k) quad.period r *
                quad.influence (quad.blockStart k + r) j)) *
          quad.sigma ^ 2 := by
  classical
  let projected : Ω → ℝ := fun ω =>
    quadraticRestrictedPrimalAverageOutput (Node := Node) i0
      (matrixMulVector
        (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
        (quadraticRestrictedPeriodNoiseInnovationCoord
          (Node := Node) quad lambda alpha i0 (oracle.noise ω) k))
  let scalar : Ω → ℝ := fun ω =>
    quadraticScalarBlockNoiseInnovation (Node := Node)
      quad lambda alpha (oracle.noise ω) k
  let w : ℕ → RowVector Node := fun r j =>
    quadraticRestrictedProjectedPeriodInputCoeff
        (Node := Node) quad lambda alpha i0 P k r j -
      (-alpha *
        quadraticScalarWindowNoiseCoeff (Node := Node)
          quad lambda alpha (quad.blockStart k) quad.period r *
        quad.influence (quad.blockStart k + r) j)
  have hpoint :
      (fun ω : Ω => projected ω - scalar ω) =
        fun ω : Ω =>
          (Finset.range quad.period).sum fun r =>
            weightedState (Node := Node) (E := ℝ) (w r)
              (oracle.noise ω (quad.blockStart k + r)) := by
    funext ω
    have hproj :=
      quadratic_restricted_projected_period_input_coeff_row_unroll
        (Node := Node) quad lambda alpha i0 P (oracle.noise ω) k
    have hscalar :=
      quadraticScalarBlockNoiseInnovation_eq_weightedCoeff_sum
        (Node := Node) quad lambda alpha (oracle.noise ω) k
    calc
      projected ω - scalar ω =
          ((Finset.range quad.period).sum fun r =>
            weightedState (Node := Node) (E := ℝ)
              (quadraticRestrictedProjectedPeriodInputCoeff
                (Node := Node) quad lambda alpha i0 P k r)
              (oracle.noise ω (k * quad.period + r))) -
            ((Finset.range quad.period).sum fun r =>
              weightedState (Node := Node) (E := ℝ)
                (fun j : Node =>
                  -alpha *
                    quadraticScalarWindowNoiseCoeff (Node := Node)
                      quad lambda alpha (quad.blockStart k) quad.period r *
                    quad.influence (quad.blockStart k + r) j)
                (oracle.noise ω (quad.blockStart k + r))) := by
            dsimp [projected, scalar]
            rw [hproj, hscalar]
      _ =
          (Finset.range quad.period).sum fun r =>
            weightedState (Node := Node) (E := ℝ) (w r)
              (oracle.noise ω (quad.blockStart k + r)) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro r _hr
            have ht : k * quad.period + r = quad.blockStart k + r := by
              simp [Setup.blockStart]
            rw [ht]
            unfold weightedState
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro j _hj
            dsimp [w]
            ring
  calc
    (∫ ω,
        |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
            (matrixMulVector
              (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
              (quadraticRestrictedPeriodNoiseInnovationCoord
                (Node := Node) quad lambda alpha i0 (oracle.noise ω) k)) -
          quadraticScalarBlockNoiseInnovation (Node := Node)
            quad lambda alpha (oracle.noise ω) k| ^ 2 ∂μ) =
        ∫ ω, |(Finset.range quad.period).sum fun r =>
          weightedState (Node := Node) (E := ℝ) (w r)
            (oracle.noise ω (quad.blockStart k + r))| ^ 2 ∂μ := by
          congr 1
          funext ω
          have h := congrFun hpoint ω
          dsimp [projected, scalar] at h
          rw [h]
    _ =
        (Finset.range quad.period).sum fun r =>
          rowNormSq (Node := Node) (w r) * quad.sigma ^ 2 := by
          exact
            finite_consecutive_weightedNoise_sum_secondMoment_exact
              (Node := Node) quad μ oracle hnoise (quad.blockStart k)
              quad.period w
    _ =
        (Finset.range quad.period).sum fun r =>
          rowNormSq (Node := Node)
            (fun j : Node =>
              quadraticRestrictedProjectedPeriodInputCoeff
                  (Node := Node) quad lambda alpha i0 P k r j -
                (-alpha *
                  quadraticScalarWindowNoiseCoeff (Node := Node)
                    quad lambda alpha (quad.blockStart k) quad.period r *
                  quad.influence (quad.blockStart k + r) j)) *
            quad.sigma ^ 2 := by
          rfl

/-- Finite row aggregation for Appendix C.1 coefficient remainders.

If every coordinate of a deterministic row is `O(alpha^2)`, its squared
Euclidean row norm is `O(alpha^4)`. -/
theorem rowNormSq_isBigO_pow_four_of_forall_isBigO_sq
    (w : ℝ → RowVector Node)
    (hcoord :
      ∀ j : Node,
        Asymptotics.IsBigO (nhds 0)
          (fun alpha : ℝ => w alpha j)
          (fun alpha : ℝ => alpha ^ 2)) :
    Asymptotics.IsBigO (nhds 0)
      (fun alpha : ℝ => rowNormSq (Node := Node) (w alpha))
      (fun alpha : ℝ => alpha ^ 4) := by
  classical
  unfold rowNormSq
  have hsum :
      Asymptotics.IsBigO (nhds 0)
        (fun alpha : ℝ => ∑ j : Node, (w alpha j) ^ 2)
        (fun alpha : ℝ => (alpha ^ 2) * (alpha ^ 2)) := by
    apply Asymptotics.IsBigO.sum
    intro j _hj
    simpa [pow_two] using (hcoord j).mul (hcoord j)
  refine hsum.congr (fun alpha => ?_) (fun alpha => ?_)
  · rfl
  · ring

/-- Appendix C.1 step 6 stochastic input bound at fixed block index.

The iid diagonalization reduces the projected/scalar input error to a finite
sum of coefficient row norms; the source-derived `O(alpha^2)` coefficient
bridge makes that second moment `O(alpha^4)`. -/
theorem quadratic_restricted_projected_period_input_scalar_block_l2_alpha4_bound_of_coeff
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (P : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle) (k : ℕ)
    (hcoeff :
      ∀ r : ℕ, r < quad.period → ∀ j : Node,
        Asymptotics.IsBigO (nhds 0)
          (fun alpha : ℝ =>
            quadraticRestrictedProjectedPeriodInputCoeff
                (Node := Node) quad lambda alpha i0 P k r j -
              (-alpha *
                quadraticScalarWindowNoiseCoeff (Node := Node)
                  quad lambda alpha (quad.blockStart k) quad.period r *
                quad.influence (quad.blockStart k + r) j))
          (fun alpha : ℝ => alpha ^ 2)) :
    Asymptotics.IsBigO (nhds 0)
      (fun alpha : ℝ =>
        ∫ ω,
          |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
              (matrixMulVector
                (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
                (quadraticRestrictedPeriodNoiseInnovationCoord
                  (Node := Node) quad lambda alpha i0
                  (oracle.noise ω) k)) -
            quadraticScalarBlockNoiseInnovation (Node := Node)
              quad lambda alpha (oracle.noise ω) k| ^ 2 ∂μ)
      (fun alpha : ℝ => alpha ^ 4) := by
  classical
  let rowErr : ℕ → ℝ → RowVector Node := fun r alpha j =>
    quadraticRestrictedProjectedPeriodInputCoeff
        (Node := Node) quad lambda alpha i0 P k r j -
      (-alpha *
        quadraticScalarWindowNoiseCoeff (Node := Node)
          quad lambda alpha (quad.blockStart k) quad.period r *
        quad.influence (quad.blockStart k + r) j)
  have hrow :
      ∀ r ∈ Finset.range quad.period,
        Asymptotics.IsBigO (nhds 0)
          (fun alpha : ℝ => rowNormSq (Node := Node) (rowErr r alpha))
          (fun alpha : ℝ => alpha ^ 4) := by
    intro r hr
    exact
      rowNormSq_isBigO_pow_four_of_forall_isBigO_sq
        (Node := Node) (w := rowErr r)
        (fun j => hcoeff r (Finset.mem_range.mp hr) j)
  have hsum :
      Asymptotics.IsBigO (nhds 0)
        (fun alpha : ℝ =>
          (Finset.range quad.period).sum fun r =>
            rowNormSq (Node := Node) (rowErr r alpha) * quad.sigma ^ 2)
        (fun alpha : ℝ => alpha ^ 4) := by
    apply Asymptotics.IsBigO.sum
    intro r hr
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (hrow r hr).const_mul_left (quad.sigma ^ 2)
  refine hsum.congr ?_ (fun _ => rfl)
  intro alpha
  rw [quadratic_restricted_projected_period_input_scalar_block_secondMoment_exact
    (Node := Node) quad lambda alpha i0 P μ oracle hnoise k]

/-- The projected/scalar block-input second moment is block-periodic.

After iid diagonalization, every deterministic coefficient row depends only on
the within-period phase.  This is the uniformization layer needed before the
slow scalar Duhamel estimate averages over horizons with `alpha * T >= 1`. -/
theorem
    quadratic_restricted_projected_period_input_scalar_block_secondMoment_block_eq_zero
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (i0 : Node)
    (P : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle) (k : ℕ) :
    (∫ ω,
        |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
            (matrixMulVector
              (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
              (quadraticRestrictedPeriodNoiseInnovationCoord
                (Node := Node) quad lambda alpha i0
                (oracle.noise ω) k)) -
          quadraticScalarBlockNoiseInnovation (Node := Node)
            quad lambda alpha (oracle.noise ω) k| ^ 2 ∂μ) =
      (∫ ω,
        |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
            (matrixMulVector
              (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
              (quadraticRestrictedPeriodNoiseInnovationCoord
                (Node := Node) quad lambda alpha i0
                (oracle.noise ω) 0)) -
          quadraticScalarBlockNoiseInnovation (Node := Node)
            quad lambda alpha (oracle.noise ω) 0| ^ 2 ∂μ) := by
  classical
  rw [quadratic_restricted_projected_period_input_scalar_block_secondMoment_exact
      (Node := Node) quad lambda alpha i0 P μ oracle hnoise k,
    quadratic_restricted_projected_period_input_scalar_block_secondMoment_exact
      (Node := Node) quad lambda alpha i0 P μ oracle hnoise 0]
  apply Finset.sum_congr rfl
  intro r _hr
  apply congrArg (fun w : RowVector Node =>
    rowNormSq (Node := Node) w * quad.sigma ^ 2)
  funext j
  have hproj :=
    congrFun
      (quadraticRestrictedProjectedPeriodInputCoeff_block_eq_zero
        (Node := Node) quad lambda alpha i0 P k r) j
  have hscalar_k :
      quadraticScalarWindowNoiseCoeff (Node := Node)
          quad lambda alpha (quad.blockStart k) quad.period r =
        quadraticScalarWindowNoiseCoeff (Node := Node)
          quad lambda alpha 0 quad.period r := by
    simpa using
      quadraticScalarWindowNoiseCoeff_blockStart_add
        (Node := Node) quad lambda alpha k 0 quad.period r
  have hscalar_0 :
      quadraticScalarWindowNoiseCoeff (Node := Node)
          quad lambda alpha (quad.blockStart 0) quad.period r =
        quadraticScalarWindowNoiseCoeff (Node := Node)
          quad lambda alpha 0 quad.period r := by
    simpa using
      quadraticScalarWindowNoiseCoeff_blockStart_add
        (Node := Node) quad lambda alpha 0 0 quad.period r
  rw [hproj, hscalar_k, hscalar_0,
    quad.influence_blockStart_add k r,
    quad.influence_blockStart_add 0 r]

/-- Uniform fixed-block `O(alpha^4)` input control from the phase-zero block.
This is the usable form for finite-horizon slow-recursion estimates: the
constant no longer depends on the block index. -/
theorem
    quadratic_restricted_projected_period_input_scalar_block_l2_alpha4_bound_uniform_of_zero
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (P : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (hzero :
      Asymptotics.IsBigO (nhds 0)
        (fun alpha : ℝ =>
          ∫ ω,
            |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                (matrixMulVector
                  (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
                  (quadraticRestrictedPeriodNoiseInnovationCoord
                    (Node := Node) quad lambda alpha i0
                    (oracle.noise ω) 0)) -
              quadraticScalarBlockNoiseInnovation (Node := Node)
                quad lambda alpha (oracle.noise ω) 0| ^ 2 ∂μ)
        (fun alpha : ℝ => alpha ^ 4)) :
    ∀ k : ℕ,
      Asymptotics.IsBigO (nhds 0)
        (fun alpha : ℝ =>
          ∫ ω,
            |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                (matrixMulVector
                  (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
                  (quadraticRestrictedPeriodNoiseInnovationCoord
                    (Node := Node) quad lambda alpha i0
                    (oracle.noise ω) k)) -
              quadraticScalarBlockNoiseInnovation (Node := Node)
                quad lambda alpha (oracle.noise ω) k| ^ 2 ∂μ)
        (fun alpha : ℝ => alpha ^ 4) := by
  intro k
  refine hzero.congr ?_ (fun _ => rfl)
  intro alpha
  exact
    quadratic_restricted_projected_period_input_scalar_block_secondMoment_block_eq_zero
      (Node := Node) quad lambda alpha i0 P μ oracle hnoise k |>.symm

/-- Extract a positive small-stepsize constant from a scalar `O(alpha^4)`
statement at the source expansion point.

The Duhamel estimates need explicit constants on a positive stepsize interval,
not just a filter-level asymptotic statement. -/
theorem real_isBigO_nhds_zero_pow_four_explicit_pos_bound
    (f : ℝ → ℝ)
    (h :
      Asymptotics.IsBigO (nhds 0) f (fun alpha : ℝ => alpha ^ 4)) :
    ∃ C alpha0 : ℝ,
      0 < C ∧ 0 < alpha0 ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
          f alpha ≤ C * alpha ^ 4 := by
  classical
  obtain ⟨C, hC_pos, hCbig⟩ := h.exists_pos
  have hbound_eventually :
      ∀ᶠ alpha : ℝ in nhds 0,
        ‖f alpha‖ ≤ C * ‖alpha ^ 4‖ := by
    simpa using (Asymptotics.isBigOWith_iff.mp hCbig)
  obtain ⟨eps, heps_pos, hbound_eps⟩ :=
    Metric.eventually_nhds_iff.mp hbound_eventually
  let alpha0 : ℝ := eps / 2
  have halpha0_pos : 0 < alpha0 := by
    dsimp [alpha0]
    positivity
  refine ⟨C, alpha0, hC_pos, halpha0_pos, ?_⟩
  intro alpha halpha_pos halpha_le
  have halpha_nonneg : 0 ≤ alpha := le_of_lt halpha_pos
  have halpha_lt_eps : alpha < eps := by
    dsimp [alpha0] at halpha_le
    nlinarith
  have hdist : dist alpha 0 < eps := by
    simpa [Real.dist_eq, abs_of_pos halpha_pos] using halpha_lt_eps
  have hbound := hbound_eps hdist
  have hnorm_pow : ‖alpha ^ 4‖ = alpha ^ 4 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg halpha_nonneg 4)]
  have hf_le_norm : f alpha ≤ ‖f alpha‖ := by
    simpa [Real.norm_eq_abs] using le_abs_self (f alpha)
  rw [hnorm_pow] at hbound
  exact le_trans hf_le_norm hbound

/-- Duhamel-usable uniform block-input estimate for Appendix C.1 step 6.

The phase-zero `O(alpha^4)` second-moment estimate and block periodicity supply
one positive constant and one positive stepsize radius that work for every
period block. -/
theorem
    quadratic_restricted_projected_period_input_scalar_block_l2_alpha4_explicit_uniform_bound
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (P : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (hzero :
      Asymptotics.IsBigO (nhds 0)
        (fun alpha : ℝ =>
          ∫ ω,
            |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                (matrixMulVector
                  (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
                  (quadraticRestrictedPeriodNoiseInnovationCoord
                    (Node := Node) quad lambda alpha i0
                    (oracle.noise ω) 0)) -
              quadraticScalarBlockNoiseInnovation (Node := Node)
                quad lambda alpha (oracle.noise ω) 0| ^ 2 ∂μ)
        (fun alpha : ℝ => alpha ^ 4)) :
    ∃ C alpha0 : ℝ,
      0 < C ∧ 0 < alpha0 ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
          ∀ k : ℕ,
            (∫ ω,
              |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                  (matrixMulVector
                    (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
                    (quadraticRestrictedPeriodNoiseInnovationCoord
                      (Node := Node) quad lambda alpha i0
                      (oracle.noise ω) k)) -
                quadraticScalarBlockNoiseInnovation (Node := Node)
                  quad lambda alpha (oracle.noise ω) k| ^ 2 ∂μ) ≤
              C * alpha ^ 4 := by
  classical
  let f0 : ℝ → ℝ := fun alpha =>
    ∫ ω,
      |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
          (matrixMulVector
            (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
            (quadraticRestrictedPeriodNoiseInnovationCoord
              (Node := Node) quad lambda alpha i0
              (oracle.noise ω) 0)) -
        quadraticScalarBlockNoiseInnovation (Node := Node)
          quad lambda alpha (oracle.noise ω) 0| ^ 2 ∂μ
  obtain ⟨C, alpha0, hC_pos, halpha0_pos, hbound0⟩ :=
    real_isBigO_nhds_zero_pow_four_explicit_pos_bound
      f0 (by simpa [f0] using hzero)
  refine ⟨C, alpha0, hC_pos, halpha0_pos, ?_⟩
  intro alpha halpha_pos halpha_le k
  rw [quadratic_restricted_projected_period_input_scalar_block_secondMoment_block_eq_zero
      (Node := Node) quad lambda alpha i0 P μ oracle hnoise k]
  exact hbound0 alpha halpha_pos halpha_le

/-- `L²` membership of the projected slow period input minus the scalar block
input.

This exposes the `MemLp` form needed to assemble the slow AR forcing term; the
square-integrability theorem below is its integral consequence. -/
theorem quadratic_restricted_projected_period_input_scalar_block_diff_memLp_two
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (P : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (alpha : ℝ) (k : ℕ) :
    MemLp
      (fun ω : Ω =>
        quadraticRestrictedPrimalAverageOutput (Node := Node) i0
            (matrixMulVector (Node := Sum Node {i : Node // i ≠ i0})
              (P alpha)
              (quadraticRestrictedPeriodNoiseInnovationCoord
                (Node := Node) quad lambda alpha i0 (oracle.noise ω) k)) -
          quadraticScalarBlockNoiseInnovation (Node := Node)
            quad lambda alpha (oracle.noise ω) k)
      2 μ := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  let projected : Ω → ℝ := fun ω =>
    quadraticRestrictedPrimalAverageOutput (Node := Node) i0
      (matrixMulVector (Node := Idx) (P alpha)
        (quadraticRestrictedPeriodNoiseInnovationCoord
          (Node := Node) quad lambda alpha i0 (oracle.noise ω) k))
  let scalar : Ω → ℝ := fun ω =>
    quadraticScalarBlockNoiseInnovation (Node := Node)
      quad lambda alpha (oracle.noise ω) k
  have hxi_coord :
      ∀ a : Idx,
        MemLp
          (fun ω : Ω =>
            quadraticRestrictedPeriodNoiseInnovationCoord
              (Node := Node) quad lambda alpha i0 (oracle.noise ω) k a)
          2 μ := by
    intro a
    exact
      quadraticRestrictedPeriodNoiseInnovationCoord_coordinate_memLp
        (Node := Node) quad lambda alpha i0 μ oracle hnoise k a
  have hprojected_coord :
      ∀ i : Node,
        MemLp
          (fun ω : Ω =>
            matrixMulVector (Node := Idx) (P alpha)
              (quadraticRestrictedPeriodNoiseInnovationCoord
                (Node := Node) quad lambda alpha i0 (oracle.noise ω) k)
              (Sum.inl i))
          2 μ := by
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
                (Node := Node) quad lambda alpha i0 (oracle.noise ω) k)
              (Sum.inl i))
        2 μ := by
    apply memLp_finset_sum Finset.univ
    intro i _hi
    exact hprojected_coord i
  have hprojected : MemLp projected 2 μ := by
    dsimp [projected]
    simpa [quadraticRestrictedPrimalAverageOutput] using
      hprojected_sum.const_smul ((nodeCount (Node := Node) : ℝ)⁻¹)
  have hscalar : MemLp scalar 2 μ := by
    dsimp [scalar]
    exact
      quadraticScalarBlockNoiseInnovation_memLp_two
        (Node := Node) quad lambda alpha μ oracle hnoise k
  simpa [projected, scalar] using hprojected.sub hscalar

/-- Square-integrability of the projected slow period input minus the scalar
block input.

This is the L² well-formedness half of the Appendix C.1 step-6 coefficient
comparison.  It packages the already-proved coordinate `MemLp` facts for the
restricted period innovation and scalar block innovation, leaving the hard
remaining source leaf as the quantitative `O(alpha^4)` second-moment bound. -/
theorem quadratic_restricted_projected_period_input_scalar_block_diff_integrable
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (P : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (alpha : ℝ) (k : ℕ) :
    Integrable
      (fun ω : Ω =>
        |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
            (matrixMulVector (Node := Sum Node {i : Node // i ≠ i0})
              (P alpha)
              (quadraticRestrictedPeriodNoiseInnovationCoord
                (Node := Node) quad lambda alpha i0 (oracle.noise ω) k)) -
          quadraticScalarBlockNoiseInnovation (Node := Node)
            quad lambda alpha (oracle.noise ω) k| ^ 2) μ := by
  classical
  exact
    real_abs_sq_integrable_of_memLp_two
      (quadratic_restricted_projected_period_input_scalar_block_diff_memLp_two
        (Node := Node) quad lambda i0 P μ oracle hnoise alpha k)

/-- The projected restricted period-input channel has zero mean.

This is the expectation-level martingale bridge needed by Appendix C.3 after
the projected/scalar block recursion has been exposed: the projected period
input is a finite deterministic row transform of fresh node noises, so the
source oracle's weighted mean-zero law cancels every phase term. -/
theorem quadratic_restricted_projected_period_input_integral_eq_zero
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (P : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (alpha : ℝ) (k : ℕ) :
    (∫ ω,
      quadraticRestrictedPrimalAverageOutput (Node := Node) i0
        (matrixMulVector
          (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
          (quadraticRestrictedPeriodNoiseInnovationCoord
            (Node := Node) quad lambda alpha i0 (oracle.noise ω) k)) ∂μ) = 0 := by
  classical
  let coeff : ℕ → RowVector Node := fun r =>
    quadraticRestrictedProjectedPeriodInputCoeff
      (Node := Node) quad lambda alpha i0 P k r
  have hpoint :
      (fun ω : Ω =>
        quadraticRestrictedPrimalAverageOutput (Node := Node) i0
          (matrixMulVector
            (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
            (quadraticRestrictedPeriodNoiseInnovationCoord
              (Node := Node) quad lambda alpha i0 (oracle.noise ω) k))) =
        fun ω : Ω =>
          (Finset.range quad.period).sum fun r =>
            weightedState (Node := Node) (E := ℝ) (coeff r)
              (oracle.noise ω (k * quad.period + r)) := by
    funext ω
    simpa [coeff] using
      quadratic_restricted_projected_period_input_coeff_row_unroll
        (Node := Node) quad lambda alpha i0 P (oracle.noise ω) k
  have hterm_int :
      ∀ r ∈ Finset.range quad.period,
        Integrable
          (fun ω : Ω =>
            weightedState (Node := Node) (E := ℝ) (coeff r)
              (oracle.noise ω (k * quad.period + r))) μ := by
    intro r _hr
    exact
      (quad.weightedNoise_memLp_two μ oracle hnoise.1
        (k * quad.period + r) (coeff r)).integrable (by norm_num)
  calc
    (∫ ω,
      quadraticRestrictedPrimalAverageOutput (Node := Node) i0
        (matrixMulVector
          (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
          (quadraticRestrictedPeriodNoiseInnovationCoord
            (Node := Node) quad lambda alpha i0 (oracle.noise ω) k)) ∂μ) =
        ∫ ω,
          (Finset.range quad.period).sum fun r =>
            weightedState (Node := Node) (E := ℝ) (coeff r)
              (oracle.noise ω (k * quad.period + r)) ∂μ := by
          rw [hpoint]
    _ =
        (Finset.range quad.period).sum fun r =>
          ∫ ω,
            weightedState (Node := Node) (E := ℝ) (coeff r)
              (oracle.noise ω (k * quad.period + r)) ∂μ := by
          rw [MeasureTheory.integral_finset_sum]
          exact hterm_int
    _ = 0 := by
          apply Finset.sum_eq_zero
          intro r _hr
          exact
            weightedNoise_integral_eq_zero
              (Node := Node) quad μ oracle hnoise.1
              (k * quad.period + r) (coeff r)

/-- The projected/scalar period-input discrepancy has zero mean.

This is the exact expectation counterpart of the C.1 `O(alpha^2)` coefficient
comparison: the discrepancy has nonzero variance, but its mean vanishes by the
same martingale cancellation on both the projected restricted input and the
scalar block innovation. -/
theorem quadratic_restricted_projected_period_input_scalar_block_diff_integral_eq_zero
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (P : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (alpha : ℝ) (k : ℕ) :
    (∫ ω,
      quadraticRestrictedPrimalAverageOutput (Node := Node) i0
          (matrixMulVector
            (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
            (quadraticRestrictedPeriodNoiseInnovationCoord
              (Node := Node) quad lambda alpha i0 (oracle.noise ω) k)) -
        quadraticScalarBlockNoiseInnovation (Node := Node)
          quad lambda alpha (oracle.noise ω) k ∂μ) = 0 := by
  classical
  let projected : Ω → ℝ := fun ω =>
    quadraticRestrictedPrimalAverageOutput (Node := Node) i0
      (matrixMulVector
        (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
        (quadraticRestrictedPeriodNoiseInnovationCoord
          (Node := Node) quad lambda alpha i0 (oracle.noise ω) k))
  let scalar : Ω → ℝ := fun ω =>
    quadraticScalarBlockNoiseInnovation (Node := Node)
      quad lambda alpha (oracle.noise ω) k
  have hdiff_mem :
      MemLp (fun ω : Ω => projected ω - scalar ω) 2 μ := by
    simpa [projected, scalar] using
      quadratic_restricted_projected_period_input_scalar_block_diff_memLp_two
        (Node := Node) quad lambda i0 P μ oracle hnoise alpha k
  have hprojected_int : Integrable projected μ := by
    have hproj_mem : MemLp projected 2 μ := by
      have hsum_mem :
          MemLp
            (fun ω : Ω =>
              (Finset.range quad.period).sum fun r =>
                weightedState (Node := Node) (E := ℝ)
                  (quadraticRestrictedProjectedPeriodInputCoeff
                    (Node := Node) quad lambda alpha i0 P k r)
                  (oracle.noise ω (k * quad.period + r))) 2 μ := by
        apply memLp_finset_sum
        intro r _hr
        exact
          quad.weightedNoise_memLp_two μ oracle hnoise.1
            (k * quad.period + r)
            (quadraticRestrictedProjectedPeriodInputCoeff
              (Node := Node) quad lambda alpha i0 P k r)
      refine MemLp.ae_eq ?_ hsum_mem
      exact Filter.Eventually.of_forall fun ω => by
        symm
        exact
          quadratic_restricted_projected_period_input_coeff_row_unroll
            (Node := Node) quad lambda alpha i0 P (oracle.noise ω) k
    exact hproj_mem.integrable (by norm_num)
  have hscalar_int : Integrable scalar μ :=
    (quadraticScalarBlockNoiseInnovation_memLp_two
      (Node := Node) quad lambda alpha μ oracle hnoise k).integrable
      (by norm_num)
  have hproj_zero :
      (∫ ω, projected ω ∂μ) = 0 := by
    simpa [projected] using
      quadratic_restricted_projected_period_input_integral_eq_zero
        (Node := Node) quad lambda i0 P μ oracle hnoise alpha k
  have hscalar_zero :
      (∫ ω, scalar ω ∂μ) = 0 := by
    simpa [scalar] using
      quadraticScalarBlockNoiseInnovation_integral_eq_zero
        (Node := Node) quad lambda alpha μ oracle hnoise k
  calc
    (∫ ω, projected ω - scalar ω ∂μ) =
        (∫ ω, projected ω ∂μ) - ∫ ω, scalar ω ∂μ := by
          rw [MeasureTheory.integral_sub hprojected_int hscalar_int]
    _ = 0 := by rw [hproj_zero, hscalar_zero]; ring

/-- Mean recursion for a scalar AR error after the martingale input cancels.

This is the deterministic expectation-level bridge needed in Appendix C.3:
once the projected/scalar block-boundary error recursion is exposed and the
period-input discrepancy has zero mean, the remaining mean error is driven only
by the deterministic multiplier mismatch against the scalar block mean. -/
theorem scalar_ar_error_integral_recursion_of_input_mean_zero
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (gamma Gamma x0 : ℝ)
    (err scalar inputDiff : Ω → ℕ → ℝ)
    (hrec :
      ∀ ω : Ω, ∀ k : ℕ,
        err ω (k + 1) =
          gamma * err ω k + ((gamma - Gamma) * scalar ω k + inputDiff ω k))
    (herr_int : ∀ k : ℕ, Integrable (fun ω : Ω => err ω k) μ)
    (hscalar_int : ∀ k : ℕ, Integrable (fun ω : Ω => scalar ω k) μ)
    (hinput_int : ∀ k : ℕ, Integrable (fun ω : Ω => inputDiff ω k) μ)
    (hinput_zero : ∀ k : ℕ, (∫ ω, inputDiff ω k ∂μ) = 0)
    (hscalar_mean :
      ∀ k : ℕ, (∫ ω, scalar ω k ∂μ) = x0 * Gamma ^ k) :
    ∀ k : ℕ,
      (∫ ω, err ω (k + 1) ∂μ) =
        gamma * (∫ ω, err ω k ∂μ) +
          (gamma - Gamma) * (x0 * Gamma ^ k) := by
  classical
  intro k
  have herrk_int : Integrable (fun ω : Ω => err ω k) μ :=
    herr_int k
  have hscalar_k_int : Integrable (fun ω : Ω => scalar ω k) μ :=
    hscalar_int k
  have hinput_k_int : Integrable (fun ω : Ω => inputDiff ω k) μ :=
    hinput_int k
  have hforcing_int :
      Integrable
        (fun ω : Ω => (gamma - Gamma) * scalar ω k + inputDiff ω k) μ :=
    (hscalar_k_int.const_mul (gamma - Gamma)).add hinput_k_int
  calc
    (∫ ω, err ω (k + 1) ∂μ) =
        ∫ ω,
          gamma * err ω k +
            ((gamma - Gamma) * scalar ω k + inputDiff ω k) ∂μ := by
          congr with ω
          rw [hrec ω k]
    _ =
        (∫ ω, gamma * err ω k ∂μ) +
          ∫ ω, (gamma - Gamma) * scalar ω k + inputDiff ω k ∂μ := by
          rw [MeasureTheory.integral_add]
          · exact herrk_int.const_mul gamma
          · exact hforcing_int
    _ =
        gamma * (∫ ω, err ω k ∂μ) +
          ((gamma - Gamma) * (∫ ω, scalar ω k ∂μ) +
            ∫ ω, inputDiff ω k ∂μ) := by
          rw [MeasureTheory.integral_const_mul]
          rw [MeasureTheory.integral_add]
          · rw [MeasureTheory.integral_const_mul]
          · exact hscalar_k_int.const_mul (gamma - Gamma)
          · exact hinput_k_int
    _ =
        gamma * (∫ ω, err ω k ∂μ) +
          (gamma - Gamma) * (x0 * Gamma ^ k) := by
          rw [hscalar_mean k, hinput_zero k]
          ring

/-- Deterministic absolute-value budget for the mean error in a scalar AR
comparison.

This is the C.3 coefficient-budget step after martingale cancellation has
already reduced the projected/scalar boundary discrepancy to a deterministic
recursion.  It keeps the remaining proof obligations separate: an initial
mean-error bound, plus the small multiplier-mismatch Duhamel sum. -/
theorem scalar_ar_mean_error_abs_le_initial_add_linear_forcing
    {gamma Gamma x0 Cmul alpha : ℝ}
    (hgamma_nonneg : 0 ≤ gamma) (hgamma_le_one : gamma ≤ 1)
    (hGamma_abs_le_one : ∀ k : ℕ, |Gamma ^ k| ≤ 1)
    (hcoeff : |gamma - Gamma| ≤ Cmul * alpha ^ 2)
    (hcoeff_nonneg : 0 ≤ Cmul * alpha ^ 2)
    (e : ℕ → ℝ)
    (hrec :
      ∀ k : ℕ, e (k + 1) =
        gamma * e k + (gamma - Gamma) * (x0 * Gamma ^ k)) :
    ∀ k : ℕ,
      |e k| ≤ |e 0| + (k : ℝ) * (Cmul * alpha ^ 2 * |x0|) := by
  classical
  intro k
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hstep :
          |e (k + 1)| ≤ gamma * |e k| +
              Cmul * alpha ^ 2 * |x0| := by
        calc
          |e (k + 1)| =
              |gamma * e k + (gamma - Gamma) * (x0 * Gamma ^ k)| := by
                rw [hrec k]
          _ ≤ |gamma * e k| +
              |(gamma - Gamma) * (x0 * Gamma ^ k)| :=
                abs_add_le _ _
          _ = gamma * |e k| +
              |gamma - Gamma| * (|Gamma ^ k| * |x0|) := by
                have hinner : |x0 * Gamma ^ k| = |Gamma ^ k| * |x0| := by
                  rw [abs_mul]
                  ring
                have hleft : |gamma * e k| = gamma * |e k| := by
                  rw [abs_mul, abs_of_nonneg hgamma_nonneg]
                have hright :
                    |(gamma - Gamma) * (x0 * Gamma ^ k)| =
                      |gamma - Gamma| * (|Gamma ^ k| * |x0|) := by
                  rw [abs_mul, hinner]
                rw [hleft, hright]
          _ ≤ gamma * |e k| +
              Cmul * alpha ^ 2 * |x0| := by
                have hx0_nonneg : 0 ≤ |x0| := abs_nonneg x0
                have hprod_nonneg : 0 ≤ |Gamma ^ k| * |x0| :=
                  mul_nonneg (abs_nonneg _) hx0_nonneg
                have hcoeff_part :
                    |gamma - Gamma| * (|Gamma ^ k| * |x0|) ≤
                      (Cmul * alpha ^ 2) * (|Gamma ^ k| * |x0|) :=
                  mul_le_mul_of_nonneg_right hcoeff hprod_nonneg
                have hgamma_part :
                    (Cmul * alpha ^ 2) * (|Gamma ^ k| * |x0|) ≤
                      (Cmul * alpha ^ 2) * |x0| :=
                  mul_le_mul_of_nonneg_left
                    (by
                      calc
                        |Gamma ^ k| * |x0| ≤ 1 * |x0| :=
                          mul_le_mul_of_nonneg_right
                            (hGamma_abs_le_one k) hx0_nonneg
                        _ = |x0| := by ring)
                    hcoeff_nonneg
                nlinarith [hcoeff_part, hgamma_part]
      have hcontract :
          gamma * |e k| ≤ |e k| :=
        calc
          gamma * |e k| ≤ 1 * |e k| :=
            mul_le_mul_of_nonneg_right hgamma_le_one (abs_nonneg _)
          _ = |e k| := by ring
      have hforcing_nonneg : 0 ≤ Cmul * alpha ^ 2 * |x0| :=
        mul_nonneg hcoeff_nonneg (abs_nonneg x0)
      calc
        |e (k + 1)| ≤ gamma * |e k| +
            Cmul * alpha ^ 2 * |x0| := hstep
        _ ≤ |e k| + Cmul * alpha ^ 2 * |x0| :=
            by linarith [hcontract]
        _ ≤
            (|e 0| + (k : ℝ) * (Cmul * alpha ^ 2 * |x0|)) +
              Cmul * alpha ^ 2 * |x0| :=
            by linarith
        _ = |e 0| + ((k + 1 : ℕ) : ℝ) *
              (Cmul * alpha ^ 2 * |x0|) := by
            norm_num
            ring

/-- Lipschitz bound for finite powers on `[0,1]`.

This is the scalar algebra needed in Appendix C.3 after the projected slow
recursion has been reduced to deterministic means: the restricted multiplier
`gamma` and the scalar multiplier `Gamma` differ by `O(alpha^2)`, hence their
`k`-th powers differ by at most `k` times that mismatch while both multipliers
remain contractions. -/
theorem real_abs_pow_sub_pow_le_nat_mul_abs_sub_of_nonneg_le_one
    {a b : ℝ} (ha_nonneg : 0 ≤ a) (ha_le_one : a ≤ 1)
    (hb_nonneg : 0 ≤ b) (hb_le_one : b ≤ 1) :
    ∀ k : ℕ, |a ^ k - b ^ k| ≤ (k : ℝ) * |a - b| := by
  classical
  intro k
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hb_pow_nonneg : 0 ≤ b ^ k := pow_nonneg hb_nonneg k
      have hb_pow_le_one : b ^ k ≤ 1 := pow_le_one₀ hb_nonneg hb_le_one
      have hsplit :
          a ^ (k + 1) - b ^ (k + 1) =
            a * (a ^ k - b ^ k) + (a - b) * b ^ k := by
        ring
      calc
        |a ^ (k + 1) - b ^ (k + 1)| =
            |a * (a ^ k - b ^ k) + (a - b) * b ^ k| := by
              rw [hsplit]
        _ ≤ |a * (a ^ k - b ^ k)| + |(a - b) * b ^ k| :=
            abs_add_le _ _
        _ = a * |a ^ k - b ^ k| + |a - b| * (b ^ k) := by
            rw [abs_mul, abs_mul, abs_of_nonneg ha_nonneg,
              abs_of_nonneg hb_pow_nonneg]
        _ ≤ |a ^ k - b ^ k| + |a - b| := by
            have hleft :
                a * |a ^ k - b ^ k| ≤ 1 * |a ^ k - b ^ k| :=
              mul_le_mul_of_nonneg_right ha_le_one
                (abs_nonneg (a ^ k - b ^ k))
            have hright :
                |a - b| * b ^ k ≤ |a - b| * 1 :=
              mul_le_mul_of_nonneg_left hb_pow_le_one (abs_nonneg (a - b))
            nlinarith
        _ ≤ (k : ℝ) * |a - b| + |a - b| := by
            linarith
        _ = ((k + 1 : ℕ) : ℝ) * |a - b| := by
            norm_num
            ring

/-- Appendix C.1 projected/scalar initial-boundary error budget.

At block zero the scalar comparison is exactly `x0`, while the alpha-zero
projected restricted average is the Perron-weighted initial consensus value,
also `x0`.  The only remaining dependence is the local `O(alpha)` movement of
the Riesz projection, hence the squared initial slow-coordinate error is
`O(alpha²)`. -/
theorem quadratic_restricted_projected_scalar_initial_error_l2_alpha2_bound
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
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ) :
    ∃ Cinit alphaInit : ℝ,
      0 ≤ Cinit ∧ 0 < alphaInit ∧ alphaInit ≤ alpha0 ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaInit →
          (∫ ω,
            |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                (matrixMulVector (Node := Sum Node {i : Node // i ≠ i0})
                  (P alpha)
                  (restrictedStateToCoord (Node := Node) i0
                    ((quad.withStepsize alpha).primalState
                        (oracle.noise ω) 0,
                      (quad.withStepsize alpha).trackerErrorZeroSum
                        (oracle.noise ω) 0))) -
              quad.quadraticScalarComparisonProcess lambda alpha
                (oracle.noise ω) 0| ^ 2 ∂μ) ≤
            Cinit * alpha ^ 2 := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  rcases hsplitting with
    ⟨halpha0_pos, _hr0theta, _htheta_lt_one, _hK_nonneg, _hgamma0,
      _hgamma_analytic, hP_analytic, _hderiv, _hlocal⟩
  have hP0_analytic : AnalyticAt ℝ P 0 :=
    hP_analytic 0 (by simpa using halpha0_pos)
  obtain ⟨deltaP, LP, hdeltaP_pos, hLP_nonneg, hP_lip⟩ :=
    analyticAt_matrix_operator_norm_sub_le_mul_near_zero
      (Node := Idx) P hP0_analytic
  obtain ⟨Cpath, alphaPath, hCpath_nonneg, halphaPath_pos,
      halphaPath_le_alpha0, hpath⟩ :=
    quadraticRestrictedStableComplement_initial_input_alpha_absolute_bound
      (Node := Node) quad i0 alpha0 deltaP LP P halpha0_pos
      hdeltaP_pos hLP_nonneg hP_lip
  let Cinit : ℝ := Cpath ^ 2
  refine ⟨Cinit, alphaPath, sq_nonneg Cpath, halphaPath_pos,
    halphaPath_le_alpha0, ?_⟩
  intro alpha halpha_pos halpha_le
  have hCα_nonneg : 0 ≤ Cpath * alpha :=
    mul_nonneg hCpath_nonneg halpha_pos.le
  have hpoint :
      ∀ ω : Ω,
        |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
            (matrixMulVector (Node := Idx)
              (P alpha)
              (restrictedStateToCoord (Node := Node) i0
                ((quad.withStepsize alpha).primalState
                    (oracle.noise ω) 0,
                  (quad.withStepsize alpha).trackerErrorZeroSum
                    (oracle.noise ω) 0))) -
          quad.quadraticScalarComparisonProcess lambda alpha
            (oracle.noise ω) 0| ≤
          Cpath * alpha := by
    intro ω
    let noise := oracle.noise ω
    let zraw : RowVector Idx :=
      restrictedStateToCoord (Node := Node) i0
        ((quad.withStepsize alpha).primalState noise 0,
          (quad.withStepsize alpha).trackerErrorZeroSum noise 0)
    let zbase : RowVector Idx :=
      restrictedStateToCoord (Node := Node) i0
        ((quad.withStepsize 0).primalState noise 0,
          (quad.withStepsize 0).trackerErrorZeroSum noise 0)
    let pα : RowVector Idx :=
      matrixMulVector (Node := Idx) (P alpha) zraw
    let p0 : RowVector Idx :=
      matrixMulVector (Node := Idx) (P 0) zbase
    have hzraw_base : zraw = zbase := by
      rw [show zraw =
          (fun a : Idx =>
            match a with
            | Sum.inl _ => quad.x0
            | Sum.inr _ => 0) by
        simpa [Idx, zraw] using
          quadraticRestrictedInitialBoundaryCoord_eq_const
            (Node := Node) quad alpha i0 noise]
      rw [show zbase =
          (fun a : Idx =>
            match a with
            | Sum.inl _ => quad.x0
            | Sum.inr _ => 0) by
        simpa [Idx, zbase] using
          quadraticRestrictedInitialBoundaryCoord_alpha_zero
            (Node := Node) quad i0 noise]
    have hbase_output :
        quadraticRestrictedPrimalAverageOutput (Node := Node) i0 p0 =
          quad.x0 := by
      have hweighted :
          weightedState (Node := Idx) (E := ℝ)
              (rowMulMatrix (Node := Idx)
                (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
                (P 0)) zbase =
            weightedState (Node := Node) (E := ℝ)
              (quad.perronLeft (quad.blockStart (0 + 1)))
              ((quad.withStepsize 0).primalState noise 0) := by
        simpa [Idx, zbase] using
          quadraticRestrictedPrimalAverageProjectedRow_alpha_zero_weighted_eq_endpoint_perron
            (Node := Node) quad i0 right left P hP0 hright_top
            hleft_top hleft_bottom 0
            ((quad.withStepsize 0).primalState noise 0,
              (quad.withStepsize 0).trackerErrorZeroSum noise 0)
      have hperron_init :
          weightedState (Node := Node) (E := ℝ)
              (quad.perronLeft (quad.blockStart (0 + 1)))
              ((quad.withStepsize 0).primalState noise 0) =
            quad.x0 := by
        have hperron_block :
            quad.perronLeft (quad.blockStart (0 + 1)) =
              quad.perronLeft 0 := by
          simpa using quad.perronLeft_blockStart_add 1 0
        rw [hperron_block]
        calc
          weightedState (Node := Node) (E := ℝ) (quad.perronLeft 0)
              ((quad.withStepsize 0).primalState noise 0) =
              (∑ i : Node, quad.perronLeft 0 i * quad.x0) := by
                simp [weightedState, withStepsize, primalState_zero,
                  initialPrimal, smul_eq_mul]
          _ = quad.x0 := by
                rw [← Finset.sum_mul]
                simpa [rowSum] using congrArg (fun y : ℝ => y * quad.x0)
                  (quad.perronLeft_sum 0)
      have hrow_apply :
          quadraticRestrictedPrimalAverageOutput (Node := Node) i0 p0 =
            weightedState (Node := Idx) (E := ℝ)
              (rowMulMatrix (Node := Idx)
                (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
                (P 0)) zbase := by
        calc
          quadraticRestrictedPrimalAverageOutput (Node := Node) i0 p0 =
              weightedState (Node := Idx) (E := ℝ)
                (quadraticRestrictedPrimalAverageRow (Node := Node) i0) p0 :=
                quadraticRestrictedPrimalAverageOutput_eq_weightedState
                  (Node := Node) i0 p0
          _ =
              weightedState (Node := Idx) (E := ℝ)
                (rowMulMatrix (Node := Idx)
                  (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
                  (P 0)) zbase := by
                symm
                simpa [p0, leftMul] using
                  weightedState_rowMulMatrix
                    (Node := Idx) (E := ℝ)
                    (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
                    (P 0) zbase
      rw [hrow_apply, hweighted, hperron_init]
    have hscalar0 :
        quad.quadraticScalarComparisonProcess lambda alpha noise 0 =
          quad.x0 :=
      quadraticScalarComparisonProcess_zero
        (Node := Node) quad lambda alpha noise
    have hstable_bound := hpath alpha halpha_pos halpha_le noise
    have hproj_diff_norm :
        rowEuclideanNorm (Node := Idx) (fun a => pα a - p0 a) ≤
          Cpath * alpha := by
      have hstable_eq :
          (fun a : Idx =>
              spectralStableComplementVector (Node := Idx) (P alpha) zraw a -
                spectralStableComplementVector (Node := Idx) (P 0) zbase a) =
            fun a : Idx => -(pα a - p0 a) := by
        funext a
        simp [spectralStableComplementVector, pα, p0, hzraw_base]
      have hnorm_eq :
          rowEuclideanNorm (Node := Idx) (fun a => pα a - p0 a) =
            rowEuclideanNorm (Node := Idx)
              (fun a : Idx =>
                spectralStableComplementVector (Node := Idx) (P alpha) zraw a -
                  spectralStableComplementVector (Node := Idx) (P 0) zbase a) := by
        rw [hstable_eq]
        symm
        exact rowEuclideanNorm_neg (Node := Idx) (fun a => pα a - p0 a)
      rw [hnorm_eq]
      simpa [Idx, zraw, zbase] using hstable_bound
    have houtput_diff :
        quadraticRestrictedPrimalAverageOutput (Node := Node) i0 pα -
            quadraticRestrictedPrimalAverageOutput (Node := Node) i0 p0 =
          quadraticRestrictedPrimalAverageOutput (Node := Node) i0
            (fun a : Idx => pα a - p0 a) := by
      unfold quadraticRestrictedPrimalAverageOutput
      simp only [Finset.sum_sub_distrib]
      ring
    calc
      |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
            (matrixMulVector (Node := Idx) (P alpha)
              (restrictedStateToCoord (Node := Node) i0
                ((quad.withStepsize alpha).primalState
                    (oracle.noise ω) 0,
                  (quad.withStepsize alpha).trackerErrorZeroSum
                    (oracle.noise ω) 0))) -
          quad.quadraticScalarComparisonProcess lambda alpha
            (oracle.noise ω) 0| =
          |quadraticRestrictedPrimalAverageOutput (Node := Node) i0 pα -
            quadraticRestrictedPrimalAverageOutput (Node := Node) i0 p0| := by
            simp [noise, zraw, pα, hbase_output, hscalar0]
      _ =
          |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
            (fun a : Idx => pα a - p0 a)| := by rw [houtput_diff]
      _ ≤
          rowEuclideanNorm (Node := Idx) (fun a : Idx => pα a - p0 a) :=
          quadraticRestrictedPrimalAverageOutput_abs_le_rowEuclideanNorm
            (Node := Node) i0 (fun a : Idx => pα a - p0 a)
      _ ≤ Cpath * alpha := hproj_diff_norm
  have hpoint_sq :
      ∀ ω : Ω,
        |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
            (matrixMulVector (Node := Idx)
              (P alpha)
              (restrictedStateToCoord (Node := Node) i0
                ((quad.withStepsize alpha).primalState
                    (oracle.noise ω) 0,
                  (quad.withStepsize alpha).trackerErrorZeroSum
                    (oracle.noise ω) 0))) -
          quad.quadraticScalarComparisonProcess lambda alpha
            (oracle.noise ω) 0| ^ 2 ≤
          (Cpath * alpha) ^ 2 := by
    intro ω
    exact pow_le_pow_left₀
      (abs_nonneg
        (quadraticRestrictedPrimalAverageOutput (Node := Node) i0
          (matrixMulVector (Node := Idx) (P alpha)
            (restrictedStateToCoord (Node := Node) i0
              ((quad.withStepsize alpha).primalState
                  (oracle.noise ω) 0,
                (quad.withStepsize alpha).trackerErrorZeroSum
                  (oracle.noise ω) 0))) -
        quad.quadraticScalarComparisonProcess lambda alpha
          (oracle.noise ω) 0))
      (hpoint ω) 2
  have hconst_int :
      Integrable (fun _ : Ω => (Cpath * alpha) ^ 2) μ :=
    integrable_const _
  have herr_fun_const :
      (fun ω : Ω =>
          |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
              (matrixMulVector (Node := Idx)
                (P alpha)
                (restrictedStateToCoord (Node := Node) i0
                  ((quad.withStepsize alpha).primalState
                      (oracle.noise ω) 0,
                    (quad.withStepsize alpha).trackerErrorZeroSum
                      (oracle.noise ω) 0))) -
            quad.quadraticScalarComparisonProcess lambda alpha
              (oracle.noise ω) 0| ^ 2) =
        fun _ : Ω =>
          |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
              (matrixMulVector (Node := Idx)
                (P alpha)
                (fun a : Idx =>
                  match a with
                  | Sum.inl _ => quad.x0
                  | Sum.inr _ => 0)) -
            quad.x0| ^ 2 := by
    funext ω
    rw [quadraticScalarComparisonProcess_zero
      (Node := Node) quad lambda alpha (oracle.noise ω)]
    rw [show
        restrictedStateToCoord (Node := Node) i0
          ((quad.withStepsize alpha).primalState (oracle.noise ω) 0,
            (quad.withStepsize alpha).trackerErrorZeroSum
              (oracle.noise ω) 0) =
          (fun a : Idx =>
            match a with
            | Sum.inl _ => quad.x0
            | Sum.inr _ => 0) by
        simpa [Idx] using
          quadraticRestrictedInitialBoundaryCoord_eq_const
            (Node := Node) quad alpha i0 (oracle.noise ω)]
  have herr_int :
      Integrable
        (fun ω : Ω =>
          |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
              (matrixMulVector (Node := Idx)
                (P alpha)
                (restrictedStateToCoord (Node := Node) i0
                  ((quad.withStepsize alpha).primalState
                      (oracle.noise ω) 0,
                    (quad.withStepsize alpha).trackerErrorZeroSum
                      (oracle.noise ω) 0))) -
            quad.quadraticScalarComparisonProcess lambda alpha
              (oracle.noise ω) 0| ^ 2) μ := by
    rw [herr_fun_const]
    exact integrable_const _
  calc
    (∫ ω,
        |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
            (matrixMulVector (Node := Idx)
              (P alpha)
              (restrictedStateToCoord (Node := Node) i0
                ((quad.withStepsize alpha).primalState
                    (oracle.noise ω) 0,
                  (quad.withStepsize alpha).trackerErrorZeroSum
                    (oracle.noise ω) 0))) -
          quad.quadraticScalarComparisonProcess lambda alpha
            (oracle.noise ω) 0| ^ 2 ∂μ) ≤
        ∫ _ω : Ω, (Cpath * alpha) ^ 2 ∂μ :=
          MeasureTheory.integral_mono_ae herr_int hconst_int
            (Filter.Eventually.of_forall hpoint_sq)
    _ = Cinit * alpha ^ 2 := by
        rw [MeasureTheory.integral_const]
        simp [Cinit]
        ring

/-- Appendix C.1 all-time slow/scalar error is square-integrable at every
fixed time.

This is only the regularity clause of the slow comparison theorem.  The
quantitative `O(alpha^2)` average remains the finite-phase propagation step. -/
theorem quadratic_restricted_slow_output_scalar_error_sq_integrable
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (P F : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (alpha : ℝ) (t : ℕ) :
    Integrable
      (fun ω : Ω =>
        |((quad.withStepsize alpha).averageIterate (oracle.noise ω) t -
            quadraticRestrictedPrimalAverageOutput (Node := Node) i0
              (quadraticRestrictedStableBoundaryResponse
                (Node := Node) quad lambda i0 P F alpha
                (oracle.noise ω) t)) -
          quad.quadraticScalarComparisonProcess lambda alpha
            (oracle.noise ω) t| ^ 2) μ := by
  classical
  let stepped := quad.withStepsize alpha
  have hstepped_oracle :
      stepped.StochasticOracleAssumptions μ oracle := by
    simpa [stepped, StochasticOracleAssumptions, withStepsize] using hnoise.1
  have hgenerated :=
    stepped.generated_pushpull_coordinate_memLp μ oracle hstepped_oracle t
  have havg_mem :
      MemLp
        (fun ω : Ω =>
          stepped.averageIterate (oracle.noise ω) t) 2 μ := by
    have hsum :
        MemLp
          (fun ω : Ω =>
            ∑ i : Node,
              stepped.primalState (oracle.noise ω) t i) 2 μ := by
      apply memLp_finset_sum Finset.univ
      intro i _hi
      exact hgenerated.1 i
    simpa [averageIterate, arithmeticAverage] using
      hsum.const_smul ((nodeCount (Node := Node) : ℝ)⁻¹)
  have hstable_mem :
      MemLp
        (fun ω : Ω =>
          quadraticRestrictedPrimalAverageOutput (Node := Node) i0
            (quadraticRestrictedStableBoundaryResponse
              (Node := Node) quad lambda i0 P F alpha
              (oracle.noise ω) t)) 2 μ :=
    quadraticRestrictedStableBoundaryResponse_output_memLp_two
      (Node := Node) quad lambda i0 P F μ oracle hnoise alpha t
  have hscalar_mem :
      MemLp
        (fun ω : Ω =>
          quad.quadraticScalarComparisonProcess lambda alpha
            (oracle.noise ω) t) 2 μ :=
    quadraticScalarComparisonProcess_memLp_two
      (Node := Node) quad lambda alpha μ oracle hnoise.1 t
  have hdiff_mem :
      MemLp
        (fun ω : Ω =>
          (stepped.averageIterate (oracle.noise ω) t -
              quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                (quadraticRestrictedStableBoundaryResponse
                  (Node := Node) quad lambda i0 P F alpha
                  (oracle.noise ω) t)) -
            quad.quadraticScalarComparisonProcess lambda alpha
              (oracle.noise ω) t) 2 μ :=
    (havg_mem.sub hstable_mem).sub hscalar_mem
  simpa [stepped] using real_abs_sq_integrable_of_memLp_two hdiff_mem

/-- Block-start C.1 step-7 square aggregation.

If the true block-start average decomposes into projected/scalar error,
stable response, and scalar boundary, then the three component square budgets
give a linear square budget for the true block-start average. -/
theorem block_start_average_l2_sum_bound_of_projected_stable_scalar_components
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (actual projected stable scalar : Ω → ℕ → ℝ)
    (hactual_int :
      ∀ k : ℕ, Integrable (fun ω : Ω => |actual ω k| ^ 2) μ)
    (herr_int :
      ∀ k : ℕ,
        Integrable (fun ω : Ω => |projected ω k - scalar ω k| ^ 2) μ)
    (hstable_int :
      ∀ k : ℕ, Integrable (fun ω : Ω => |stable ω k| ^ 2) μ)
    (hscalar_int :
      ∀ k : ℕ, Integrable (fun ω : Ω => |scalar ω k| ^ 2) μ)
    (hdecomp :
      ∀ (ω : Ω) (k : ℕ),
        actual ω k = (projected ω k - scalar ω k) + stable ω k + scalar ω k)
    {T : ℕ} {Cerr Cstable Cscalar : ℝ}
    (herr_sum_bound :
      Finset.sum (Finset.range T) (fun k =>
        ∫ ω, |projected ω k - scalar ω k| ^ 2 ∂μ) ≤
        Cerr * (T : ℝ))
    (hstable_sum_bound :
      Finset.sum (Finset.range T) (fun k =>
        ∫ ω, |stable ω k| ^ 2 ∂μ) ≤
        Cstable * (T : ℝ))
    (hscalar_sum_bound :
      Finset.sum (Finset.range T) (fun k =>
        ∫ ω, |scalar ω k| ^ 2 ∂μ) ≤
        Cscalar * (T : ℝ)) :
    Finset.sum (Finset.range T) (fun k =>
      ∫ ω, |actual ω k| ^ 2 ∂μ) ≤
      (2 * Cerr + 4 * Cstable + 4 * Cscalar) * (T : ℝ) := by
  classical
  have hper_time :
      ∀ k : ℕ,
        (∫ ω, |actual ω k| ^ 2 ∂μ) ≤
          2 * (∫ ω, |projected ω k - scalar ω k| ^ 2 ∂μ) +
            (4 * (∫ ω, |stable ω k| ^ 2 ∂μ) +
              4 * (∫ ω, |scalar ω k| ^ 2 ∂μ)) := by
    intro k
    let A : Ω → ℝ := fun ω => |actual ω k| ^ 2
    let B : Ω → ℝ := fun ω => |projected ω k - scalar ω k| ^ 2
    let C : Ω → ℝ := fun ω => |stable ω k| ^ 2
    let D : Ω → ℝ := fun ω => |scalar ω k| ^ 2
    let U : Ω → ℝ := fun ω => 2 * B ω + (4 * C ω + 4 * D ω)
    have hU_int : Integrable U μ :=
      ((herr_int k).const_mul 2).add
        (((hstable_int k).const_mul 4).add
          ((hscalar_int k).const_mul 4))
    have hpoint : A ≤ U := by
      intro ω
      have hfirst :=
        real_abs_add_sq_le_two_sq (projected ω k - scalar ω k)
          (stable ω k + scalar ω k)
      have hsecond := real_abs_add_sq_le_two_sq (stable ω k) (scalar ω k)
      have hrewrite :
          actual ω k =
            (projected ω k - scalar ω k) + (stable ω k + scalar ω k) := by
        rw [hdecomp ω k]
        ring
      dsimp [A, B, C, D, U]
      rw [hrewrite]
      nlinarith
    have hmono :
        (∫ ω, A ω ∂μ) ≤ ∫ ω, U ω ∂μ :=
      MeasureTheory.integral_mono (hactual_int k) hU_int hpoint
    calc
      (∫ ω, |actual ω k| ^ 2 ∂μ) = ∫ ω, A ω ∂μ := by rfl
      _ ≤ ∫ ω, U ω ∂μ := hmono
      _ =
          2 * (∫ ω, B ω ∂μ) +
            (4 * (∫ ω, C ω ∂μ) +
              4 * (∫ ω, D ω ∂μ)) := by
            dsimp [U]
            rw [MeasureTheory.integral_add]
            · rw [MeasureTheory.integral_add]
              · rw [MeasureTheory.integral_const_mul]
                rw [MeasureTheory.integral_const_mul]
                rw [MeasureTheory.integral_const_mul]
              · exact (hstable_int k).const_mul 4
              · exact (hscalar_int k).const_mul 4
            · exact (herr_int k).const_mul 2
            · exact ((hstable_int k).const_mul 4).add
                ((hscalar_int k).const_mul 4)
      _ =
          2 * (∫ ω, |projected ω k - scalar ω k| ^ 2 ∂μ) +
            (4 * (∫ ω, |stable ω k| ^ 2 ∂μ) +
              4 * (∫ ω, |scalar ω k| ^ 2 ∂μ)) := by rfl
  have hsum :
      Finset.sum (Finset.range T) (fun k =>
          ∫ ω, |actual ω k| ^ 2 ∂μ) ≤
        Finset.sum (Finset.range T) (fun k =>
          2 * (∫ ω, |projected ω k - scalar ω k| ^ 2 ∂μ) +
            (4 * (∫ ω, |stable ω k| ^ 2 ∂μ) +
              4 * (∫ ω, |scalar ω k| ^ 2 ∂μ))) :=
    Finset.sum_le_sum fun k _hk => hper_time k
  calc
    Finset.sum (Finset.range T) (fun k =>
        ∫ ω, |actual ω k| ^ 2 ∂μ) ≤
      Finset.sum (Finset.range T) (fun k =>
        2 * (∫ ω, |projected ω k - scalar ω k| ^ 2 ∂μ) +
          (4 * (∫ ω, |stable ω k| ^ 2 ∂μ) +
            4 * (∫ ω, |scalar ω k| ^ 2 ∂μ))) := hsum
    _ =
      2 * Finset.sum (Finset.range T) (fun k =>
          ∫ ω, |projected ω k - scalar ω k| ^ 2 ∂μ) +
        4 * Finset.sum (Finset.range T) (fun k =>
          ∫ ω, |stable ω k| ^ 2 ∂μ) +
        4 * Finset.sum (Finset.range T) (fun k =>
          ∫ ω, |scalar ω k| ^ 2 ∂μ) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
        ring
    _ ≤ (2 * Cerr + 4 * Cstable + 4 * Cscalar) * (T : ℝ) := by
        nlinarith [herr_sum_bound, hstable_sum_bound, hscalar_sum_bound]

/-- Homogeneous quadratic gradient transport from block-start average L² to
block-gradient energy. -/
theorem blockGradientEnergy_le_linear_average_block_start_l2_of_havg_linear
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (havg_linear : ∀ x : ℝ, quad.averageGradient x = lambda * x)
    {alpha Cavg : ℝ} {T : ℕ}
    (havg_sum_bound :
      Finset.sum (Finset.range T) (fun k =>
        ∫ ω,
          |(quad.withStepsize alpha).averageIterate
              (oracle.noise ω) (k * quad.period)| ^ 2 ∂μ) ≤
        Cavg * (T : ℝ)) :
    (quad.withStepsize alpha).blockGradientEnergy μ oracle T ≤
      (lambda ^ 2 * Cavg) * (T : ℝ) := by
  classical
  let stepped := quad.withStepsize alpha
  have hterm :
      ∀ k : ℕ,
        (∫ ω, ‖stepped.blockAverageGradient (oracle.noise ω) k‖ ^ 2 ∂μ) =
          lambda ^ 2 *
            (∫ ω, |stepped.averageIterate
                (oracle.noise ω) (k * quad.period)| ^ 2 ∂μ) := by
    intro k
    have hfun :
        (fun ω : Ω =>
          ‖stepped.blockAverageGradient (oracle.noise ω) k‖ ^ 2) =
        fun ω : Ω =>
          lambda ^ 2 *
            |stepped.averageIterate
              (oracle.noise ω) (k * quad.period)| ^ 2 := by
      funext ω
      have hgrad :
          stepped.blockAverageGradient (oracle.noise ω) k =
            lambda *
              stepped.averageIterate (oracle.noise ω) (k * quad.period) := by
        rw [blockAverageGradient]
        change stepped.averageGradient
            (stepped.averageIterate (oracle.noise ω) (stepped.blockStart k)) =
          lambda *
            stepped.averageIterate (oracle.noise ω) (k * quad.period)
        have hstart : stepped.blockStart k = k * quad.period := by
          simp [stepped, withStepsize, blockStart]
        rw [hstart]
        change quad.averageGradient
            (stepped.averageIterate (oracle.noise ω) (k * quad.period)) =
          lambda *
            stepped.averageIterate (oracle.noise ω) (k * quad.period)
        exact havg_linear _
      rw [hgrad]
      simp [Real.norm_eq_abs, abs_mul, mul_pow, sq_abs]
    rw [hfun]
    rw [MeasureTheory.integral_const_mul]
  calc
    (quad.withStepsize alpha).blockGradientEnergy μ oracle T =
        Finset.sum (Finset.range T) (fun k =>
          ∫ ω, ‖stepped.blockAverageGradient (oracle.noise ω) k‖ ^ 2 ∂μ) := by
        simp [stepped, blockGradientEnergy]
    _ =
        Finset.sum (Finset.range T) (fun k =>
          lambda ^ 2 *
            (∫ ω, |stepped.averageIterate
                (oracle.noise ω) (k * quad.period)| ^ 2 ∂μ)) := by
        exact Finset.sum_congr rfl fun k _hk => hterm k
    _ =
        lambda ^ 2 *
          Finset.sum (Finset.range T) (fun k =>
            ∫ ω, |stepped.averageIterate
                (oracle.noise ω) (k * quad.period)| ^ 2 ∂μ) := by
        rw [Finset.mul_sum]
    _ ≤ lambda ^ 2 * (Cavg * (T : ℝ)) :=
        mul_le_mul_of_nonneg_left (by simpa [stepped] using havg_sum_bound)
          (sq_nonneg lambda)
    _ = (lambda ^ 2 * Cavg) * (T : ℝ) := by ring

set_option maxHeartbeats 2000000 in
/-- Appendix C.1 step 6, isolated at the source proof granularity.

The slow output is the true averaged quadratic output after subtracting the
canonical projected stable boundary output.  The remaining proof obligation is
the printed Duhamel comparison between this slow recursion and the scalar
process: the period multiplier and phase-noise coefficient errors are
`O(alpha^2)`, giving an averaged `O(alpha^2)` square error on
`alpha * T >= 1`. -/
theorem quadratic_restricted_slow_output_scalar_average_l2_bound
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (r0 alpha_restricted theta K : ℝ)
    (right left : RowVector (Sum Node {i : Node // i ≠ i0}))
    (gamma : ℝ → ℝ)
    (P F : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hP0 :
      P 0 = (fun i j : Sum Node {i : Node // i ≠ i0} => right i * left j))
    (hright_eq :
      right =
        quadraticRestrictedAlphaZeroRightVector
          (Node := Node) quad lambda i0 0)
    (hright_top : ∀ i : Node, right (Sum.inl i) = 1)
    (hleft_top : ∀ i : Node, left (Sum.inl i) = quad.perronLeft 0 i)
    (hleft_bottom : ∀ j : {i : Node // i ≠ i0}, left (Sum.inr j) = 0)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (hgrad_linear :
      ∀ i : Node, ∀ x : ℝ, quad.componentGradient i x = lambda * x)
    (havg_linear :
      ∀ x : ℝ, quad.averageGradient x = lambda * x)
    (toRestrictedCoord :
      State Node ℝ × ZeroSumState Node ℝ →
        RowVector (Sum Node {i : Node // i ≠ i0}))
    (ofRestrictedCoord :
      RowVector (Sum Node {i : Node // i ≠ i0}) →
        State Node ℝ × ZeroSumState Node ℝ)
    (hrestrictedCoord_left :
      ∀ S : State Node ℝ × ZeroSumState Node ℝ,
        ofRestrictedCoord (toRestrictedCoord S) = S)
    (hrestrictedCoord_right :
      ∀ y : RowVector (Sum Node {i : Node // i ≠ i0}),
        toRestrictedCoord (ofRestrictedCoord y) = y)
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
    (hsplitting_restricted :
      PeriodicSpectralSplitting
        (Node := Sum Node {i : Node // i ≠ i0})
        (fun alpha => quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda alpha i0)
        r0 alpha_restricted theta K right left gamma P F)
    (hrestricted_splitting_at :
      ∀ alpha : ℝ, |alpha| ≤ alpha_restricted →
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
                    K * theta ^ j)
    (hstable_output_average_l2 :
      ∃ Cstable alphaStable : ℝ,
        0 < Cstable ∧ 0 < alphaStable ∧
          ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaStable →
            ∀ T : ℕ, 1 ≤ T →
              ((T : ℝ)⁻¹) *
                Finset.sum (Finset.range T) (fun t =>
                  ∫ ω,
                    |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                        (quadraticRestrictedStableBoundaryResponse
                          (Node := Node) quad lambda i0 P F alpha
                          (oracle.noise ω) t)| ^ 2 ∂μ) ≤
                Cstable * alpha ^ 2) :
    let slowOutput : ℝ → Ω → ℕ → ℝ := fun alpha ω t =>
      (quad.withStepsize alpha).averageIterate (oracle.noise ω) t -
        quadraticRestrictedPrimalAverageOutput (Node := Node) i0
          (quadraticRestrictedStableBoundaryResponse
            (Node := Node) quad lambda i0 P F alpha (oracle.noise ω) t)
    ∃ Cslow alphaSlow : ℝ,
      0 < Cslow ∧ 0 < alphaSlow ∧
        (∀ alpha : ℝ, ∀ t : ℕ,
          Integrable
            (fun ω : Ω =>
              |slowOutput alpha ω t -
                quad.quadraticScalarComparisonProcess lambda alpha
                  (oracle.noise ω) t| ^ 2) μ) ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaSlow →
          ∀ T : ℕ, 1 ≤ alpha * (T : ℝ) →
            ((T : ℝ)⁻¹) *
              Finset.sum (Finset.range T) (fun t =>
                ∫ ω,
                  |slowOutput alpha ω t -
                    quad.quadraticScalarComparisonProcess lambda alpha
                      (oracle.noise ω) t| ^ 2 ∂μ) ≤
              Cslow * alpha ^ 2 := by
  classical
  /- Direct proof attempt setup: these are exactly the source step-6 inputs.
  The remaining hard subgoal is the coefficient-error Duhamel estimate:
  compare the scalar coordinate of the `P alpha` period recursion with
  `quadraticScalarComparisonProcess`, using the `O(alpha^2)` multiplier and
  phase-noise coefficient remainders from Appendix C.1. -/
  have _hperiod := hrestricted_period_boundary_recursion
  have _hsplit := hrestricted_splitting_at
  have _hsplitting := hsplitting_restricted
  have _hgrad := hgrad_linear
  have _havg := havg_linear
  have _hcoord_left := hrestrictedCoord_left
  have _hcoord_right := hrestrictedCoord_right
  have _hnoise := hnoise
  have _hP0 := hP0
  have _hright_top := hright_top
  have _hleft_top := hleft_top
  have _hleft_bottom := hleft_bottom
  have hprojected_boundary_recursion :
      ∀ alpha : ℝ, |alpha| ≤ alpha_restricted →
        ∀ noise : NoisePath Node ℝ, ∀ k : ℕ,
          let stepped := quad.withStepsize alpha
          let yk : RowVector (Sum Node {i : Node // i ≠ i0}) :=
            restrictedStateToCoord (Node := Node) i0
              (stepped.primalState noise (k * quad.period),
                stepped.trackerErrorZeroSum noise (k * quad.period))
          let yNext : RowVector (Sum Node {i : Node // i ≠ i0}) :=
            restrictedStateToCoord (Node := Node) i0
              (stepped.primalState noise ((k + 1) * quad.period),
                stepped.trackerErrorZeroSum noise ((k + 1) * quad.period))
          let xi : RowVector (Sum Node {i : Node // i ≠ i0}) :=
            quadraticRestrictedPeriodNoiseInnovationCoord
              (Node := Node) quad lambda alpha i0 noise k
          quadraticRestrictedPrimalAverageOutput (Node := Node) i0
              (matrixMulVector (Node := Sum Node {i : Node // i ≠ i0})
                (P alpha) yNext) =
            gamma alpha *
              quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                (matrixMulVector (Node := Sum Node {i : Node // i ≠ i0})
                  (P alpha) yk) +
              quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                (matrixMulVector (Node := Sum Node {i : Node // i ≠ i0})
                  (P alpha) xi) := by
    intro alpha halpha_abs noise k
    let Idx := Sum Node {i : Node // i ≠ i0}
    let stepped := quad.withStepsize alpha
    let yk : RowVector Idx :=
      restrictedStateToCoord (Node := Node) i0
        (stepped.primalState noise (k * quad.period),
          stepped.trackerErrorZeroSum noise (k * quad.period))
    let yNext : RowVector Idx :=
      restrictedStateToCoord (Node := Node) i0
        (stepped.primalState noise ((k + 1) * quad.period),
          stepped.trackerErrorZeroSum noise ((k + 1) * quad.period))
    let xi : RowVector Idx :=
      quadraticRestrictedPeriodNoiseInnovationCoord
        (Node := Node) quad lambda alpha i0 noise k
    have hlocal := hrestricted_splitting_at alpha halpha_abs
    have hyNext :
        yNext =
          matrixMulVector (Node := Idx)
            (quadraticRestrictedPeriodMatrix (Node := Node)
              quad lambda alpha i0) yk + xi := by
      simpa [Idx, stepped, yk, yNext, xi] using
        hrestricted_period_boundary_recursion alpha noise k
    exact
      quadratic_restricted_projected_slow_boundary_recursion
        (Node := Node) i0 (gamma alpha) (P alpha) (F alpha)
        (quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda alpha i0)
        hlocal.1.1.1 hlocal.2.1 hlocal.2.2.1
        yk xi yNext hyNext
  have _hprojected_boundary_recursion := hprojected_boundary_recursion
  have hprojected_average_row_left_eigen :
      ∀ alpha : ℝ, |alpha| ≤ alpha_restricted →
        rowMulMatrix
            (Node := Sum Node {i : Node // i ≠ i0})
            (rowMulMatrix
              (Node := Sum Node {i : Node // i ≠ i0})
              (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
              (P alpha))
            (quadraticRestrictedPeriodMatrix (Node := Node)
              quad lambda alpha i0) =
          gamma alpha •
            rowMulMatrix
              (Node := Sum Node {i : Node // i ≠ i0})
              (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
              (P alpha) := by
    intro alpha halpha_abs
    exact
      quadraticRestrictedPrimalAverageProjectedRow_left_eigen
        (Node := Node) i0 (gamma alpha)
        (quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda alpha i0)
        (P alpha)
        (hrestricted_splitting_at alpha halpha_abs).1
  have _hprojected_average_row_left_eigen :=
    hprojected_average_row_left_eigen
  have hprojected_average_row_left_eigen_eventually :
      ∀ᶠ alpha : ℝ in 𝓝 0,
        rowMulMatrix
            (Node := Sum Node {i : Node // i ≠ i0})
            (rowMulMatrix
              (Node := Sum Node {i : Node // i ≠ i0})
              (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
              (P alpha))
            (quadraticRestrictedPeriodMatrix (Node := Node)
              quad lambda alpha i0) =
          gamma alpha •
            rowMulMatrix
              (Node := Sum Node {i : Node // i ≠ i0})
              (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
              (P alpha) := by
    have halpha_restricted_pos : 0 < alpha_restricted := by
      rcases hsplitting_restricted with
        ⟨halpha0_pos, _hr0theta, _htheta_lt_one, _hK_nonneg, _hgamma0,
          _hgamma_analytic, _hP_analytic, _hderiv, _hlocal⟩
      exact halpha0_pos
    have hsmall :
        ∀ᶠ alpha : ℝ in 𝓝 0, |alpha| ≤ alpha_restricted := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) halpha_restricted_pos]
        with alpha hdist
      have hlt : |alpha| < alpha_restricted := by
        simpa [Real.dist_eq] using hdist
      exact le_of_lt hlt
    filter_upwards [hsmall] with alpha halpha
    exact hprojected_average_row_left_eigen alpha halpha
  have _hprojected_average_row_left_eigen_eventually :=
    hprojected_average_row_left_eigen_eventually
  have hprojected_average_row_derivative_left_eigen_pairing :
      ∀ rowDeriv : RowVector (Sum Node {i : Node // i ≠ i0}),
        HasDerivAt
          (fun alpha : ℝ =>
            rowMulMatrix (Node := Sum Node {i : Node // i ≠ i0})
              (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
              (P alpha))
          rowDeriv 0 →
        ∀ Aderiv : NodeMatrix (Sum Node {i : Node // i ≠ i0}),
          HasDerivAt
            (fun alpha : ℝ =>
              quadraticRestrictedPeriodMatrix (Node := Node)
                quad lambda alpha i0)
            Aderiv 0 →
        ∀ gammaDeriv : ℝ,
          HasDerivAt gamma gammaDeriv 0 →
        ∀ z : RowVector (Sum Node {i : Node // i ≠ i0}),
          weightedState (Node := Sum Node {i : Node // i ≠ i0}) (E := ℝ)
              rowDeriv
              (matrixMulVector (Node := Sum Node {i : Node // i ≠ i0})
                (quadraticRestrictedPeriodMatrix (Node := Node)
                  quad lambda 0 i0) z) +
            weightedState (Node := Sum Node {i : Node // i ≠ i0}) (E := ℝ)
              (rowMulMatrix (Node := Sum Node {i : Node // i ≠ i0})
                (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
                (P 0))
              (matrixMulVector (Node := Sum Node {i : Node // i ≠ i0})
                Aderiv z) =
              gammaDeriv *
                weightedState (Node := Sum Node {i : Node // i ≠ i0})
                  (E := ℝ)
                  (rowMulMatrix (Node := Sum Node {i : Node // i ≠ i0})
                    (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
                    (P 0)) z +
                weightedState (Node := Sum Node {i : Node // i ≠ i0})
                  (E := ℝ) rowDeriv z := by
    intro rowDeriv hrow Aderiv hAderiv gammaDeriv hgammaDeriv z
    have hgamma0 : gamma 0 = 1 := by
      rcases hsplitting_restricted with
        ⟨_halpha0_pos, _hr0theta, _htheta_lt_one, _hK_nonneg, hgamma0,
          _hgamma_analytic, _hP_analytic, _hderiv, _hlocal⟩
      exact hgamma0
    exact
      weightedState_left_eigenrow_derivative_pairing
        (Node := Sum Node {i : Node // i ≠ i0})
        (fun alpha : ℝ =>
          quadraticRestrictedPeriodMatrix (Node := Node)
            quad lambda alpha i0)
        gamma
        (fun alpha : ℝ =>
          rowMulMatrix (Node := Sum Node {i : Node // i ≠ i0})
            (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
            (P alpha))
        Aderiv gammaDeriv rowDeriv hAderiv hgammaDeriv hrow hgamma0
        hprojected_average_row_left_eigen_eventually z
  have _hprojected_average_row_derivative_left_eigen_pairing :=
    hprojected_average_row_derivative_left_eigen_pairing
  have hperiod_matrix_tracker_deriv_pairing :
      ∀ Aderiv : NodeMatrix (Sum Node {i : Node // i ≠ i0}),
        HasDerivAt
          (fun alpha : ℝ =>
            quadraticRestrictedPeriodMatrix (Node := Node)
              quad lambda alpha i0)
          Aderiv 0 →
        ∀ W : ZeroSumState Node ℝ,
          rowDot (Node := Sum Node {i : Node // i ≠ i0})
              (fun a =>
                match a with
                | Sum.inl i => quad.perronLeft 0 i
                | Sum.inr _ => 0)
              (matrixMulVector
                (Node := Sum Node {i : Node // i ≠ i0}) Aderiv
                (restrictedStateToCoord (Node := Node) i0
                  ((fun _ : Node => (0 : ℝ)), W))) =
            quad.correctedLift quad.period
                ((quadraticRestrictedHomogeneousOrbit (Node := Node)
                  quad lambda 0 0 quad.period
                  ((fun _ : Node => (0 : ℝ)), W)).2) -
              quad.correctedLift 0 W := by
    intro Aderiv hAderiv W
    exact
      quadraticRestrictedPeriodMatrix_deriv_tracker_pairing_eq_correctedLift_difference
        (Node := Node) quad lambda i0 Aderiv hAderiv W
  have _hperiod_matrix_tracker_deriv_pairing :=
    hperiod_matrix_tracker_deriv_pairing
  have hprojected_rowDeriv_correctedLift_tracker_period_invariant :
      ∀ rowDeriv : RowVector (Sum Node {i : Node // i ≠ i0}),
        HasDerivAt
          (fun alpha : ℝ =>
            rowMulMatrix (Node := Sum Node {i : Node // i ≠ i0})
              (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
              (P alpha))
          rowDeriv 0 →
        ∀ Aderiv : NodeMatrix (Sum Node {i : Node // i ≠ i0}),
          HasDerivAt
            (fun alpha : ℝ =>
              quadraticRestrictedPeriodMatrix (Node := Node)
                quad lambda alpha i0)
            Aderiv 0 →
        ∀ gammaDeriv : ℝ,
          HasDerivAt gamma gammaDeriv 0 →
        ∀ W : ZeroSumState Node ℝ,
          let Wnext : ZeroSumState Node ℝ :=
            (quadraticRestrictedHomogeneousOrbit (Node := Node)
              quad lambda 0 0 quad.period
              ((fun _ : Node => (0 : ℝ)), W)).2
          weightedState
              (Node := Sum Node {i : Node // i ≠ i0}) (E := ℝ)
              rowDeriv
              (restrictedStateToCoord (Node := Node) i0
                ((fun _ : Node => (0 : ℝ)), Wnext)) +
            quad.correctedLift 0 Wnext =
              weightedState
                (Node := Sum Node {i : Node // i ≠ i0}) (E := ℝ)
                rowDeriv
                (restrictedStateToCoord (Node := Node) i0
                  ((fun _ : Node => (0 : ℝ)), W)) +
              quad.correctedLift 0 W := by
    intro rowDeriv hrow Aderiv hAderiv gammaDeriv hgammaDeriv W
    have hgamma0 : gamma 0 = 1 := by
      rcases hsplitting_restricted with
        ⟨_halpha0_pos, _hr0theta, _htheta_lt_one, _hK_nonneg, hgamma0,
          _hgamma_analytic, _hP_analytic, _hderiv, _hlocal⟩
      exact hgamma0
    have hrow0_eq_left :
        rowMulMatrix
            (Node := Sum Node {i : Node // i ≠ i0})
            (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
            (P 0) =
          left := by
      simpa using
        quadraticRestrictedPrimalAverageRow_mul_rankOneProjection_eq_left
          (Node := Node) i0 right left P hP0 hright_top
    exact
      quadraticRestrictedProjectedRowDeriv_correctedLift_tracker_period_invariant
        (Node := Node) quad lambda i0 left P gamma Aderiv gammaDeriv
        rowDeriv hleft_top hleft_bottom hrow hAderiv hgammaDeriv hgamma0
        hprojected_average_row_left_eigen_eventually hrow0_eq_left W
  have _hprojected_rowDeriv_correctedLift_tracker_period_invariant :=
    hprojected_rowDeriv_correctedLift_tracker_period_invariant
  have hprojected_average_row_alpha_zero_endpoint_perron :
      ∀ k : ℕ, ∀ S : State Node ℝ × ZeroSumState Node ℝ,
        weightedState (Node := Sum Node {i : Node // i ≠ i0}) (E := ℝ)
            (rowMulMatrix (Node := Sum Node {i : Node // i ≠ i0})
              (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
              (P 0))
            (restrictedStateToCoord (Node := Node) i0 S) =
          weightedState (Node := Node) (E := ℝ)
            (quad.perronLeft (quad.blockStart (k + 1))) S.1 := by
    intro k S
    exact
      quadraticRestrictedPrimalAverageProjectedRow_alpha_zero_weighted_eq_endpoint_perron
        (Node := Node) quad i0 right left P hP0 hright_top hleft_top
        hleft_bottom k S
  have _hprojected_average_row_alpha_zero_endpoint_perron :=
    hprojected_average_row_alpha_zero_endpoint_perron
  have hprojected_average_row_hasDerivAt_zero :
      ∃ rowDeriv : RowVector (Sum Node {i : Node // i ≠ i0}),
        HasDerivAt
          (fun alpha : ℝ =>
            rowMulMatrix (Node := Sum Node {i : Node // i ≠ i0})
              (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
              (P alpha))
          rowDeriv 0 := by
    exact
      quadraticRestrictedPrimalAverageProjectedRow_hasDerivAt_zero
        (Node := Node) i0 r0 alpha_restricted theta K right left gamma
        (fun alpha : ℝ =>
          quadraticRestrictedPeriodMatrix (Node := Node)
            quad lambda alpha i0)
        P F hsplitting_restricted
  have _hprojected_average_row_hasDerivAt_zero :=
    hprojected_average_row_hasDerivAt_zero
  have hprojected_corrected_firstVariation_of_rowDeriv_value :
      ∀ rowDeriv : RowVector (Sum Node {i : Node // i ≠ i0}),
        HasDerivAt
          (fun alpha : ℝ =>
            rowMulMatrix (Node := Sum Node {i : Node // i ≠ i0})
              (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
              (P alpha))
          rowDeriv 0 →
        (∀ k r : ℕ, r < quad.period → ∀ j : Node,
          let t : ℕ := quad.blockStart k + r
          let n : ℕ := quad.period - 1 - r
          let Snoise0 : State Node ℝ × ZeroSumState Node ℝ :=
            (fun _ : Node => 0, quad.pullColumnInnovation t j)
          let Sout0 :=
            quadraticRestrictedHomogeneousOrbit (Node := Node)
              quad lambda 0 (t + 1) n Snoise0
          weightedState
              (Node := Sum Node {i : Node // i ≠ i0}) (E := ℝ)
              rowDeriv (restrictedStateToCoord (Node := Node) i0 Sout0) +
            quad.correctedLift (t + 1 + n) Sout0.2 = 0) →
        ∀ k r : ℕ, r < quad.period → ∀ j : Node,
          HasDerivAt
            (fun alpha : ℝ =>
              weightedState
                (Node := Sum Node {i : Node // i ≠ i0}) (E := ℝ)
                (rowMulMatrix (Node := Sum Node {i : Node // i ≠ i0})
                  (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
                  (P alpha))
                (restrictedStateToCoord (Node := Node) i0
                  (quadraticRestrictedHomogeneousOrbit (Node := Node)
                    quad lambda alpha (k * quad.period + r + 1)
                    (quad.period - 1 - r)
                    (fun i : Node =>
                      -alpha * if i = j then (1 : ℝ) else 0,
                      quad.pullColumnInnovation
                        (k * quad.period + r) j))) -
                (let t : ℕ := quad.blockStart k + r
                 let n : ℕ := quad.period - 1 - r
                 let Snoise : State Node ℝ × ZeroSumState Node ℝ :=
                  (fun i : Node => -alpha * if i = j then (1 : ℝ) else 0,
                    quad.pullColumnInnovation t j)
                 let Sout :=
                  quadraticRestrictedHomogeneousOrbit (Node := Node)
                    quad lambda alpha (t + 1) n Snoise
                 weightedState (Node := Node) (E := ℝ)
                    (quad.perronLeft (t + 1 + n)) Sout.1 -
                  alpha * quad.correctedLift (t + 1 + n) Sout.2))
            0 0 := by
    intro rowDeriv hrow hvalue k r hr j
    exact
      quadraticRestrictedProjectedCorrected_firstVariation_of_rowDeriv_value
        (Node := Node) quad lambda i0 P rowDeriv k r j hr hrow
        (fun S => hprojected_average_row_alpha_zero_endpoint_perron k S)
        (hvalue k r hr j)
  have _hprojected_corrected_firstVariation_of_rowDeriv_value :=
    hprojected_corrected_firstVariation_of_rowDeriv_value
  have hrestricted_all_lengths_stable_blocks :
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
    exact quadratic_restricted_all_lengths_stable_blocks (Node := Node) quad
  have hprojected_rowDeriv_correctedLift_tracker_zero :
      ∀ rowDeriv : RowVector (Sum Node {i : Node // i ≠ i0}),
        HasDerivAt
          (fun alpha : ℝ =>
            rowMulMatrix (Node := Sum Node {i : Node // i ≠ i0})
              (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
              (P alpha))
          rowDeriv 0 →
        ∀ W : ZeroSumState Node ℝ,
          weightedState
              (Node := Sum Node {i : Node // i ≠ i0}) (E := ℝ)
              rowDeriv
              (restrictedStateToCoord (Node := Node) i0
                ((fun _ : Node => (0 : ℝ)), W)) +
            quad.correctedLift 0 W = 0 := by
    intro rowDeriv hrow W
    rcases hsplitting_restricted with
      ⟨_halpha0_pos, _hr0theta, _htheta_lt_one, _hK_nonneg, _hgamma0,
        _hgamma_analytic, _hP_analytic, hderiv, _hlocal⟩
    rcases hderiv with ⟨Aderiv, hAderiv, hgammaDeriv⟩
    exact
      quadraticRestrictedTrackerInvariantFunctional_eq_zero
        (Node := Node) quad lambda i0 rowDeriv
        hrestricted_all_lengths_stable_blocks
        (hprojected_rowDeriv_correctedLift_tracker_period_invariant
          rowDeriv hrow Aderiv hAderiv
          (rowDot (Node := Sum Node {i : Node // i ≠ i0}) left
            (matrixMulVector (Node := Sum Node {i : Node // i ≠ i0})
              Aderiv right))
          hgammaDeriv)
        W
  have _hprojected_rowDeriv_correctedLift_tracker_zero :=
    hprojected_rowDeriv_correctedLift_tracker_zero
  have hprojected_rowDeriv_value_zero :
      ∀ rowDeriv : RowVector (Sum Node {i : Node // i ≠ i0}),
        HasDerivAt
          (fun alpha : ℝ =>
            rowMulMatrix (Node := Sum Node {i : Node // i ≠ i0})
              (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
              (P alpha))
          rowDeriv 0 →
        ∀ k r : ℕ, r < quad.period → ∀ j : Node,
          let t : ℕ := quad.blockStart k + r
          let n : ℕ := quad.period - 1 - r
          let Snoise0 : State Node ℝ × ZeroSumState Node ℝ :=
            (fun _ : Node => 0, quad.pullColumnInnovation t j)
          let Sout0 :=
            quadraticRestrictedHomogeneousOrbit (Node := Node)
              quad lambda 0 (t + 1) n Snoise0
          weightedState
              (Node := Sum Node {i : Node // i ≠ i0}) (E := ℝ)
              rowDeriv (restrictedStateToCoord (Node := Node) i0 Sout0) +
            quad.correctedLift (t + 1 + n) Sout0.2 = 0 := by
    intro rowDeriv hrow k r hr j
    let t : ℕ := quad.blockStart k + r
    let n : ℕ := quad.period - 1 - r
    let Snoise0 : State Node ℝ × ZeroSumState Node ℝ :=
      (fun _ : Node => 0, quad.pullColumnInnovation t j)
    let Sout0 : State Node ℝ × ZeroSumState Node ℝ :=
      quadraticRestrictedHomogeneousOrbit (Node := Node)
        quad lambda 0 (t + 1) n Snoise0
    have hSout_top : Sout0.1 = fun _ : Node => (0 : ℝ) := by
      have horbit :=
        quadraticRestrictedHomogeneousOrbit_alpha_zero_tracker_only
          (Node := Node) quad lambda (t + 1) n
          (quad.pullColumnInnovation t j)
      simpa [Sout0, Snoise0] using congrArg Prod.fst horbit
    have hSout_eq : Sout0 = ((fun _ : Node => (0 : ℝ)), Sout0.2) := by
      exact Prod.ext hSout_top rfl
    have ht_eq : t = k * quad.period + r := by
      simp [t, Setup.blockStart]
    have hendpoint_time : t + 1 + n = quad.blockStart (k + 1) := by
      have hr_succ : r + 1 ≤ quad.period := Nat.succ_le_of_lt hr
      have hn_alt : n = quad.period - (r + 1) := by
        dsimp [n]
        rw [Nat.sub_sub, Nat.add_comm]
      have hcancel : r + 1 + n = quad.period := by
        rw [hn_alt]
        exact Nat.add_sub_of_le hr_succ
      calc
        t + 1 + n = k * quad.period + r + 1 + n := by rw [ht_eq]
        _ = k * quad.period + (r + 1 + n) := by omega
        _ = k * quad.period + quad.period := by rw [hcancel]
        _ = (k + 1) * quad.period := by
          exact (Nat.succ_mul k quad.period).symm
        _ = quad.blockStart (k + 1) := by rfl
    have hzero :=
      hprojected_rowDeriv_correctedLift_tracker_zero rowDeriv hrow Sout0.2
    have hcorr_time :
        quad.correctedLift (t + 1 + n) Sout0.2 =
          quad.correctedLift 0 Sout0.2 := by
      rw [hendpoint_time]
      simpa [Setup.blockStart] using
        quad.correctedLift_blockStart (k + 1) Sout0.2
    change
      weightedState
          (Node := Sum Node {i : Node // i ≠ i0}) (E := ℝ)
          rowDeriv (restrictedStateToCoord (Node := Node) i0 Sout0) +
        quad.correctedLift (t + 1 + n) Sout0.2 = 0
    rw [hSout_eq, hcorr_time]
    exact hzero
  have _hprojected_rowDeriv_value_zero :=
    hprojected_rowDeriv_value_zero
  have hprojected_corrected_firstVariation :
      ∀ k r : ℕ, r < quad.period → ∀ j : Node,
        HasDerivAt
          (fun alpha : ℝ =>
            weightedState
              (Node := Sum Node {i : Node // i ≠ i0}) (E := ℝ)
              (rowMulMatrix (Node := Sum Node {i : Node // i ≠ i0})
                (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
                (P alpha))
              (restrictedStateToCoord (Node := Node) i0
                (quadraticRestrictedHomogeneousOrbit (Node := Node)
                  quad lambda alpha (k * quad.period + r + 1)
                  (quad.period - 1 - r)
                  (fun i : Node =>
                    -alpha * if i = j then (1 : ℝ) else 0,
                    quad.pullColumnInnovation
                      (k * quad.period + r) j))) -
              (let t : ℕ := quad.blockStart k + r
               let n : ℕ := quad.period - 1 - r
               let Snoise : State Node ℝ × ZeroSumState Node ℝ :=
                (fun i : Node => -alpha * if i = j then (1 : ℝ) else 0,
                  quad.pullColumnInnovation t j)
               let Sout :=
                quadraticRestrictedHomogeneousOrbit (Node := Node)
                  quad lambda alpha (t + 1) n Snoise
               weightedState (Node := Node) (E := ℝ)
                  (quad.perronLeft (t + 1 + n)) Sout.1 -
                alpha * quad.correctedLift (t + 1 + n) Sout.2))
          0 0 := by
    intro k r hr j
    rcases hprojected_average_row_hasDerivAt_zero with ⟨rowDeriv, hrow⟩
    exact
      hprojected_corrected_firstVariation_of_rowDeriv_value
        rowDeriv hrow
        (hprojected_rowDeriv_value_zero rowDeriv hrow) k r hr j
  have _hprojected_corrected_firstVariation :=
    hprojected_corrected_firstVariation
  have hprojected_input_coeff_deriv :
      ∀ k r : ℕ, r < quad.period → ∀ j : Node,
        HasDerivAt
          (fun alpha : ℝ =>
            quadraticRestrictedProjectedPeriodInputCoeff
              (Node := Node) quad lambda alpha i0 P k r j)
          (-(quad.influence (quad.blockStart k + r) j)) 0 := by
    intro k r hr j
    exact
      quadraticRestrictedProjectedPeriodInputCoeff_hasDerivAt_zero
        (Node := Node) quad lambda i0 r0 alpha_restricted theta K
        right left gamma P F hsplitting_restricted hP0 hright_top
        hleft_top hleft_bottom k r hr j
  have _hprojected_input_coeff_deriv := hprojected_input_coeff_deriv
  have hmultO :
      Asymptotics.IsBigO (nhds 0)
        (fun alpha : ℝ =>
          gamma alpha -
            quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha)
        (fun alpha : ℝ => alpha ^ 2) :=
    quadratic_restricted_slow_multiplier_matches_scalar_period_multiplier_isBigO_sq
      (Node := Node) quad lambda i0 r0 alpha_restricted theta K right left
      gamma P F hsplitting_restricted hP0 hright_eq hright_top hleft_top
      hleft_bottom
  have _hmultO := hmultO
  obtain ⟨alphaGamma, cGamma, Cmul, halphaGamma_pos, hcGamma_pos,
      hCmul_pos, hgamma_contract⟩ :=
    restricted_gamma_smallAlpha_contract_from_scalar_squeeze
      (Node := Node) quad lambda i0 gamma hquad hmultO
  have _hgamma_contract := hgamma_contract
  have hprojected_input_scalar_block_alpha_zero :
      ∀ noise : NoisePath Node ℝ, ∀ k : ℕ,
        quadraticRestrictedPrimalAverageOutput (Node := Node) i0
            (matrixMulVector
              (Node := Sum Node {i : Node // i ≠ i0}) (P 0)
              (quadraticRestrictedPeriodNoiseInnovationCoord
                (Node := Node) quad lambda 0 i0 noise k)) -
          quadraticScalarBlockNoiseInnovation (Node := Node)
            quad lambda 0 noise k = 0 := by
    intro noise k
    exact
      quadratic_restricted_projected_period_input_scalar_block_alpha_zero
        (Node := Node) quad lambda i0 right left P hP0 hleft_bottom noise k
  have hprojected_input_scalar_block_diff_integrable :
      ∀ alpha : ℝ, ∀ k : ℕ,
        Integrable
          (fun ω : Ω =>
            |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                (matrixMulVector
                  (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
                  (quadraticRestrictedPeriodNoiseInnovationCoord
                    (Node := Node) quad lambda alpha i0 (oracle.noise ω) k)) -
              quadraticScalarBlockNoiseInnovation (Node := Node)
                quad lambda alpha (oracle.noise ω) k| ^ 2) μ := by
    intro alpha k
    exact
      quadratic_restricted_projected_period_input_scalar_block_diff_integrable
        (Node := Node) quad lambda i0 P μ oracle hnoise alpha k
  have _hprojected_input_scalar_block_alpha_zero :=
    hprojected_input_scalar_block_alpha_zero
  have _hprojected_input_scalar_block_diff_integrable :=
    hprojected_input_scalar_block_diff_integrable
  have hprojected_period_input_output_unroll :
      ∀ alpha : ℝ, ∀ noise : NoisePath Node ℝ, ∀ k : ℕ,
        let Idx := Sum Node {i : Node // i ≠ i0}
        let step : ℕ → NodeMatrix Idx := fun t =>
          quadraticRestrictedOneStepMatrix (Node := Node)
            quad lambda alpha i0 t
        quadraticRestrictedPrimalAverageOutput (Node := Node) i0
            (matrixMulVector (Node := Idx) (P alpha)
              (quadraticRestrictedPeriodNoiseInnovationCoord
                (Node := Node) quad lambda alpha i0 noise k)) =
          (Finset.range quad.period).sum fun r =>
            quadraticRestrictedPrimalAverageOutput (Node := Node) i0
              (matrixMulVector (Node := Idx) (P alpha)
                (matrixMulVector (Node := Idx)
                  (consecutiveProduct (Node := Idx) step
                    (k * quad.period + r + 1) (quad.period - 1 - r))
                  (quadraticRestrictedNoiseInnovationCoord
                    (Node := Node) quad alpha i0 noise
                    (k * quad.period + r)))) := by
    intro alpha noise k
    exact
      quadratic_restricted_projected_period_input_output_unroll
        (Node := Node) quad lambda alpha i0 P noise k
  have _hprojected_period_input_output_unroll :=
    hprojected_period_input_output_unroll
  have hprojected_period_input_coeff_row_unroll :
      ∀ alpha : ℝ, ∀ noise : NoisePath Node ℝ, ∀ k : ℕ,
        quadraticRestrictedPrimalAverageOutput (Node := Node) i0
            (matrixMulVector
              (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
              (quadraticRestrictedPeriodNoiseInnovationCoord
                (Node := Node) quad lambda alpha i0 noise k)) =
          (Finset.range quad.period).sum fun r =>
            weightedState (Node := Node) (E := ℝ)
              (quadraticRestrictedProjectedPeriodInputCoeff
                (Node := Node) quad lambda alpha i0 P k r)
              (noise (k * quad.period + r)) := by
    intro alpha noise k
    exact
      quadratic_restricted_projected_period_input_coeff_row_unroll
        (Node := Node) quad lambda alpha i0 P noise k
  have _hprojected_period_input_coeff_row_unroll :=
    hprojected_period_input_coeff_row_unroll
  have hscalar_block_coeff_row_unroll :
      ∀ alpha : ℝ, ∀ noise : NoisePath Node ℝ, ∀ k : ℕ,
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
    intro alpha noise k
    exact
      quadraticScalarBlockNoiseInnovation_eq_weightedCoeff_sum
        (Node := Node) quad lambda alpha noise k
  have _hscalar_block_coeff_row_unroll := hscalar_block_coeff_row_unroll
  have hprojected_input_scalar_block_secondMoment_exact :
      ∀ alpha : ℝ, ∀ k : ℕ,
        (∫ ω,
            |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                (matrixMulVector
                  (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
                  (quadraticRestrictedPeriodNoiseInnovationCoord
                    (Node := Node) quad lambda alpha i0
                    (oracle.noise ω) k)) -
              quadraticScalarBlockNoiseInnovation (Node := Node)
                quad lambda alpha (oracle.noise ω) k| ^ 2 ∂μ) =
          (Finset.range quad.period).sum fun r =>
            rowNormSq (Node := Node)
              (fun j : Node =>
                quadraticRestrictedProjectedPeriodInputCoeff
                    (Node := Node) quad lambda alpha i0 P k r j -
                  (-alpha *
                    quadraticScalarWindowNoiseCoeff (Node := Node)
                      quad lambda alpha (quad.blockStart k) quad.period r *
                    quad.influence (quad.blockStart k + r) j)) *
              quad.sigma ^ 2 := by
    intro alpha k
    exact
      quadratic_restricted_projected_period_input_scalar_block_secondMoment_exact
        (Node := Node) quad lambda alpha i0 P μ oracle hnoise k
  have _hprojected_input_scalar_block_secondMoment_exact :=
    hprojected_input_scalar_block_secondMoment_exact
  have hprojected_input_coeff_analytic :
      ∀ k r : ℕ, ∀ j : Node,
        AnalyticAt ℝ
          (fun alpha : ℝ =>
            quadraticRestrictedProjectedPeriodInputCoeff
              (Node := Node) quad lambda alpha i0 P k r j) 0 := by
    intro k r j
    exact
      quadraticRestrictedProjectedPeriodInputCoeff_analyticAt_zero
        (Node := Node) quad lambda i0 r0 alpha_restricted theta K
        right left gamma P F hsplitting_restricted k r j
  have _hprojected_input_coeff_analytic := hprojected_input_coeff_analytic
  have hprojected_input_coeff_row_sub_scalar_isBigO_sq :
      ∀ k r : ℕ, r < quad.period → ∀ j : Node,
        Asymptotics.IsBigO (nhds 0)
          (fun alpha : ℝ =>
            quadraticRestrictedProjectedPeriodInputCoeff
                (Node := Node) quad lambda alpha i0 P k r j -
              (-alpha *
                quadraticScalarWindowNoiseCoeff (Node := Node)
                  quad lambda alpha (quad.blockStart k) quad.period r *
                quad.influence (quad.blockStart k + r) j))
          (fun alpha : ℝ => alpha ^ 2) := by
    intro k r hr j
    exact
      quadratic_restricted_projected_period_input_coeff_row_sub_scalar_isBigO_sq_of_hasDerivAt
        (Node := Node) quad lambda i0 right left P hP0 hleft_bottom
        k r j hr
        (hprojected_input_coeff_analytic k r j)
        (hprojected_input_coeff_deriv k r hr j)
  have _hprojected_input_coeff_row_sub_scalar_isBigO_sq :=
    hprojected_input_coeff_row_sub_scalar_isBigO_sq
  have hprojected_input_scalar_block_l2_alpha4_bound :
      ∀ k : ℕ,
        Asymptotics.IsBigO (nhds 0)
          (fun alpha : ℝ =>
            ∫ ω,
              |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                  (matrixMulVector
                    (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
                    (quadraticRestrictedPeriodNoiseInnovationCoord
                      (Node := Node) quad lambda alpha i0
                      (oracle.noise ω) k)) -
                quadraticScalarBlockNoiseInnovation (Node := Node)
                  quad lambda alpha (oracle.noise ω) k| ^ 2 ∂μ)
          (fun alpha : ℝ => alpha ^ 4) := by
    intro k
    exact
      quadratic_restricted_projected_period_input_scalar_block_l2_alpha4_bound_of_coeff
        (Node := Node) quad lambda i0 P μ oracle hnoise k
        (hprojected_input_coeff_row_sub_scalar_isBigO_sq k)
  have _hprojected_input_scalar_block_l2_alpha4_bound :=
    hprojected_input_scalar_block_l2_alpha4_bound
  have hprojected_input_scalar_block_l2_alpha4_explicit_uniform :
      ∃ Cinput alphaInput : ℝ,
        0 < Cinput ∧ 0 < alphaInput ∧
          ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaInput →
            ∀ k : ℕ,
              (∫ ω,
                |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                    (matrixMulVector
                      (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
                      (quadraticRestrictedPeriodNoiseInnovationCoord
                        (Node := Node) quad lambda alpha i0
                        (oracle.noise ω) k)) -
                  quadraticScalarBlockNoiseInnovation (Node := Node)
                    quad lambda alpha (oracle.noise ω) k| ^ 2 ∂μ) ≤
                Cinput * alpha ^ 4 := by
    exact
      quadratic_restricted_projected_period_input_scalar_block_l2_alpha4_explicit_uniform_bound
        (Node := Node) quad lambda i0 P μ oracle hnoise
        (hprojected_input_scalar_block_l2_alpha4_bound 0)
  have _hprojected_input_scalar_block_l2_alpha4_explicit_uniform :=
    hprojected_input_scalar_block_l2_alpha4_explicit_uniform
  have hunit_noise_coeff_orbit_coord :
      ∀ alpha : ℝ, ∀ k r : ℕ, ∀ j : Node,
        matrixMulVector
            (Node := Sum Node {i : Node // i ≠ i0})
            (consecutiveProduct
              (Node := Sum Node {i : Node // i ≠ i0})
              (fun s =>
                quadraticRestrictedOneStepMatrix
                  (Node := Node) quad lambda alpha i0 s)
              (k * quad.period + r + 1) (quad.period - 1 - r))
            (fun a : Sum Node {i : Node // i ≠ i0} =>
              quadraticRestrictedNoiseInnovationCoeff
                (Node := Node) quad alpha i0 (k * quad.period + r) a j) =
          restrictedStateToCoord (Node := Node) i0
            (quadraticRestrictedHomogeneousOrbit (Node := Node)
              quad lambda alpha (k * quad.period + r + 1)
              (quad.period - 1 - r)
              (fun i : Node => -alpha * if i = j then (1 : ℝ) else 0,
                quad.pullColumnInnovation (k * quad.period + r) j)) := by
    intro alpha k r j
    exact
      quadraticRestrictedUnitNoiseCoeff_consecutiveProduct_eq_orbit_coord
        (Node := Node) quad lambda alpha i0 (k * quad.period + r)
        (quad.period - 1 - r) j
  have _hunit_noise_coeff_orbit_coord := hunit_noise_coeff_orbit_coord
  have hphase_unit_noise_correctedFunctional_deriv :
      ∀ k r : ℕ, ∀ j : Node,
        HasDerivAt
          (fun alpha : ℝ =>
            let t : ℕ := quad.blockStart k + r
            let n : ℕ := quad.period - 1 - r
            let Snoise : State Node ℝ × ZeroSumState Node ℝ :=
              (fun i : Node => -alpha * if i = j then (1 : ℝ) else 0,
                quad.pullColumnInnovation t j)
            let Sout :=
              quadraticRestrictedHomogeneousOrbit (Node := Node)
                quad lambda alpha (t + 1) n Snoise
            weightedState (Node := Node) (E := ℝ)
                (quad.perronLeft (t + 1 + n)) Sout.1 -
              alpha * quad.correctedLift (t + 1 + n) Sout.2)
          (-(quad.influence (quad.blockStart k + r) j)) 0 := by
    intro k r j
    exact
      quadraticRestrictedPeriodPhaseUnitNoise_correctedFunctional_hasDerivAt_zero
        (Node := Node) quad lambda k r j
  have _hphase_unit_noise_correctedFunctional_deriv :=
    hphase_unit_noise_correctedFunctional_deriv
  have hprojected_input_coeff_orbit_pairing :
      ∀ alpha : ℝ, ∀ k r : ℕ, ∀ j : Node,
        quadraticRestrictedProjectedPeriodInputCoeff
            (Node := Node) quad lambda alpha i0 P k r j =
          weightedState (Node := Sum Node {i : Node // i ≠ i0}) (E := ℝ)
            (rowMulMatrix (Node := Sum Node {i : Node // i ≠ i0})
              (quadraticRestrictedPrimalAverageRow (Node := Node) i0)
              (P alpha))
            (restrictedStateToCoord (Node := Node) i0
              (quadraticRestrictedHomogeneousOrbit (Node := Node)
                quad lambda alpha (k * quad.period + r + 1)
                (quad.period - 1 - r)
                (fun i : Node => -alpha * if i = j then (1 : ℝ) else 0,
                  quad.pullColumnInnovation (k * quad.period + r) j))) := by
    intro alpha k r j
    exact
      quadraticRestrictedProjectedPeriodInputCoeff_eq_projected_orbit_pairing
        (Node := Node) quad lambda alpha i0 P k r j
  have _hprojected_input_coeff_orbit_pairing :=
    hprojected_input_coeff_orbit_pairing
  have haverage_block_boundary_coord :
      ∀ alpha : ℝ, ∀ noise : NoisePath Node ℝ, ∀ k : ℕ,
        quadraticRestrictedPrimalAverageOutput (Node := Node) i0
            (restrictedStateToCoord (Node := Node) i0
              ((quad.withStepsize alpha).primalState noise (k * quad.period),
                (quad.withStepsize alpha).trackerErrorZeroSum noise
                  (k * quad.period))) =
          (quad.withStepsize alpha).averageIterate noise (k * quad.period) := by
    intro alpha noise k
    exact
      quadraticRestrictedPrimalAverageOutput_restrictedStateToCoord_eq_averageIterate
        (Node := Node) quad i0 alpha noise (k * quad.period)
  have _haverage_block_boundary_coord := haverage_block_boundary_coord
  have hprojected_scalar_boundary_error_recursion :
      ∀ alpha : ℝ, |alpha| ≤ alpha_restricted →
        ∀ noise : NoisePath Node ℝ, ∀ k : ℕ,
          let stepped := quad.withStepsize alpha
          let projectedBoundary : ℕ → ℝ := fun m =>
            quadraticRestrictedPrimalAverageOutput (Node := Node) i0
              (matrixMulVector (Node := Sum Node {i : Node // i ≠ i0})
                (P alpha)
                (restrictedStateToCoord (Node := Node) i0
                  (stepped.primalState noise (m * quad.period),
                    stepped.trackerErrorZeroSum noise
                      (m * quad.period))))
          let scalarBoundary : ℕ → ℝ := fun m =>
            quad.quadraticScalarComparisonProcess lambda alpha noise
              (m * quad.period)
          let projectedInput : ℕ → ℝ := fun m =>
            quadraticRestrictedPrimalAverageOutput (Node := Node) i0
              (matrixMulVector (Node := Sum Node {i : Node // i ≠ i0})
                (P alpha)
                (quadraticRestrictedPeriodNoiseInnovationCoord
                  (Node := Node) quad lambda alpha i0 noise m))
          let scalarInput : ℕ → ℝ := fun m =>
            quadraticScalarBlockNoiseInnovation (Node := Node)
              quad lambda alpha noise m
          projectedBoundary (k + 1) - scalarBoundary (k + 1) =
            gamma alpha * (projectedBoundary k - scalarBoundary k) +
              ((gamma alpha -
                  quadraticScalarPeriodMultiplier (Node := Node)
                    quad lambda alpha) *
                  scalarBoundary k +
                (projectedInput k - scalarInput k)) := by
    intro alpha halpha_abs noise k
    let stepped := quad.withStepsize alpha
    let projectedBoundary : ℕ → ℝ := fun m =>
      quadraticRestrictedPrimalAverageOutput (Node := Node) i0
        (matrixMulVector (Node := Sum Node {i : Node // i ≠ i0})
          (P alpha)
          (restrictedStateToCoord (Node := Node) i0
            (stepped.primalState noise (m * quad.period),
              stepped.trackerErrorZeroSum noise (m * quad.period))))
    let scalarBoundary : ℕ → ℝ := fun m =>
      quad.quadraticScalarComparisonProcess lambda alpha noise
        (m * quad.period)
    let projectedInput : ℕ → ℝ := fun m =>
      quadraticRestrictedPrimalAverageOutput (Node := Node) i0
        (matrixMulVector (Node := Sum Node {i : Node // i ≠ i0})
          (P alpha)
          (quadraticRestrictedPeriodNoiseInnovationCoord
            (Node := Node) quad lambda alpha i0 noise m))
    let scalarInput : ℕ → ℝ := fun m =>
      quadraticScalarBlockNoiseInnovation (Node := Node)
        quad lambda alpha noise m
    have hprojected_rec :
        ∀ m : ℕ,
          projectedBoundary (m + 1) =
            gamma alpha * projectedBoundary m + projectedInput m := by
      intro m
      simpa [projectedBoundary, projectedInput, stepped] using
        hprojected_boundary_recursion alpha halpha_abs noise m
    have hscalar_rec :
        ∀ m : ℕ,
          scalarBoundary (m + 1) =
            quadraticScalarPeriodMultiplier (Node := Node)
              quad lambda alpha * scalarBoundary m + scalarInput m := by
      intro m
      simpa [scalarBoundary, scalarInput] using
        quadraticScalarBlockARRecursion
          (Node := Node) quad lambda alpha noise m
    exact
      scalar_ar_difference_recursion_of_two_recursions
        (gamma := gamma alpha)
        (Gamma := quadraticScalarPeriodMultiplier (Node := Node)
          quad lambda alpha)
        projectedBoundary scalarBoundary projectedInput scalarInput
        hprojected_rec hscalar_rec k
  have _hprojected_scalar_boundary_error_recursion :=
    hprojected_scalar_boundary_error_recursion
  obtain ⟨alphaScalarBoundary, CscalarBoundary,
      halphaScalarBoundary_pos, hCscalarBoundary_nonneg,
      hscalar_boundary_moment_sum_raw⟩ :=
    quadraticScalarBlockBoundarySecondMoment_sum_linear_bound
      (Node := Node) quad lambda μ oracle hquad hnoise
  have hscalar_boundary_square_integrable :
      ∀ alpha : ℝ, ∀ k : ℕ,
        Integrable
          (fun ω : Ω =>
            |quad.quadraticScalarComparisonProcess lambda alpha
              (oracle.noise ω) (k * quad.period)| ^ 2) μ := by
    intro alpha k
    exact
      real_abs_sq_integrable_of_memLp_two
        (quadraticScalarComparisonProcess_memLp_two
          (Node := Node) quad lambda alpha μ oracle hnoise.1
          (k * quad.period))
  have hscalar_boundary_square_sum_bound :
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaScalarBoundary →
        ∀ N : ℕ,
          Finset.sum (Finset.range N) (fun k =>
            ∫ ω,
              |quad.quadraticScalarComparisonProcess lambda alpha
                (oracle.noise ω) (k * quad.period)| ^ 2 ∂μ) ≤
            CscalarBoundary * (N : ℝ) := by
    intro alpha halpha_pos halpha_le N
    simpa [quadraticScalarBlockBoundarySecondMoment] using
      hscalar_boundary_moment_sum_raw alpha halpha_pos halpha_le N
  have _hscalar_boundary_square_integrable :=
    hscalar_boundary_square_integrable
  have _hscalar_boundary_square_sum_bound :=
    hscalar_boundary_square_sum_bound
  obtain ⟨Cinput, alphaInput, hCinput_pos, halphaInput_pos,
      hprojected_input_scalar_block_l2_alpha4_explicit_bound⟩ :=
    hprojected_input_scalar_block_l2_alpha4_explicit_uniform
  have hCinput_nonneg : 0 ≤ Cinput := le_of_lt hCinput_pos
  have hprojected_input_scalar_block_l2_alpha4_sum_bound :
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaInput →
        ∀ N : ℕ,
          Finset.sum (Finset.range N) (fun k =>
            ∫ ω,
              |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                  (matrixMulVector
                    (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
                    (quadraticRestrictedPeriodNoiseInnovationCoord
                      (Node := Node) quad lambda alpha i0
                      (oracle.noise ω) k)) -
                quadraticScalarBlockNoiseInnovation (Node := Node)
                  quad lambda alpha (oracle.noise ω) k| ^ 2 ∂μ) ≤
            Cinput * alpha ^ 4 * (N : ℝ) := by
    intro alpha halpha_pos halpha_le N
    calc
      Finset.sum (Finset.range N) (fun k =>
          ∫ ω,
            |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                (matrixMulVector
                  (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
                  (quadraticRestrictedPeriodNoiseInnovationCoord
                    (Node := Node) quad lambda alpha i0
                    (oracle.noise ω) k)) -
              quadraticScalarBlockNoiseInnovation (Node := Node)
                quad lambda alpha (oracle.noise ω) k| ^ 2 ∂μ) ≤
          Finset.sum (Finset.range N) (fun _k =>
            Cinput * alpha ^ 4) :=
            Finset.sum_le_sum fun k _hk =>
              hprojected_input_scalar_block_l2_alpha4_explicit_bound
                alpha halpha_pos halpha_le k
      _ = Cinput * alpha ^ 4 * (N : ℝ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  have hprojected_scalar_forcing_square_integrable :
      ∀ alpha : ℝ, ∀ k : ℕ,
        Integrable
          (fun ω : Ω =>
            |(gamma alpha -
                  quadraticScalarPeriodMultiplier (Node := Node)
                    quad lambda alpha) *
                quad.quadraticScalarComparisonProcess lambda alpha
                  (oracle.noise ω) (k * quad.period) +
              (quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                  (matrixMulVector
                    (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
                    (quadraticRestrictedPeriodNoiseInnovationCoord
                      (Node := Node) quad lambda alpha i0
                      (oracle.noise ω) k)) -
                quadraticScalarBlockNoiseInnovation (Node := Node)
                  quad lambda alpha (oracle.noise ω) k)| ^ 2) μ := by
    intro alpha k
    let scalarBoundary : Ω → ℝ := fun ω =>
      quad.quadraticScalarComparisonProcess lambda alpha
        (oracle.noise ω) (k * quad.period)
    let inputDiff : Ω → ℝ := fun ω =>
      quadraticRestrictedPrimalAverageOutput (Node := Node) i0
          (matrixMulVector
            (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
            (quadraticRestrictedPeriodNoiseInnovationCoord
              (Node := Node) quad lambda alpha i0
              (oracle.noise ω) k)) -
        quadraticScalarBlockNoiseInnovation (Node := Node)
          quad lambda alpha (oracle.noise ω) k
    have hscalar_mem : MemLp scalarBoundary 2 μ := by
      dsimp [scalarBoundary]
      exact
        quadraticScalarComparisonProcess_memLp_two
          (Node := Node) quad lambda alpha μ oracle hnoise.1
          (k * quad.period)
    have hinput_mem : MemLp inputDiff 2 μ := by
      dsimp [inputDiff]
      exact
        quadratic_restricted_projected_period_input_scalar_block_diff_memLp_two
          (Node := Node) quad lambda i0 P μ oracle hnoise alpha k
    have hforcing_mem :
        MemLp
          (fun ω : Ω =>
            (gamma alpha -
                quadraticScalarPeriodMultiplier (Node := Node)
                  quad lambda alpha) * scalarBoundary ω + inputDiff ω)
          2 μ := by
      simpa [Pi.add_apply, smul_eq_mul] using
        (hscalar_mem.const_smul
            (gamma alpha -
              quadraticScalarPeriodMultiplier (Node := Node)
                quad lambda alpha)).add hinput_mem
    simpa [scalarBoundary, inputDiff] using
      real_abs_sq_integrable_of_memLp_two hforcing_mem
  have hprojected_scalar_forcing_square_sum_bound :
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaGamma →
        alpha ≤ alphaScalarBoundary → alpha ≤ alphaInput →
          ∀ N : ℕ,
            Finset.sum (Finset.range N) (fun k =>
              ∫ ω,
                |(gamma alpha -
                    quadraticScalarPeriodMultiplier (Node := Node)
                      quad lambda alpha) *
                    quad.quadraticScalarComparisonProcess lambda alpha
                      (oracle.noise ω) (k * quad.period) +
                  (quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                      (matrixMulVector
                        (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
                        (quadraticRestrictedPeriodNoiseInnovationCoord
                          (Node := Node) quad lambda alpha i0
                          (oracle.noise ω) k)) -
                    quadraticScalarBlockNoiseInnovation (Node := Node)
                      quad lambda alpha (oracle.noise ω) k)| ^ 2 ∂μ) ≤
              (2 * Cmul ^ 2 * CscalarBoundary + 2 * Cinput) *
                alpha ^ 4 * (N : ℝ) := by
    intro alpha halpha_pos halpha_le_gamma halpha_le_scalar
      halpha_le_input N
    let scalarBoundary : Ω → ℕ → ℝ := fun ω k =>
      quad.quadraticScalarComparisonProcess lambda alpha
        (oracle.noise ω) (k * quad.period)
    let inputDiff : Ω → ℕ → ℝ := fun ω k =>
      quadraticRestrictedPrimalAverageOutput (Node := Node) i0
          (matrixMulVector
            (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
            (quadraticRestrictedPeriodNoiseInnovationCoord
              (Node := Node) quad lambda alpha i0
              (oracle.noise ω) k)) -
        quadraticScalarBlockNoiseInnovation (Node := Node)
          quad lambda alpha (oracle.noise ω) k
    have hgamma_data :=
      hgamma_contract alpha halpha_pos halpha_le_gamma
    have hcoeff_bound :
        |gamma alpha -
            quadraticScalarPeriodMultiplier (Node := Node)
              quad lambda alpha| ≤ Cmul * alpha ^ 2 :=
      hgamma_data.2.2.1
    have hscalar_sq_int :
        ∀ k : ℕ,
          Integrable (fun ω : Ω => |scalarBoundary ω k| ^ 2) μ := by
      intro k
      simpa [scalarBoundary] using
        hscalar_boundary_square_integrable alpha k
    have hinput_sq_int :
        ∀ k : ℕ,
          Integrable (fun ω : Ω => |inputDiff ω k| ^ 2) μ := by
      intro k
      simpa [inputDiff] using
        hprojected_input_scalar_block_diff_integrable alpha k
    have hforcing_sq_int :
        ∀ k : ℕ,
          Integrable
            (fun ω : Ω =>
              |(gamma alpha -
                  quadraticScalarPeriodMultiplier (Node := Node)
                    quad lambda alpha) *
                  scalarBoundary ω k + inputDiff ω k| ^ 2) μ := by
      intro k
      simpa [scalarBoundary, inputDiff] using
        hprojected_scalar_forcing_square_integrable alpha k
    have hscalar_sum :
        ∀ N : ℕ,
          Finset.sum (Finset.range N) (fun k =>
            ∫ ω, |scalarBoundary ω k| ^ 2 ∂μ) ≤
            CscalarBoundary * (N : ℝ) := by
      intro N
      simpa [scalarBoundary] using
        hscalar_boundary_square_sum_bound alpha halpha_pos
          halpha_le_scalar N
    have hinput_sum :
        ∀ N : ℕ,
          Finset.sum (Finset.range N) (fun k =>
            ∫ ω, |inputDiff ω k| ^ 2 ∂μ) ≤
            Cinput * alpha ^ 4 * (N : ℝ) := by
      intro N
      simpa [inputDiff] using
        hprojected_input_scalar_block_l2_alpha4_sum_bound
          alpha halpha_pos halpha_le_input N
    simpa [scalarBoundary, inputDiff] using
      slow_ar_difference_forcing_square_sum_bound_of_parts
        (μ := μ) (alpha := alpha) (Cmul := Cmul)
        (Cscalar := CscalarBoundary) (Cinput := Cinput)
        (gamma := gamma alpha)
        (Gamma := quadraticScalarPeriodMultiplier (Node := Node)
          quad lambda alpha)
        hCscalarBoundary_nonneg hCinput_nonneg hcoeff_bound
        scalarBoundary inputDiff hscalar_sq_int hinput_sq_int
        hforcing_sq_int hscalar_sum hinput_sum N
  have hprojected_scalar_forcing_constant_nonneg :
      0 ≤ 2 * Cmul ^ 2 * CscalarBoundary + 2 * Cinput := by
    positivity
  obtain ⟨Cinit, alphaInit, hCinit_nonneg, halphaInit_pos,
      halphaInit_le_restricted, hprojected_scalar_initial_error_bound⟩ :=
    quadratic_restricted_projected_scalar_initial_error_l2_alpha2_bound
      (Node := Node) quad lambda i0 r0 alpha_restricted theta K
      right left gamma P F hP0 hright_top hleft_top hleft_bottom
      hsplitting_restricted μ oracle
  have hprojected_scalar_error_square_integrable :
      ∀ alpha : ℝ, ∀ k : ℕ,
        Integrable
          (fun ω : Ω =>
            |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                (matrixMulVector
                  (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
                  (restrictedStateToCoord (Node := Node) i0
                    ((quad.withStepsize alpha).primalState
                        (oracle.noise ω) (k * quad.period),
                      (quad.withStepsize alpha).trackerErrorZeroSum
                        (oracle.noise ω) (k * quad.period)))) -
              quad.quadraticScalarComparisonProcess lambda alpha
                (oracle.noise ω) (k * quad.period)| ^ 2) μ := by
    intro alpha k
    let Idx := Sum Node {i : Node // i ≠ i0}
    let stepped := quad.withStepsize alpha
    let coord : Ω → RowVector Idx := fun ω =>
      restrictedStateToCoord (Node := Node) i0
        (stepped.primalState (oracle.noise ω) (k * quad.period),
          stepped.trackerErrorZeroSum (oracle.noise ω) (k * quad.period))
    let projectedBoundary : Ω → ℝ := fun ω =>
      quadraticRestrictedPrimalAverageOutput (Node := Node) i0
        (matrixMulVector (Node := Idx) (P alpha) (coord ω))
    let scalarBoundary : Ω → ℝ := fun ω =>
      quad.quadraticScalarComparisonProcess lambda alpha
        (oracle.noise ω) (k * quad.period)
    have hcoord :
        ∀ a : Idx, MemLp (fun ω : Ω => coord ω a) 2 μ := by
      intro a
      simpa [Idx, stepped, coord] using
        quadraticRestrictedBoundaryCoord_coordinate_memLp
          (Node := Node) quad alpha i0 μ oracle hnoise
          (k * quad.period) a
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
        MemLp projectedBoundary 2 μ := by
      dsimp [projectedBoundary]
      simpa [quadraticRestrictedPrimalAverageOutput] using
        hprojected_sum.const_smul ((nodeCount (Node := Node) : ℝ)⁻¹)
    have hscalar_mem :
        MemLp scalarBoundary 2 μ := by
      dsimp [scalarBoundary]
      exact
        quadraticScalarComparisonProcess_memLp_two
          (Node := Node) quad lambda alpha μ oracle hnoise.1
          (k * quad.period)
    simpa [projectedBoundary, scalarBoundary, coord, stepped] using
      real_abs_sq_integrable_of_memLp_two
        (hprojected_mem.sub hscalar_mem)
  let Ceta : ℝ := 2 * Cmul ^ 2 * CscalarBoundary + 2 * Cinput
  let Cblock : ℝ := 2 * Cinit / cGamma + 2 * Ceta / cGamma ^ 2 + 1
  let alphaBlock : ℝ :=
    min alpha_restricted
      (min alphaGamma
        (min alphaScalarBoundary (min alphaInput alphaInit)))
  have halphaBlock_pos : 0 < alphaBlock := by
    dsimp [alphaBlock]
    exact lt_min hsplitting_restricted.1
      (lt_min halphaGamma_pos
        (lt_min halphaScalarBoundary_pos
          (lt_min halphaInput_pos halphaInit_pos)))
  have halphaBlock_le_restricted : alphaBlock ≤ alpha_restricted := by
    dsimp [alphaBlock]
    exact min_le_left _ _
  have hprojected_scalar_block_boundary_average_l2_bound :
      0 < Cblock ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaBlock →
          ∀ T : ℕ, 1 ≤ alpha * (T : ℝ) →
            ((T : ℝ)⁻¹) *
              Finset.sum (Finset.range T) (fun k =>
                ∫ ω,
                  |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                      (matrixMulVector
                        (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
                        (restrictedStateToCoord (Node := Node) i0
                          ((quad.withStepsize alpha).primalState
                              (oracle.noise ω) (k * quad.period),
                            (quad.withStepsize alpha).trackerErrorZeroSum
                              (oracle.noise ω) (k * quad.period)))) -
                    quad.quadraticScalarComparisonProcess lambda alpha
                      (oracle.noise ω) (k * quad.period)| ^ 2 ∂μ) ≤
                Cblock * alpha ^ 2 := by
    have hCeta_nonneg : 0 ≤ Ceta := by
      dsimp [Ceta]
      exact hprojected_scalar_forcing_constant_nonneg
    have hCblock_pos : 0 < Cblock := by
      have hterm1_nonneg : 0 ≤ 2 * Cinit / cGamma := by positivity
      have hterm2_nonneg : 0 ≤ 2 * Ceta / cGamma ^ 2 := by positivity
      dsimp [Cblock]
      nlinarith
    refine ⟨hCblock_pos, ?_⟩
    intro alpha halpha_pos halpha_le_block T halphaT
    let projectedBoundary : Ω → ℕ → ℝ := fun ω k =>
      quadraticRestrictedPrimalAverageOutput (Node := Node) i0
        (matrixMulVector (Node := Sum Node {i : Node // i ≠ i0})
          (P alpha)
          (restrictedStateToCoord (Node := Node) i0
            ((quad.withStepsize alpha).primalState
                (oracle.noise ω) (k * quad.period),
              (quad.withStepsize alpha).trackerErrorZeroSum
                (oracle.noise ω) (k * quad.period))))
    let scalarBoundary : Ω → ℕ → ℝ := fun ω k =>
      quad.quadraticScalarComparisonProcess lambda alpha
        (oracle.noise ω) (k * quad.period)
    let err : Ω → ℕ → ℝ := fun ω k =>
      projectedBoundary ω k - scalarBoundary ω k
    let eta : Ω → ℕ → ℝ := fun ω k =>
      (gamma alpha -
          quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha) *
        scalarBoundary ω k +
        (quadraticRestrictedPrimalAverageOutput (Node := Node) i0
            (matrixMulVector
              (Node := Sum Node {i : Node // i ≠ i0}) (P alpha)
              (quadraticRestrictedPeriodNoiseInnovationCoord
                (Node := Node) quad lambda alpha i0
                (oracle.noise ω) k)) -
          quadraticScalarBlockNoiseInnovation (Node := Node)
            quad lambda alpha (oracle.noise ω) k)
    have halpha_le_restricted : alpha ≤ alpha_restricted :=
      le_trans halpha_le_block halphaBlock_le_restricted
    have halpha_abs : |alpha| ≤ alpha_restricted := by
      simpa [abs_of_pos halpha_pos] using halpha_le_restricted
    have halpha_le_gamma : alpha ≤ alphaGamma := by
      exact le_trans halpha_le_block
        (le_trans (min_le_right _ _) (min_le_left _ _))
    have halpha_le_scalar : alpha ≤ alphaScalarBoundary := by
      exact le_trans halpha_le_block
        (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (min_le_left _ _)))
    have halpha_le_input : alpha ≤ alphaInput := by
      exact le_trans halpha_le_block
        (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _) (min_le_left _ _))))
    have halpha_le_init : alpha ≤ alphaInit := by
      exact le_trans halpha_le_block
        (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _) (min_le_right _ _))))
    have hgamma_data :=
      hgamma_contract alpha halpha_pos halpha_le_gamma
    have hrec :
        ∀ ω : Ω, ∀ k : ℕ,
          err ω (k + 1) = gamma alpha * err ω k + eta ω k := by
      intro ω k
      simpa [err, eta, projectedBoundary, scalarBoundary] using
        hprojected_scalar_boundary_error_recursion
          alpha halpha_abs (oracle.noise ω) k
    have herr_int :
        ∀ k : ℕ, Integrable (fun ω : Ω => |err ω k| ^ 2) μ := by
      intro k
      simpa [err, projectedBoundary, scalarBoundary] using
        hprojected_scalar_error_square_integrable alpha k
    have heta_int :
        ∀ k : ℕ, Integrable (fun ω : Ω => |eta ω k| ^ 2) μ := by
      intro k
      simpa [eta, scalarBoundary] using
        hprojected_scalar_forcing_square_integrable alpha k
    have hinit_bound :
        (∫ ω, |err ω 0| ^ 2 ∂μ) ≤ Cinit * alpha ^ 2 := by
      simpa [err, projectedBoundary, scalarBoundary] using
        hprojected_scalar_initial_error_bound alpha halpha_pos halpha_le_init
    have heta_sum_bound :
        ∀ N : ℕ,
          Finset.sum (Finset.range N) (fun k =>
            ∫ ω, |eta ω k| ^ 2 ∂μ) ≤
            Ceta * alpha ^ 4 * (N : ℝ) := by
      intro N
      simpa [Ceta, eta, scalarBoundary] using
        hprojected_scalar_forcing_square_sum_bound alpha halpha_pos
          halpha_le_gamma halpha_le_scalar halpha_le_input N
    have hslow :=
      slow_ar_difference_average_l2_bound
        (μ := μ) (alpha := alpha) (cGamma := cGamma)
        (Cinit := Cinit) (Ceta := Ceta) (gamma := gamma alpha)
        halpha_pos hcGamma_pos hgamma_data.2.2.2.2.2
        hgamma_data.2.2.2.1 hgamma_data.2.2.2.2.1
        hCinit_nonneg hCeta_nonneg err eta hrec herr_int heta_int
        hinit_bound heta_sum_bound
    simpa [Cblock, Ceta, err, projectedBoundary, scalarBoundary] using
      hslow.2 T halphaT
  have _hprojected_input_scalar_block_l2_alpha4_sum_bound :=
    hprojected_input_scalar_block_l2_alpha4_sum_bound
  have _hprojected_scalar_forcing_square_integrable :=
    hprojected_scalar_forcing_square_integrable
  have _hprojected_scalar_forcing_square_sum_bound :=
    hprojected_scalar_forcing_square_sum_bound
  have _hprojected_scalar_forcing_constant_nonneg :=
    hprojected_scalar_forcing_constant_nonneg
  have _hprojected_scalar_initial_error_bound :=
    hprojected_scalar_initial_error_bound
  have _hprojected_scalar_error_square_integrable :=
    hprojected_scalar_error_square_integrable
  have _hprojected_scalar_block_boundary_average_l2_bound :=
    hprojected_scalar_block_boundary_average_l2_bound
  rcases hstable_output_average_l2 with
    ⟨Cstable, alphaStable, hCstable_pos, halphaStable_pos,
      hstable_average_bound⟩
  obtain ⟨alphaScalarFloorPhase, CscalarFloorPhase,
      halphaScalarFloorPhase_pos, hCscalarFloorPhase_nonneg,
      hscalar_floor_phase⟩ :=
    quadraticScalarWithinPeriodMultiplier_residue_uniform_bound
      (Node := Node) quad lambda
  obtain ⟨alphaScalarFloorBoundary, CscalarFloorBoundary,
      halphaScalarFloorBoundary_pos, hCscalarFloorBoundary_nonneg,
      hscalar_floor_boundary⟩ :=
    quadraticScalarBlockBoundarySecondMoment_uniform_bound
      (Node := Node) quad lambda μ oracle hquad hnoise
  obtain ⟨alphaScalarFloorFresh, CscalarFloorFresh,
      halphaScalarFloorFresh_pos, hCscalarFloorFresh_nonneg,
      hscalar_floor_fresh⟩ :=
    quadraticScalarWindowPropagatedNoiseFinset_phase_secondMoment_uniform_bound
      (Node := Node) quad lambda μ oracle hnoise
  let CstablePhase : ℝ := 2 * Cstable
  let CscalarFloor : ℝ :=
    2 * CscalarFloorPhase ^ 2 * CscalarFloorBoundary +
      2 * CscalarFloorFresh
  let alphaScalarFloor : ℝ :=
    min alphaScalarFloorPhase
      (min alphaScalarFloorBoundary alphaScalarFloorFresh)
  have hactual_floor_block_gradient_linear_budget :
      ∃ Cgrad alphaGrad : ℝ,
        0 ≤ Cgrad ∧ 0 < alphaGrad ∧
          ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaGrad →
            ∀ T : ℕ, 1 ≤ alpha * (T : ℝ) →
              (quad.withStepsize alpha).blockGradientEnergy μ oracle T ≤
                Cgrad * (T : ℝ) := by
    classical
    let Cavg : ℝ := 2 * Cblock + 4 * Cstable + 4 * CscalarBoundary + 1
    let Cgrad : ℝ := lambda ^ 2 * Cavg
    let alphaGrad : ℝ :=
      min 1 (min alphaBlock (min alphaStable alphaScalarBoundary))
    have hCavg_nonneg : 0 ≤ Cavg := by
      have hCblock_nonneg : 0 ≤ Cblock :=
        le_of_lt hprojected_scalar_block_boundary_average_l2_bound.1
      have hCstable_nonneg : 0 ≤ Cstable := le_of_lt hCstable_pos
      dsimp [Cavg]
      nlinarith [hCblock_nonneg, hCstable_nonneg,
        hCscalarBoundary_nonneg]
    have hCgrad_nonneg : 0 ≤ Cgrad := by
      dsimp [Cgrad]
      exact mul_nonneg (sq_nonneg lambda) hCavg_nonneg
    have halphaGrad_pos : 0 < alphaGrad := by
      dsimp [alphaGrad]
      exact lt_min zero_lt_one
        (lt_min halphaBlock_pos
          (lt_min halphaStable_pos halphaScalarBoundary_pos))
    refine ⟨Cgrad, alphaGrad, hCgrad_nonneg, halphaGrad_pos, ?_⟩
    intro alpha halpha_pos halpha_le_grad T halphaT
    let stepped := quad.withStepsize alpha
    have halpha_le_one : alpha ≤ 1 := by
      exact le_trans halpha_le_grad
        (by dsimp [alphaGrad]; exact min_le_left _ _)
    have halpha_sq_le_one : alpha ^ 2 ≤ 1 := by
      have hmul_nonneg : 0 ≤ alpha * (1 - alpha) :=
        mul_nonneg halpha_pos.le (sub_nonneg.mpr halpha_le_one)
      nlinarith
    have halpha_le_block : alpha ≤ alphaBlock := by
      exact le_trans halpha_le_grad
        (by
          dsimp [alphaGrad]
          exact le_trans (min_le_right _ _) (min_le_left _ _))
    have halpha_le_stable : alpha ≤ alphaStable := by
      exact le_trans halpha_le_grad
        (by
          dsimp [alphaGrad]
          exact le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _) (min_le_left _ _)))
    have halpha_le_scalar_boundary :
        alpha ≤ alphaScalarBoundary := by
      exact le_trans halpha_le_grad
        (by
          dsimp [alphaGrad]
          exact le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _) (min_le_right _ _)))
    have halpha_le_restricted : alpha ≤ alpha_restricted :=
      le_trans halpha_le_block halphaBlock_le_restricted
    have halpha_abs : |alpha| ≤ alpha_restricted := by
      simpa [abs_of_pos halpha_pos] using halpha_le_restricted
    have hT_pos : 0 < (T : ℝ) := by
      by_contra hnot
      have hT_nonpos : (T : ℝ) ≤ 0 := le_of_not_gt hnot
      have hT_zero : (T : ℝ) = 0 :=
        le_antisymm hT_nonpos (Nat.cast_nonneg T)
      have hprod_zero : alpha * (T : ℝ) = 0 := by
        rw [hT_zero, mul_zero]
      nlinarith
    have hT_ne : (T : ℝ) ≠ 0 := ne_of_gt hT_pos
    have hT_nat_pos : 0 < T := Nat.cast_pos.mp hT_pos
    have hT_ge_one : 1 ≤ T := Nat.succ_le_of_lt hT_nat_pos
    let projected : Ω → ℕ → ℝ := fun ω k =>
      quadraticRestrictedPrimalAverageOutput (Node := Node) i0
        (matrixMulVector
          (Node := Sum Node {i : Node // i ≠ i0})
          (P alpha)
          (restrictedStateToCoord (Node := Node) i0
            (stepped.primalState (oracle.noise ω) (k * quad.period),
              stepped.trackerErrorZeroSum (oracle.noise ω)
                (k * quad.period))))
    let stable : Ω → ℕ → ℝ := fun ω k =>
      quadraticRestrictedPrimalAverageOutput (Node := Node) i0
        (quadraticRestrictedStableBoundaryResponse
          (Node := Node) quad lambda i0 P F alpha (oracle.noise ω) k)
    let scalar : Ω → ℕ → ℝ := fun ω k =>
      quad.quadraticScalarComparisonProcess lambda alpha
        (oracle.noise ω) (k * quad.period)
    let actual : Ω → ℕ → ℝ := fun ω k =>
      stepped.averageIterate (oracle.noise ω) (k * quad.period)
    have hactual_int :
        ∀ k : ℕ, Integrable (fun ω : Ω => |actual ω k| ^ 2) μ := by
      intro k
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
          MemLp (fun ω : Ω => actual ω k) 2 μ := by
        simpa [actual, stepped, averageIterate, arithmeticAverage] using
          hsum.const_smul ((nodeCount (Node := Node) : ℝ)⁻¹)
      exact real_abs_sq_integrable_of_memLp_two havg_mem
    have herr_int :
        ∀ k : ℕ,
          Integrable
            (fun ω : Ω => |projected ω k - scalar ω k| ^ 2) μ := by
      intro k
      simpa [projected, scalar, stepped] using
        hprojected_scalar_error_square_integrable alpha k
    have hstable_int :
        ∀ k : ℕ, Integrable (fun ω : Ω => |stable ω k| ^ 2) μ := by
      intro k
      simpa [stable] using
        quadraticRestrictedStableBoundaryResponse_output_sq_integrable
          (Node := Node) quad lambda i0 P F μ oracle hnoise alpha k
    have hscalar_int :
        ∀ k : ℕ, Integrable (fun ω : Ω => |scalar ω k| ^ 2) μ := by
      intro k
      simpa [scalar] using hscalar_boundary_square_integrable alpha k
    have hdecomp :
        ∀ (ω : Ω) (k : ℕ),
          actual ω k =
            (projected ω k - scalar ω k) + stable ω k + scalar ω k := by
      intro ω k
      have hslow :
          actual ω k - stable ω k = projected ω k := by
        simpa [actual, projected, stable, stepped] using
          quadraticRestrictedSlowOutput_eq_projectedBoundary_at_block_start
            (Node := Node) quad lambda i0 r0 alpha_restricted theta K
            right left gamma P F hsplitting_restricted
            hrestricted_period_boundary_recursion halpha_abs
            (oracle.noise ω) k
      nlinarith
    have hproj_norm :=
      hprojected_scalar_block_boundary_average_l2_bound.2
        alpha halpha_pos halpha_le_block T halphaT
    have hproj_sum :
        Finset.sum (Finset.range T) (fun k =>
          ∫ ω, |projected ω k - scalar ω k| ^ 2 ∂μ) ≤
          Cblock * (T : ℝ) := by
      have hCblock_nonneg : 0 ≤ Cblock :=
        le_of_lt hprojected_scalar_block_boundary_average_l2_bound.1
      calc
        Finset.sum (Finset.range T) (fun k =>
            ∫ ω, |projected ω k - scalar ω k| ^ 2 ∂μ) =
          (T : ℝ) *
            ((T : ℝ)⁻¹ *
              Finset.sum (Finset.range T) (fun k =>
                ∫ ω, |projected ω k - scalar ω k| ^ 2 ∂μ)) := by
            field_simp [hT_ne]
        _ ≤ (T : ℝ) * (Cblock * alpha ^ 2) :=
            mul_le_mul_of_nonneg_left
              (by simpa [projected, scalar, stepped] using hproj_norm)
              hT_pos.le
        _ ≤ Cblock * (T : ℝ) := by
            calc
              (T : ℝ) * (Cblock * alpha ^ 2) =
                  (Cblock * (T : ℝ)) * alpha ^ 2 := by ring
              _ ≤ (Cblock * (T : ℝ)) * 1 :=
                  mul_le_mul_of_nonneg_left halpha_sq_le_one
                    (mul_nonneg hCblock_nonneg hT_pos.le)
              _ = Cblock * (T : ℝ) := by ring
    have hstable_norm :=
      hstable_average_bound alpha halpha_pos halpha_le_stable T hT_ge_one
    have hstable_sum :
        Finset.sum (Finset.range T) (fun k =>
          ∫ ω, |stable ω k| ^ 2 ∂μ) ≤
          Cstable * (T : ℝ) := by
      have hCstable_nonneg : 0 ≤ Cstable := le_of_lt hCstable_pos
      calc
        Finset.sum (Finset.range T) (fun k =>
            ∫ ω, |stable ω k| ^ 2 ∂μ) =
          (T : ℝ) *
            ((T : ℝ)⁻¹ *
              Finset.sum (Finset.range T) (fun k =>
                ∫ ω, |stable ω k| ^ 2 ∂μ)) := by
            field_simp [hT_ne]
        _ ≤ (T : ℝ) * (Cstable * alpha ^ 2) :=
            mul_le_mul_of_nonneg_left
              (by simpa [stable] using hstable_norm) hT_pos.le
        _ ≤ Cstable * (T : ℝ) := by
            calc
              (T : ℝ) * (Cstable * alpha ^ 2) =
                  (Cstable * (T : ℝ)) * alpha ^ 2 := by ring
              _ ≤ (Cstable * (T : ℝ)) * 1 :=
                  mul_le_mul_of_nonneg_left halpha_sq_le_one
                    (mul_nonneg hCstable_nonneg hT_pos.le)
              _ = Cstable * (T : ℝ) := by ring
    have hscalar_sum :
        Finset.sum (Finset.range T) (fun k =>
          ∫ ω, |scalar ω k| ^ 2 ∂μ) ≤
          CscalarBoundary * (T : ℝ) := by
      simpa [scalar] using
        hscalar_boundary_square_sum_bound alpha halpha_pos
          halpha_le_scalar_boundary T
    have havg_sum_raw :
        Finset.sum (Finset.range T) (fun k =>
          ∫ ω, |actual ω k| ^ 2 ∂μ) ≤
          (2 * Cblock + 4 * Cstable + 4 * CscalarBoundary) *
            (T : ℝ) :=
      block_start_average_l2_sum_bound_of_projected_stable_scalar_components
        (μ := μ) actual projected stable scalar hactual_int herr_int
        hstable_int hscalar_int hdecomp hproj_sum hstable_sum hscalar_sum
    have havg_sum :
        Finset.sum (Finset.range T) (fun k =>
          ∫ ω,
            |stepped.averageIterate (oracle.noise ω)
                (k * quad.period)| ^ 2 ∂μ) ≤
          Cavg * (T : ℝ) := by
      calc
        Finset.sum (Finset.range T) (fun k =>
            ∫ ω,
              |stepped.averageIterate (oracle.noise ω)
                  (k * quad.period)| ^ 2 ∂μ) =
            Finset.sum (Finset.range T) (fun k =>
              ∫ ω, |actual ω k| ^ 2 ∂μ) := by rfl
        _ ≤ (2 * Cblock + 4 * Cstable + 4 * CscalarBoundary) *
              (T : ℝ) := havg_sum_raw
        _ ≤ Cavg * (T : ℝ) := by
            dsimp [Cavg]
            nlinarith [hT_pos.le]
    simpa [Cgrad, stepped] using
      blockGradientEnergy_le_linear_average_block_start_l2_of_havg_linear
        (Node := Node) quad lambda μ oracle havg_linear
        (alpha := alpha) (Cavg := Cavg) (T := T) havg_sum
  obtain ⟨alphaActualFloor, CactualFloor, halphaActualFloor_pos,
      hCactualFloor_nonneg, hactual_floor_component_bound⟩ :
      ∃ alphaActualFloor CactualFloor : ℝ,
        0 < alphaActualFloor ∧ 0 ≤ CactualFloor ∧
          ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaActualFloor →
            ∀ T : ℕ, 1 ≤ alpha * (T : ℝ) →
              ((T : ℝ)⁻¹) *
                Finset.sum (Finset.range T) (fun t =>
                  ∫ ω,
                    |(quad.withStepsize alpha).averageIterate
                        (oracle.noise ω) t -
                      (quad.withStepsize alpha).averageIterate
                        (oracle.noise ω)
                          ((t / quad.period) * quad.period)| ^ 2 ∂μ) ≤
                CactualFloor * alpha ^ 2 := by
    obtain ⟨Cgrad, alphaGrad, hCgrad_nonneg, halphaGrad_pos,
      hblockGradient_linear⟩ :=
      hactual_floor_block_gradient_linear_budget
    let Cd : ℝ :=
      quad.finalDisplacementInitialConstant *
          quad.initialGradientHeterogeneity ^ 2 +
        quad.finalDisplacementGradientConstant * Cgrad +
        quad.finalDisplacementNoiseConstant *
          (nodeCount (Node := Node) : ℝ) * quad.sigma ^ 2 *
            (quad.period : ℝ) + 1
    let alphaD : ℝ := min quad.alphaStable alphaGrad
    have halphaD_pos : 0 < alphaD := by
      dsimp [alphaD]
      exact lt_min quad.alphaStable_pos halphaGrad_pos
    have hD0_nonneg : 0 ≤ quad.finalDisplacementInitialConstant := by
      simpa [sectionSixFinalConstants] using
        quad.sectionSixFinalConstants_nonneg ⟨0, by decide⟩
    have hDg_nonneg : 0 ≤ quad.finalDisplacementGradientConstant := by
      simpa [sectionSixFinalConstants] using
        quad.sectionSixFinalConstants_nonneg ⟨1, by decide⟩
    have hDsigma_nonneg : 0 ≤ quad.finalDisplacementNoiseConstant := by
      simpa [sectionSixFinalConstants] using
        quad.sectionSixFinalConstants_nonneg ⟨2, by decide⟩
    have hCd_nonneg : 0 ≤ Cd := by
      dsimp [Cd]
      positivity
    have horacle_all :
        ∀ alpha : ℝ,
          (quad.withStepsize alpha).StochasticOracleAssumptions μ oracle := by
      intro alpha
      simpa [StochasticOracleAssumptions, withStepsize] using hnoise.1
    have hD_budget :
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaD →
          ∀ T : ℕ, 1 ≤ alpha * (T : ℝ) →
            (quad.withStepsize alpha).displacementEnergy μ oracle
                (T * quad.period) ≤
              Cd * alpha ^ 2 * (T : ℝ) := by
      intro alpha halpha_pos halpha_le T halphaT
      let stepped := quad.withStepsize alpha
      have halpha_le_stable : alpha ≤ quad.alphaStable := by
        exact le_trans halpha_le (by dsimp [alphaD]; exact min_le_left _ _)
      have halpha_le_grad : alpha ≤ alphaGrad := by
        exact le_trans halpha_le (by dsimp [alphaD]; exact min_le_right _ _)
      have hsection0 :=
        quad.SectionSixFinalDisplacementConsensusEstimates
          μ oracle alpha T hnoise.1 halpha_pos halpha_le_stable
      dsimp only at hsection0
      have hsection :
          stepped.displacementEnergy μ oracle (T * quad.period) ≤
            alpha ^ 2 *
              (quad.finalDisplacementInitialConstant *
                  quad.initialGradientHeterogeneity ^ 2 +
                quad.finalDisplacementGradientConstant *
                  stepped.blockGradientEnergy μ oracle T +
                quad.finalDisplacementNoiseConstant *
                  (nodeCount (Node := Node) : ℝ) * quad.sigma ^ 2 *
                    (T * quad.period)) := by
        simpa [stepped, completeBlockHorizon] using hsection0.1
      have hT_pos : 0 < T := by
        by_contra hnot
        have hT_zero : T = 0 := by omega
        simp [hT_zero] at halphaT
        norm_num at halphaT
      have hT_nonneg : 0 ≤ (T : ℝ) := Nat.cast_nonneg T
      have hblockG :=
        hblockGradient_linear alpha halpha_pos halpha_le_grad T halphaT
      have hinside_le :
          quad.finalDisplacementInitialConstant *
              quad.initialGradientHeterogeneity ^ 2 +
            quad.finalDisplacementGradientConstant *
              stepped.blockGradientEnergy μ oracle T +
            quad.finalDisplacementNoiseConstant *
              (nodeCount (Node := Node) : ℝ) * quad.sigma ^ 2 *
                (T * quad.period) ≤
          Cd * (T : ℝ) := by
        have hT_ge_one_real : (1 : ℝ) ≤ T := by
          exact_mod_cast Nat.succ_le_of_lt hT_pos
        have hinit_le :
            quad.finalDisplacementInitialConstant *
                quad.initialGradientHeterogeneity ^ 2 ≤
              (quad.finalDisplacementInitialConstant *
                quad.initialGradientHeterogeneity ^ 2) * (T : ℝ) := by
          have hinit_nonneg :
              0 ≤ quad.finalDisplacementInitialConstant *
                quad.initialGradientHeterogeneity ^ 2 := by
            positivity
          nlinarith
        have hG_le :
            quad.finalDisplacementGradientConstant *
                stepped.blockGradientEnergy μ oracle T ≤
              (quad.finalDisplacementGradientConstant * Cgrad) * (T : ℝ) := by
          have hscale :=
            mul_le_mul_of_nonneg_left hblockG hDg_nonneg
          nlinarith
        have hnoise_eq :
            quad.finalDisplacementNoiseConstant *
                (nodeCount (Node := Node) : ℝ) * quad.sigma ^ 2 *
                  (T * quad.period) =
              (quad.finalDisplacementNoiseConstant *
                (nodeCount (Node := Node) : ℝ) * quad.sigma ^ 2 *
                  (quad.period : ℝ)) * (T : ℝ) := by
          norm_num [Nat.cast_mul]
          ring
        rw [hnoise_eq]
        dsimp [Cd]
        nlinarith
      calc
        stepped.displacementEnergy μ oracle (T * quad.period) ≤
            alpha ^ 2 *
              (quad.finalDisplacementInitialConstant *
                  quad.initialGradientHeterogeneity ^ 2 +
                quad.finalDisplacementGradientConstant *
                  stepped.blockGradientEnergy μ oracle T +
                quad.finalDisplacementNoiseConstant *
                  (nodeCount (Node := Node) : ℝ) * quad.sigma ^ 2 *
                    (T * quad.period)) := hsection
        _ ≤ alpha ^ 2 * (Cd * (T : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hinside_le (sq_nonneg alpha)
        _ = Cd * alpha ^ 2 * (T : ℝ) := by ring
    exact
      actual_floor_block_average_l2_bound_of_displacement_energy_budget
        (Node := Node) quad μ oracle quad.period
        (Nat.succ_le_of_lt quad.period_pos) alphaD Cd
        halphaD_pos hCd_nonneg horacle_all hD_budget
  let CstableSample : ℝ :=
    (quad.period : ℝ) *
      (2 * Cstable + 2 * ((quad.period : ℝ) * Cstable))
  let CstableFloor : ℝ :=
    2 * Cstable +
      2 * ((quad.period : ℝ) * ((quad.period : ℝ) * Cstable))
  let CremFull : ℝ :=
    4 * CstableSample + 6 * CactualFloor +
      6 * CstableFloor + 6 * CscalarFloor
  let Cphase : ℝ := 4
  let Cslow : ℝ :=
    Cphase * (quad.period : ℝ) * Cblock + CremFull + 1
  let alphaSlow : ℝ :=
    min (min (min alphaBlock alphaStable) alphaScalarFloor) alphaActualFloor
  have hCslow_pos : 0 < Cslow := by
    have hCblock_pos :=
      hprojected_scalar_block_boundary_average_l2_bound.1
    have hperiod_nonneg : 0 ≤ (quad.period : ℝ) := Nat.cast_nonneg quad.period
    have hCstable_nonneg : 0 ≤ Cstable := le_of_lt hCstable_pos
    have hCstableSample_nonneg : 0 ≤ CstableSample := by
      dsimp [CstableSample]
      positivity
    have hCstableFloor_nonneg : 0 ≤ CstableFloor := by
      dsimp [CstableFloor]
      positivity
    have hCscalarFloor_nonneg : 0 ≤ CscalarFloor := by
      dsimp [CscalarFloor]
      positivity
    have hCremFull_nonneg : 0 ≤ CremFull := by
      dsimp [CremFull]
      nlinarith [hCstableSample_nonneg, hCactualFloor_nonneg,
        hCstableFloor_nonneg, hCscalarFloor_nonneg]
    have hphase_nonneg : 0 ≤ Cphase := by
      dsimp [Cphase]
      nlinarith [hCstable_pos]
    dsimp [Cslow]
    nlinarith [hCblock_pos, hperiod_nonneg, hphase_nonneg,
      hCremFull_nonneg]
  have halphaSlow_pos : 0 < alphaSlow := by
    dsimp [alphaSlow]
    exact
      lt_min
        (lt_min (lt_min halphaBlock_pos halphaStable_pos)
          (lt_min halphaScalarFloorPhase_pos
            (lt_min halphaScalarFloorBoundary_pos
              halphaScalarFloorFresh_pos)))
        halphaActualFloor_pos
  refine ⟨Cslow, alphaSlow, hCslow_pos, halphaSlow_pos, ?_, ?_⟩
  · intro alpha t
    simpa using
      quadratic_restricted_slow_output_scalar_error_sq_integrable
        (Node := Node) quad lambda i0 P F μ oracle hnoise alpha t
  · intro alpha halpha_pos halpha_le_slow T halphaT
    have halpha_le_block : alpha ≤ alphaBlock := by
      exact le_trans halpha_le_slow
        (le_trans (by dsimp [alphaSlow]; exact min_le_left _ _)
          (le_trans (min_le_left _ _) (min_le_left _ _)))
    have halpha_le_stable : alpha ≤ alphaStable := by
      exact le_trans halpha_le_slow
        (le_trans (by dsimp [alphaSlow]; exact min_le_left _ _)
          (le_trans (min_le_left _ _) (min_le_right _ _)))
    have halpha_le_scalar_floor : alpha ≤ alphaScalarFloor := by
      exact le_trans halpha_le_slow
        (le_trans (by dsimp [alphaSlow]; exact min_le_left _ _)
          (min_le_right _ _))
    have halpha_le_actual_floor : alpha ≤ alphaActualFloor := by
      exact le_trans halpha_le_slow
        (by dsimp [alphaSlow]; exact min_le_right _ _)
    have halpha_le_scalar_floor_phase :
        alpha ≤ alphaScalarFloorPhase := by
      exact le_trans halpha_le_scalar_floor
        (by dsimp [alphaScalarFloor]; exact min_le_left _ _)
    have halpha_le_scalar_floor_boundary :
        alpha ≤ alphaScalarFloorBoundary := by
      exact le_trans halpha_le_scalar_floor
        (by
          dsimp [alphaScalarFloor]
          exact le_trans (min_le_right _ _) (min_le_left _ _))
    have halpha_le_scalar_floor_fresh :
        alpha ≤ alphaScalarFloorFresh := by
      exact le_trans halpha_le_scalar_floor
        (by
          dsimp [alphaScalarFloor]
          exact le_trans (min_le_right _ _) (min_le_right _ _))
    have hblock_bound :=
      hprojected_scalar_block_boundary_average_l2_bound.2
        alpha halpha_pos halpha_le_block T halphaT
    have halpha_le_restricted : alpha ≤ alpha_restricted :=
      le_trans halpha_le_block halphaBlock_le_restricted
    have halpha_abs : |alpha| ≤ alpha_restricted := by
      simpa [abs_of_pos halpha_pos] using halpha_le_restricted
    let stableOut : Ω → ℕ → ℝ := fun ω t =>
      quadraticRestrictedPrimalAverageOutput (Node := Node) i0
        (quadraticRestrictedStableBoundaryResponse
          (Node := Node) quad lambda i0 P F alpha (oracle.noise ω) t)
    let out : Ω → ℕ → ℝ := fun ω t => Real.sqrt 2 * stableOut ω t
    let f : ℕ → ℝ := fun t =>
      ∫ ω,
        |((quad.withStepsize alpha).averageIterate (oracle.noise ω) t -
            stableOut ω t) -
          quad.quadraticScalarComparisonProcess lambda alpha
            (oracle.noise ω) t| ^ 2 ∂μ
    let g : ℕ → ℝ := fun k =>
      ∫ ω,
        |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
            (matrixMulVector
              (Node := Sum Node {i : Node // i ≠ i0})
              (P alpha)
              (restrictedStateToCoord (Node := Node) i0
                ((quad.withStepsize alpha).primalState
                    (oracle.noise ω) (k * quad.period),
                  (quad.withStepsize alpha).trackerErrorZeroSum
                    (oracle.noise ω) (k * quad.period)))) -
          quad.quadraticScalarComparisonProcess lambda alpha
            (oracle.noise ω) (k * quad.period)| ^ 2 ∂μ
    have hblock_start_phase_majorant :
        ∀ ω : Ω, ∀ k : ℕ,
          |((quad.withStepsize alpha).averageIterate (oracle.noise ω)
                (k * quad.period) -
              quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                (quadraticRestrictedStableBoundaryResponse
                  (Node := Node) quad lambda i0 P F alpha
                  (oracle.noise ω) (k * quad.period))) -
            quad.quadraticScalarComparisonProcess lambda alpha
              (oracle.noise ω) (k * quad.period)| ^ 2 ≤
            2 *
              |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                    (matrixMulVector
                      (Node := Sum Node {i : Node // i ≠ i0})
                      (P alpha)
                      (restrictedStateToCoord (Node := Node) i0
                        ((quad.withStepsize alpha).primalState
                            (oracle.noise ω) (k * quad.period),
                          (quad.withStepsize alpha).trackerErrorZeroSum
                            (oracle.noise ω) (k * quad.period)))) -
                  quad.quadraticScalarComparisonProcess lambda alpha
                    (oracle.noise ω) (k * quad.period)| ^ 2 +
              2 *
                |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                      (quadraticRestrictedStableBoundaryResponse
                        (Node := Node) quad lambda i0 P F alpha
                        (oracle.noise ω) k) -
                    quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                      (quadraticRestrictedStableBoundaryResponse
                        (Node := Node) quad lambda i0 P F alpha
                        (oracle.noise ω) (k * quad.period))| ^ 2 := by
      intro ω k
      simpa using
        quadraticRestrictedSlowOutput_block_start_error_sq_le_projectedBoundary_add_stable_remainder
          (Node := Node) quad lambda i0 r0 alpha_restricted theta K
          right left gamma P F hsplitting_restricted
          hrestricted_period_boundary_recursion halpha_abs
          (oracle.noise ω) k
    have hg_nonneg : ∀ k : ℕ, 0 ≤ g k := by
      intro k
      dsimp [g]
      exact integral_nonneg fun ω => sq_nonneg _
    have hout_int :
        ∀ t : ℕ, Integrable (fun ω : Ω => |out ω t| ^ 2) μ := by
      intro t
      have hbase :
          Integrable (fun ω : Ω => |stableOut ω t| ^ 2) μ := by
        simpa [stableOut] using
          quadraticRestrictedStableBoundaryResponse_output_sq_integrable
            (Node := Node) quad lambda i0 P F μ oracle hnoise alpha t
      have hscale :
          (fun ω : Ω => |out ω t| ^ 2) =
            fun ω : Ω => (Real.sqrt 2) ^ 2 * |stableOut ω t| ^ 2 := by
        funext ω
        change |Real.sqrt 2 * stableOut ω t| ^ 2 =
          (Real.sqrt 2) ^ 2 * |stableOut ω t| ^ 2
        rw [abs_mul, mul_pow, sq_abs (Real.sqrt 2)]
      rw [hscale]
      exact hbase.const_mul ((Real.sqrt 2) ^ 2)
    have hdiff_int :
        ∀ t : ℕ,
          Integrable (fun ω : Ω =>
            |out ω t - out ω (t * quad.period)| ^ 2) μ := by
      intro t
      have hmem_t :
          MemLp (fun ω : Ω => out ω t) 2 μ := by
        have hstable_mem :=
          quadraticRestrictedStableBoundaryResponse_output_memLp_two
            (Node := Node) quad lambda i0 P F μ oracle hnoise alpha t
        simpa [out, stableOut] using hstable_mem.const_smul (Real.sqrt 2)
      have hmem_tp :
          MemLp (fun ω : Ω => out ω (t * quad.period)) 2 μ := by
        have hstable_mem :=
          quadraticRestrictedStableBoundaryResponse_output_memLp_two
            (Node := Node) quad lambda i0 P F μ oracle hnoise alpha
            (t * quad.period)
        simpa [out, stableOut] using hstable_mem.const_smul (Real.sqrt 2)
      exact real_abs_sq_integrable_of_memLp_two (hmem_t.sub hmem_tp)
    let scalarOut : Ω → ℕ → ℝ := fun ω t =>
      quad.quadraticScalarComparisonProcess lambda alpha
        (oracle.noise ω) t
    let rem : ℕ → ℝ := fun t =>
      ∫ ω,
        (2 *
            (2 *
              |stableOut ω (t / quad.period) -
                stableOut ω ((t / quad.period) * quad.period)| ^ 2) +
          6 *
            |(quad.withStepsize alpha).averageIterate
                (oracle.noise ω) t -
              (quad.withStepsize alpha).averageIterate
                (oracle.noise ω) ((t / quad.period) * quad.period)| ^ 2 +
          6 *
            |stableOut ω t -
              stableOut ω ((t / quad.period) * quad.period)| ^ 2 +
          6 *
            |scalarOut ω t -
              scalarOut ω ((t / quad.period) * quad.period)| ^ 2) ∂μ
    have hactual_mem :
        ∀ t : ℕ,
          MemLp
            (fun ω : Ω =>
              (quad.withStepsize alpha).averageIterate
                (oracle.noise ω) t) 2 μ := by
      intro t
      let stepped := quad.withStepsize alpha
      have hstepped_oracle :
          stepped.StochasticOracleAssumptions μ oracle := by
        simpa [stepped, StochasticOracleAssumptions, withStepsize] using
          hnoise.1
      have hgenerated :=
        stepped.generated_pushpull_coordinate_memLp μ oracle hstepped_oracle t
      have hsum :
          MemLp
            (fun ω : Ω =>
              ∑ i : Node,
                stepped.primalState (oracle.noise ω) t i) 2 μ := by
        apply memLp_finset_sum Finset.univ
        intro i _hi
        exact hgenerated.1 i
      simpa [stepped, averageIterate, arithmeticAverage] using
        hsum.const_smul ((nodeCount (Node := Node) : ℝ)⁻¹)
    have hstable_mem :
        ∀ t : ℕ,
          MemLp (fun ω : Ω => stableOut ω t) 2 μ := by
      intro t
      simpa [stableOut] using
        quadraticRestrictedStableBoundaryResponse_output_memLp_two
          (Node := Node) quad lambda i0 P F μ oracle hnoise alpha t
    have hscalar_mem :
        ∀ t : ℕ,
          MemLp (fun ω : Ω => scalarOut ω t) 2 μ := by
      intro t
      simpa [scalarOut] using
        quadraticScalarComparisonProcess_memLp_two
          (Node := Node) quad lambda alpha μ oracle hnoise.1 t
    have hrem_int :
        ∀ t : ℕ,
          Integrable
            (fun ω : Ω =>
              (2 *
                  (2 *
                    |stableOut ω (t / quad.period) -
                      stableOut ω ((t / quad.period) * quad.period)| ^ 2) +
                6 *
                  |(quad.withStepsize alpha).averageIterate
                      (oracle.noise ω) t -
                    (quad.withStepsize alpha).averageIterate
                      (oracle.noise ω)
                        ((t / quad.period) * quad.period)| ^ 2 +
                6 *
                  |stableOut ω t -
                    stableOut ω ((t / quad.period) * quad.period)| ^ 2 +
                6 *
                  |scalarOut ω t -
                    scalarOut ω ((t / quad.period) * quad.period)| ^ 2)) μ := by
      intro t
      have hblock_stable :
          Integrable
            (fun ω : Ω =>
              |stableOut ω (t / quad.period) -
                stableOut ω ((t / quad.period) * quad.period)| ^ 2) μ :=
        real_abs_sq_integrable_of_memLp_two
          ((hstable_mem (t / quad.period)).sub
            (hstable_mem ((t / quad.period) * quad.period)))
      have hactual :
          Integrable
            (fun ω : Ω =>
              |(quad.withStepsize alpha).averageIterate
                  (oracle.noise ω) t -
                (quad.withStepsize alpha).averageIterate
                  (oracle.noise ω)
                    ((t / quad.period) * quad.period)| ^ 2) μ :=
        real_abs_sq_integrable_of_memLp_two
          ((hactual_mem t).sub
            (hactual_mem ((t / quad.period) * quad.period)))
      have hstable :
          Integrable
            (fun ω : Ω =>
              |stableOut ω t -
                stableOut ω ((t / quad.period) * quad.period)| ^ 2) μ :=
        real_abs_sq_integrable_of_memLp_two
          ((hstable_mem t).sub
            (hstable_mem ((t / quad.period) * quad.period)))
      have hscalar :
          Integrable
            (fun ω : Ω =>
              |scalarOut ω t -
                scalarOut ω ((t / quad.period) * quad.period)| ^ 2) μ :=
        real_abs_sq_integrable_of_memLp_two
          ((hscalar_mem t).sub
            (hscalar_mem ((t / quad.period) * quad.period)))
      simpa [add_assoc] using
        (((hblock_stable.const_mul 2).const_mul 2).add
          (hactual.const_mul 6)).add
            ((hstable.const_mul 6).add (hscalar.const_mul 6))
    have hphase :
        ∀ t : ℕ,
          f t ≤
            Cphase * g (t / quad.period) + rem t := by
      intro t
      let boundaryErr : Ω → ℝ := fun ω =>
        |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
            (matrixMulVector
              (Node := Sum Node {i : Node // i ≠ i0})
              (P alpha)
              (restrictedStateToCoord (Node := Node) i0
                ((quad.withStepsize alpha).primalState
                    (oracle.noise ω)
                    ((t / quad.period) * quad.period),
                  (quad.withStepsize alpha).trackerErrorZeroSum
                    (oracle.noise ω)
                    ((t / quad.period) * quad.period)))) -
          scalarOut ω ((t / quad.period) * quad.period)| ^ 2
      let rpoint : Ω → ℝ := fun ω =>
        2 *
            (2 *
              |stableOut ω (t / quad.period) -
                stableOut ω ((t / quad.period) * quad.period)| ^ 2) +
          6 *
            |(quad.withStepsize alpha).averageIterate
                (oracle.noise ω) t -
              (quad.withStepsize alpha).averageIterate
                (oracle.noise ω) ((t / quad.period) * quad.period)| ^ 2 +
          6 *
            |stableOut ω t -
              stableOut ω ((t / quad.period) * quad.period)| ^ 2 +
          6 *
            |scalarOut ω t -
              scalarOut ω ((t / quad.period) * quad.period)| ^ 2
      have hboundary_int : Integrable boundaryErr μ := by
        simpa [boundaryErr, scalarOut] using
          hprojected_scalar_error_square_integrable alpha
            (t / quad.period)
      have hpoint :
          (fun ω : Ω =>
            |((quad.withStepsize alpha).averageIterate
                (oracle.noise ω) t -
                stableOut ω t) -
              scalarOut ω t| ^ 2) ≤
            fun ω : Ω => 4 * boundaryErr ω + 1 * rpoint ω := by
        intro ω
        have hblockω :
            ∀ k : ℕ,
              |((quad.withStepsize alpha).averageIterate
                    (oracle.noise ω) (k * quad.period) -
                  stableOut ω (k * quad.period)) -
                scalarOut ω (k * quad.period)| ^ 2 ≤
                2 *
                  |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                      (matrixMulVector
                        (Node := Sum Node {i : Node // i ≠ i0})
                        (P alpha)
                        (restrictedStateToCoord (Node := Node) i0
                          ((quad.withStepsize alpha).primalState
                              (oracle.noise ω) (k * quad.period),
                            (quad.withStepsize alpha).trackerErrorZeroSum
                              (oracle.noise ω) (k * quad.period)))) -
                    scalarOut ω (k * quad.period)| ^ 2 +
                  2 *
                    |stableOut ω k -
                      stableOut ω (k * quad.period)| ^ 2 := by
          intro k
          simpa [stableOut, scalarOut] using
            hblock_start_phase_majorant ω k
        have hraw :=
          quadraticRestrictedSlowOutput_raw_time_error_sq_le_block_boundary_add_within_period_remainder
            (actual := fun s : ℕ =>
              (quad.withStepsize alpha).averageIterate
                (oracle.noise ω) s)
            (stable := fun s : ℕ => stableOut ω s)
            (scalar := fun s : ℕ => scalarOut ω s)
            (p := quad.period)
            (g := fun k : ℕ =>
              |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                  (matrixMulVector
                    (Node := Sum Node {i : Node // i ≠ i0})
                    (P alpha)
                    (restrictedStateToCoord (Node := Node) i0
                      ((quad.withStepsize alpha).primalState
                          (oracle.noise ω) (k * quad.period),
                        (quad.withStepsize alpha).trackerErrorZeroSum
                          (oracle.noise ω) (k * quad.period)))) -
                scalarOut ω (k * quad.period)| ^ 2)
            (blockR := fun k : ℕ =>
              2 * |stableOut ω k -
                stableOut ω (k * quad.period)| ^ 2)
            (Cphase := 2)
            (by
              intro k
              simpa [scalarOut] using hblockω k)
            t
        dsimp [boundaryErr, rpoint, scalarOut] at hraw ⊢
        nlinarith [hraw]
      have hraw_int :
          Integrable
            (fun ω : Ω =>
              |((quad.withStepsize alpha).averageIterate
                  (oracle.noise ω) t -
                  stableOut ω t) -
                scalarOut ω t| ^ 2) μ := by
        simpa [stableOut, scalarOut] using
          quadratic_restricted_slow_output_scalar_error_sq_integrable
            (Node := Node) quad lambda i0 P F μ oracle hnoise alpha t
      have hupper :=
        integral_le_integral_affine_combination μ
          (fun ω : Ω =>
            |((quad.withStepsize alpha).averageIterate
                (oracle.noise ω) t -
                stableOut ω t) -
              scalarOut ω t| ^ 2)
          boundaryErr rpoint 4 1 hraw_int hboundary_int
          (by simpa [rpoint] using hrem_int t) hpoint
      simpa [f, g, rem, boundaryErr, rpoint, Cphase, scalarOut] using
        hupper
    have hblock_for_bridge :
        ((T : ℝ)⁻¹) * Finset.sum (Finset.range T) g ≤
          Cblock * alpha ^ 2 := by
      simpa [g] using hblock_bound
    have hremainder :
        ((T : ℝ)⁻¹) * Finset.sum (Finset.range T) rem ≤
          CremFull * alpha ^ 2 := by
      have hperiod_one : 1 ≤ quad.period :=
        Nat.succ_le_of_lt quad.period_pos
      have hstable_raw_average :
          ∀ N : ℕ, 1 ≤ alpha * (N : ℝ) →
            ((N : ℝ)⁻¹) *
              Finset.sum (Finset.range N) (fun t =>
                ∫ ω, |stableOut ω t| ^ 2 ∂μ) ≤
              Cstable * alpha ^ 2 := by
        intro N hNalpha
        have hN_one : 1 ≤ N := by
          cases N with
          | zero =>
              have hbad : ¬ ((1 : ℝ) ≤ alpha * (0 : ℝ)) := by norm_num
              exact False.elim (hbad (by simpa using hNalpha))
          | succ N =>
              exact Nat.succ_le_succ (Nat.zero_le N)
        simpa using
          hstable_average_bound alpha halpha_pos halpha_le_stable N hN_one
      have hstable_index_int :
          ∀ k : ℕ,
            Integrable
              (fun ω : Ω =>
                |stableOut ω k - stableOut ω (k * quad.period)| ^ 2) μ := by
        intro k
        exact
          real_abs_sq_integrable_of_memLp_two
            ((hstable_mem k).sub (hstable_mem (k * quad.period)))
      have hstable_floor_int :
          ∀ t : ℕ,
            Integrable
              (fun ω : Ω =>
                |stableOut ω t -
                  stableOut ω ((t / quad.period) * quad.period)| ^ 2) μ := by
        intro t
        exact
          real_abs_sq_integrable_of_memLp_two
            ((hstable_mem t).sub
              (hstable_mem ((t / quad.period) * quad.period)))
      have hstable_components :=
        stable_phase_remainder_components_average_bound
          (μ := μ) (p := quad.period) hperiod_one stableOut
          (C := Cstable) (alpha := alpha)
          (by
            intro t
            exact
              real_abs_sq_integrable_of_memLp_two (hstable_mem t))
          hstable_index_int hstable_floor_int hstable_raw_average halphaT
      have hstable_sample_component :
          ((T : ℝ)⁻¹) *
              Finset.sum (Finset.range T) (fun t =>
                ∫ ω,
                  |stableOut ω (t / quad.period) -
                    stableOut ω ((t / quad.period) * quad.period)| ^ 2 ∂μ) ≤
            CstableSample *
              alpha ^ 2 :=
        by simpa [CstableSample] using hstable_components.1
      have hstable_floor_component :
          ((T : ℝ)⁻¹) *
              Finset.sum (Finset.range T) (fun t =>
                ∫ ω,
                  |stableOut ω t -
                    stableOut ω ((t / quad.period) * quad.period)| ^ 2 ∂μ) ≤
            CstableFloor *
              alpha ^ 2 :=
        by simpa [CstableFloor] using hstable_components.2
      have hactual_floor_component :
          ((T : ℝ)⁻¹) *
              Finset.sum (Finset.range T) (fun t =>
                ∫ ω,
                  |(quad.withStepsize alpha).averageIterate
                      (oracle.noise ω) t -
                    (quad.withStepsize alpha).averageIterate
                      (oracle.noise ω)
                        ((t / quad.period) * quad.period)| ^ 2 ∂μ) ≤
            CactualFloor * alpha ^ 2 :=
        hactual_floor_component_bound alpha halpha_pos
          halpha_le_actual_floor T halphaT
      have hscalar_floor_component :
          ((T : ℝ)⁻¹) *
              Finset.sum (Finset.range T) (fun t =>
                ∫ ω,
                  |scalarOut ω t -
                    scalarOut ω ((t / quad.period) * quad.period)| ^ 2 ∂μ) ≤
            CscalarFloor * alpha ^ 2 := by
        have hphase_residue :
            ∀ r : ℕ, r < quad.period →
              |quadraticScalarWithinPeriodMultiplier (Node := Node)
                  quad lambda alpha r - 1| ≤
                CscalarFloorPhase * alpha := by
          intro r hr
          exact hscalar_floor_phase alpha halpha_pos
            halpha_le_scalar_floor_phase r hr
        have hboundary_uniform :
            ∀ k : ℕ,
              quadraticScalarBlockBoundarySecondMoment (Node := Node)
                quad lambda alpha μ oracle k ≤ CscalarFloorBoundary := by
          intro k
          exact hscalar_floor_boundary alpha halpha_pos
            halpha_le_scalar_floor_boundary k
        have hfresh_uniform :
            ∀ k r : ℕ, r < quad.period →
              (∫ ω,
                |quadraticScalarWindowPropagatedNoiseFinset (Node := Node)
                  quad lambda alpha (oracle.noise ω) (quad.blockStart k) r| ^ 2
                  ∂μ) ≤ CscalarFloorFresh := by
          intro k r hr
          exact hscalar_floor_fresh alpha halpha_pos
            halpha_le_scalar_floor_fresh k r hr
        simpa [scalarOut, CscalarFloor] using
          quadraticScalarComparisonProcess_floor_block_average_l2_bound_of_components
            (Node := Node) quad lambda μ oracle hnoise
            (alpha := alpha) (Cphase := CscalarFloorPhase)
            (Cboundary := CscalarFloorBoundary)
            (Cfresh := CscalarFloorFresh)
            halpha_pos hCscalarFloorPhase_nonneg
            hCscalarFloorBoundary_nonneg hCscalarFloorFresh_nonneg
            hphase_residue hboundary_uniform hfresh_uniform
            (T := T) halphaT
      let stableSample : ℕ → ℝ := fun t =>
        ∫ ω,
          |stableOut ω (t / quad.period) -
            stableOut ω ((t / quad.period) * quad.period)| ^ 2 ∂μ
      let actualFloor : ℕ → ℝ := fun t =>
        ∫ ω,
          |(quad.withStepsize alpha).averageIterate
              (oracle.noise ω) t -
            (quad.withStepsize alpha).averageIterate
              (oracle.noise ω) ((t / quad.period) * quad.period)| ^ 2 ∂μ
      let stableFloor : ℕ → ℝ := fun t =>
        ∫ ω,
          |stableOut ω t -
            stableOut ω ((t / quad.period) * quad.period)| ^ 2 ∂μ
      let scalarFloor : ℕ → ℝ := fun t =>
        ∫ ω,
          |scalarOut ω t -
            scalarOut ω ((t / quad.period) * quad.period)| ^ 2 ∂μ
      have hr :
          ∀ t : ℕ,
            rem t ≤
              4 * stableSample t + 6 * actualFloor t +
                6 * stableFloor t + 6 * scalarFloor t := by
        intro t
        let A : Ω → ℝ := fun ω =>
          2 *
            (2 *
              |stableOut ω (t / quad.period) -
                stableOut ω ((t / quad.period) * quad.period)| ^ 2)
        let B : Ω → ℝ := fun ω =>
          6 *
            |(quad.withStepsize alpha).averageIterate
                (oracle.noise ω) t -
              (quad.withStepsize alpha).averageIterate
                (oracle.noise ω) ((t / quad.period) * quad.period)| ^ 2
        let C : Ω → ℝ := fun ω =>
          6 *
            |stableOut ω t -
              stableOut ω ((t / quad.period) * quad.period)| ^ 2
        let D : Ω → ℝ := fun ω =>
          6 *
            |scalarOut ω t -
              scalarOut ω ((t / quad.period) * quad.period)| ^ 2
        have hSA :
            Integrable
              (fun ω : Ω =>
                |stableOut ω (t / quad.period) -
                  stableOut ω ((t / quad.period) * quad.period)| ^ 2) μ :=
          real_abs_sq_integrable_of_memLp_two
            ((hstable_mem (t / quad.period)).sub
              (hstable_mem ((t / quad.period) * quad.period)))
        have hAF :
            Integrable
              (fun ω : Ω =>
                |(quad.withStepsize alpha).averageIterate
                    (oracle.noise ω) t -
                  (quad.withStepsize alpha).averageIterate
                    (oracle.noise ω)
                      ((t / quad.period) * quad.period)| ^ 2) μ :=
          real_abs_sq_integrable_of_memLp_two
            ((hactual_mem t).sub
              (hactual_mem ((t / quad.period) * quad.period)))
        have hSF :
            Integrable
              (fun ω : Ω =>
                |stableOut ω t -
                  stableOut ω ((t / quad.period) * quad.period)| ^ 2) μ :=
          real_abs_sq_integrable_of_memLp_two
            ((hstable_mem t).sub
              (hstable_mem ((t / quad.period) * quad.period)))
        have hSC :
            Integrable
              (fun ω : Ω =>
                |scalarOut ω t -
                  scalarOut ω ((t / quad.period) * quad.period)| ^ 2) μ :=
          real_abs_sq_integrable_of_memLp_two
            ((hscalar_mem t).sub
              (hscalar_mem ((t / quad.period) * quad.period)))
        have hA : Integrable A μ := by
          dsimp [A]
          exact (hSA.const_mul 2).const_mul 2
        have hB : Integrable B μ := by
          dsimp [B]
          exact hAF.const_mul 6
        have hC : Integrable C μ := by
          dsimp [C]
          exact hSF.const_mul 6
        have hD : Integrable D μ := by
          dsimp [D]
          exact hSC.const_mul 6
        dsimp [rem, stableSample, actualFloor, stableFloor, scalarFloor]
        change (∫ ω, ((A ω + B ω) + C ω) + D ω ∂μ) ≤
          4 * (∫ ω,
                |stableOut ω (t / quad.period) -
                  stableOut ω ((t / quad.period) * quad.period)| ^ 2 ∂μ) +
            6 * (∫ ω,
                |(quad.withStepsize alpha).averageIterate
                    (oracle.noise ω) t -
                  (quad.withStepsize alpha).averageIterate
                    (oracle.noise ω)
                      ((t / quad.period) * quad.period)| ^ 2 ∂μ) +
            6 * (∫ ω,
                |stableOut ω t -
                  stableOut ω ((t / quad.period) * quad.period)| ^ 2 ∂μ) +
            6 * (∫ ω,
                |scalarOut ω t -
                  scalarOut ω ((t / quad.period) * quad.period)| ^ 2 ∂μ)
        rw [MeasureTheory.integral_add, MeasureTheory.integral_add,
          MeasureTheory.integral_add]
        · dsimp [A, B, C, D]
          rw [MeasureTheory.integral_const_mul,
            MeasureTheory.integral_const_mul,
            MeasureTheory.integral_const_mul,
            MeasureTheory.integral_const_mul,
            MeasureTheory.integral_const_mul]
          linarith
        all_goals
          first
          | exact hA
          | exact hB
          | exact hC
          | exact hD
          | exact hA.add hB
          | exact (hA.add hB).add hC
      simpa [CremFull, stableSample, actualFloor, stableFloor, scalarFloor] using
        finite_phase_remainder_average_bound_of_component_bounds
          rem stableSample actualFloor stableFloor scalarFloor hr
          hstable_sample_component hactual_floor_component
          hstable_floor_component hscalar_floor_component
    have hfinite_phase :
        ((T : ℝ)⁻¹) * Finset.sum (Finset.range T) f ≤
          (Cphase * (quad.period : ℝ) * Cblock + CremFull) *
            alpha ^ 2 :=
      finite_phase_average_l2_bound_of_block_majorant_add_remainder
        (p := quad.period) quad.period_pos (f := f) (g := g) (r := rem)
        (T := T) (Cphase := Cphase) (Cblock := Cblock)
        (Crem := CremFull)
        (alpha := alpha)
        (by dsimp [Cphase]; norm_num) hg_nonneg hphase
        hblock_for_bridge hremainder
    have hconst_le :
        Cphase * (quad.period : ℝ) * Cblock + CremFull ≤
          Cslow := by
      dsimp [Cslow]
      linarith
    exact le_trans (by simpa [f, stableOut] using hfinite_phase)
      (mul_le_mul_of_nonneg_right hconst_le (sq_nonneg alpha))

theorem QuadraticSlowComparisonDetails :
    ∀ (quad : Setup Node ℝ) (lambda : ℝ)
      {Ω : Type} [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (oracle : OracleNoiseProcess Ω Node ℝ),
        HomogeneousQuadraticComponents (Node := Node) quad lambda →
          quad.ExactVarianceIidAdditiveNoise μ oracle →
        QuadraticSlowComparisonStatement (Node := Node) quad lambda μ oracle := by
  classical
  intro quad lambda Ω hΩ μ hμ oracle hquad hnoise
  have hgrad_linear :
      ∀ i : Node, ∀ x : ℝ, quad.componentGradient i x = lambda * x :=
    homogeneousQuadratic_componentGradient_eq_linear
      (Node := Node) quad lambda hquad
  have havg_linear :
      ∀ x : ℝ, quad.averageGradient x = lambda * x :=
    homogeneousQuadratic_averageGradient_eq_linear
      (Node := Node) quad lambda hquad
  have hfeedback_constants :
      ∀ alpha : ℝ,
        let stepped := quad.withStepsize alpha
        stepped.rhoInitialConstant = quad.rhoInitialConstant ∧
          stepped.stateFeedbackConsensusCoefficient =
              quad.stateFeedbackConsensusCoefficient ∧
            stepped.stateFeedbackDisplacementCoefficient =
              quad.stateFeedbackDisplacementCoefficient := by
    intro alpha
    exact quad.withStepsize_feedback_constants_eq alpha
  have hlift_step :
      ∀ alpha : ℝ, ∀ noise : NoisePath Node ℝ, ∀ t : ℕ,
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
    intro alpha noise t
    exact quadratic_true_lifted_one_step_recursion
      (Node := Node) quad lambda alpha hquad noise t
  have hblock_step :
      ∀ alpha : ℝ, ∀ noise : NoisePath Node ℝ, ∀ t : ℕ,
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
    intro alpha noise t
    exact quadratic_true_lifted_one_step_block_action
      (Node := Node) quad lambda alpha hquad noise t
  have hzero_sum_step :
      ∀ alpha : ℝ, ∀ noise : NoisePath Node ℝ, ∀ t : ℕ,
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
    intro alpha noise t
    exact quadratic_zero_sum_lifted_step_action
      (Node := Node) quad lambda alpha hquad noise t
  have hrestricted_base_stable_blocks :
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
                (consensusError (Node := Node) (E := ℝ) X)) :=
    quadratic_restricted_base_period_stable_blocks (Node := Node) quad
  let i0 : Node := Classical.choice (inferInstance : Nonempty Node)
  obtain ⟨toRestrictedCoord, ofRestrictedCoord,
      hrestrictedCoord_left, hrestrictedCoord_right⟩ :=
    restricted_state_coordinate_chart (Node := Node) i0
  have hrestricted_coord_step :
      ∀ alpha : ℝ, ∀ noise : NoisePath Node ℝ, ∀ t : ℕ,
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
        toRestrictedCoord
          (stepped.primalState noise (t + 1),
            stepped.trackerErrorZeroSum noise (t + 1)) =
          toRestrictedCoord
            (leftMul (Node := Node) (E := ℝ) (stepped.R t) X -
                alpha • (W.1 + Z + noise t),
              ⟨transported.1 + innovation.1,
                zeroSumState_add_mem transported innovation⟩) := by
    intro alpha noise t
    have hstep := hzero_sum_step alpha noise t
    exact congrArg toRestrictedCoord (Prod.ext hstep.1 hstep.2)
  have hrestricted_affine_coord_step :
      ∀ alpha : ℝ, ∀ noise : NoisePath Node ℝ, ∀ t : ℕ,
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
    intro alpha noise t
    exact
      quadraticRestrictedOneStepMatrix_affine_process_action
        (Node := Node) quad lambda alpha i0 hquad noise t
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
  have hrestricted_tracker_base_stable :
      ∀ (t : ℕ) (W : ZeroSumState Node ℝ),
        stateFrobeniusNorm (Node := Node) (E := ℝ)
            (leftMul (Node := Node) (E := ℝ)
              (quad.pullLiftProduct t quad.period) W.1) ≤
          quad.columnContractionConstant * quad.contractionRate ^ quad.period *
            stateFrobeniusNorm (Node := Node) (E := ℝ) W.1 :=
    hrestricted_base_stable_blocks.2.2.1
  have hrestricted_primal_base_stable :
      ∀ (t : ℕ) (X : State Node ℝ),
        stateFrobeniusNorm (Node := Node) (E := ℝ)
            (consensusError (Node := Node) (E := ℝ)
              (leftMul (Node := Node) (E := ℝ)
                (quad.pushLiftProduct t quad.period) X)) ≤
          quad.rowContractionConstant * quad.contractionRate ^ quad.period *
            stateFrobeniusNorm (Node := Node) (E := ℝ)
              (consensusError (Node := Node) (E := ℝ) X) :=
    hrestricted_base_stable_blocks.2.2.2
  obtain ⟨r0_restricted, right_restricted, left_restricted,
      alpha_restricted, theta_restricted, K_restricted,
      gamma_restricted, P_restricted, F_restricted,
      hr0_restricted_nonneg, halpha_restricted_le_one,
      hP0_restricted, hright_restricted_eq, hright_restricted_top,
      hleft_restricted_top, hleft_restricted_bottom,
      hsplitting_restricted⟩ :=
    quadraticRestrictedPeriodMatrix_periodic_spectral_splitting
      (Node := Node) quad lambda i0 hquad
  have hrestricted_base_projection :
      P_restricted 0 =
        (fun i j : Sum Node {i : Node // i ≠ i0} =>
          right_restricted i * left_restricted j) :=
    hP0_restricted
  have htheta_restricted_pos : 0 < theta_restricted :=
    lt_of_le_of_lt hr0_restricted_nonneg hsplitting_restricted.2.1
  have htheta_restricted_lt_one : theta_restricted < 1 :=
    hsplitting_restricted.2.2.1
  have hK_restricted_nonneg : 0 ≤ K_restricted :=
    hsplitting_restricted.2.2.2.1
  have hrestricted_splitting_at :
      ∀ alpha : ℝ, |alpha| ≤ alpha_restricted →
        IsRieszProjectionAtEigenvalue
            (Node := Sum Node {i : Node // i ≠ i0})
            (quadraticRestrictedPeriodMatrix (Node := Node)
              quad lambda alpha i0)
            (gamma_restricted alpha) (P_restricted alpha) ∧
          quadraticRestrictedPeriodMatrix (Node := Node)
              quad lambda alpha i0 =
            matrixAdd (Node := Sum Node {i : Node // i ≠ i0})
              ((gamma_restricted alpha) • P_restricted alpha)
              (F_restricted alpha) ∧
            matrixMul (Node := Sum Node {i : Node // i ≠ i0})
                (P_restricted alpha) (F_restricted alpha) = 0 ∧
              matrixMul (Node := Sum Node {i : Node // i ≠ i0})
                  (F_restricted alpha) (P_restricted alpha) = 0 ∧
                ∀ j : ℕ,
                  matrixEuclideanOperatorNorm
                      (Node := Sum Node {i : Node // i ≠ i0})
                      (matrixPower (Node := Sum Node {i : Node // i ≠ i0})
                        (F_restricted alpha) j) ≤
                    K_restricted * theta_restricted ^ j := by
    intro alpha halpha
    exact hsplitting_restricted.2.2.2.2.2.2.2.2 alpha halpha
  have hrestricted_stable_power_bound :
      ∀ alpha : ℝ, |alpha| ≤ alpha_restricted → ∀ j : ℕ,
        matrixEuclideanOperatorNorm
            (Node := Sum Node {i : Node // i ≠ i0})
            (matrixPower (Node := Sum Node {i : Node // i ≠ i0})
              (F_restricted alpha) j) ≤
          K_restricted * theta_restricted ^ j := by
    intro alpha halpha j
    exact (hrestricted_splitting_at alpha halpha).2.2.2.2 j
  have hrestricted_stable_duhamel_square_sum_bound :
      ∀ alpha : ℝ, 0 ≤ alpha → alpha ≤ alpha_restricted →
        ∀ noise : NoisePath Node ℝ,
        ∀ z0 : RowVector (Sum Node {i : Node // i ≠ i0}),
        ∀ N : ℕ,
          Finset.sum (Finset.range (N + 1)) (fun t =>
            rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
              (stablePowerDuhamelClosedResponse
                (Node := Sum Node {i : Node // i ≠ i0})
                (F_restricted alpha) z0
                (fun k =>
                  quadraticRestrictedPeriodNoiseInnovationCoord
                    (Node := Node) quad lambda alpha i0 noise k) t) ^ 2) ≤
            (2 * K_restricted ^ 2 / (1 - theta_restricted ^ 2)) *
              (rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
                z0) ^ 2 +
            (2 * K_restricted ^ 2 / (1 - theta_restricted) ^ 2) *
              Finset.sum (Finset.range N) (fun k =>
                (rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
                  (quadraticRestrictedPeriodNoiseInnovationCoord
                    (Node := Node) quad lambda alpha i0 noise k)) ^ 2) := by
    intro alpha halpha_nonneg halpha_le noise z0 N
    have halpha_abs : |alpha| ≤ alpha_restricted := by
      simpa [abs_of_nonneg halpha_nonneg] using halpha_le
    exact
      quadratic_restricted_stable_duhamel_square_sum_bound
        (Node := Node) quad lambda alpha i0 (F_restricted alpha)
        hK_restricted_nonneg htheta_restricted_pos htheta_restricted_lt_one
        (hrestricted_stable_power_bound alpha halpha_abs)
        noise z0 N
  let stableBoundaryResponse :
      ℝ → Ω → ℕ → RowVector (Sum Node {i : Node // i ≠ i0}) :=
    fun alpha ω t =>
      quadraticRestrictedStableBoundaryResponse
        (Node := Node) quad lambda i0 P_restricted F_restricted alpha
        (oracle.noise ω) t
  have hrestricted_projected_stable_duhamel_square_sum_bound :
      ∀ alpha : ℝ, 0 ≤ alpha → alpha ≤ alpha_restricted →
        ∀ noise : NoisePath Node ℝ,
        ∀ z0 : RowVector (Sum Node {i : Node // i ≠ i0}),
        ∀ N : ℕ,
          Finset.sum (Finset.range (N + 1)) (fun t =>
            rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
              (stablePowerDuhamelClosedResponse
                (Node := Sum Node {i : Node // i ≠ i0})
                (F_restricted alpha)
                (spectralStableComplementVector
                  (Node := Sum Node {i : Node // i ≠ i0})
                  (P_restricted alpha) z0)
                (fun k =>
                  spectralStableComplementVector
                    (Node := Sum Node {i : Node // i ≠ i0})
                    (P_restricted alpha)
                    (quadraticRestrictedPeriodNoiseInnovationCoord
                      (Node := Node) quad lambda alpha i0 noise k)) t) ^ 2) ≤
            (2 * K_restricted ^ 2 / (1 - theta_restricted ^ 2)) *
              (rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
                (spectralStableComplementVector
                  (Node := Sum Node {i : Node // i ≠ i0})
                  (P_restricted alpha) z0)) ^ 2 +
            (2 * K_restricted ^ 2 / (1 - theta_restricted) ^ 2) *
              Finset.sum (Finset.range N) (fun k =>
                (rowEuclideanNorm (Node := Sum Node {i : Node // i ≠ i0})
                  (spectralStableComplementVector
                    (Node := Sum Node {i : Node // i ≠ i0})
                    (P_restricted alpha)
                    (quadraticRestrictedPeriodNoiseInnovationCoord
                      (Node := Node) quad lambda alpha i0 noise k))) ^ 2) := by
    intro alpha halpha_nonneg halpha_le noise z0 N
    have halpha_abs : |alpha| ≤ alpha_restricted := by
      simpa [abs_of_nonneg halpha_nonneg] using halpha_le
    exact
      quadratic_restricted_projected_stable_duhamel_square_sum_bound
        (Node := Sum Node {i : Node // i ≠ i0})
        (P_restricted alpha) (F_restricted alpha)
        hK_restricted_nonneg htheta_restricted_pos htheta_restricted_lt_one
        (hrestricted_stable_power_bound alpha halpha_abs)
        z0
        (fun k =>
          quadraticRestrictedPeriodNoiseInnovationCoord
            (Node := Node) quad lambda alpha i0 noise k) N
  have hrestricted_projected_stable_average_duhamel_l2_budget :
      ∃ alphaBudget Cduh : ℝ,
        0 < alphaBudget ∧ alphaBudget ≤ alpha_restricted ∧
          0 ≤ Cduh ∧
            ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaBudget →
              ∀ T : ℕ, 1 ≤ T →
              Finset.sum (Finset.range T) (fun t =>
                ∫ ω,
                  rowEuclideanNorm
                    (Node := Sum Node {i : Node // i ≠ i0})
                    (stableBoundaryResponse alpha ω t) ^ 2 ∂μ) ≤
                Cduh * (T : ℝ) := by
    let A_restricted : ℝ :=
      2 * K_restricted ^ 2 / (1 - theta_restricted ^ 2)
    let B_restricted : ℝ :=
      2 * K_restricted ^ 2 / (1 - theta_restricted) ^ 2
    have hA_restricted_nonneg : 0 ≤ A_restricted := by
      dsimp [A_restricted]
      have htheta_sq_lt_theta : theta_restricted ^ 2 < theta_restricted := by
        calc
          theta_restricted ^ 2 = theta_restricted * theta_restricted := by ring
          _ < 1 * theta_restricted :=
              mul_lt_mul_of_pos_right htheta_restricted_lt_one
                htheta_restricted_pos
          _ = theta_restricted := by ring
      have hden_pos : 0 < 1 - theta_restricted ^ 2 := by
        nlinarith
      exact div_nonneg (by positivity) hden_pos.le
    have hB_restricted_nonneg : 0 ≤ B_restricted := by
      dsimp [B_restricted]
      have hden_pos : 0 < (1 - theta_restricted) ^ 2 := by
        apply sq_pos_of_ne_zero
        nlinarith
      exact div_nonneg (by positivity) hden_pos.le
    obtain ⟨alphaInit_restricted, Cz0_restricted,
        halphaInit_restricted_pos, halphaInit_restricted_le,
        hCz0_restricted_nonneg, hz0_restricted_second_moment⟩ :=
      quadratic_restricted_projected_initial_second_moment_source_bound
        (Node := Node) quad lambda i0
        r0_restricted alpha_restricted theta_restricted K_restricted
        right_restricted left_restricted gamma_restricted
        P_restricted F_restricted hsplitting_restricted μ oracle
    obtain ⟨alphaXi_restricted, Cxi_restricted,
        halphaXi_restricted_pos, halphaXi_restricted_le,
        hCxi_restricted_nonneg, hxi_restricted_second_moment⟩ :=
      quadratic_restricted_projected_innovation_second_moment_source_bound
        (Node := Node) quad lambda i0
        r0_restricted alpha_restricted theta_restricted K_restricted
        right_restricted left_restricted gamma_restricted
        P_restricted F_restricted hsplitting_restricted μ oracle hnoise
    let alphaBudget : ℝ :=
      min alpha_restricted (min alphaInit_restricted alphaXi_restricted)
    have halphaBudget_pos : 0 < alphaBudget := by
      dsimp [alphaBudget]
      exact lt_min hsplitting_restricted.1
        (lt_min halphaInit_restricted_pos halphaXi_restricted_pos)
    have halphaBudget_le_restricted : alphaBudget ≤ alpha_restricted := by
      dsimp [alphaBudget]
      exact min_le_left _ _
    have halphaBudget_le_init : alphaBudget ≤ alphaInit_restricted := by
      dsimp [alphaBudget]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    have halphaBudget_le_xi : alphaBudget ≤ alphaXi_restricted := by
      dsimp [alphaBudget]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    have hdeterministic_duhamel :
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaBudget →
          ∀ noise : NoisePath Node ℝ, ∀ N : ℕ,
            Finset.sum (Finset.range (N + 1)) (fun t =>
              rowEuclideanNorm
                (Node := Sum Node {i : Node // i ≠ i0})
                (quadraticRestrictedStableBoundaryResponse
                  (Node := Node) quad lambda i0 P_restricted F_restricted
                  alpha noise t) ^ 2) ≤
              A_restricted *
                rowEuclideanNorm
                  (Node := Sum Node {i : Node // i ≠ i0})
                  (spectralStableComplementVector
                    (Node := Sum Node {i : Node // i ≠ i0})
                    (P_restricted alpha)
                    (restrictedStateToCoord (Node := Node) i0
                      ((quad.withStepsize alpha).primalState noise 0,
                        (quad.withStepsize alpha).trackerErrorZeroSum
                          noise 0))) ^ 2 +
              B_restricted *
                Finset.sum (Finset.range N) (fun k =>
                  rowEuclideanNorm
                    (Node := Sum Node {i : Node // i ≠ i0})
                    (spectralStableComplementVector
                      (Node := Sum Node {i : Node // i ≠ i0})
                      (P_restricted alpha)
                      (quadraticRestrictedPeriodNoiseInnovationCoord
                        (Node := Node) quad lambda alpha i0 noise k)) ^ 2) := by
      intro alpha halpha_pos halpha_le noise N
      simpa [A_restricted, B_restricted,
        quadraticRestrictedStableBoundaryResponse] using
        hrestricted_projected_stable_duhamel_square_sum_bound
          alpha halpha_pos.le
          (le_trans halpha_le halphaBudget_le_restricted) noise
          (restrictedStateToCoord (Node := Node) i0
            ((quad.withStepsize alpha).primalState noise 0,
              (quad.withStepsize alpha).trackerErrorZeroSum noise 0)) N
    have hz0_restricted_second_moment_budget :
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaBudget →
          (∫ ω,
            rowEuclideanNorm
              (Node := Sum Node {i : Node // i ≠ i0})
              (spectralStableComplementVector
                (Node := Sum Node {i : Node // i ≠ i0})
                (P_restricted alpha)
                (restrictedStateToCoord (Node := Node) i0
                  ((quad.withStepsize alpha).primalState
                      (oracle.noise ω) 0,
                    (quad.withStepsize alpha).trackerErrorZeroSum
                      (oracle.noise ω) 0))) ^ 2 ∂μ) ≤ Cz0_restricted := by
      intro alpha halpha_pos halpha_le
      exact hz0_restricted_second_moment alpha halpha_pos
        (le_trans halpha_le halphaBudget_le_init)
    have hxi_restricted_second_moment_budget :
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaBudget →
          ∀ k : ℕ,
            (∫ ω,
              rowEuclideanNorm
                (Node := Sum Node {i : Node // i ≠ i0})
                (spectralStableComplementVector
                  (Node := Sum Node {i : Node // i ≠ i0})
                  (P_restricted alpha)
                  (quadraticRestrictedPeriodNoiseInnovationCoord
                    (Node := Node) quad lambda alpha i0
                    (oracle.noise ω) k)) ^ 2 ∂μ) ≤ Cxi_restricted := by
      intro alpha halpha_pos halpha_le k
      exact hxi_restricted_second_moment alpha halpha_pos
        (le_trans halpha_le halphaBudget_le_xi) k
    obtain ⟨Cduh, hCduh_nonneg, hbudget⟩ :=
      quadratic_restricted_projected_stable_average_duhamel_l2_budget
        (Node := Node) quad lambda i0 alphaBudget
        P_restricted F_restricted μ oracle hnoise
        hA_restricted_nonneg hB_restricted_nonneg
        hCz0_restricted_nonneg hCxi_restricted_nonneg
        hdeterministic_duhamel
        hz0_restricted_second_moment_budget
        hxi_restricted_second_moment_budget
    refine ⟨alphaBudget, Cduh, halphaBudget_pos,
      halphaBudget_le_restricted, hCduh_nonneg, ?_⟩
    intro alpha halpha_pos halpha_le T hT
    simpa [stableBoundaryResponse] using
      hbudget alpha halpha_pos halpha_le T hT
  obtain ⟨alphaBudget, Cduh_restricted, halphaBudget_pos,
      halphaBudget_le_restricted, hCduh_restricted_nonneg,
      hstable_duhamel_l2⟩ :=
    hrestricted_projected_stable_average_duhamel_l2_budget
  obtain ⟨Cimp_restricted, thetaImpulse_restricted, alphaImpulse_restricted,
      hCimp_restricted_nonneg, hthetaImpulse_restricted,
      hthetaImpulse_restricted_lt_one, halphaImpulse_restricted_pos,
      halphaImpulse_restricted_le, hstable_impulse_geometric⟩ :=
    quadratic_restricted_stable_output_impulse_geometric_bound
      (Node := Node) quad lambda i0
      r0_restricted alpha_restricted theta_restricted K_restricted
      right_restricted left_restricted gamma_restricted
      P_restricted F_restricted hquad hP0_restricted
      hright_restricted_top hleft_restricted_top hleft_restricted_bottom
      hr0_restricted_nonneg
      hsplitting_restricted
  have hrestricted_stable_output_average_l2 :
      ∃ C alphaStable : ℝ,
        0 < C ∧ 0 < alphaStable ∧
          ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaStable →
            ∀ T : ℕ, 1 ≤ T →
              ((T : ℝ)⁻¹) *
                Finset.sum (Finset.range T) (fun t =>
                  ∫ ω,
                    |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                        (stableBoundaryResponse alpha ω t)| ^ 2 ∂μ) ≤
                C * alpha ^ 2 := by
    /- Source-cone migration point.

    The stable branch now consumes the Appendix C.1 geometric impulse bridge
    `hstable_impulse_geometric` instead of the retired response-relative
    domination leaf.  The only remaining source leaf is the unaveraged
    step-5 square-summation estimate below: square the compiled geometric
    impulse envelope, use the deterministic initial-boundary identity plus the
    iid exact-variance law for every finite period-noise window, and sum the
    geometric convolution over `t < T`. -/
    have hstable_output_sum_l2_from_impulse :
        ∃ Csum alphaSum : ℝ,
          0 ≤ Csum ∧ 0 < alphaSum ∧ alphaSum ≤ alphaImpulse_restricted ∧
            ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaSum →
              ∀ T : ℕ, 1 ≤ T →
                Finset.sum (Finset.range T) (fun t =>
                  ∫ ω,
                    |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                        (stableBoundaryResponse alpha ω t)| ^ 2 ∂μ) ≤
                  Csum * alpha ^ 2 * (T : ℝ) := by
      /- Exact remaining Appendix C.1 step-5 leaf.

      Available source data in this scope:
      * `hstable_impulse_geometric`, the proved step-4 geometric impulse
        supplier with the raw period-window envelope;
      * `quadraticRestrictedInitialBoundaryCoord_eq_const`, making the initial
        envelope deterministic;
      * `hnoise`, whose exact iid variance clauses give
        `E ||epsilon_t||^2 = |Node| * sigma^2`;
      * `SquareSummableGeometricConvolution` / finite geometric square-sum
        helpers for the deterministic convolution in `t`.

        This is deliberately routed through the active geometric impulse
        supplier, not through any retired response-relative output-operator
        or period-innovation helper. -/
        classical
        obtain ⟨Cwin, hCwin_nonneg, hwin_bound⟩ :=
          quadraticRestrictedPeriodNoiseWindowEnvelope_secondMoment_bound
            (Node := Node) quad μ oracle hnoise
        let Idx := Sum Node {i : Node // i ≠ i0}
        let A0 : ℝ :=
          1 +
            rowEuclideanNorm (Node := Idx)
              (fun a : Idx =>
                match a with
                | Sum.inl _ => quad.x0
                | Sum.inr _ => 0)
        let init : ℝ :=
          (2 / (1 - thetaImpulse_restricted ^ 2)) * A0 ^ 2
        let coeff : ℝ :=
          2 / (1 - thetaImpulse_restricted) ^ 2
        let Ccore : ℝ := Cimp_restricted ^ 2 * (init + coeff * Cwin)
        let Csum : ℝ := Ccore + 1
        have hthetaImpulse_pos : 0 < thetaImpulse_restricted := by
          linarith [htheta_restricted_pos, hthetaImpulse_restricted]
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
        have hinit_nonneg : 0 ≤ init := by
          have htheta_sq_lt_one : thetaImpulse_restricted ^ 2 < 1 := by
            nlinarith [hthetaImpulse_pos, hthetaImpulse_restricted_lt_one]
          have hden_nonneg : 0 ≤ 1 - thetaImpulse_restricted ^ 2 := by
            linarith
          have hfactor_nonneg :
              0 ≤ 2 / (1 - thetaImpulse_restricted ^ 2) :=
            div_nonneg (by norm_num) hden_nonneg
          dsimp [init]
          exact mul_nonneg hfactor_nonneg (sq_nonneg A0)
        have hcoeff_nonneg : 0 ≤ coeff := by
          have hden_pos : 0 < (1 - thetaImpulse_restricted) ^ 2 := by
            apply sq_pos_of_ne_zero
            linarith
          dsimp [coeff]
          positivity
        have hCcore_nonneg : 0 ≤ Ccore := by
          dsimp [Ccore]
          exact mul_nonneg (sq_nonneg Cimp_restricted)
            (add_nonneg hinit_nonneg
              (mul_nonneg hcoeff_nonneg hCwin_nonneg))
        refine ⟨Csum, alphaImpulse_restricted, ?_, halphaImpulse_restricted_pos,
          le_rfl, ?_⟩
        · dsimp [Csum]
          linarith
        intro alpha halpha_pos halpha_le T hT
        have hwindow_sum :
            Finset.sum (Finset.range T) (fun k =>
              ∫ ω,
                quadraticRestrictedPeriodNoiseWindowEnvelope
                  (Node := Node) quad (oracle.noise ω) k ^ 2 ∂μ) ≤
              (T : ℝ) * Cwin :=
          quadraticRestrictedPeriodNoiseWindowEnvelope_integral_sum_le
            (Node := Node) quad μ oracle hwin_bound T
        have hsum_impulse :
            Finset.sum (Finset.range T) (fun t =>
              ∫ ω,
                |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                    (stableBoundaryResponse alpha ω t)| ^ 2 ∂μ) ≤
              (Cimp_restricted ^ 2 * alpha ^ 2) *
                (init + coeff * ((T : ℝ) * Cwin)) := by
          simpa [init, coeff] using
            stable_output_square_integral_sum_bound_of_geometric_impulse
              (μ := μ) (C := Cimp_restricted)
              (theta := thetaImpulse_restricted) (A := A0)
              (alpha := alpha) (Cwin := Cwin)
              hCimp_restricted_nonneg halpha_pos.le hthetaImpulse_pos
              hthetaImpulse_restricted_lt_one hA0_nonneg hCwin_nonneg
              (fun ω k =>
                quadraticRestrictedPeriodNoiseWindowEnvelope
                  (Node := Node) quad (oracle.noise ω) k)
              (fun ω k =>
                quadraticRestrictedPeriodNoiseWindowEnvelope_nonneg
                  (Node := Node) quad (oracle.noise ω) k)
              (fun ω t =>
                quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                  (stableBoundaryResponse alpha ω t))
              (fun ω t => by
                have h :=
                  hstable_impulse_geometric alpha halpha_pos halpha_le
                    (oracle.noise ω) t
                have hinit_eq :=
                  quadraticRestrictedInitialBoundaryCoord_eq_const
                    (Node := Node) quad alpha i0 (oracle.noise ω)
                simpa [stableBoundaryResponse, A0, Idx, hinit_eq] using h)
              (fun t => by
                simpa [stableBoundaryResponse] using
                  quadraticRestrictedStableBoundaryResponse_output_sq_integrable
                    (Node := Node) quad lambda i0 P_restricted F_restricted
                    μ oracle hnoise alpha t)
              (fun k => by
                simpa using
                  quadraticRestrictedPeriodNoiseWindowEnvelope_sq_integrable
                    (Node := Node) quad μ oracle hnoise k)
              (fun N =>
                quadraticRestrictedPeriodNoiseWindowEnvelope_integral_sum_le
                  (Node := Node) quad μ oracle hwin_bound N)
              T hT
        have hT_real : 1 ≤ (T : ℝ) := by exact_mod_cast hT
        have hinside_absorb :
            init + coeff * ((T : ℝ) * Cwin) ≤
              (init + coeff * Cwin) * (T : ℝ) := by
          have hinit_mul : init ≤ init * (T : ℝ) := by
            nlinarith [hinit_nonneg, hT_real]
          calc
            init + coeff * ((T : ℝ) * Cwin) =
                init + (coeff * Cwin) * (T : ℝ) := by ring
            _ ≤ init * (T : ℝ) + (coeff * Cwin) * (T : ℝ) := by
                exact add_le_add hinit_mul
                  (le_refl ((coeff * Cwin) * (T : ℝ)))
            _ = (init + coeff * Cwin) * (T : ℝ) := by ring
        have hscaled_absorb :
            (Cimp_restricted ^ 2 * alpha ^ 2) *
                (init + coeff * ((T : ℝ) * Cwin)) ≤
              (Cimp_restricted ^ 2 * (init + coeff * Cwin)) *
                alpha ^ 2 * (T : ℝ) := by
          calc
            (Cimp_restricted ^ 2 * alpha ^ 2) *
                (init + coeff * ((T : ℝ) * Cwin)) ≤
                (Cimp_restricted ^ 2 * alpha ^ 2) *
                  ((init + coeff * Cwin) * (T : ℝ)) := by
                  exact mul_le_mul_of_nonneg_left hinside_absorb
                    (mul_nonneg (sq_nonneg Cimp_restricted)
                      (sq_nonneg alpha))
            _ = (Cimp_restricted ^ 2 * (init + coeff * Cwin)) *
                  alpha ^ 2 * (T : ℝ) := by ring
        have hcore_le_sum : Ccore ≤ Csum := by
          dsimp [Csum]
          linarith
        calc
          Finset.sum (Finset.range T) (fun t =>
              ∫ ω,
                |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                    (stableBoundaryResponse alpha ω t)| ^ 2 ∂μ) ≤
              (Cimp_restricted ^ 2 * alpha ^ 2) *
                (init + coeff * ((T : ℝ) * Cwin)) := hsum_impulse
          _ ≤ (Cimp_restricted ^ 2 * (init + coeff * Cwin)) *
                alpha ^ 2 * (T : ℝ) := hscaled_absorb
          _ = Ccore * alpha ^ 2 * (T : ℝ) := by rfl
          _ ≤ Csum * alpha ^ 2 * (T : ℝ) := by
            calc
              Ccore * alpha ^ 2 * (T : ℝ) =
                  Ccore * (alpha ^ 2 * (T : ℝ)) := by ring
              _ ≤ Csum * (alpha ^ 2 * (T : ℝ)) := by
                  exact mul_le_mul_of_nonneg_right hcore_le_sum
                    (mul_nonneg (sq_nonneg alpha) (Nat.cast_nonneg T))
              _ = Csum * alpha ^ 2 * (T : ℝ) := by ring
    rcases hstable_output_sum_l2_from_impulse with
      ⟨Csum, alphaSum, hCsum_nonneg, halphaSum_pos,
        _halphaSum_le_impulse, hsum_bound⟩
    exact
      quadratic_restricted_stable_output_average_l2_from_sum_bound
        (Node := Node) i0 μ stableBoundaryResponse
        halphaSum_pos hCsum_nonneg hsum_bound
  unfold QuadraticSlowComparisonStatement
  rcases hrestricted_stable_output_average_l2 with
    ⟨Cst, alphaSt, hCst_pos, halphaSt_pos, hstable_bound⟩
  let slowOutput : ℝ → Ω → ℕ → ℝ := fun alpha ω t =>
    (quad.withStepsize alpha).averageIterate (oracle.noise ω) t -
      quadraticRestrictedPrimalAverageOutput (Node := Node) i0
        (stableBoundaryResponse alpha ω t)
  obtain ⟨Cslow, alphaSlow, hCslow_pos, halphaSlow_pos,
      hslow_int, hslow_bound⟩ :=
    quadratic_restricted_slow_output_scalar_average_l2_bound
      (Node := Node) quad lambda i0
      r0_restricted alpha_restricted theta_restricted K_restricted
      right_restricted left_restricted gamma_restricted
      P_restricted F_restricted
      hquad
      hP0_restricted hright_restricted_eq hright_restricted_top
      hleft_restricted_top
      hleft_restricted_bottom μ oracle hnoise
      hgrad_linear havg_linear
      toRestrictedCoord ofRestrictedCoord
      hrestrictedCoord_left hrestrictedCoord_right
      hrestricted_period_boundary_recursion
      hsplitting_restricted hrestricted_splitting_at
      ⟨Cst, alphaSt, hCst_pos, halphaSt_pos, hstable_bound⟩
  refine ⟨2 * Cslow + 2 * Cst + 1, min alphaSlow alphaSt, ?_, ?_, ?_⟩
  · nlinarith [hCslow_pos, hCst_pos]
  · exact lt_min halphaSlow_pos halphaSt_pos
  intro alpha halpha_pos halpha_le T halphaT
  have halpha_le_slow : alpha ≤ alphaSlow :=
    le_trans halpha_le (min_le_left _ _)
  have halpha_le_stable : alpha ≤ alphaSt :=
    le_trans halpha_le (min_le_right _ _)
  have hT_ne : T ≠ 0 := by
    intro hzero
    subst T
    norm_num at halphaT
  have hT_one : 1 ≤ T :=
    Nat.succ_le_of_lt (Nat.pos_of_ne_zero hT_ne)
  have hslow_bound_alpha :
      ((T : ℝ)⁻¹) *
        Finset.sum (Finset.range T) (fun t =>
          ∫ ω,
            |slowOutput alpha ω t -
              quad.quadraticScalarComparisonProcess lambda alpha
                (oracle.noise ω) t| ^ 2 ∂μ) ≤
        Cslow * alpha ^ 2 := by
    simpa [slowOutput, stableBoundaryResponse] using
      hslow_bound alpha halpha_pos halpha_le_slow T halphaT
  have hstable_bound_alpha :
      ((T : ℝ)⁻¹) *
        Finset.sum (Finset.range T) (fun t =>
          ∫ ω,
            |quadraticRestrictedPrimalAverageOutput (Node := Node) i0
                (stableBoundaryResponse alpha ω t)| ^ 2 ∂μ) ≤
        Cst * alpha ^ 2 :=
    hstable_bound alpha halpha_pos halpha_le_stable T hT_one
  exact
    average_l2_triangle_combine_two_errors
      (μ := μ)
      (actual := fun ω t =>
        (quad.withStepsize alpha).averageIterate (oracle.noise ω) t)
      (slow := fun ω t => slowOutput alpha ω t)
      (stable := fun ω t =>
        quadraticRestrictedPrimalAverageOutput (Node := Node) i0
          (stableBoundaryResponse alpha ω t))
      (scalar := fun ω t =>
        quad.quadraticScalarComparisonProcess lambda alpha
          (oracle.noise ω) t)
      (T := T) (Cslow := Cslow) (Cstable := Cst) (alpha := alpha)
      (hslow_int := by
        intro t
        simpa [slowOutput, stableBoundaryResponse] using hslow_int alpha t)
      (hstable_int := by
        intro t
        simpa [stableBoundaryResponse] using
          quadraticRestrictedStableBoundaryResponse_output_sq_integrable
            (Node := Node) quad lambda i0 P_restricted F_restricted
            μ oracle hnoise alpha t)
      (htotal_int := by
        intro t
        let stepped := quad.withStepsize alpha
        have hstepped_oracle :
            stepped.StochasticOracleAssumptions μ oracle := by
          simpa [stepped, StochasticOracleAssumptions, withStepsize]
            using hnoise.1
        have hgenerated :=
          stepped.generated_pushpull_coordinate_memLp μ oracle
            hstepped_oracle t
        have havg_mem :
            MemLp
              (fun ω : Ω =>
                stepped.averageIterate (oracle.noise ω) t) 2 μ := by
          have hsum :
              MemLp
                (fun ω : Ω =>
                  ∑ i : Node,
                    stepped.primalState (oracle.noise ω) t i) 2 μ := by
            apply memLp_finset_sum Finset.univ
            intro i _hi
            exact hgenerated.1 i
          simpa [averageIterate, arithmeticAverage] using
            hsum.const_smul ((nodeCount (Node := Node) : ℝ)⁻¹)
        have hscalar_mem :
            MemLp
              (fun ω : Ω =>
                quad.quadraticScalarComparisonProcess lambda alpha
                  (oracle.noise ω) t) 2 μ :=
          quadraticScalarComparisonProcess_memLp_two
            (Node := Node) quad lambda alpha μ oracle hnoise.1 t
        simpa [stepped] using
          real_abs_sq_integrable_of_memLp_two (havg_mem.sub hscalar_mem))
      (hdecomp := by
        intro ω t
        dsimp [slowOutput]
        ring)
      hslow_bound_alpha hstable_bound_alpha

/-- Appendix C.2: scalar moment expansion for the periodic quadratic
comparison process, uniform for sufficiently small positive `alpha`, together
with the `alpha -> 0`, `alpha*T -> infinity` asymptotic consequence used in
Theorem 8.1. -/
theorem QuadraticPeriodicScalarMomentExpansion
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (_hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle) :
    QuadraticScalarMomentExpansion (Node := Node) quad lambda μ oracle ∧
      QuadraticScalarMomentAsymptoticConsequence (Node := Node)
        quad lambda μ oracle := by
  classical
  have hGamma_zero :
      quadraticScalarPeriodMultiplier (Node := Node) quad lambda 0 = 1 :=
    quadraticScalarPeriodMultiplier_zero (Node := Node) quad lambda
  have hperiod_gain :
      (∑ r : Fin quad.period, quad.scalarComparisonGain r.1) =
        (quad.period : ℝ) * quad.influenceGain :=
    quadraticScalarGain_period_sum_eq_period_mul_influenceGain
      (Node := Node) quad
  have hprocess_zero :
      ∀ alpha : ℝ, ∀ noise : NoisePath Node ℝ,
        quad.quadraticScalarComparisonProcess lambda alpha noise 0 = quad.x0 := by
    intro alpha noise
    exact quadraticScalarComparisonProcess_zero
      (Node := Node) quad lambda alpha noise
  have hprocess_step :
      ∀ alpha : ℝ, ∀ noise : NoisePath Node ℝ, ∀ t : ℕ,
        quad.quadraticScalarComparisonProcess lambda alpha noise (t + 1) =
          quadraticScalarPhaseMultiplier (Node := Node) quad lambda alpha t *
            quad.quadraticScalarComparisonProcess lambda alpha noise t -
              alpha * weightedState (Node := Node) (E := ℝ)
                (quad.influence t) (noise t) := by
    intro alpha noise t
    exact quadraticScalarComparisonProcess_succ
      (Node := Node) quad lambda alpha noise t
  have hblock_ar :
      ∀ alpha : ℝ, ∀ noise : NoisePath Node ℝ, ∀ k : ℕ,
        quad.quadraticScalarComparisonProcess lambda alpha noise
            ((k + 1) * quad.period) =
          quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha *
            quad.quadraticScalarComparisonProcess lambda alpha noise
              (k * quad.period) +
              quadraticScalarBlockNoiseInnovation (Node := Node)
                quad lambda alpha noise k := by
    intro alpha noise k
    exact quadraticScalarBlockARRecursion
      (Node := Node) quad lambda alpha noise k
  let blockInnovationSecondMoment : ℝ → ℕ → ℝ :=
    fun alpha k =>
      quadraticScalarBlockInnovationSecondMoment (Node := Node)
        quad lambda alpha μ oracle k
  let biasBlockAverage : ℝ → ℕ → ℝ :=
    fun alpha K =>
      quadraticScalarBiasBlockAverage (Node := Node)
        quad lambda alpha K
  let steadyBoundaryVariance : ℝ → ℝ → ℝ :=
    fun alpha blockNoiseSecondMoment =>
      quadraticScalarSteadyBoundaryVariance (Node := Node)
        quad lambda alpha blockNoiseSecondMoment
  have hGamma_firstOrder :=
    quadraticScalarPeriodMultiplier_firstOrder_isBigO_sq
      (Node := Node) quad lambda
  have hden_firstOrder :=
    quadraticScalarPeriodDenominator_firstOrder_isBigO_sq
      (Node := Node) quad lambda
  have hden_coeff_pos :=
    quadraticScalarPeriodDenominator_linearCoefficient_pos
      (Node := Node) quad lambda hquad
  have hsqueeze :=
    quadraticScalarPeriodMultiplier_smallAlpha_squeeze
      (Node := Node) quad lambda hquad
  have hblock_secondMoment :=
    quadraticScalarBlockInnovationSecondMoment_expansion
      (Node := Node) quad lambda μ oracle _hnoise
  have hblock_secondMoment_uniform :=
    quadraticScalarBlockInnovationSecondMoment_expansion_uniform
      (Node := Node) quad lambda μ oracle _hnoise
  have hbias_bound :=
    quadraticScalarBiasBlockAverage_bound
      (Node := Node) quad lambda hquad
  have hsteady_expansion :=
    quadraticScalarSteadyBoundaryVariance_expansion
      (Node := Node) quad lambda μ oracle hquad _hnoise hblock_secondMoment
  have hvariance_formula :
      ∀ alpha : ℝ, ∀ K : ℕ,
        quadraticScalarBlockBoundaryVariance (Node := Node)
            quad lambda alpha μ oracle K =
          quadraticScalarBlockBoundaryVarianceARFormula (Node := Node)
            quad lambda alpha μ oracle K :=
    quadraticScalarBlockBoundaryVariance_formula_from_source
      (Node := Node) quad lambda μ oracle _hnoise
  have hcomplete_to_steady :
      ∃ alpha0 Cphase Ctransient : ℝ,
        0 < alpha0 ∧ 0 ≤ Cphase ∧ 0 ≤ Ctransient ∧
          ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
            ∀ K : ℕ, 1 ≤ K →
              let T : ℝ := ((K * quad.period : ℕ) : ℝ)
              let steadyAverage : ℝ :=
                lambda ^ 2 * (K : ℝ)⁻¹ *
                  ((Finset.range K).sum fun k =>
                    quadraticScalarSteadyBoundaryVariance (Node := Node)
                      quad lambda alpha
                      (quadraticScalarBlockInnovationSecondMoment (Node := Node)
                        quad lambda alpha μ oracle k))
              |(quad.quadraticScalarMomentFunctional lambda alpha μ oracle
                    (K * quad.period) -
                  quadraticScalarBiasBlockAverage (Node := Node)
                    quad lambda alpha K) -
                steadyAverage| ≤
              Cphase * alpha ^ 2 + Ctransient * T⁻¹ :=
    quadraticScalarMomentFunctional_completePeriod_to_steadyBoundaryAverage_bound
      (Node := Node) quad lambda μ oracle hquad _hnoise hvariance_formula
  have hcomplete_period :
      ∃ alpha0 c C : ℝ, 0 < alpha0 ∧ 0 < c ∧ 0 ≤ C ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
          ∀ K : ℕ, 1 ≤ K →
            |quad.quadraticScalarMomentFunctional lambda alpha μ oracle
                (K * quad.period) -
              (quad.Delta /
                  (quad.influenceGain * alpha *
                    ((K * quad.period : ℕ) : ℝ)) +
                (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
                  (2 * quad.influenceGain)) * alpha)| ≤
            C * ((((K * quad.period : ℕ) : ℝ)⁻¹) + alpha ^ 2 +
              Real.exp (-(c * alpha *
                ((K * quad.period : ℕ) : ℝ))) /
                (alpha * ((K * quad.period : ℕ) : ℝ))) :=
    quadraticScalarMomentFunctional_completePeriod_expansion_bound
      (Node := Node) quad lambda μ oracle hquad _hnoise
      hcomplete_to_steady hsqueeze hblock_secondMoment hblock_secondMoment_uniform
      hbias_bound hsteady_expansion
  have hscalar :
      QuadraticScalarMomentExpansion (Node := Node)
        quad lambda μ oracle :=
    quadraticScalarMomentFunctional_tail_bound
      (Node := Node) quad lambda μ oracle hquad _hnoise hcomplete_period
  exact ⟨hscalar,
    quadraticScalarMomentAsymptotic_from_uniformExpansion
      (Node := Node) quad lambda μ oracle hscalar⟩

theorem exists_le_csInf_add_of_nonempty_bddBelow
    {s : Set ℝ} (hs_nonempty : s.Nonempty) (_hs_bddBelow : BddBelow s)
    {eps : ℝ} (heps_pos : 0 < eps) :
    ∃ x : ℝ, x ∈ s ∧ x ≤ sInf s + eps := by
  have hlt : sInf s < sInf s + eps := by linarith
  rcases exists_lt_of_csInf_lt hs_nonempty hlt with ⟨x, hx_mem, hx_lt⟩
  exact ⟨x, hx_mem, le_of_lt hx_lt⟩

theorem expectedGradientNormSq_nonneg
    (setup : Setup Node ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (oracle : OracleNoiseProcess Ω Node ℝ) (t : ℕ) :
    0 ≤ setup.expectedGradientNormSq μ oracle t := by
  unfold expectedGradientNormSq
  exact MeasureTheory.integral_nonneg fun _ω => sq_nonneg _

theorem stationarityAverage_nonneg
    (setup : Setup Node ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (oracle : OracleNoiseProcess Ω Node ℝ) (T : ℕ) :
    0 ≤ setup.stationarityAverage μ oracle T := by
  unfold stationarityAverage
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg T))
    (Finset.sum_nonneg fun t _ht =>
      expectedGradientNormSq_nonneg (Node := Node) setup μ oracle t)

theorem quadraticLowerBoundStationarityFunctional_nonneg
    (quad : Setup Node ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (oracle : OracleNoiseProcess Ω Node ℝ)
    (T : ℕ) (alpha : ℝ) :
    0 ≤ quad.quadraticLowerBoundStationarityFunctional μ oracle T alpha := by
  simpa [quadraticLowerBoundStationarityFunctional] using
    stationarityAverage_nonneg (Node := Node) (quad.withStepsize alpha) μ oracle T

theorem exists_quadratic_lower_bound_near_sInf_sequence
    (quad : Setup Node ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (oracle : OracleNoiseProcess Ω Node ℝ) :
    ∃ alphaNearOpt : ℕ → ℝ,
      (∀ T : ℕ, 1 ≤ T → 0 ≤ alphaNearOpt T) ∧
        ∀ T : ℕ, 1 ≤ T →
          quad.quadraticLowerBoundStationarityFunctional μ oracle T
              (alphaNearOpt T) ≤
            sInf { value : ℝ |
              ∃ alpha : ℝ, 0 ≤ alpha ∧
                value =
                  quad.quadraticLowerBoundStationarityFunctional μ oracle T alpha } +
            (T : ℝ)⁻¹ := by
  classical
  let valueSet : ℕ → Set ℝ := fun T =>
    { value : ℝ |
      ∃ alpha : ℝ, 0 ≤ alpha ∧
        value =
          quad.quadraticLowerBoundStationarityFunctional μ oracle T alpha }
  have hselect :
      ∀ T : ℕ, 1 ≤ T →
        ∃ alpha : ℝ, 0 ≤ alpha ∧
          quad.quadraticLowerBoundStationarityFunctional μ oracle T alpha ≤
            sInf (valueSet T) + (T : ℝ)⁻¹ := by
    intro T hT
    have hnonempty : (valueSet T).Nonempty := by
      refine ⟨quad.quadraticLowerBoundStationarityFunctional μ oracle T 0, ?_⟩
      exact ⟨0, le_rfl, rfl⟩
    have hbddBelow : BddBelow (valueSet T) := by
      refine ⟨0, ?_⟩
      intro value hvalue
      rcases hvalue with ⟨alpha, _halpha_nonneg, rfl⟩
      exact quadraticLowerBoundStationarityFunctional_nonneg
        (Node := Node) quad μ oracle T alpha
    have heps_pos : 0 < (T : ℝ)⁻¹ := by
      exact inv_pos.mpr (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT))
    rcases exists_le_csInf_add_of_nonempty_bddBelow
        hnonempty hbddBelow heps_pos with ⟨value, hvalue_mem, hvalue_le⟩
    rcases hvalue_mem with ⟨alpha, halpha_nonneg, rfl⟩
    exact ⟨alpha, halpha_nonneg, hvalue_le⟩
  let alphaNearOpt : ℕ → ℝ := fun T =>
    if hT : 1 ≤ T then Classical.choose (hselect T hT) else 0
  refine ⟨alphaNearOpt, ?_, ?_⟩
  · intro T hT
    have hspec := Classical.choose_spec (hselect T hT)
    simpa [alphaNearOpt, hT] using hspec.1
  · intro T hT
    have hspec := Classical.choose_spec (hselect T hT)
    simpa [alphaNearOpt, valueSet, hT] using hspec.2

theorem real_two_mul_sqrt_mul_le_div_add_mul
    {a b x : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 < x) :
    2 * Real.sqrt (a * b) ≤ a / x + b * x := by
  have hdiv_nonneg : 0 ≤ a / x := div_nonneg ha hx.le
  have hmul_nonneg : 0 ≤ b * x := mul_nonneg hb hx.le
  have hsq :
      (Real.sqrt (a * b)) ^ 2 = (a / x) * (b * x) := by
    rw [Real.sq_sqrt (mul_nonneg ha hb)]
    field_simp [ne_of_gt hx]
  exact two_mul_le_add_of_sq_eq_mul hdiv_nonneg hmul_nonneg hsq

theorem quadratic_leading_two_term_amgm_effective_node_lower
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (T : ℕ) (alpha : ℝ) (halpha_pos : 0 < alpha) (hT : 1 ≤ T) :
    quad.Delta / (quad.influenceGain * alpha * (T : ℝ)) +
        (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
            (2 * quad.influenceGain)) * alpha ≥
      quad.sigma *
        Real.sqrt (2 * lambda * quad.Delta /
          (quad.effectiveNodeCount * (T : ℝ))) := by
  have hlambda_pos : 0 < lambda := hquad.1
  have hsigma_pos : 0 < quad.sigma := hnoise.2.1
  have hsigma_sq_pos : 0 < quad.sigma ^ 2 := sq_pos_of_pos hsigma_pos
  have hTreal : 0 < (T : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
  let a : ℝ := quad.Delta / (quad.influenceGain * (T : ℝ))
  let b : ℝ :=
    lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
      (2 * quad.influenceGain)
  have ha_nonneg : 0 ≤ a := by
    exact div_nonneg quad.Delta_positive.le
      (mul_pos quad.influenceGain_pos hTreal).le
  have hb_nonneg : 0 ≤ b := by
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg hlambda_pos.le hsigma_sq_pos.le)
        quad.influenceSecondMoment_pos.le)
      (mul_pos (by norm_num) quad.influenceGain_pos).le
  have hamgm :
      2 * Real.sqrt (a * b) ≤ a / alpha + b * alpha :=
    real_two_mul_sqrt_mul_le_div_add_mul ha_nonneg hb_nonneg halpha_pos
  have harg_nonneg :
      0 ≤ 2 * lambda * quad.Delta /
        (quad.effectiveNodeCount * (T : ℝ)) := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hlambda_pos.le)
        quad.Delta_positive.le)
      (mul_nonneg quad.effectiveNodeCount_pos_and_le_nodeCount.1.le hTreal.le)
  have hroot_eq :
      2 * Real.sqrt (a * b) =
        quad.sigma *
          Real.sqrt (2 * lambda * quad.Delta /
            (quad.effectiveNodeCount * (T : ℝ))) := by
    have hleft_nonneg : 0 ≤ 2 * Real.sqrt (a * b) := by positivity
    have hright_nonneg :
        0 ≤ quad.sigma *
          Real.sqrt (2 * lambda * quad.Delta /
            (quad.effectiveNodeCount * (T : ℝ))) := by
      exact mul_nonneg hsigma_pos.le (Real.sqrt_nonneg _)
    have hsquare :
        (2 * Real.sqrt (a * b)) ^ 2 =
          (quad.sigma *
            Real.sqrt (2 * lambda * quad.Delta /
              (quad.effectiveNodeCount * (T : ℝ)))) ^ 2 := by
      calc
        (2 * Real.sqrt (a * b)) ^ 2 = 4 * (a * b) := by
          rw [show (2 * Real.sqrt (a * b)) ^ 2 =
              4 * (Real.sqrt (a * b)) ^ 2 by ring]
          rw [Real.sq_sqrt (mul_nonneg ha_nonneg hb_nonneg)]
        _ = quad.sigma ^ 2 *
              (2 * lambda * quad.Delta /
                (quad.effectiveNodeCount * (T : ℝ))) := by
          unfold a b effectiveNodeCount
          field_simp [ne_of_gt quad.influenceGain_pos,
            ne_of_gt quad.influenceSecondMoment_pos, ne_of_gt hTreal]
          ring
        _ =
          (quad.sigma *
            Real.sqrt (2 * lambda * quad.Delta /
              (quad.effectiveNodeCount * (T : ℝ)))) ^ 2 := by
          rw [show
            (quad.sigma *
              Real.sqrt (2 * lambda * quad.Delta /
                (quad.effectiveNodeCount * (T : ℝ)))) ^ 2 =
                quad.sigma ^ 2 *
                  (Real.sqrt (2 * lambda * quad.Delta /
                    (quad.effectiveNodeCount * (T : ℝ)))) ^ 2 by ring]
          rw [Real.sq_sqrt harg_nonneg]
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsquare with heq | heq
    · exact heq
    · nlinarith
  calc
    quad.sigma *
        Real.sqrt (2 * lambda * quad.Delta /
          (quad.effectiveNodeCount * (T : ℝ))) =
        2 * Real.sqrt (a * b) := hroot_eq.symm
    _ ≤ a / alpha + b * alpha := hamgm
    _ =
        quad.Delta / (quad.influenceGain * alpha * (T : ℝ)) +
          (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
              (2 * quad.influenceGain)) * alpha := by
      unfold a b
      field_simp [ne_of_gt quad.influenceGain_pos, ne_of_gt halpha_pos,
        ne_of_gt hTreal]

theorem near_minimizer_eventual_amgm_bound_of_product_tendsto_atTop
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (alphaNearOpt : ℕ → ℝ)
    (hnear_nonneg : ∀ T : ℕ, 1 ≤ T → 0 ≤ alphaNearOpt T)
    (hprod_tendsto :
      Filter.Tendsto (fun T : ℕ => alphaNearOpt T * (T : ℝ))
        Filter.atTop Filter.atTop) :
    ∃ T0 : ℕ, ∀ T : ℕ, T0 ≤ T →
      1 ≤ T ∧ 0 < alphaNearOpt T ∧
        quad.Delta /
            (quad.influenceGain * alphaNearOpt T * (T : ℝ)) +
          (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
              (2 * quad.influenceGain)) * alphaNearOpt T ≥
            quad.sigma *
              Real.sqrt (2 * lambda * quad.Delta /
                (quad.effectiveNodeCount * (T : ℝ))) := by
  have hT_ge_one : ∀ᶠ T : ℕ in Filter.atTop, 1 ≤ T :=
    Filter.eventually_atTop.2 ⟨1, fun T hT => hT⟩
  have hprod_pos :
      ∀ᶠ T : ℕ in Filter.atTop, 0 < alphaNearOpt T * (T : ℝ) :=
    hprod_tendsto.eventually_gt_atTop (0 : ℝ)
  have heventual :
      ∀ᶠ T : ℕ in Filter.atTop,
        1 ≤ T ∧ 0 < alphaNearOpt T ∧
          quad.Delta /
              (quad.influenceGain * alphaNearOpt T * (T : ℝ)) +
            (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
                (2 * quad.influenceGain)) * alphaNearOpt T ≥
              quad.sigma *
                Real.sqrt (2 * lambda * quad.Delta /
                  (quad.effectiveNodeCount * (T : ℝ))) := by
    filter_upwards [hT_ge_one, hprod_pos] with T hT hprodT
    have hTreal_pos : 0 < (T : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
    have halpha_pos : 0 < alphaNearOpt T :=
      pos_of_mul_pos_left hprodT hTreal_pos.le
    exact ⟨hT, halpha_pos,
      quadratic_leading_two_term_amgm_effective_node_lower
        (Node := Node) quad lambda μ oracle hquad hnoise T
        (alphaNearOpt T) halpha_pos hT⟩
  exact Filter.eventually_atTop.1 heventual

/-- Transfer the Appendix C.1 slow-comparison estimate to the true quadratic
stationarity functional.

For homogeneous quadratic data, the stationarity integrand is
`|lambda * averageIterate|^2`.  The elementary inequality
`|a+b|^2 <= 2|a|^2 + 2|b|^2` then compares it with the scalar comparison
moment plus the averaged slow-comparison error. -/
theorem quadraticLowerBoundStationarityFunctional_le_scalarMoment_add_slowError
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (hslow : QuadraticSlowComparisonStatement (Node := Node) quad lambda μ oracle) :
    ∃ C alpha0 : ℝ, 0 ≤ C ∧ 0 < alpha0 ∧
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
        ∀ T : ℕ, 1 ≤ alpha * (T : ℝ) →
          quad.quadraticLowerBoundStationarityFunctional μ oracle T alpha ≤
            2 * quad.quadraticScalarMomentFunctional lambda alpha μ oracle T +
              C * alpha ^ 2 := by
  classical
  rcases hslow with ⟨C2, alpha0, hC2_pos, halpha0_pos, hslow_bound⟩
  refine ⟨2 * lambda ^ 2 * C2, alpha0, ?_, halpha0_pos, ?_⟩
  · positivity
  · intro alpha halpha_pos halpha_le T halphaT
    have havg_linear :
        ∀ x : ℝ, quad.averageGradient x = lambda * x :=
      homogeneousQuadratic_averageGradient_eq_linear
        (Node := Node) quad lambda hquad
    have hslowT :=
      hslow_bound alpha halpha_pos halpha_le T halphaT
    have hpoint :
        ∀ t : ℕ, ∀ ω : Ω,
          ‖quad.averageGradient
              ((quad.withStepsize alpha).averageIterate
                (oracle.noise ω) t)‖ ^ 2 ≤
            2 * |lambda *
              quad.quadraticScalarComparisonProcess lambda alpha
                (oracle.noise ω) t| ^ 2 +
              2 * lambda ^ 2 *
                |(quad.withStepsize alpha).averageIterate
                    (oracle.noise ω) t -
                  quad.quadraticScalarComparisonProcess lambda alpha
                    (oracle.noise ω) t| ^ 2 := by
      intro t ω
      let x :=
        (quad.withStepsize alpha).averageIterate (oracle.noise ω) t
      let u :=
        quad.quadraticScalarComparisonProcess lambda alpha
          (oracle.noise ω) t
      have hgrad :
          quad.averageGradient x = lambda * x := havg_linear x
      have hsplit : lambda * x = lambda * u + lambda * (x - u) := by ring
      have hbase := real_abs_add_sq_le_two_sq
        (lambda * u) (lambda * (x - u))
      have hnorm :
          ‖quad.averageGradient x‖ ^ 2 = |lambda * x| ^ 2 := by
        rw [hgrad]
        simp [Real.norm_eq_abs]
      have hmul :
          |lambda * (x - u)| ^ 2 =
            lambda ^ 2 * |x - u| ^ 2 := by
        rw [abs_mul, mul_pow, sq_abs]
      rw [hnorm, hsplit]
      nlinarith [hbase, hmul, sq_nonneg lambda]
    have hsum_point :
        Finset.sum (Finset.range T) (fun t =>
            ∫ ω,
              ‖quad.averageGradient
                ((quad.withStepsize alpha).averageIterate
                  (oracle.noise ω) t)‖ ^ 2 ∂μ) ≤
          Finset.sum (Finset.range T) (fun t =>
            2 * (∫ ω,
              |lambda *
                quad.quadraticScalarComparisonProcess lambda alpha
                  (oracle.noise ω) t| ^ 2 ∂μ) +
              2 * lambda ^ 2 *
                (∫ ω,
                  |(quad.withStepsize alpha).averageIterate
                      (oracle.noise ω) t -
                    quad.quadraticScalarComparisonProcess lambda alpha
                      (oracle.noise ω) t| ^ 2 ∂μ)) := by
      refine Finset.sum_le_sum ?_
      intro t _ht
      let stepped := quad.withStepsize alpha
      let actual : Ω → ℝ := fun ω =>
        stepped.averageIterate (oracle.noise ω) t
      let scalar : Ω → ℝ := fun ω =>
        quad.quadraticScalarComparisonProcess lambda alpha
          (oracle.noise ω) t
      let A : Ω → ℝ := fun ω =>
        ‖quad.averageGradient (actual ω)‖ ^ 2
      let B : Ω → ℝ := fun ω => |lambda * scalar ω| ^ 2
      let C : Ω → ℝ := fun ω => |actual ω - scalar ω| ^ 2
      have hstepped_oracle :
          stepped.StochasticOracleAssumptions μ oracle := by
        simpa [stepped, StochasticOracleAssumptions, withStepsize]
          using hnoise.1
      have hgenerated :=
        stepped.generated_pushpull_coordinate_memLp μ oracle
          hstepped_oracle t
      have hactual_mem :
          MemLp actual 2 μ := by
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
      have hscalar_mem :
          MemLp scalar 2 μ := by
        simpa [scalar] using
          quadraticScalarComparisonProcess_memLp_two
            (Node := Node) quad lambda alpha μ oracle hnoise.1 t
      have hA_int : Integrable A μ := by
        have hmul_mem : MemLp (fun ω : Ω => lambda * actual ω) 2 μ := by
          simpa using hactual_mem.const_smul lambda
        have hA_eq :
            A = fun ω : Ω => |lambda * actual ω| ^ 2 := by
          funext ω
          dsimp [A]
          rw [havg_linear]
        rw [hA_eq]
        exact real_abs_sq_integrable_of_memLp_two hmul_mem
      have hB_int : Integrable B μ := by
        have hmul_mem : MemLp (fun ω : Ω => lambda * scalar ω) 2 μ := by
          simpa using hscalar_mem.const_smul lambda
        simpa [B] using real_abs_sq_integrable_of_memLp_two hmul_mem
      have hC_int : Integrable C μ := by
        simpa [C, actual, scalar] using
          real_abs_sq_integrable_of_memLp_two
            (hactual_mem.sub hscalar_mem)
      have hterm :=
        integral_le_integral_affine_combination μ
          A B C 2 (2 * lambda ^ 2) hA_int hB_int hC_int
          (fun ω => by
            dsimp [A, B, C, actual, scalar]
            exact hpoint t ω)
      simpa [A, B, C, actual, scalar] using hterm
    have hTinv_nonneg : 0 ≤ (T : ℝ)⁻¹ :=
      inv_nonneg.mpr (Nat.cast_nonneg T)
    calc
      quad.quadraticLowerBoundStationarityFunctional μ oracle T alpha =
          ((T : ℝ)⁻¹) *
            Finset.sum (Finset.range T) (fun t =>
              ∫ ω,
                ‖quad.averageGradient
                  ((quad.withStepsize alpha).averageIterate
                    (oracle.noise ω) t)‖ ^ 2 ∂μ) := by
          unfold quadraticLowerBoundStationarityFunctional
            stationarityAverage expectedGradientNormSq randomAverageIterate
          congr 1
      _ ≤
          ((T : ℝ)⁻¹) *
            Finset.sum (Finset.range T) (fun t =>
              2 * (∫ ω,
                |lambda *
                  quad.quadraticScalarComparisonProcess lambda alpha
                    (oracle.noise ω) t| ^ 2 ∂μ) +
                2 * lambda ^ 2 *
                  (∫ ω,
                    |(quad.withStepsize alpha).averageIterate
                        (oracle.noise ω) t -
                      quad.quadraticScalarComparisonProcess lambda alpha
                        (oracle.noise ω) t| ^ 2 ∂μ)) := by
          exact mul_le_mul_of_nonneg_left hsum_point hTinv_nonneg
      _ =
          2 * quad.quadraticScalarMomentFunctional lambda alpha μ oracle T +
            2 * lambda ^ 2 *
              (((T : ℝ)⁻¹) *
                Finset.sum (Finset.range T) (fun t =>
                  ∫ ω,
                    |(quad.withStepsize alpha).averageIterate
                        (oracle.noise ω) t -
                      quad.quadraticScalarComparisonProcess lambda alpha
                    (oracle.noise ω) t| ^ 2 ∂μ)) := by
          unfold quadraticScalarMomentFunctional
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          ring
      _ ≤
          2 * quad.quadraticScalarMomentFunctional lambda alpha μ oracle T +
            (2 * lambda ^ 2 * C2) * alpha ^ 2 := by
          have hcoeff_nonneg : 0 ≤ 2 * lambda ^ 2 := by positivity
          have hscaled :=
            mul_le_mul_of_nonneg_left hslowT hcoeff_nonneg
          nlinarith [hscaled]
      _ =
          2 * quad.quadraticScalarMomentFunctional lambda alpha μ oracle T +
            (2 * lambda ^ 2 * C2) * alpha ^ 2 := by
          rfl

theorem quadraticLowerBound_near_value_le_test_value_add_inv
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
    (T : ℕ) (hT : 1 ≤ T) (alpha : ℝ) (halpha_nonneg : 0 ≤ alpha) :
    quad.quadraticLowerBoundStationarityFunctional μ oracle T
        (alphaNearOpt T) ≤
      quad.quadraticLowerBoundStationarityFunctional μ oracle T alpha +
        (T : ℝ)⁻¹ := by
  let valueSet : Set ℝ :=
    { value : ℝ |
      ∃ beta : ℝ, 0 ≤ beta ∧
        value =
          quad.quadraticLowerBoundStationarityFunctional μ oracle T beta }
  have hbddBelow : BddBelow valueSet := by
    refine ⟨0, ?_⟩
    intro value hvalue
    rcases hvalue with ⟨beta, _hbeta_nonneg, rfl⟩
    exact quadraticLowerBoundStationarityFunctional_nonneg
      (Node := Node) quad μ oracle T beta
  have htest_mem :
      quad.quadraticLowerBoundStationarityFunctional μ oracle T alpha ∈
        valueSet := by
    exact ⟨alpha, halpha_nonneg, rfl⟩
  have hsInf_le :
      sInf valueSet ≤
        quad.quadraticLowerBoundStationarityFunctional μ oracle T alpha :=
    csInf_le hbddBelow htest_mem
  have hnear := hnear_value T hT
  change
    quad.quadraticLowerBoundStationarityFunctional μ oracle T
        (alphaNearOpt T) ≤
      sInf valueSet + (T : ℝ)⁻¹ at hnear
  linarith

theorem real_nat_inv_le_inv_sqrt_of_one_le
    {T : ℕ} (hT : 1 ≤ T) :
    ((T : ℝ)⁻¹) ≤ (Real.sqrt (T : ℝ))⁻¹ := by
  have hTreal_ge_one : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have hTreal_pos : 0 < (T : ℝ) :=
    lt_of_lt_of_le (by norm_num) hTreal_ge_one
  have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (T : ℝ) := by
    simpa using Real.sqrt_le_sqrt hTreal_ge_one
  have hsqrt_le_T : Real.sqrt (T : ℝ) ≤ (T : ℝ) := by
    nlinarith [Real.sq_sqrt (le_of_lt hTreal_pos)]
  have hsqrt_pos : 0 < Real.sqrt (T : ℝ) :=
    lt_of_lt_of_le (by norm_num) hsqrt_ge_one
  exact (inv_le_inv₀ hTreal_pos hsqrt_pos).2 hsqrt_le_T

theorem real_balancing_alpha_sq_le_inv_sqrt
    {A : ℝ} (hA_pos : 0 < A) {T : ℕ} (hT : 1 ≤ T) :
    (Real.sqrt A * (Real.sqrt (T : ℝ))⁻¹) ^ 2 ≤
      A * (Real.sqrt (T : ℝ))⁻¹ := by
  have hTreal_ge_one : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have hTreal_pos : 0 < (T : ℝ) :=
    lt_of_lt_of_le (by norm_num) hTreal_ge_one
  have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (T : ℝ) := by
    simpa using Real.sqrt_le_sqrt hTreal_ge_one
  have hinv_nonneg : 0 ≤ (Real.sqrt (T : ℝ))⁻¹ :=
    inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hinv_le_one : (Real.sqrt (T : ℝ))⁻¹ ≤ 1 := by
    simpa using inv_le_one_of_one_le₀ hsqrt_ge_one
  have hsq_sqrtA : (Real.sqrt A) ^ 2 = A :=
    Real.sq_sqrt hA_pos.le
  calc
    (Real.sqrt A * (Real.sqrt (T : ℝ))⁻¹) ^ 2 =
        A * ((Real.sqrt (T : ℝ))⁻¹) ^ 2 := by
      rw [mul_pow, hsq_sqrtA]
    _ ≤ A * (Real.sqrt (T : ℝ))⁻¹ := by
      have hA_nonneg : 0 ≤ A := hA_pos.le
      have hinv_sq_le : ((Real.sqrt (T : ℝ))⁻¹) ^ 2 ≤
          (Real.sqrt (T : ℝ))⁻¹ := by
        nlinarith [sq_nonneg ((Real.sqrt (T : ℝ))⁻¹), hinv_nonneg,
          hinv_le_one]
      exact mul_le_mul_of_nonneg_left hinv_sq_le hA_nonneg

theorem real_exp_balancing_quotient_le_inv_sqrt
    {A c : ℝ} (hA_pos : 0 < A) (hc_pos : 0 < c) {T : ℕ}
    (hT : 1 ≤ T) :
    Real.exp (-(c * (Real.sqrt A * (Real.sqrt (T : ℝ))⁻¹) *
        (T : ℝ))) /
        ((Real.sqrt A * (Real.sqrt (T : ℝ))⁻¹) * (T : ℝ)) ≤
      (Real.sqrt A)⁻¹ * (Real.sqrt (T : ℝ))⁻¹ := by
  have hTreal_ge_one : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have hTreal_pos : 0 < (T : ℝ) :=
    lt_of_lt_of_le (by norm_num) hTreal_ge_one
  have hsqrtT_pos : 0 < Real.sqrt (T : ℝ) :=
    Real.sqrt_pos.2 hTreal_pos
  have hsqrtA_pos : 0 < Real.sqrt A := Real.sqrt_pos.2 hA_pos
  have hsqrtT_ne : Real.sqrt (T : ℝ) ≠ 0 := ne_of_gt hsqrtT_pos
  have hprod_eq :
      (Real.sqrt A * (Real.sqrt (T : ℝ))⁻¹) * (T : ℝ) =
        Real.sqrt A * Real.sqrt (T : ℝ) := by
    have hsqrt_sq : Real.sqrt (T : ℝ) ^ 2 = (T : ℝ) :=
      Real.sq_sqrt hTreal_pos.le
    field_simp [hsqrtT_ne]
    exact hsqrt_sq.symm
  have hprod_pos :
      0 < (Real.sqrt A * (Real.sqrt (T : ℝ))⁻¹) * (T : ℝ) := by
    rw [hprod_eq]
    positivity
  have hexp_le_one :
      Real.exp (-(c * (Real.sqrt A * (Real.sqrt (T : ℝ))⁻¹) *
        (T : ℝ))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have harg_nonneg :
        0 ≤ c * ((Real.sqrt A * (Real.sqrt (T : ℝ))⁻¹) *
          (T : ℝ)) := by positivity
    nlinarith
  calc
    Real.exp (-(c * (Real.sqrt A * (Real.sqrt (T : ℝ))⁻¹) *
        (T : ℝ))) /
        ((Real.sqrt A * (Real.sqrt (T : ℝ))⁻¹) * (T : ℝ)) ≤
        1 / ((Real.sqrt A * (Real.sqrt (T : ℝ))⁻¹) * (T : ℝ)) := by
      exact div_le_div_of_nonneg_right hexp_le_one hprod_pos.le
    _ = (Real.sqrt A)⁻¹ * (Real.sqrt (T : ℝ))⁻¹ := by
      rw [hprod_eq]
      field_simp [ne_of_gt hsqrtA_pos, ne_of_gt hsqrtT_pos]

theorem near_minimizer_eventually_lt_delta_of_upper_and_fresh_floor
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (alphaNearOpt : ℕ → ℝ)
    (hnear_nonneg : ∀ T : ℕ, 1 ≤ T → 0 ≤ alphaNearOpt T)
    (hupper :
      ∃ C T0, 0 ≤ C ∧ ∀ T : ℕ, T0 ≤ T →
        quad.quadraticLowerBoundStationarityFunctional μ oracle T
            (alphaNearOpt T) ≤ C * (Real.sqrt (T : ℝ))⁻¹)
    (hfloor :
      ∀ T : ℕ, ∀ alpha : ℝ, 2 ≤ T → 0 ≤ alpha →
        quad.quadraticLowerBoundStationarityFunctional μ oracle T alpha ≥
          ((T - 1 : ℝ) / (T : ℝ)) *
            (lambda ^ 2 * quad.sigma ^ 2 /
              (nodeCount (Node := Node) : ℝ)) * alpha ^ 2) :
    ∀ δ : ℝ, 0 < δ →
      ∀ᶠ T : ℕ in Filter.atTop, alphaNearOpt T < δ := by
  classical
  rcases hupper with ⟨C, T0, hC_nonneg, hupper_bound⟩
  have hlambda_pos : 0 < lambda := hquad.1
  have hsigma_pos : 0 < quad.sigma := hnoise.2.1
  have hnode_pos : 0 < (nodeCount (Node := Node) : ℝ) := by
    exact_mod_cast (nodeCount_pos (Node := Node))
  let K : ℝ :=
    lambda ^ 2 * quad.sigma ^ 2 / (nodeCount (Node := Node) : ℝ)
  have hK_pos : 0 < K := by
    dsimp [K]
    positivity
  have hsqrt_atTop :
      Filter.Tendsto (fun T : ℕ => Real.sqrt (T : ℝ))
        Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv_sqrt_zero :
      Filter.Tendsto (fun T : ℕ => (Real.sqrt (T : ℝ))⁻¹)
        Filter.atTop (nhds 0) :=
    hsqrt_atTop.inv_tendsto_atTop
  have hscaled_zero :
      Filter.Tendsto (fun T : ℕ => C * (Real.sqrt (T : ℝ))⁻¹)
        Filter.atTop (nhds 0) := by
    simpa using (Filter.Tendsto.const_mul C hinv_sqrt_zero)
  intro δ hδ_pos
  let A : ℝ := (1 / 2) * K * δ ^ 2
  have hA_pos : 0 < A := by
    dsimp [A]
    positivity
  have hsmall :
      ∀ᶠ T : ℕ in Filter.atTop,
        C * (Real.sqrt (T : ℝ))⁻¹ < A := by
    have hdist :
        ∀ᶠ T : ℕ in Filter.atTop,
          dist (C * (Real.sqrt (T : ℝ))⁻¹) 0 < A :=
      (Metric.tendsto_nhds.mp hscaled_zero) A hA_pos
    filter_upwards [hdist] with T hT
    have habs :
        |C * (Real.sqrt (T : ℝ))⁻¹| < A := by
      simpa [Real.dist_eq] using hT
    exact lt_of_le_of_lt (le_abs_self _) habs
  have hlarge :
      ∀ᶠ T : ℕ in Filter.atTop, T0 ≤ T ∧ 2 ≤ T :=
    Filter.eventually_atTop.2
      ⟨max T0 2, fun T hT =>
        ⟨le_trans (Nat.le_max_left T0 2) hT,
          le_trans (Nat.le_max_right T0 2) hT⟩⟩
  filter_upwards [hsmall, hlarge] with T hsmallT hlargeT
  rcases hlargeT with ⟨hT0, hT2⟩
  by_contra hnot
  have hdelta_le : δ ≤ alphaNearOpt T := le_of_not_gt hnot
  have hT1 : 1 ≤ T := le_trans (by norm_num) hT2
  have halpha_nonneg : 0 ≤ alphaNearOpt T :=
    hnear_nonneg T hT1
  have hTreal_pos : 0 < (T : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hT2)
  have hTreal_ne : (T : ℝ) ≠ 0 := ne_of_gt hTreal_pos
  have hcoef_ge :
      (1 / 2 : ℝ) ≤ ((T - 1 : ℕ) : ℝ) / (T : ℝ) := by
    have hT2_real : (2 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT2
    rw [Nat.cast_sub hT1]
    rw [le_div_iff₀ hTreal_pos]
    nlinarith
  have halpha_sq_ge : δ ^ 2 ≤ alphaNearOpt T ^ 2 := by
    nlinarith [hdelta_le, hδ_pos.le, halpha_nonneg,
      sq_nonneg (alphaNearOpt T - δ)]
  have hfloorT :=
    hfloor T (alphaNearOpt T) hT2 halpha_nonneg
  have hfloor_lower :
      A ≤
        ((T - 1 : ℝ) / (T : ℝ)) *
          (lambda ^ 2 * quad.sigma ^ 2 /
            (nodeCount (Node := Node) : ℝ)) *
          alphaNearOpt T ^ 2 := by
    have hcoef_ge' :
        (1 / 2 : ℝ) ≤ ((T : ℝ) - 1) / (T : ℝ) := by
      simpa [Nat.cast_sub hT1] using hcoef_ge
    have hcoef_nonneg :
        0 ≤ ((T : ℝ) - 1) / (T : ℝ) :=
      le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) hcoef_ge'
    have hKexpr_pos :
        0 < lambda ^ 2 * quad.sigma ^ 2 /
          (nodeCount (Node := Node) : ℝ) := by
      simpa [K] using hK_pos
    have hcoefK_ge :
        (1 / 2 : ℝ) *
            (lambda ^ 2 * quad.sigma ^ 2 /
              (nodeCount (Node := Node) : ℝ)) ≤
          (((T : ℝ) - 1) / (T : ℝ)) *
            (lambda ^ 2 * quad.sigma ^ 2 /
              (nodeCount (Node := Node) : ℝ)) :=
      mul_le_mul_of_nonneg_right hcoef_ge' hKexpr_pos.le
    have hcoefK_nonneg :
        0 ≤ (((T : ℝ) - 1) / (T : ℝ)) *
          (lambda ^ 2 * quad.sigma ^ 2 /
            (nodeCount (Node := Node) : ℝ)) :=
      mul_nonneg hcoef_nonneg hKexpr_pos.le
    have hmul :=
      mul_le_mul hcoefK_ge halpha_sq_ge (sq_nonneg δ) hcoefK_nonneg
    simpa [A, K, mul_assoc] using hmul
  have hupperT := hupper_bound T hT0
  nlinarith [hfloorT, hfloor_lower, hupperT, hsmallT]

theorem tendsto_zero_of_eventually_nonneg_and_lt_delta
    (alpha : ℕ → ℝ)
    (hnonneg : ∀ T : ℕ, 1 ≤ T → 0 ≤ alpha T)
    (hlt_delta :
      ∀ δ : ℝ, 0 < δ →
        ∀ᶠ T : ℕ in Filter.atTop, alpha T < δ) :
    Filter.Tendsto alpha Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro eps heps
  have hlt := hlt_delta eps heps
  have hlarge : ∀ᶠ T : ℕ in Filter.atTop, 1 ≤ T :=
    Filter.eventually_atTop.2 ⟨1, fun T hT => hT⟩
  filter_upwards [hlt, hlarge] with T hltT hT1
  have hnonnegT := hnonneg T hT1
  have habs : |alpha T| = alpha T := abs_of_nonneg hnonnegT
  simpa [Real.dist_eq, habs] using hltT

end Setup
end Algorithms.Unverified.TimeVaryingPushPull
