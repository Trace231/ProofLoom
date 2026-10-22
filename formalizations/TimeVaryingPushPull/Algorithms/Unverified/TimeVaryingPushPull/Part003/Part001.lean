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

/-- Audit-facing source-route certificate for the row half of Lemma 4.2.

The generic Dobrushin route requested by the Phase 2b arbiter is available
from `Part001`: `rowMinorized_statePairwiseDiameter_contraction` feeds
`rowConsecutiveProduct_consensusError_frobenius_rate_of_blockMinorization`.
`Part002` exposes the paper-specific row-product specialization directly from
that generic API.  This theorem keeps that exact source-stage consumer visible
from the active module without rebuilding the retired lower-level route. -/
theorem PeriodicProductContraction_push_consensusError_frobenius_sourceRoute
    (t j : ℕ) (X : State Node E) :
    stateFrobeniusNorm (Node := Node) (E := E)
        (consensusError (Node := Node) (E := E)
          (leftMul (Node := Node) (E := E) (setup.pushLiftProduct t j) X)) ≤
      setup.rowContractionConstant * setup.contractionRate ^ j *
        stateFrobeniusNorm (Node := Node) (E := E)
          (consensusError (Node := Node) (E := E) X) := by
  exact setup.pushLiftProduct_consensusError_frobenius_rate_from_rowMinorized_source t j X

theorem normalized_outer_product_rankOneProjection
    (right left : RowVector Node)
    (hright : right ≠ 0) (hleft : left ≠ 0)
    (hnormalized : rowDot (Node := Node) left right = 1) :
    RankOneProjection (Node := Node)
      (fun i j : Node => right i * left j) := by
  unfold RankOneProjection
  unfold rowDot at hnormalized
  constructor
  · funext i j
    unfold matrixMul
    calc
      (∑ k : Node, (right i * left k) * (right k * left j)) =
          right i * (∑ k : Node, left k * right k) * left j := by
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = right i * left j := by rw [hnormalized]; ring
  · refine ⟨right, left, hright, hleft, ?_, ?_⟩
    · exact hnormalized
    · intro x
      funext i
      unfold matrixMulVector rowDot
      simp only [Pi.smul_apply, smul_eq_mul]
      calc
        (∑ j : Node, right i * left j * x j) =
            ∑ j : Node, right i * (left j * x j) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = right i * ∑ j : Node, left j * x j := by
          rw [Finset.mul_sum]
        _ = (∑ j : Node, left j * x j) * right i := by ring

theorem normalized_outer_product_apply
    (right left x : RowVector Node) :
    matrixMulVector (Node := Node) (fun i j : Node => right i * left j) x =
      rowDot (Node := Node) left x • right := by
  classical
  funext i
  unfold matrixMulVector rowDot
  simp only [Pi.smul_apply, smul_eq_mul]
  calc
    (∑ j : Node, right i * left j * x j) =
        ∑ j : Node, right i * (left j * x j) := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = right i * ∑ j : Node, left j * x j := by
      rw [Finset.mul_sum]
    _ = (∑ j : Node, left j * x j) * right i := by
      ring

theorem normalized_outer_product_matrixMul_left_eq
    (A0 : NodeMatrix Node) (right left : RowVector Node)
    (hright :
      matrixMulVector (Node := Node) A0 right = right) :
    matrixMul (Node := Node) A0
        (fun i j : Node => right i * left j) =
      fun i j : Node => right i * left j := by
  classical
  funext i k
  unfold matrixMul
  calc
    (∑ j : Node, A0 i j * (right j * left k)) =
        (∑ j : Node, A0 i j * right j) * left k := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = right i * left k := by
      have hi : (∑ j : Node, A0 i j * right j) = right i := by
        simpa [matrixMulVector] using congrFun hright i
      rw [hi]

theorem normalized_outer_product_matrixMul_right_eq
    (A0 : NodeMatrix Node) (right left : RowVector Node)
    (hleft :
      rowMulMatrix (Node := Node) left A0 = left) :
    matrixMul (Node := Node)
        (fun i j : Node => right i * left j) A0 =
      fun i j : Node => right i * left j := by
  classical
  funext i k
  unfold matrixMul
  calc
    (∑ j : Node, (right i * left j) * A0 j k) =
        right i * (∑ j : Node, left j * A0 j k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = right i * left k := by
      have hk : (∑ j : Node, left j * A0 j k) = left k := by
        simpa [rowMulMatrix] using congrFun hleft k
      rw [hk]

theorem unit_eigenvector_normalized_outer_product_apply_eq
    (A0 : NodeMatrix Node) (right left x : RowVector Node)
    (hnormalized : rowDot (Node := Node) left right = 1)
    (halgebraicallySimple :
      UnitEigenvalueAlgebraicallySimple (Node := Node) A0 right)
    (hx : matrixMulVector (Node := Node) A0 x = x) :
    matrixMulVector (Node := Node) (fun i j : Node => right i * left j) x = x := by
  classical
  have hcomplexEigen :
      complexMatrixMulVector (Node := Node) A0
          (complexOfRealRow (Node := Node) x) =
        (1 : ℂ) • complexOfRealRow (Node := Node) x := by
    funext i
    simp only [complexMatrixMulVector, complexOfRealRow,
      Pi.smul_apply, one_mul]
    norm_cast
    simpa using congrFun hx i
  obtain ⟨c, hc⟩ := halgebraicallySimple.1 _ hcomplexEigen
  have hcomplexNormalized :
      (∑ i : Node, (left i : ℂ) * (right i : ℂ)) = 1 := by
    have hcast := congrArg Complex.ofReal hnormalized
    simpa [rowDot] using hcast
  have hc_eq_dot : c = (rowDot (Node := Node) left x : ℂ) := by
    calc
      c = c * (∑ i : Node, (left i : ℂ) * (right i : ℂ)) := by
        rw [hcomplexNormalized, mul_one]
      _ = ∑ i : Node, (left i : ℂ) * (x i : ℂ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        have hci := congrFun hc i
        simp only [complexOfRealRow, Pi.smul_apply, smul_eq_mul] at hci
        rw [hci]
        ring
      _ = (rowDot (Node := Node) left x : ℂ) := by
        norm_cast
  rw [normalized_outer_product_apply]
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  have hci := congrFun hc i
  simp only [complexOfRealRow, Pi.smul_apply, smul_eq_mul] at hci
  have hcoord :
      (((rowDot (Node := Node) left x) * right i : ℝ) : ℂ) = (x i : ℂ) := by
    rw [hci, hc_eq_dot]
    norm_cast
  exact_mod_cast hcoord

theorem normalized_unit_outer_product_isUnitRieszProjection_at_base
    (A0 : NodeMatrix Node) (r0 : ℝ) (right left : RowVector Node)
    (hspectrum :
      SimpleIsolatedUnitEigenvalueStableSpectrum
        (Node := Node) A0 r0 right left) :
    IsUnitRieszProjection (Node := Node) (fun _ : ℝ => A0) 0
      (fun i j : Node => right i * left j) := by
  classical
  let P : NodeMatrix Node := fun i j : Node => right i * left j
  have hright : IsRightUnitEigenvector (Node := Node) A0 right :=
    hspectrum.2.2.1
  have hleft : IsLeftUnitEigenvector (Node := Node) A0 left :=
    hspectrum.2.2.2.1
  have hnormalized : rowDot (Node := Node) left right = 1 :=
    hspectrum.2.2.2.2.1
  have halgebraicallySimple :
      UnitEigenvalueAlgebraicallySimple (Node := Node) A0 right :=
    hspectrum.unit_algebraicallySimple
  have hAP :
      matrixMul (Node := Node) A0 P = P := by
    simpa [P] using
      normalized_outer_product_matrixMul_left_eq (Node := Node)
        A0 right left hright.2
  have hPA :
      matrixMul (Node := Node) P A0 = P := by
    simpa [P] using
      normalized_outer_product_matrixMul_right_eq (Node := Node)
        A0 right left hleft.2
  refine ⟨?_, ?_⟩
  · simpa [P] using
      normalized_outer_product_rankOneProjection (Node := Node)
        right left hright.1 hleft.1 hnormalized
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [P] using hAP
    · simpa [P] using hPA
    · intro x
      constructor
      · intro hPx
        have hx_unit :
            matrixMulVector (Node := Node) A0 x = x := by
          calc
            matrixMulVector (Node := Node) A0 x =
                matrixMulVector (Node := Node) A0
                  (matrixMulVector (Node := Node) P x) := by
              rw [hPx]
            _ = matrixMulVector (Node := Node)
                  (matrixMul (Node := Node) A0 P) x := by
              rw [matrixMulVector_matrixMul]
            _ = matrixMulVector (Node := Node) P x := by
              rw [hAP]
            _ = x := hPx
        simpa using hx_unit
      · intro hx
        have hx_unit :
            matrixMulVector (Node := Node) A0 x = x := by
          simpa [Pi.smul_apply, smul_eq_mul] using hx
        simpa [P] using
          unit_eigenvector_normalized_outer_product_apply_eq
            (Node := Node) A0 right left x hnormalized
            halgebraicallySimple hx_unit
    · exact exists_unit_spectral_separating_circle (Node := Node)
        A0 r0 right left hspectrum

theorem rowDot_matrixMulVector_eq_rowMulMatrix_rowDot
    (w v : RowVector Node) (M : NodeMatrix Node) :
    rowDot (Node := Node) w (matrixMulVector (Node := Node) M v) =
      rowDot (Node := Node) (rowMulMatrix (Node := Node) w M) v := by
  classical
  unfold rowDot matrixMulVector rowMulMatrix
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem bordered_unit_eigenpair_jacobian_equiv
    (A0 : NodeMatrix Node) (right left : RowVector Node)
    (hleft : rowMulMatrix (Node := Node) left A0 = left)
    (hnormalized : rowDot (Node := Node) left right = 1)
    (halgebraicallySimple :
      UnitEigenvalueAlgebraicallySimple (Node := Node) A0 right) :
    ∃ e : (ℝ × RowVector Node) ≃L[ℝ] (ℝ × RowVector Node),
      ∀ x : ℝ × RowVector Node,
        e x = (rowDot (Node := Node) left x.2,
          fun i : Node => matrixMulVector (Node := Node) A0 x.2 i -
            x.2 i - x.1 * right i) := by
  classical
  let B : (ℝ × RowVector Node) →ₗ[ℝ] (ℝ × RowVector Node) :=
    { toFun := fun x =>
        (rowDot (Node := Node) left x.2,
          fun i : Node => matrixMulVector (Node := Node) A0 x.2 i -
            x.2 i - x.1 * right i)
      map_add' := by
        intro x y
        ext i
        · simp only [rowDot, Prod.fst_add, Prod.snd_add, Pi.add_apply]
          simp_rw [mul_add]
          exact Finset.sum_add_distrib
        · simp only [matrixMulVector, Prod.fst_add, Prod.snd_add, Pi.add_apply]
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib]
          ring
      map_smul' := by
        intro c x
        ext i
        · simp only [rowDot, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply,
            smul_eq_mul]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          simp only [RingHom.id_apply]
          ring
        · simp only [matrixMulVector, Prod.smul_fst, Prod.smul_snd,
            Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
          rw [show (∑ j : Node, A0 i j * (c * x.2 j)) =
              c * ∑ j : Node, A0 i j * x.2 j by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring]
          ring }
  have hB_injective : Function.Injective B := by
    have hker : ∀ x : ℝ × RowVector Node, B x = 0 → x = 0 := by
      rintro ⟨dgamma, dr⟩ hx
      have hnormal : rowDot (Node := Node) left dr = 0 := by
        exact congrArg Prod.fst hx
      have hresidual : ∀ i : Node,
          matrixMulVector (Node := Node) A0 dr i - dr i -
              dgamma * right i = 0 := by
        intro i
        exact congrFun (congrArg Prod.snd hx) i
      have hweighted :
          (∑ i : Node, left i *
            (matrixMulVector (Node := Node) A0 dr i - dr i -
              dgamma * right i)) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [hresidual i, mul_zero]
      have hleft_action :
          (∑ i : Node, left i * matrixMulVector (Node := Node) A0 dr i) =
            rowDot (Node := Node) left dr := by
        unfold matrixMulVector rowDot
        calc
          (∑ i : Node, left i * ∑ j : Node, A0 i j * dr j) =
              ∑ j : Node, (∑ i : Node, left i * A0 i j) * dr j := by
            simp_rw [Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j hj
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = ∑ j : Node, left j * dr j := by
            apply Finset.sum_congr rfl
            intro j hj
            have hj' := congrFun hleft j
            simpa [rowMulMatrix] using congrArg (fun a : ℝ => a * dr j) hj'
      have hdgamma : dgamma = 0 := by
        have hright_scaled :
            (∑ i : Node, left i * (dgamma * right i)) =
              dgamma * rowDot (Node := Node) left right := by
          unfold rowDot
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        have hsplit :
            (∑ i : Node, left i *
              (matrixMulVector (Node := Node) A0 dr i - dr i -
                dgamma * right i)) =
              (∑ i : Node,
                left i * matrixMulVector (Node := Node) A0 dr i) -
                rowDot (Node := Node) left dr -
                  dgamma * rowDot (Node := Node) left right := by
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hright_scaled]
          rfl
        rw [hsplit, hleft_action, hnormal, hnormalized] at hweighted
        linarith
      have hrealEigen :
          matrixMulVector (Node := Node) A0 dr = dr := by
        funext i
        specialize hresidual i
        rw [hdgamma, zero_mul, sub_zero] at hresidual
        linarith
      have hcomplexEigen :
          complexMatrixMulVector (Node := Node) A0
              (complexOfRealRow (Node := Node) dr) =
            (1 : ℂ) • complexOfRealRow (Node := Node) dr := by
        funext i
        simp only [complexMatrixMulVector, complexOfRealRow,
          Pi.smul_apply, one_mul]
        norm_cast
        simpa using congrFun hrealEigen i
      obtain ⟨c, hc⟩ := halgebraicallySimple.1 _ hcomplexEigen
      have hcomplexNormal :
          (∑ i : Node, (left i : ℂ) * (dr i : ℂ)) = 0 := by
        norm_cast
      have hc_zero : c = 0 := by
        have hcomplexNormalized :
            (∑ i : Node, (left i : ℂ) * (right i : ℂ)) = 1 := by
          have hcast := congrArg Complex.ofReal hnormalized
          simpa [rowDot] using hcast
        calc
          c = c * (∑ i : Node, (left i : ℂ) * (right i : ℂ)) := by
            rw [hcomplexNormalized, mul_one]
          _ = ∑ i : Node, (left i : ℂ) * (dr i : ℂ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            have hci := congrFun hc i
            simp only [complexOfRealRow, Pi.smul_apply, smul_eq_mul] at hci
            rw [hci]
            ring
          _ = 0 := hcomplexNormal
      have hdr : dr = 0 := by
        funext i
        have hci := congrFun hc i
        simp [complexOfRealRow, hc_zero] at hci
        exact_mod_cast hci
      simp [hdgamma, hdr]
    intro x y hxy
    rw [← sub_eq_zero]
    apply hker (x - y)
    rw [map_sub, hxy, sub_self]
  let e : (ℝ × RowVector Node) ≃L[ℝ] (ℝ × RowVector Node) :=
    (LinearEquiv.ofInjectiveEndo B hB_injective).toContinuousLinearEquiv
  refine ⟨e, ?_⟩
  intro x
  rfl

theorem transposed_bordered_unit_eigenpair_jacobian_equiv
    (A0 : NodeMatrix Node) (right left : RowVector Node)
    (bordered : (ℝ × RowVector Node) ≃L[ℝ] (ℝ × RowVector Node))
    (hbordered : ∀ x : ℝ × RowVector Node,
      bordered x = (rowDot (Node := Node) left x.2,
        fun i : Node => matrixMulVector (Node := Node) A0 x.2 i -
          x.2 i - x.1 * right i)) :
    ∃ e : (ℝ × RowVector Node) ≃L[ℝ] (ℝ × RowVector Node),
      ∀ x : ℝ × RowVector Node,
        e x = (-rowDot (Node := Node) x.2 right,
          fun j : Node => rowMulMatrix (Node := Node) x.2 A0 j -
            x.2 j + x.1 * left j) := by
  classical
  let T : (ℝ × RowVector Node) →ₗ[ℝ] (ℝ × RowVector Node) :=
    { toFun := fun x => (-rowDot (Node := Node) x.2 right,
        fun j : Node => rowMulMatrix (Node := Node) x.2 A0 j -
          x.2 j + x.1 * left j)
      map_add' := by
        intro x y
        ext j
        · simp only [rowDot, Prod.snd_add, Pi.add_apply, Prod.fst_add]
          simp_rw [add_mul]
          rw [Finset.sum_add_distrib]
          ring
        · simp only [rowMulMatrix, Prod.snd_add, Pi.add_apply, Prod.fst_add]
          simp_rw [add_mul]
          rw [Finset.sum_add_distrib]
          ring
      map_smul' := by
        intro c x
        ext j
        · simp only [rowDot, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
            RingHom.id_apply]
          change -(∑ i : Node, c * x.2 i * right i) =
            c * -(∑ i : Node, x.2 i * right i)
          rw [mul_neg, Finset.mul_sum]
          apply congrArg Neg.neg
          apply Finset.sum_congr rfl
          intro i hi
          ring
        · simp only [rowMulMatrix, Prod.smul_snd, Pi.smul_apply,
            Prod.smul_fst, smul_eq_mul, RingHom.id_apply]
          rw [show (∑ i : Node, c * x.2 i * A0 i j) =
              c * ∑ i : Node, x.2 i * A0 i j by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring]
          ring }
  have hT_injective : Function.Injective T := by
    have hker : ∀ x : ℝ × RowVector Node, T x = 0 → x = 0 := by
      intro x hx
      have hxfirst : -rowDot (Node := Node) x.2 right = 0 :=
        congrArg Prod.fst hx
      have hxsecond : (fun j : Node =>
          rowMulMatrix (Node := Node) x.2 A0 j - x.2 j + x.1 * left j) = 0 :=
        congrArg Prod.snd hx
      have hmatrix (u v : RowVector Node) :
          rowDot (Node := Node) u (matrixMulVector (Node := Node) A0 v) =
            rowDot (Node := Node) (rowMulMatrix (Node := Node) u A0) v := by
        unfold rowDot matrixMulVector rowMulMatrix
        calc
          (∑ i : Node, u i * ∑ j : Node, A0 i j * v j) =
              ∑ j : Node, (∑ i : Node, u i * A0 i j) * v j := by
            simp_rw [Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j hj
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = _ := rfl
      have htranspose (z : ℝ × RowVector Node) :
          x.1 * rowDot (Node := Node) left z.2 +
              rowDot (Node := Node) x.2
                (fun i : Node => matrixMulVector (Node := Node) A0 z.2 i -
                  z.2 i - z.1 * right i) =
            (-rowDot (Node := Node) x.2 right) * z.1 +
              rowDot (Node := Node)
                (fun j : Node => rowMulMatrix (Node := Node) x.2 A0 j -
                  x.2 j + x.1 * left j) z.2 := by
        change x.1 * (∑ j : Node, left j * z.2 j) +
              ∑ i : Node, x.2 i *
                (matrixMulVector (Node := Node) A0 z.2 i - z.2 i - z.1 * right i) =
            (-(∑ i : Node, x.2 i * right i)) * z.1 +
              ∑ j : Node,
                (rowMulMatrix (Node := Node) x.2 A0 j - x.2 j + x.1 * left j) * z.2 j
        simp only [mul_sub, mul_add, sub_mul, add_mul]
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          Finset.sum_add_distrib, Finset.sum_sub_distrib]
        have hm := hmatrix x.2 z.2
        unfold rowDot at hm
        rw [hm]
        simp_rw [Finset.mul_sum]
        rw [show (∑ i : Node, x.2 i * (z.1 * right i)) =
            z.1 * ∑ i : Node, x.2 i * right i by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring]
        ring
      have hpair (z : ℝ × RowVector Node) :
          x.1 * (bordered z).1 +
            rowDot (Node := Node) x.2 (bordered z).2 = 0 := by
        rw [hbordered z, htranspose z, hxfirst]
        rw [hxsecond]
        simp [rowDot]
      have hxone : x.1 = 0 := by
        have h := hpair (bordered.symm (1, 0))
        rw [bordered.apply_symm_apply] at h
        simpa [rowDot] using h
      have hxtwo : x.2 = 0 := by
        funext i
        have h := hpair
          (bordered.symm (0, fun j : Node => if j = i then 1 else 0))
        rw [bordered.apply_symm_apply] at h
        simpa [rowDot] using h
      exact Prod.ext hxone hxtwo
    intro x y hxy
    rw [← sub_eq_zero]
    apply hker (x - y)
    rw [map_sub, hxy, sub_self]
  let e : (ℝ × RowVector Node) ≃L[ℝ] (ℝ × RowVector Node) :=
    (LinearEquiv.ofInjectiveEndo T hT_injective).toContinuousLinearEquiv
  exact ⟨e, fun x => rfl⟩

theorem standard_left_bordered_unit_eigenpair_jacobian_equiv
    (A0 : NodeMatrix Node) (right left : RowVector Node)
    (transposed : (ℝ × RowVector Node) ≃L[ℝ] (ℝ × RowVector Node))
    (htransposed : ∀ x : ℝ × RowVector Node,
      transposed x = (-rowDot (Node := Node) x.2 right,
        fun j : Node => rowMulMatrix (Node := Node) x.2 A0 j -
          x.2 j + x.1 * left j)) :
    ∃ e : (ℝ × RowVector Node) ≃L[ℝ] (ℝ × RowVector Node),
      ∀ x : ℝ × RowVector Node,
        e x = (rowDot (Node := Node) right x.2,
          fun j : Node => rowMulMatrix (Node := Node) x.2 A0 j -
            x.2 j - x.1 * left j) := by
  classical
  let S : (ℝ × RowVector Node) →ₗ[ℝ] (ℝ × RowVector Node) :=
    { toFun := fun x => (rowDot (Node := Node) right x.2,
        fun j : Node => rowMulMatrix (Node := Node) x.2 A0 j -
          x.2 j - x.1 * left j)
      map_add' := by
        intro x y
        ext j
        · simp only [rowDot, Prod.snd_add, Pi.add_apply, Prod.fst_add]
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib]
        · simp only [rowMulMatrix, Prod.snd_add, Pi.add_apply, Prod.fst_add]
          simp_rw [add_mul]
          rw [Finset.sum_add_distrib]
          ring
      map_smul' := by
        intro c x
        ext j
        · simp only [rowDot, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
            RingHom.id_apply]
          change (∑ i : Node, right i * (c * x.2 i)) =
            c * ∑ i : Node, right i * x.2 i
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        · simp only [rowMulMatrix, Prod.smul_snd, Pi.smul_apply,
            Prod.smul_fst, smul_eq_mul, RingHom.id_apply]
          rw [show (∑ i : Node, c * x.2 i * A0 i j) =
              c * ∑ i : Node, x.2 i * A0 i j by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring]
          ring }
  have hS_injective : Function.Injective S := by
    have hker : ∀ x : ℝ × RowVector Node, S x = 0 → x = 0 := by
      intro x hx
      let y : ℝ × RowVector Node := (-x.1, x.2)
      have hy : transposed y = 0 := by
        rw [htransposed]
        have hxfirst := congrArg Prod.fst hx
        have hxsecond := congrArg Prod.snd hx
        ext j
        · simpa [S, y, rowDot, mul_comm] using congrArg Neg.neg hxfirst
        · simpa [S, y] using congrFun hxsecond j
      have hy0 : y = 0 := transposed.injective (by simpa using hy)
      have hyfirst := congrArg Prod.fst hy0
      have hysecond := congrArg Prod.snd hy0
      apply Prod.ext
      · simpa [y] using congrArg Neg.neg hyfirst
      · simpa [y] using hysecond
    intro x y hxy
    rw [← sub_eq_zero]
    apply hker (x - y)
    rw [map_sub, hxy, sub_self]
  let e : (ℝ × RowVector Node) ≃L[ℝ] (ℝ × RowVector Node) :=
    (LinearEquiv.ofInjectiveEndo S hS_injective).toContinuousLinearEquiv
  exact ⟨e, fun x => rfl⟩

theorem augmented_bordered_unit_eigenpair_jacobian_equiv
    (vderiv : RowVector Node)
    (bordered : (ℝ × RowVector Node) ≃L[ℝ] (ℝ × RowVector Node)) :
    ∃ e : (ℝ × (ℝ × RowVector Node)) ≃L[ℝ]
        (ℝ × (ℝ × RowVector Node)),
      ∀ x : ℝ × (ℝ × RowVector Node),
        e x = (x.1, bordered x.2 + (0, x.1 • vderiv)) := by
  let T : (ℝ × (ℝ × RowVector Node)) →ₗ[ℝ]
      (ℝ × (ℝ × RowVector Node)) :=
    { toFun := fun x => (x.1, bordered x.2 + (0, x.1 • vderiv))
      map_add' := by
        intro x y
        ext i <;> simp <;> ring
      map_smul' := by
        intro c x
        ext i <;> simp [smul_add] <;> ring }
  have hT_injective : Function.Injective T := by
    have hker : ∀ x : ℝ × (ℝ × RowVector Node), T x = 0 → x = 0 := by
      intro x hx
      have hx1 : x.1 = 0 := congrArg Prod.fst hx
      have hx2 : bordered x.2 = 0 := by
        have h := congrArg Prod.snd hx
        change bordered x.2 + (0, x.1 • vderiv) = 0 at h
        rw [hx1] at h
        have hzero : (0, (0 : RowVector Node)) =
            (0 : ℝ × RowVector Node) := rfl
        rw [zero_smul, hzero, add_zero] at h
        exact h
      have : x.2 = 0 := bordered.injective (by simpa using hx2)
      exact Prod.ext hx1 this
    intro x y hxy
    rw [← sub_eq_zero]
    apply hker (x - y)
    rw [map_sub, hxy, sub_self]
  let e : (ℝ × (ℝ × RowVector Node)) ≃L[ℝ]
      (ℝ × (ℝ × RowVector Node)) :=
    (LinearEquiv.ofInjectiveEndo T hT_injective).toContinuousLinearEquiv
  exact ⟨e, fun x => rfl⟩

theorem analytic_normalized_right_eigenbranch_eventually_of_bordered
    (A : ℝ → NodeMatrix Node) (alpha1 : ℝ)
    (right left : RowVector Node)
    (hanalytic : RealAnalyticMatrixFamilyNear (Node := Node) A alpha1)
    (hright : matrixMulVector (Node := Node) (A 0) right = right)
    (hnormalized : rowDot (Node := Node) left right = 1)
    (bordered : (ℝ × RowVector Node) ≃L[ℝ] (ℝ × RowVector Node))
    (hbordered : ∀ x : ℝ × RowVector Node,
      bordered x = (rowDot (Node := Node) left x.2,
        fun i : Node => matrixMulVector (Node := Node) (A 0) x.2 i -
          x.2 i - x.1 * right i)) :
    ∃ gamma : ℝ → ℝ, ∃ r : ℝ → RowVector Node,
      gamma 0 = 1 ∧ r 0 = right ∧
        ∀ᶠ alpha : ℝ in 𝓝 0,
          AnalyticAt ℝ gamma alpha ∧ AnalyticAt ℝ r alpha ∧
            matrixMulVector (Node := Node) (A alpha) (r alpha) =
              gamma alpha • r alpha ∧
            rowDot (Node := Node) left (r alpha) = 1 := by
  classical
  have hAanalytic : AnalyticAt ℝ A 0 :=
    hanalytic.2 0 (by simpa using hanalytic.1)
  obtain ⟨Aderiv, hAderiv⟩ : ∃ Aderiv : NodeMatrix Node,
      HasDerivAt A Aderiv 0 :=
    ⟨_, hAanalytic.differentiableAt.hasDerivAt⟩
  obtain ⟨jacobian, hjacobian⟩ :=
    augmented_bordered_unit_eigenpair_jacobian_equiv
      (matrixMulVector (Node := Node) Aderiv right) bordered
  let base : ℝ × (ℝ × RowVector Node) := (0, (1, right))
  let target : ℝ × (ℝ × RowVector Node) := (0, (1, 0))
  let Phi : (ℝ × (ℝ × RowVector Node)) →
      (ℝ × (ℝ × RowVector Node)) := fun x =>
    (x.1, (rowDot (Node := Node) left x.2.2,
      matrixMulVector (Node := Node) (A x.1) x.2.2 - x.2.1 • x.2.2))
  have hPhi_base : Phi base = target := by
    simp [Phi, base, target, hright, hnormalized]
  have hPhi_analytic : AnalyticAt ℝ Phi base := by
    have hx1 : AnalyticAt ℝ
        (fun x : ℝ × (ℝ × RowVector Node) => x.1) base :=
      analyticAt_fst
    have hx2 : AnalyticAt ℝ
        (fun x : ℝ × (ℝ × RowVector Node) => x.2) base :=
      analyticAt_snd
    have hx21 : AnalyticAt ℝ
        (fun x : ℝ × (ℝ × RowVector Node) => x.2.1) base :=
      analyticAt_fst.comp' hx2
    have hx22 : AnalyticAt ℝ
        (fun x : ℝ × (ℝ × RowVector Node) => x.2.2) base :=
      analyticAt_snd.comp' hx2
    have hAcomp : AnalyticAt ℝ
        (fun x : ℝ × (ℝ × RowVector Node) => A x.1) base :=
      hAanalytic.comp_of_eq' hx1 (by simp [base])
    have hnormalAnalytic : AnalyticAt ℝ
        (fun x : ℝ × (ℝ × RowVector Node) =>
          rowDot (Node := Node) left x.2.2) base := by
      unfold rowDot
      exact Finset.analyticAt_fun_sum Finset.univ (fun i hi =>
        analyticAt_const.mul (analyticAt_pi_iff.mp hx22 i))
    have hresidualAnalytic : AnalyticAt ℝ
        (fun x : ℝ × (ℝ × RowVector Node) =>
          matrixMulVector (Node := Node) (A x.1) x.2.2 -
            x.2.1 • x.2.2) base := by
      apply AnalyticAt.pi
      intro i
      simp only [matrixMulVector, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      apply (Finset.analyticAt_fun_sum Finset.univ ?_).sub
        (hx21.mul (analyticAt_pi_iff.mp hx22 i))
      intro j hj
      exact (analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hAcomp i) j).mul
        (analyticAt_pi_iff.mp hx22 j)
    exact hx1.prod (hnormalAnalytic.prod hresidualAnalytic)
  have hPhi_deriv : HasFDerivAt Phi
      (jacobian : (ℝ × (ℝ × RowVector Node)) →L[ℝ]
        (ℝ × (ℝ × RowVector Node))) base := by
    let rawDeriv : (ℝ × (ℝ × RowVector Node)) →
        (ℝ × (ℝ × RowVector Node)) := fun d =>
      (d.1, (rowDot (Node := Node) left d.2.2,
        d.1 • matrixMulVector (Node := Node) Aderiv right +
          matrixMulVector (Node := Node) (A 0) d.2.2 -
            (d.2.1 • right + d.2.2)))
    have hraw_eq (d : ℝ × (ℝ × RowVector Node)) :
        rawDeriv d = jacobian d := by
      rw [hjacobian d, hbordered d.2]
      ext i <;> simp [rawDeriv]
      ring
    have hline (d : ℝ × (ℝ × RowVector Node)) :
        HasDerivAt (fun t : ℝ => Phi (base + t • d)) (rawDeriv d) 0 := by
      have hparam : HasDerivAt
          (fun t : ℝ => (base + t • d).1) d.1 0 := by
        simpa [base] using (hasDerivAt_id (0 : ℝ)).smul_const d.1
      have hgammaLine : HasDerivAt
          (fun t : ℝ => (base + t • d).2.1) d.2.1 0 := by
        simpa [base, add_comm] using
          ((hasDerivAt_id (0 : ℝ)).smul_const d.2.1).const_add 1
      have hrLine : HasDerivAt
          (fun t : ℝ => (base + t • d).2.2) d.2.2 0 := by
        simpa [base, add_comm] using
          ((hasDerivAt_id (0 : ℝ)).smul_const d.2.2).const_add right
      have hALine : HasDerivAt
          (fun t : ℝ => A ((base + t • d).1)) (d.1 • Aderiv) 0 :=
        by
          simpa [Function.comp_def] using
            hAderiv.scomp_of_eq 0 hparam (by simp [base])
      have hnormalLine : HasDerivAt
          (fun t : ℝ => rowDot (Node := Node) left (base + t • d).2.2)
          (rowDot (Node := Node) left d.2.2) 0 := by
        unfold rowDot
        apply HasDerivAt.fun_sum
        intro i hi
        have hiDeriv : HasDerivAt
            (fun t : ℝ => (base + t • d).2.2 i) (d.2.2 i) 0 := by
          have hi := (hasFDerivAt_apply (𝕜 := ℝ) i right).comp_hasDerivAt_of_eq
            0 hrLine (by simp [base])
          convert hi using 1 <;>
            simp [Function.comp_def, ContinuousLinearMap.one_apply]
        exact hiDeriv.const_mul (left i)
      have hmatrixLine : HasDerivAt
          (fun t : ℝ => matrixMulVector (Node := Node)
            (A ((base + t • d).1)) (base + t • d).2.2)
          (d.1 • matrixMulVector (Node := Node) Aderiv right +
            matrixMulVector (Node := Node) (A 0) d.2.2) 0 := by
        rw [hasDerivAt_pi]
        intro i
        unfold matrixMulVector
        have hsum : HasDerivAt
            (fun t : ℝ => ∑ j : Node,
              A ((base + t • d).1) i j * (base + t • d).2.2 j)
            (∑ j : Node,
              ((d.1 • Aderiv) i j * right j + A 0 i j * d.2.2 j)) 0 := by
          apply HasDerivAt.fun_sum
          intro j hj
          have hAij : HasDerivAt
              (fun t : ℝ => A ((base + t • d).1) i j)
              ((d.1 • Aderiv) i j) 0 := by
            have hi := (hasFDerivAt_apply (𝕜 := ℝ) i (A 0)).comp_hasDerivAt_of_eq
              0 hALine (by simp [base])
            have hij := (hasFDerivAt_apply (𝕜 := ℝ) j (A 0 i)).comp_hasDerivAt_of_eq
              0 hi (by simp [base])
            convert hij using 1 <;>
              simp [Function.comp_def, ContinuousLinearMap.one_apply]
          have hrj : HasDerivAt
              (fun t : ℝ => (base + t • d).2.2 j) (d.2.2 j) 0 := by
            have hj := (hasFDerivAt_apply (𝕜 := ℝ) j right).comp_hasDerivAt_of_eq
              0 hrLine (by simp [base])
            convert hj using 1 <;>
              simp [Function.comp_def, ContinuousLinearMap.one_apply]
          convert hAij.mul hrj using 1 <;> simp [base, Pi.smul_apply]
        convert hsum using 1
        simp only [Pi.add_apply, Pi.smul_apply]
        rw [Finset.sum_add_distrib]
        congr 1
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [smul_eq_mul]
        ring
      have hscalarLine : HasDerivAt
          (fun t : ℝ => (base + t • d).2.1 • (base + t • d).2.2)
          (d.2.1 • right + d.2.2) 0 := by
        rw [hasDerivAt_pi]
        intro i
        have hrj : HasDerivAt
            (fun t : ℝ => (base + t • d).2.2 i) (d.2.2 i) 0 :=
          by
            have hi := (hasFDerivAt_apply (𝕜 := ℝ) i right).comp_hasDerivAt_of_eq
              0 hrLine (by simp [base])
            convert hi using 1 <;>
              simp [Function.comp_def, ContinuousLinearMap.one_apply]
        simpa [Pi.smul_apply, smul_eq_mul, base] using hgammaLine.mul hrj
      have hcombined := hparam.prodMk
        (hnormalLine.prodMk (hmatrixLine.sub hscalarLine))
      convert hcombined using 1 <;> simp [Phi, rawDeriv]
    have hcanonical := hPhi_analytic.differentiableAt.hasFDerivAt
    have hderiv_eq : fderiv ℝ Phi base =
        (jacobian : (ℝ × (ℝ × RowVector Node)) →L[ℝ]
          (ℝ × (ℝ × RowVector Node))) := by
      apply ContinuousLinearMap.ext
      intro d
      let line : ℝ → ℝ × (ℝ × RowVector Node) :=
        fun t => base + t • d
      have hlineDeriv : HasDerivAt line d 0 := by
        simpa [line] using
          ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add base
      have hcomp := hcanonical.comp_hasDerivAt_of_eq 0 hlineDeriv (by simp [line])
      have hline' := hline d
      rw [hraw_eq d] at hline'
      exact hcomp.unique (by simpa [Function.comp_def, line] using hline')
    rw [← hderiv_eq]
    exact hcanonical
  have hPhi_strict : HasStrictFDerivAt Phi
      (jacobian : (ℝ × (ℝ × RowVector Node)) →L[ℝ]
        (ℝ × (ℝ × RowVector Node))) base := by
    have h := hPhi_analytic.hasStrictFDerivAt
    convert h using 1
    exact hPhi_deriv.fderiv.symm
  let H : OpenPartialHomeomorph
      (ℝ × (ℝ × RowVector Node))
      (ℝ × (ℝ × RowVector Node)) :=
    hPhi_strict.toOpenPartialHomeomorph Phi
  have hbase_source : base ∈ H.source := by
    exact hPhi_strict.mem_toOpenPartialHomeomorph_source
  have htarget_target : target ∈ H.target := by
    rw [← hPhi_base]
    exact H.map_source hbase_source
  let embed : ℝ → ℝ × (ℝ × RowVector Node) :=
    fun alpha => (alpha, (1, 0))
  have hembed0 : embed 0 = target := by rfl
  have hinv_analytic : AnalyticAt ℝ H.symm target := by
    rw [← hPhi_base]
    apply H.analyticAt_symm'
    · exact hbase_source
    · simpa [H] using hPhi_analytic
    · simpa [H] using hPhi_deriv.fderiv
  have hembed_analytic : AnalyticAt ℝ embed 0 := by
    fun_prop
  have hbranch_analytic : AnalyticAt ℝ (fun alpha => H.symm (embed alpha)) 0 := by
    exact hinv_analytic.comp_of_eq' hembed_analytic hembed0
  let gamma : ℝ → ℝ := fun alpha => (H.symm (embed alpha)).2.1
  let r : ℝ → RowVector Node := fun alpha => (H.symm (embed alpha)).2.2
  have hbase_inverse : H.symm target = base := by
    rw [← hPhi_base]
    exact H.left_inv hbase_source
  have hgamma0 : gamma 0 = 1 := by
    simp [gamma, hembed0, hbase_inverse, base]
  have hr0 : r 0 = right := by
    simp [r, hembed0, hbase_inverse, base]
  have hgamma_analytic : AnalyticAt ℝ gamma 0 := by
    exact analyticAt_fst.comp'
      (analyticAt_snd.comp' hbranch_analytic)
  have hr_analytic : AnalyticAt ℝ r 0 := by
    exact analyticAt_snd.comp'
      (analyticAt_snd.comp' hbranch_analytic)
  have hembed_tendsto : Tendsto embed (𝓝 0) (𝓝 (Phi base)) := by
    rw [hPhi_base, ← hembed0]
    exact hembed_analytic.continuousAt
  have hright_inverse : ∀ᶠ alpha : ℝ in 𝓝 0,
      Phi (H.symm (embed alpha)) = embed alpha :=
    hembed_tendsto.eventually hPhi_strict.eventually_right_inverse
  refine ⟨gamma, r, hgamma0, hr0, ?_⟩
  filter_upwards [hgamma_analytic.eventually_analyticAt,
    hr_analytic.eventually_analyticAt, hright_inverse] with alpha hga hra hinv
  have hnormal := congrArg (fun x => x.2.1) hinv
  have heigen := congrArg (fun x => x.2.2) hinv
  have hparameter := congrArg Prod.fst hinv
  have hparameter' : (H.symm (embed alpha)).1 = alpha := by
    simpa [embed] using hparameter
  refine ⟨hga, hra, ?_, ?_⟩
  · have heigen' :
        matrixMulVector (Node := Node) (A (H.symm (embed alpha)).1)
            (H.symm (embed alpha)).2.2 =
          (H.symm (embed alpha)).2.1 • (H.symm (embed alpha)).2.2 :=
        sub_eq_zero.mp (by simpa [Phi, embed] using heigen)
    rw [hparameter'] at heigen'
    simpa [gamma, r] using heigen'
  · simpa [Phi, embed, r] using hnormal

theorem analytic_normalized_right_eigenbranch_eventually
    (A : ℝ → NodeMatrix Node) (alpha1 : ℝ)
    (right left : RowVector Node)
    (hanalytic : RealAnalyticMatrixFamilyNear (Node := Node) A alpha1)
    (hright : matrixMulVector (Node := Node) (A 0) right = right)
    (hleft : rowMulMatrix (Node := Node) left (A 0) = left)
    (hnormalized : rowDot (Node := Node) left right = 1)
    (halgebraicallySimple :
      UnitEigenvalueAlgebraicallySimple (Node := Node) (A 0) right) :
    ∃ gamma : ℝ → ℝ, ∃ r : ℝ → RowVector Node,
      gamma 0 = 1 ∧ r 0 = right ∧
        ∀ᶠ alpha : ℝ in 𝓝 0,
          AnalyticAt ℝ gamma alpha ∧ AnalyticAt ℝ r alpha ∧
            matrixMulVector (Node := Node) (A alpha) (r alpha) =
              gamma alpha • r alpha ∧
            rowDot (Node := Node) left (r alpha) = 1 := by
  obtain ⟨bordered, hbordered⟩ :=
    bordered_unit_eigenpair_jacobian_equiv (A 0) right left hleft
      hnormalized halgebraicallySimple
  exact analytic_normalized_right_eigenbranch_eventually_of_bordered
    A alpha1 right left hanalytic hright hnormalized bordered hbordered

theorem realAnalyticMatrixFamilyNear_hasDerivAt_zero
    (A : ℝ → NodeMatrix Node) (alpha1 : ℝ)
    (hanalytic : RealAnalyticMatrixFamilyNear (Node := Node) A alpha1) :
    ∃ Aderiv : NodeMatrix Node, HasDerivAt A Aderiv 0 := by
  have hAanalytic : AnalyticAt ℝ A 0 :=
    hanalytic.2 0 (by simpa using hanalytic.1)
  exact ⟨_, hAanalytic.differentiableAt.hasDerivAt⟩

theorem simple_eigenvalue_branch_derivative_pairing
    (A : ℝ → NodeMatrix Node) (gamma : ℝ → ℝ)
    (r : ℝ → RowVector Node)
    (Aderiv : NodeMatrix Node) (gammaDeriv : ℝ)
    (rderiv right left : RowVector Node)
    (hA : HasDerivAt A Aderiv 0)
    (hgamma : HasDerivAt gamma gammaDeriv 0)
    (hr : HasDerivAt r rderiv 0)
    (hleft : rowMulMatrix (Node := Node) left (A 0) = left)
    (hright : r 0 = right)
    (hnormalized : rowDot (Node := Node) left right = 1)
    (hgamma0 : gamma 0 = 1)
    (heigen : ∀ᶠ alpha : ℝ in 𝓝 0,
      matrixMulVector (Node := Node) (A alpha) (r alpha) =
        gamma alpha • r alpha) :
    HasDerivAt gamma
      (rowDot (Node := Node) left
        (matrixMulVector (Node := Node) Aderiv right)) 0 := by
  have hAij (i j : Node) :
      HasDerivAt (fun alpha : ℝ => A alpha i j) (Aderiv i j) 0 := by
    have hi :=
      (hasFDerivAt_apply (𝕜 := ℝ) i (A 0)).comp 0 hA.hasFDerivAt
    have hij :=
      (hasFDerivAt_apply (𝕜 := ℝ) j (A 0 i)).comp 0 hi
    convert hij.hasDerivAt using 1 <;>
      simp [Function.comp_def, ContinuousLinearMap.one_apply]
  have hrj (j : Node) :
      HasDerivAt (fun alpha : ℝ => r alpha j) (rderiv j) 0 := by
    have hj :=
      (hasFDerivAt_apply (𝕜 := ℝ) j (r 0)).comp 0 hr.hasFDerivAt
    convert hj.hasDerivAt using 1 <;>
      simp [Function.comp_def, ContinuousLinearMap.one_apply]
  have hlhs :
      HasDerivAt
        (fun alpha : ℝ =>
          rowDot (Node := Node) left
            (matrixMulVector (Node := Node) (A alpha) (r alpha)))
        (∑ i : Node, left i *
          ∑ j : Node, (Aderiv i j * r 0 j + A 0 i j * rderiv j)) 0 := by
    unfold rowDot matrixMulVector
    apply HasDerivAt.fun_sum
    intro i hi
    exact (HasDerivAt.fun_sum fun j _ =>
      (hAij i j).mul (hrj j)).const_mul (left i)
  have hrhs :
      HasDerivAt
        (fun alpha : ℝ =>
          rowDot (Node := Node) left (gamma alpha • r alpha))
        (gammaDeriv * rowDot (Node := Node) left (r 0) +
          gamma 0 * rowDot (Node := Node) left rderiv) 0 := by
    unfold rowDot
    simp only [Pi.smul_apply, smul_eq_mul]
    convert (hgamma.mul
      (HasDerivAt.fun_sum fun i _ =>
        (hrj i).const_mul (left i))) using 1
    · funext alpha
      simp only [Pi.mul_apply]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
  have heq : (fun alpha : ℝ =>
      rowDot (Node := Node) left
        (matrixMulVector (Node := Node) (A alpha) (r alpha))) =ᶠ[𝓝 0]
      (fun alpha : ℝ =>
        rowDot (Node := Node) left (gamma alpha • r alpha)) := by
    filter_upwards [heigen] with alpha halpha
    rw [halpha]
  have hderivEq :
      (∑ i : Node, left i *
          ∑ j : Node, (Aderiv i j * r 0 j + A 0 i j * rderiv j)) =
        gammaDeriv * rowDot (Node := Node) left (r 0) +
          gamma 0 * rowDot (Node := Node) left rderiv :=
    hlhs.unique (hrhs.congr_of_eventuallyEq heq)
  have hleft_deriv :
      (∑ i : Node, left i * ∑ j : Node, Aderiv i j * right j) =
        rowDot (Node := Node) left
          (matrixMulVector (Node := Node) Aderiv right) := by
    rfl
  have hleft_rderiv :
      (∑ i : Node, left i * ∑ j : Node, A 0 i j * rderiv j) =
        rowDot (Node := Node) left rderiv := by
    unfold rowMulMatrix at hleft
    calc
      (∑ i : Node, left i * ∑ j : Node, A 0 i j * rderiv j) =
          ∑ j : Node, (∑ i : Node, left i * A 0 i j) * rderiv j := by
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = ∑ j : Node, left j * rderiv j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [congrFun hleft j]
      _ = rowDot (Node := Node) left rderiv := by rfl
  have hgammaDeriv :
      gammaDeriv =
        rowDot (Node := Node) left
          (matrixMulVector (Node := Node) Aderiv right) := by
    rw [hright, hgamma0, hnormalized] at hderivEq
    have hsplit :
        (∑ i : Node, left i *
          ∑ j : Node, (Aderiv i j * right j + A 0 i j * rderiv j)) =
            (∑ i : Node, left i * ∑ j : Node, Aderiv i j * right j) +
              ∑ i : Node, left i * ∑ j : Node, A 0 i j * rderiv j := by
      simp_rw [Finset.sum_add_distrib, mul_add]
      rw [Finset.sum_add_distrib]
    rw [hsplit, hleft_deriv, hleft_rderiv] at hderivEq
    linarith
  rw [hgammaDeriv] at hgamma
  exact hgamma

theorem normalized_eigenbranch_derivative_pairing_eventual
    (A : ℝ → NodeMatrix Node) (gamma : ℝ → ℝ)
    (r : ℝ → RowVector Node) (alpha1 : ℝ)
    (right left : RowVector Node)
    (hanalytic : RealAnalyticMatrixFamilyNear (Node := Node) A alpha1)
    (hleft : rowMulMatrix (Node := Node) left (A 0) = left)
    (hright : r 0 = right)
    (hnormalized : rowDot (Node := Node) left right = 1)
    (hgamma0 : gamma 0 = 1)
    (hbranch : ∀ᶠ alpha : ℝ in 𝓝 0,
      AnalyticAt ℝ gamma alpha ∧ AnalyticAt ℝ r alpha ∧
        matrixMulVector (Node := Node) (A alpha) (r alpha) =
          gamma alpha • r alpha ∧
        rowDot (Node := Node) left (r alpha) = 1) :
    ∃ Aderiv : NodeMatrix Node,
      HasDerivAt A Aderiv 0 ∧
        HasDerivAt gamma
          (rowDot (Node := Node) left
            (matrixMulVector (Node := Node) Aderiv right)) 0 := by
  classical
  obtain ⟨Aderiv, hAderiv⟩ :=
    realAnalyticMatrixFamilyNear_hasDerivAt_zero (Node := Node) A alpha1 hanalytic
  have hbranch0 := hbranch.self_of_nhds
  have hgammaDeriv :
      HasDerivAt gamma ((fderiv ℝ gamma 0) 1) 0 :=
    hbranch0.1.differentiableAt.hasDerivAt
  have hrDeriv :
      HasDerivAt r ((fderiv ℝ r 0) 1) 0 :=
    hbranch0.2.1.differentiableAt.hasDerivAt
  have heigen : ∀ᶠ alpha : ℝ in 𝓝 0,
      matrixMulVector (Node := Node) (A alpha) (r alpha) =
        gamma alpha • r alpha :=
    hbranch.mono fun alpha halpha => halpha.2.2.1
  refine ⟨Aderiv, hAderiv, ?_⟩
  exact simple_eigenvalue_branch_derivative_pairing (Node := Node)
    A gamma r Aderiv ((fderiv ℝ gamma 0) 1) ((fderiv ℝ r 0) 1)
      right left hAderiv hgammaDeriv hrDeriv hleft hright hnormalized
      hgamma0 heigen

/-- Stable complement matrix in Appendix A:
`F = A - lambda P`, where `P` is the Riesz projection onto the slow
eigenspace. -/
def stableComplementMatrix
    (Aalpha : NodeMatrix Node) (lambda : ℝ) (P : NodeMatrix Node) :
    NodeMatrix Node :=
  matrixSub (Node := Node) Aalpha (lambda • P)

/-- Parameterized stable complement `F(α)=A(α)-γ(α)P(α)` from Lemma A.1. -/
def stableComplementFromRiesz
    (A : ℝ → NodeMatrix Node) (gamma : ℝ → ℝ)
    (P : ℝ → NodeMatrix Node) (alpha : ℝ) : NodeMatrix Node :=
  stableComplementMatrix (Node := Node) (A alpha) (gamma alpha) (P alpha)

theorem stableComplementFromRiesz_analyticAt
    (A : ℝ → NodeMatrix Node) (gamma : ℝ → ℝ)
    (P : ℝ → NodeMatrix Node) (alpha : ℝ)
    (hA : AnalyticAt ℝ A alpha)
    (hgamma : AnalyticAt ℝ gamma alpha)
    (hP : AnalyticAt ℝ P alpha) :
    AnalyticAt ℝ
      (stableComplementFromRiesz (Node := Node) A gamma P) alpha := by
  classical
  unfold stableComplementFromRiesz stableComplementMatrix matrixSub
  apply AnalyticAt.pi
  intro i
  apply AnalyticAt.pi
  intro j
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact (analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hA i) j).sub
    (hgamma.mul (analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hP i) j))

/-- The algebraic part of Lemma A.1 after the contour Riesz projection has
been identified: the stable complement gives the splitting and annihilates the
slow projection on both sides. -/
theorem rieszProjection_stableComplementMatrix_algebra
    (Aalpha : NodeMatrix Node) (lambda : ℝ) (P : NodeMatrix Node)
    (hRiesz :
      IsRieszProjectionAtEigenvalue (Node := Node) Aalpha lambda P) :
    Aalpha =
        matrixAdd (Node := Node) (lambda • P)
          (stableComplementMatrix (Node := Node) Aalpha lambda P) ∧
      matrixMul (Node := Node) P
          (stableComplementMatrix (Node := Node) Aalpha lambda P) = 0 ∧
        matrixMul (Node := Node)
          (stableComplementMatrix (Node := Node) Aalpha lambda P) P = 0 := by
  classical
  have hPP : matrixMul (Node := Node) P P = P := hRiesz.1.1
  have hAP : matrixMul (Node := Node) Aalpha P = lambda • P := hRiesz.2.1
  have hPA : matrixMul (Node := Node) P Aalpha = lambda • P := hRiesz.2.2.1
  refine ⟨?_, ?_, ?_⟩
  · funext i j
    simp [stableComplementMatrix, matrixAdd, matrixSub]
  · funext i k
    have hPAik := congrFun (congrFun hPA i) k
    have hPPik := congrFun (congrFun hPP i) k
    calc
      matrixMul (Node := Node) P
          (stableComplementMatrix (Node := Node) Aalpha lambda P) i k
          = matrixMul (Node := Node) P Aalpha i k -
              lambda * matrixMul (Node := Node) P P i k := by
            simp only [stableComplementMatrix, matrixMul, matrixSub,
              Pi.smul_apply, smul_eq_mul]
            simp_rw [mul_sub]
            rw [Finset.sum_sub_distrib]
            congr 1
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _hj
            ring
      _ = 0 := by
            rw [hPAik, hPPik]
            simp
  · funext i k
    have hAPik := congrFun (congrFun hAP i) k
    have hPPik := congrFun (congrFun hPP i) k
    calc
      matrixMul (Node := Node)
          (stableComplementMatrix (Node := Node) Aalpha lambda P) P i k
          = matrixMul (Node := Node) Aalpha P i k -
              lambda * matrixMul (Node := Node) P P i k := by
            simp only [stableComplementMatrix, matrixMul, matrixSub,
              Pi.smul_apply, smul_eq_mul]
            simp_rw [sub_mul]
            rw [Finset.sum_sub_distrib]
            congr 1
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _hj
            ring
      _ = 0 := by
            rw [hAPik, hPPik]
            simp

/-- Source-level stable resolvent disk for the complement in Lemma A.1.

This is the contour/Cauchy hypothesis used in the paper after constructing the
Riesz projection: all complex eigenvalues of the stable complement lie strictly
inside the fixed circle `|z| = theta`, uniformly for `|alpha| ≤ alpha0`.
It is deliberately phrased for the real matrix's complex scalar extension so it
can feed the finite-dimensional resolvent power estimate without referring to
the local left/right eigenbranch surrogate. -/
def StableRemainderResolventDisk
    (F : ℝ → NodeMatrix Node) (alpha0 theta : ℝ) : Prop :=
  ∀ alpha : ℝ, |alpha| ≤ alpha0 →
    (∀ z : ℂ, IsComplexRightEigenvalue (Node := Node) (F alpha) z →
      ‖z‖ < theta) ∧
      ∀ z : ℂ, ‖z‖ = theta →
        ¬ IsComplexRightEigenvalue (Node := Node) (F alpha) z

/-- Complex node matrices used only for the Appendix A resolvent argument.

The paper works with the complex scalar extension of a finite real matrix.
Using Mathlib's `Matrix` here keeps the local `NodeMatrix` notation while
exposing determinant, inverse, and `mulVec` APIs for the resolvent leaves. -/
abbrev ComplexNodeMatrix (Node : Type*) := Matrix Node Node ℂ

/-- Identity matrix over the complex scalar extension. -/
noncomputable def complexIdentityMatrix : ComplexNodeMatrix Node := by
  classical
  exact 1

/-- Embed a real node matrix into its complex scalar extension. -/
def complexOfRealMatrix (A : NodeMatrix Node) : ComplexNodeMatrix Node :=
  fun i j => (A i j : ℂ)

/-- Complex matrix subtraction in the fixed finite node coordinates. -/
def complexMatrixSub (A B : ComplexNodeMatrix Node) : ComplexNodeMatrix Node :=
  fun i j => A i j - B i j

/-- Complex matrix multiplication in the fixed finite node coordinates. -/
noncomputable def complexMatrixMul
    (A B : ComplexNodeMatrix Node) : ComplexNodeMatrix Node :=
  A * B

/-- Action of a complex node matrix on a complex node vector. -/
noncomputable def complexNodeMatrixMulVector
    (A : ComplexNodeMatrix Node) (v : ComplexRowVector Node) :
    ComplexRowVector Node :=
  Matrix.mulVec A v

/-- The resolvent matrix `zI - A` in the complex scalar extension. -/
noncomputable def complexResolventMatrix
    (A : NodeMatrix Node) (z : ℂ) : ComplexNodeMatrix Node :=
  complexMatrixSub (Node := Node)
    (fun i j : Node => z * complexIdentityMatrix (Node := Node) i j)
    (complexOfRealMatrix (Node := Node) A)

/-- The complex contour Riesz projection
`(2πi)⁻¹ ∮ (zI-A)⁻¹ dz` on a fixed circle.

This is the canonical Appendix A object.  It is intentionally defined from
Mathlib's `circleIntegral` and the concrete nonsingular inverse for the
complex scalar extension, rather than by choosing an arbitrary projection
branch from an existence theorem. -/
noncomputable def complexRieszProjectionOnCircle
    (A : NodeMatrix Node) (center : ℂ) (radius : ℝ) :
    ComplexNodeMatrix Node := by
  classical
  exact fun i j : Node =>
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
      (∮ z in C(center, radius),
        ((complexResolventMatrix (Node := Node) A z)⁻¹) i j)

/-- Entrywise real part of a complex node matrix. -/
noncomputable def realPartComplexNodeMatrix
    (M : ComplexNodeMatrix Node) : NodeMatrix Node :=
  fun i j : Node => (M i j).re

/-- Real Riesz projection branch obtained by descending the fixed complex
contour projection to real coordinates. -/
noncomputable def fixedCircleRieszProjection
    (A : NodeMatrix Node) (center : ℂ) (radius : ℝ) : NodeMatrix Node :=
  realPartComplexNodeMatrix (Node := Node)
    (complexRieszProjectionOnCircle (Node := Node) A center radius)

/-- Real descent for the fixed-circle contour projection.

Once the complex contour projection has analytic entries as a function of the
real parameter, the real matrix-valued `fixedCircleRieszProjection` is
analytic entrywise by composing each entry with complex real-part. -/
theorem fixedCircleRieszProjection_analyticAt_of_complex_entries
    (A : ℝ → NodeMatrix Node) (center : ℂ) (radius : ℝ) {alpha : ℝ}
    (hentry : ∀ i j : Node,
      AnalyticAt ℝ
        (fun a : ℝ =>
          complexRieszProjectionOnCircle (Node := Node) (A a) center radius i j)
        alpha) :
    AnalyticAt ℝ
      (fun a : ℝ =>
        fixedCircleRieszProjection (Node := Node) (A a) center radius)
      alpha := by
  classical
  apply AnalyticAt.pi
  intro i
  apply AnalyticAt.pi
  intro j
  have hre :
      AnalyticAt ℝ
        (fun z : ℂ => z.re)
        (complexRieszProjectionOnCircle (Node := Node) (A alpha) center radius i j) := by
    simpa [Complex.reCLM_apply] using
      (Complex.reCLM.analyticAt
        (complexRieszProjectionOnCircle (Node := Node) (A alpha) center radius i j))
  exact AnalyticAt.comp_of_eq' (𝕜 := ℝ)
    (g := fun z : ℂ => z.re)
    (f := fun a : ℝ =>
      complexRieszProjectionOnCircle (Node := Node) (A a) center radius i j)
    (y := complexRieszProjectionOnCircle (Node := Node) (A alpha) center radius i j)
    (x := alpha) hre (hentry i j) rfl

/-- Entrywise interval-integral form of the complex fixed-contour projection.

This is a bookkeeping bridge from the canonical contour notation to the
real-interval integrand used by parametric-integral APIs. -/
theorem circleIntegral_eq_Icc_integral_deriv_mul
    (f : ℂ → ℂ) (center : ℂ) (radius : ℝ) :
    (∮ z in C(center, radius), f z) =
      ∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
        deriv (circleMap center radius) theta *
          f (circleMap center radius theta) := by
  simpa only [smul_eq_mul] using
    (circleIntegral_def_Icc f center radius)

theorem complexRieszProjectionOnCircle_entry_eq_Icc_integral
    (A : NodeMatrix Node) (center : ℂ) (radius : ℝ) (i j : Node) :
    complexRieszProjectionOnCircle (Node := Node) A center radius i j =
      (letI : DecidableEq Node := Classical.decEq Node;
        (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
          (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
            deriv (circleMap center radius) theta •
              ((complexResolventMatrix (Node := Node) A
                (circleMap center radius theta))⁻¹) i j)) := by
  letI : DecidableEq Node := Classical.decEq Node
  rw [complexRieszProjectionOnCircle,
    circleIntegral_eq_Icc_integral_deriv_mul]
  rfl

/-- Pointwise analyticity of the real-parameter integrand after restricting
the fixed spectral parameter to the source circle.

This consumes the already-proved fixed-`z` scaled resolvent analyticity and
the `circleMap` sphere identity; it leaves only the genuine
analytic-under-interval-integral step for the contour entry. -/
theorem fixedCircle_scaledResolvent_intervalIntegrand_analyticAt
    [DecidableEq Node]
    (A : ℝ → NodeMatrix Node) {alpha : ℝ} (center : ℂ) (radius : ℝ)
    (hradius_nonneg : 0 ≤ radius)
    (hscaled :
      ∀ z : ℂ, ‖z - center‖ = radius →
        ∀ i j : Node,
          AnalyticAt ℝ
            (fun a : ℝ =>
              (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
                (complexResolventMatrix (Node := Node) (A a) z)⁻¹ i j)
            alpha)
    (theta : ℝ) (i j : Node) :
    AnalyticAt ℝ
      (fun a : ℝ =>
        deriv (circleMap center radius) theta *
          ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
            (complexResolventMatrix (Node := Node) (A a)
              (circleMap center radius theta))⁻¹ i j))
      alpha := by
  classical
  have htheta :
      ‖circleMap center radius theta - center‖ = radius := by
    have hmem : circleMap center radius theta ∈ Metric.sphere center radius :=
      circleMap_mem_sphere center hradius_nonneg theta
    simpa [Metric.mem_sphere, dist_eq_norm] using hmem
  exact analyticAt_const.mul
    (hscaled (circleMap center radius theta) htheta i j)

/-- Two-sided inverse specification for complex node matrices. -/
def ComplexMatrixInverseSpec
    (A R : ComplexNodeMatrix Node) : Prop :=
  complexMatrixMul (Node := Node) A R = complexIdentityMatrix (Node := Node) ∧
    complexMatrixMul (Node := Node) R A = complexIdentityMatrix (Node := Node)

/-- A concrete inverse for the resolvent `zI - A`. -/
def HasComplexResolvent
    (A : NodeMatrix Node) (z : ℂ) (R : ComplexNodeMatrix Node) : Prop :=
  ComplexMatrixInverseSpec (Node := Node)
    (complexResolventMatrix (Node := Node) A z) R

theorem complexIdentityMatrix_apply [DecidableEq Node] (i j : Node) :
    complexIdentityMatrix (Node := Node) i j =
      if i = j then (1 : ℂ) else 0 := by
  by_cases hij : i = j
  · subst j
    simp [complexIdentityMatrix]
  · simp [complexIdentityMatrix, hij]

theorem complexIdentityMatrix_eq_one [DecidableEq Node] :
    complexIdentityMatrix (Node := Node) = (1 : Matrix Node Node ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [complexIdentityMatrix]
  · simp [complexIdentityMatrix, hij]

theorem complexMatrixMul_apply
    (A B : ComplexNodeMatrix Node) (i k : Node) :
    complexMatrixMul (Node := Node) A B i k =
      ∑ j : Node, A i j * B j k := by
  classical
  simp [complexMatrixMul, Matrix.mul_apply, dotProduct]

theorem complexNodeMatrixMulVector_apply
    (A : ComplexNodeMatrix Node) (v : ComplexRowVector Node) (i : Node) :
    complexNodeMatrixMulVector (Node := Node) A v i =
      ∑ j : Node, A i j * v j := by
  classical
  simp [complexNodeMatrixMulVector, Matrix.mulVec, dotProduct]

theorem complexNodeMatrixMulVector_complexOfRealMatrix
    (A : NodeMatrix Node) (v : ComplexRowVector Node) :
    complexNodeMatrixMulVector (Node := Node)
        (complexOfRealMatrix (Node := Node) A) v =
      complexMatrixMulVector (Node := Node) A v := by
  classical
  funext i
  simp [complexNodeMatrixMulVector_apply, complexOfRealMatrix,
    complexMatrixMulVector]

theorem complex_resolvent_row_sum_eq [DecidableEq Node]
    (A : NodeMatrix Node) (z : ℂ) (v : ComplexRowVector Node) (i : Node) :
    (∑ x : Node, ((if i = x then z else 0) - (A i x : ℂ)) * v x) =
      z * v i - ∑ x : Node, (A i x : ℂ) * v x := by
  classical
  calc
    (∑ x : Node, ((if i = x then z else 0) - (A i x : ℂ)) * v x)
        = (∑ x : Node, (if i = x then z else 0) * v x) -
            ∑ x : Node, (A i x : ℂ) * v x := by
          simp_rw [sub_mul]
          rw [Finset.sum_sub_distrib]
    _ = z * v i - ∑ x : Node, (A i x : ℂ) * v x := by
          simp

theorem complexResolventMatrix_mulVec_eq_zero_iff_eigen
    (A : NodeMatrix Node) (z : ℂ) (v : ComplexRowVector Node) :
    complexNodeMatrixMulVector (Node := Node)
        (complexResolventMatrix (Node := Node) A z) v = 0 ↔
      complexMatrixMulVector (Node := Node) A v = z • v := by
  classical
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    simp [complexNodeMatrixMulVector_apply, complexResolventMatrix,
      complexMatrixSub, complexIdentityMatrix_apply, complexOfRealMatrix,
      complexMatrixMulVector, Pi.smul_apply] at hi ⊢
    rw [complex_resolvent_row_sum_eq (Node := Node) A z v i] at hi
    exact (sub_eq_zero.mp hi).symm
  · intro h
    funext i
    have hi := congrFun h i
    simp [complexNodeMatrixMulVector_apply, complexResolventMatrix,
      complexMatrixSub, complexIdentityMatrix_apply, complexOfRealMatrix,
      complexMatrixMulVector, Pi.smul_apply] at hi ⊢
    rw [complex_resolvent_row_sum_eq (Node := Node) A z v i]
    exact sub_eq_zero.mpr hi.symm

theorem complexResolventMatrix_eq_algebraMap_sub [DecidableEq Node]
    (A : NodeMatrix Node) (z : ℂ) :
    complexResolventMatrix (Node := Node) A z =
      algebraMap ℂ (ComplexNodeMatrix Node) z -
        complexOfRealMatrix (Node := Node) A := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [complexResolventMatrix, complexMatrixSub, complexIdentityMatrix,
      complexOfRealMatrix, Matrix.algebraMap_eq_diagonal]
  · simp [complexResolventMatrix, complexMatrixSub, complexIdentityMatrix,
      complexOfRealMatrix, Matrix.algebraMap_eq_diagonal, hij]

theorem complexMatrix_not_isUnit_iff_det_eq_zero [DecidableEq Node]
    (M : ComplexNodeMatrix Node) :
    ¬ IsUnit M ↔ Matrix.det M = 0 := by
  constructor
  · intro hnot
    by_contra hdet
    apply hnot
    exact (Matrix.isUnit_iff_isUnit_det M).2 (isUnit_iff_ne_zero.mpr hdet)
  · intro hdet hunit
    have hdetUnit : IsUnit (Matrix.det M) :=
      (Matrix.isUnit_iff_isUnit_det M).1 hunit
    exact (isUnit_iff_ne_zero.mp hdetUnit) hdet

theorem isComplexRightEigenvalue_iff_mem_spectrum_complexOfRealMatrix
    [DecidableEq Node] (A : NodeMatrix Node) (z : ℂ) :
    IsComplexRightEigenvalue (Node := Node) A z ↔
      z ∈ spectrum ℂ (complexOfRealMatrix (Node := Node) A) := by
  classical
  rw [spectrum.mem_iff]
  rw [complexMatrix_not_isUnit_iff_det_eq_zero (Node := Node)
    (algebraMap ℂ (ComplexNodeMatrix Node) z -
      complexOfRealMatrix (Node := Node) A)]
  rw [← complexResolventMatrix_eq_algebraMap_sub (Node := Node) A z]
  rw [← Matrix.exists_mulVec_eq_zero_iff
    (M := complexResolventMatrix (Node := Node) A z)]
  constructor
  · intro hz
    obtain ⟨v, hvne, hv⟩ := hz
    refine ⟨v, hvne, ?_⟩
    simpa [complexNodeMatrixMulVector] using
      (complexResolventMatrix_mulVec_eq_zero_iff_eigen
        (Node := Node) A z v).2 hv
  · rintro ⟨v, hvne, hv⟩
    refine ⟨v, hvne, ?_⟩
    exact (complexResolventMatrix_mulVec_eq_zero_iff_eigen
      (Node := Node) A z v).1 (by
        simpa [complexNodeMatrixMulVector] using hv)

theorem stableRemainderResolventDisk_iff_mathlib_spectrum
    [DecidableEq Node] (F : ℝ → NodeMatrix Node)
    (alpha0 theta : ℝ) :
    StableRemainderResolventDisk (Node := Node) F alpha0 theta ↔
      ∀ alpha : ℝ, |alpha| ≤ alpha0 →
        (∀ z : ℂ,
          z ∈ spectrum ℂ (complexOfRealMatrix (Node := Node) (F alpha)) →
            ‖z‖ < theta) ∧
          ∀ z : ℂ, ‖z‖ = theta →
            z ∉ spectrum ℂ (complexOfRealMatrix (Node := Node) (F alpha)) := by
  classical
  constructor
  · intro h alpha halpha
    constructor
    · intro z hz
      exact (h alpha halpha).1 z
        ((isComplexRightEigenvalue_iff_mem_spectrum_complexOfRealMatrix
          (Node := Node) (F alpha) z).2 hz)
    · intro z hz hspec
      exact (h alpha halpha).2 z hz
        ((isComplexRightEigenvalue_iff_mem_spectrum_complexOfRealMatrix
          (Node := Node) (F alpha) z).2 hspec)
  · intro h alpha halpha
    constructor
    · intro z hz
      exact (h alpha halpha).1 z
        ((isComplexRightEigenvalue_iff_mem_spectrum_complexOfRealMatrix
          (Node := Node) (F alpha) z).1 hz)
    · intro z hz heig
      exact (h alpha halpha).2 z hz
        ((isComplexRightEigenvalue_iff_mem_spectrum_complexOfRealMatrix
          (Node := Node) (F alpha) z).1 heig)

/-- The real-to-complex scalar extension of a finite node matrix is continuous.

This is the entrywise continuity bridge needed before invoking finite-dimensional
spectral upper-semicontinuity for the complex scalar extension. -/
theorem complexOfRealMatrix_continuous :
    Continuous
      (fun A : NodeMatrix Node =>
        complexOfRealMatrix (Node := Node) A) := by
  classical
  change Continuous
    (fun A : NodeMatrix Node => fun i : Node => fun j : Node => (A i j : ℂ))
  fun_prop

/-- Analytic real matrix families induce continuous complex scalar extensions at
the base point. -/
theorem complexOfRealMatrix_family_continuousAt_zero_of_analytic
    (F : ℝ → NodeMatrix Node) (alphaAnalytic : ℝ)
    (hFanalytic :
      ∀ alpha : ℝ, |alpha| < alphaAnalytic → AnalyticAt ℝ F alpha)
    (halphaAnalytic_pos : 0 < alphaAnalytic) :
    ContinuousAt
      (fun alpha : ℝ =>
        complexOfRealMatrix (Node := Node) (F alpha)) 0 := by
  classical
  have hF0 : AnalyticAt ℝ F 0 := by
    exact hFanalytic 0 (by simpa using halphaAnalytic_pos)
  exact (complexOfRealMatrix_continuous (Node := Node)).continuousAt.comp
    hF0.continuousAt

/-- A point outside the spectrum has nonzero determinant for the native
Mathlib resolvent matrix `z • 1 - A`. -/
theorem complexNodeMatrix_det_ne_zero_of_not_mem_spectrum
    [DecidableEq Node] (A : ComplexNodeMatrix Node) (z : ℂ)
    (hnot : z ∉ spectrum ℂ A) :
    Matrix.det (algebraMap ℂ (ComplexNodeMatrix Node) z - A) ≠ 0 := by
  intro hdet
  apply hnot
  have hnotUnit :
      ¬ IsUnit (algebraMap ℂ (ComplexNodeMatrix Node) z - A) := by
    exact (complexMatrix_not_isUnit_iff_det_eq_zero
      (Node := Node)
      (M := algebraMap ℂ (ComplexNodeMatrix Node) z - A)).2 hdet
  simpa [spectrum.mem_iff] using hnotUnit

/-- Compact-annulus determinant persistence near the base matrix.

If the base matrix has no spectrum on a closed annulus, then continuity of the
matrix family keeps the determinant of `z • 1 - G alpha` nonzero uniformly for
all `z` in that annulus after shrinking `alpha` around zero. -/
theorem complex_det_no_zero_on_compact_annulus_near_base
    [DecidableEq Node]
    (G : ℝ → ComplexNodeMatrix Node) (theta R : ℝ)
    (hG : ContinuousAt G 0)
    (hbaseNo :
      ∀ z : ℂ, theta ≤ ‖z‖ → ‖z‖ ≤ R → z ∉ spectrum ℂ (G 0)) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ alpha : ℝ, |alpha| < eps →
        ∀ z : ℂ, theta ≤ ‖z‖ → ‖z‖ ≤ R →
          z ∉ spectrum ℂ (G alpha) := by
  classical
  let K : Set ℂ := {z : ℂ | theta ≤ ‖z‖ ∧ ‖z‖ ≤ R}
  have hKcompact : IsCompact K := by
    have hKclosed : IsClosed K := by
      exact (isClosed_Ici.preimage continuous_norm).inter
        (isClosed_Iic.preimage continuous_norm)
    have hKsubset : K ⊆ Metric.closedBall (0 : ℂ) R := by
      intro z hz
      simpa [K, Metric.mem_closedBall, dist_eq_norm] using hz.2
    exact (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset hKclosed hKsubset
  let H : ℝ × ℂ → ℂ := fun p =>
    Matrix.det (algebraMap ℂ (ComplexNodeMatrix Node) p.2 - G p.1)
  let n : Set (ℝ × ℂ) := interior (H ⁻¹' {w : ℂ | w ≠ 0})
  have hn_open : IsOpen n := isOpen_interior
  have hprod_subset : ({0} : Set ℝ) ×ˢ K ⊆ n := by
    rintro ⟨alpha, z⟩ ⟨halpha, hzK⟩
    simp only [Set.mem_singleton_iff] at halpha
    subst alpha
    have hdet0 : H (0, z) ≠ 0 := by
      exact complexNodeMatrix_det_ne_zero_of_not_mem_spectrum
        (Node := Node) (A := G 0) (z := z)
        (hbaseNo z hzK.1 hzK.2)
    have hHcont : ContinuousAt H (0, z) := by
      have hleft :
          ContinuousAt
            (fun p : ℝ × ℂ =>
              algebraMap ℂ (ComplexNodeMatrix Node) p.2) (0, z) := by
        change ContinuousAt
          (fun p : ℝ × ℂ => fun i : Node => fun j : Node =>
            (algebraMap ℂ (ComplexNodeMatrix Node) p.2) i j) (0, z)
        fun_prop
      have hright : ContinuousAt (fun p : ℝ × ℂ => G p.1) (0, z) := by
        have hfst : ContinuousAt (fun p : ℝ × ℂ => p.1) (0, z) :=
          continuous_fst.continuousAt
        simpa only [Function.comp_apply] using
          (ContinuousAt.comp
            (f := fun p : ℝ × ℂ => p.1) (g := G) hG hfst)
      have hmat :
          ContinuousAt
            (fun p : ℝ × ℂ =>
              algebraMap ℂ (ComplexNodeMatrix Node) p.2 - G p.1) (0, z) :=
        hleft.sub hright
      exact (Continuous.matrix_det (A := fun M : ComplexNodeMatrix Node => M)
        continuous_id).continuousAt.comp hmat
    exact mem_interior_iff_mem_nhds.mpr
      (hHcont (isOpen_ne.mem_nhds hdet0))
  obtain ⟨u, v, hu_open, _hv_open, h0u, hKv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton hKcompact hn_open hprod_subset
  have h0_mem_u : (0 : ℝ) ∈ u := h0u (by simp)
  rcases Metric.mem_nhds_iff.mp (hu_open.mem_nhds h0_mem_u) with
    ⟨eps, heps_pos, heps_sub⟩
  refine ⟨eps, heps_pos, ?_⟩
  intro alpha halpha z htheta hR hspec
  have hzK : z ∈ K := ⟨htheta, hR⟩
  have halpha_u : alpha ∈ u := by
    apply heps_sub
    simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using halpha
  have hz_v : z ∈ v := hKv hzK
  have hdet_ne : H (alpha, z) ≠ 0 :=
    interior_subset (huv ⟨halpha_u, hz_v⟩)
  have hdet_zero : H (alpha, z) = 0 := by
    have hnotUnit :
        ¬ IsUnit (algebraMap ℂ (ComplexNodeMatrix Node) z - G alpha) := by
      simpa [spectrum.mem_iff] using hspec
    exact (complexMatrix_not_isUnit_iff_det_eq_zero
      (Node := Node)
      (M := algebraMap ℂ (ComplexNodeMatrix Node) z - G alpha)).1 hnotUnit
  exact hdet_ne hdet_zero

/-- Finite-dimensional spectral upper-semicontinuity for complex node matrices.

This is the source's Appendix A sentence "by upper semicontinuity of the
spectrum": if every base eigenvalue lies in `‖z‖ ≤ r0`, then a continuous
finite complex matrix perturbation has all eigenvalues in the strictly larger
disk `‖z‖ < theta` after shrinking the parameter interval.

The remaining proof is a Mathlib finite-spectrum/characteristic-polynomial
compactness gap, independent of the paper-specific `NodeMatrix` and Riesz
objects.  A direct search found `Matrix.mem_spectrum_iff_isRoot_charpoly` and
polynomial Cauchy root bounds, but no packaged theorem turning coefficient
continuity into this open spectral enclosure. -/
theorem complexNodeMatrix_spectrum_upperSemicontinuity_norm_lt
    [DecidableEq Node]
    (G : ℝ → ComplexNodeMatrix Node) (r0 theta : ℝ)
    (hG_continuousAt : ContinuousAt G 0)
    (hr0_theta : r0 < theta)
    (hbaseSpectrum : ∀ z : ℂ, z ∈ spectrum ℂ (G 0) → ‖z‖ ≤ r0) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ alpha : ℝ, |alpha| < eps →
        ∀ z : ℂ, z ∈ spectrum ℂ (G alpha) → ‖z‖ < theta := by
  classical
  have hbaseStrict :
      ∀ z : ℂ, z ∈ spectrum ℂ (G 0) → ‖z‖ < theta := by
    intro z hz
    exact lt_of_le_of_lt (hbaseSpectrum z hz) hr0_theta
  have hbaseRoots :
      ∀ z : ℂ, (G 0).charpoly.IsRoot z → ‖z‖ < theta := by
    intro z hz
    exact hbaseStrict z
      ((Matrix.mem_spectrum_iff_isRoot_charpoly (A := G 0) (r := z)).2 hz)
  have hdetContinuousAt_fixed :
      ∀ z : ℂ,
        ContinuousAt
          (fun alpha : ℝ =>
            Matrix.det
              (algebraMap ℂ (ComplexNodeMatrix Node) z - G alpha)) 0 := by
    intro z
    have hmat :
        ContinuousAt
          (fun alpha : ℝ =>
            algebraMap ℂ (ComplexNodeMatrix Node) z - G alpha) 0 :=
      continuousAt_const.sub hG_continuousAt
    exact (Continuous.matrix_det (A := fun M : ComplexNodeMatrix Node => M)
      continuous_id).continuousAt.comp hmat
  have hbound :
      ∃ epsBound R : ℝ, 0 < epsBound ∧ 0 < R ∧
        ∀ alpha : ℝ, |alpha| < epsBound →
          ∀ z : ℂ, z ∈ spectrum ℂ (G alpha) → ‖z‖ ≤ R := by
    have hnormCont : ContinuousAt (fun alpha : ℝ => ‖G alpha‖) 0 := by
      exact continuous_norm.continuousAt.comp hG_continuousAt
    have hEventually : ∀ᶠ alpha : ℝ in 𝓝 0, ‖G alpha‖ < ‖G 0‖ + 1 := by
      have htarget : ‖G 0‖ < ‖G 0‖ + 1 := by
        linarith
      exact hnormCont (Iio_mem_nhds htarget)
    rcases Metric.eventually_nhds_iff.mp hEventually with
      ⟨epsBound, hepsBound_pos, hepsBound⟩
    refine ⟨epsBound, ‖G 0‖ + 1, hepsBound_pos, ?_, ?_⟩
    · have hnonneg : 0 ≤ ‖G 0‖ := norm_nonneg _
      linarith
    · intro alpha halpha z hz
      have hdist : dist alpha 0 < epsBound := by
        simpa [Real.dist_eq, abs_sub_comm] using halpha
      have hGnorm_lt : ‖G alpha‖ < ‖G 0‖ + 1 := hepsBound hdist
      have hz_le : ‖z‖ ≤ ‖G alpha‖ := by
        exact spectrum.norm_le_norm_of_mem hz
      exact le_trans hz_le (le_of_lt hGnorm_lt)
  obtain ⟨epsBound, R, hepsBound, _hRpos, hspecBound⟩ := hbound
  have hbaseNoAnnulus :
      ∀ z : ℂ, theta ≤ ‖z‖ → ‖z‖ ≤ R → z ∉ spectrum ℂ (G 0) := by
    intro z htheta _hR hz
    exact (not_le_of_gt (hbaseStrict z hz)) htheta
  obtain ⟨epsAnnulus, hepsAnnulus, hnoAnnulus⟩ :=
    complex_det_no_zero_on_compact_annulus_near_base
      (Node := Node) (G := G) (theta := theta) (R := R)
      hG_continuousAt hbaseNoAnnulus
  refine ⟨min epsBound epsAnnulus, lt_min hepsBound hepsAnnulus, ?_⟩
  intro alpha halpha z hz
  have halphaBound : |alpha| < epsBound :=
    lt_of_lt_of_le halpha (min_le_left epsBound epsAnnulus)
  have halphaAnnulus : |alpha| < epsAnnulus :=
    lt_of_lt_of_le halpha (min_le_right epsBound epsAnnulus)
  have hzR : ‖z‖ ≤ R := hspecBound alpha halphaBound z hz
  by_contra hnot
  have htheta : theta ≤ ‖z‖ := le_of_not_gt hnot
  exact hnoAnnulus alpha halphaAnnulus z htheta hzR hz

theorem complexResolvent_det_ne_zero_of_not_eigen [DecidableEq Node]
    (A : NodeMatrix Node) (z : ℂ)
    (hnot : ¬ IsComplexRightEigenvalue (Node := Node) A z) :
    Matrix.det (complexResolventMatrix (Node := Node) A z) ≠ 0 := by
  classical
  intro hdet
  obtain ⟨v, hvne, hvker⟩ :=
    (Matrix.exists_mulVec_eq_zero_iff
      (M := complexResolventMatrix (Node := Node) A z)).2 hdet
  apply hnot
  refine ⟨v, hvne, ?_⟩
  exact (complexResolventMatrix_mulVec_eq_zero_iff_eigen
    (Node := Node) A z v).1 (by
      simpa [complexNodeMatrixMulVector] using hvker)

/-- Conversely, a nonsingular concrete resolvent excludes complex right
eigenvectors at the spectral parameter. -/
theorem not_isComplexRightEigenvalue_of_complexResolvent_det_ne_zero
    [DecidableEq Node]
    (A : NodeMatrix Node) (z : ℂ)
    (hdet : Matrix.det (complexResolventMatrix (Node := Node) A z) ≠ 0) :
    ¬ IsComplexRightEigenvalue (Node := Node) A z := by
  classical
  intro heig
  obtain ⟨v, hvne, hv⟩ := heig
  apply hdet
  exact (Matrix.exists_mulVec_eq_zero_iff
    (M := complexResolventMatrix (Node := Node) A z)).1
    ⟨v, hvne, by
      simpa [complexNodeMatrixMulVector] using
        (complexResolventMatrix_mulVec_eq_zero_iff_eigen
          (Node := Node) A z v).2 hv⟩

/-- For fixed `A`, the resolvent matrix is continuous as a function of the
complex spectral parameter. -/
theorem complexResolventMatrix_continuous_z
    (A : NodeMatrix Node) :
    Continuous (fun z : ℂ =>
      complexResolventMatrix (Node := Node) A z) := by
  classical
  change Continuous (fun z : ℂ => fun i : Node => fun j : Node =>
    complexResolventMatrix (Node := Node) A z i j)
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  unfold complexResolventMatrix complexMatrixSub complexOfRealMatrix
  exact (continuous_id.mul continuous_const).sub continuous_const

/-- For fixed `A`, the determinant of the resolvent matrix is continuous in the
complex spectral parameter. -/
theorem complexResolventDet_continuous_z [DecidableEq Node]
    (A : NodeMatrix Node) :
    Continuous (fun z : ℂ =>
      Matrix.det (complexResolventMatrix (Node := Node) A z)) := by
  exact (Continuous.matrix_det continuous_id).comp
    (complexResolventMatrix_continuous_z (Node := Node) A)

theorem exists_complexResolvent_of_not_eigen
    (A : NodeMatrix Node) (z : ℂ)
    (hnot : ¬ IsComplexRightEigenvalue (Node := Node) A z) :
    ∃ R : ComplexNodeMatrix Node,
      HasComplexResolvent (Node := Node) A z R := by
  classical
  let M : ComplexNodeMatrix Node := complexResolventMatrix (Node := Node) A z
  have hdet : Matrix.det M ≠ 0 := by
    simpa [M] using
      complexResolvent_det_ne_zero_of_not_eigen (Node := Node) A z hnot
  have hunit : IsUnit (Matrix.det M) := isUnit_iff_ne_zero.mpr hdet
  refine ⟨M⁻¹, ?_, ?_⟩
  · calc
      complexMatrixMul (Node := Node) M M⁻¹ =
          (1 : Matrix Node Node ℂ) := by
            simpa [complexMatrixMul] using Matrix.mul_nonsing_inv M hunit
      _ = complexIdentityMatrix (Node := Node) := by
            exact (complexIdentityMatrix_eq_one (Node := Node)).symm
  · calc
      complexMatrixMul (Node := Node) M⁻¹ M =
          (1 : Matrix Node Node ℂ) := by
            simpa [complexMatrixMul] using Matrix.nonsing_inv_mul M hunit
      _ = complexIdentityMatrix (Node := Node) := by
            exact (complexIdentityMatrix_eq_one (Node := Node)).symm

/-- The canonical nonsingular inverse of `zI-A` realizes the resolvent whenever
`z` is outside the complex point spectrum.  This is the inverse branch used for
the compact-continuity argument, avoiding an arbitrary existential choice. -/
theorem complexResolvent_nonsing_inv_spec_of_not_eigen [DecidableEq Node]
    (A : NodeMatrix Node) (z : ℂ)
    (hnot : ¬ IsComplexRightEigenvalue (Node := Node) A z) :
    HasComplexResolvent (Node := Node) A z
      ((complexResolventMatrix (Node := Node) A z)⁻¹) := by
  classical
  let M : ComplexNodeMatrix Node := complexResolventMatrix (Node := Node) A z
  have hdet : Matrix.det M ≠ 0 := by
    simpa [M] using
      complexResolvent_det_ne_zero_of_not_eigen (Node := Node) A z hnot
  have hunit : IsUnit (Matrix.det M) := isUnit_iff_ne_zero.mpr hdet
  refine ⟨?_, ?_⟩
  · calc
      complexMatrixMul (Node := Node) M M⁻¹ =
          (1 : Matrix Node Node ℂ) := by
            simpa [complexMatrixMul] using Matrix.mul_nonsing_inv M hunit
      _ = complexIdentityMatrix (Node := Node) := by
            exact (complexIdentityMatrix_eq_one (Node := Node)).symm
  · calc
      complexMatrixMul (Node := Node) M⁻¹ M =
          (1 : Matrix Node Node ℂ) := by
            simpa [complexMatrixMul] using Matrix.nonsing_inv_mul M hunit
      _ = complexIdentityMatrix (Node := Node) := by
            exact (complexIdentityMatrix_eq_one (Node := Node)).symm

theorem complexResolvent_inv_commutes_complexOfRealMatrix
    [DecidableEq Node]
    (A : NodeMatrix Node) (z : ℂ)
    (hnot : ¬ IsComplexRightEigenvalue (Node := Node) A z) :
    complexOfRealMatrix (Node := Node) A *
        (complexResolventMatrix (Node := Node) A z)⁻¹ =
      (complexResolventMatrix (Node := Node) A z)⁻¹ *
        complexOfRealMatrix (Node := Node) A := by
  classical
  let Ac : ComplexNodeMatrix Node := complexOfRealMatrix (Node := Node) A
  let M : ComplexNodeMatrix Node := complexResolventMatrix (Node := Node) A z
  have hdet : Matrix.det M ≠ 0 := by
    simpa [M] using
      complexResolvent_det_ne_zero_of_not_eigen (Node := Node) A z hnot
  have hunit : IsUnit (Matrix.det M) := isUnit_iff_ne_zero.mpr hdet
  have hM_def :
      M =
        algebraMap ℂ (ComplexNodeMatrix Node) z - Ac := by
    simpa [M, Ac] using
      complexResolventMatrix_eq_algebraMap_sub (Node := Node) A z
  have hscalar_comm :
      algebraMap ℂ (ComplexNodeMatrix Node) z * Ac =
        Ac * algebraMap ℂ (ComplexNodeMatrix Node) z := by
    ext i j
    simp [Ac, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_mul,
      Matrix.mul_diagonal, mul_comm]
  have hcomm : M * Ac = Ac * M := by
    calc
      M * Ac =
          (algebraMap ℂ (ComplexNodeMatrix Node) z - Ac) * Ac := by
            rw [hM_def]
      _ = algebraMap ℂ (ComplexNodeMatrix Node) z * Ac - Ac * Ac := by
            rw [sub_mul]
      _ = Ac * algebraMap ℂ (ComplexNodeMatrix Node) z - Ac * Ac := by
            rw [hscalar_comm]
      _ = Ac * (algebraMap ℂ (ComplexNodeMatrix Node) z - Ac) := by
            rw [mul_sub]
      _ = Ac * M := by
            rw [hM_def]
  calc
    Ac * M⁻¹ = (M⁻¹ * M) * (Ac * M⁻¹) := by
        rw [Matrix.nonsing_inv_mul M hunit]
        simp
    _ = M⁻¹ * ((M * Ac) * M⁻¹) := by
        rw [Matrix.mul_assoc M⁻¹ M (Ac * M⁻¹)]
        rw [← Matrix.mul_assoc M Ac M⁻¹]
    _ = M⁻¹ * ((Ac * M) * M⁻¹) := by
        rw [hcomm]
    _ = M⁻¹ * (Ac * (M * M⁻¹)) := by
        rw [Matrix.mul_assoc]
    _ = M⁻¹ * Ac := by
        rw [Matrix.mul_nonsing_inv M hunit]
        simp

/-- For fixed spectral parameter `z`, each concrete resolvent-matrix entry
depends analytically on the real matrix parameter. -/
theorem complexResolventMatrix_entry_analyticAt_alpha
    (A : ℝ → NodeMatrix Node) (z : ℂ) {alpha : ℝ}
    (hA : AnalyticAt ℝ A alpha) (i j : Node) :
    AnalyticAt ℝ
      (fun a : ℝ => complexResolventMatrix (Node := Node) (A a) z i j)
      alpha := by
  classical
  unfold complexResolventMatrix complexMatrixSub complexOfRealMatrix
  simp only [Pi.sub_apply]
  have hAij : AnalyticAt ℝ (fun a : ℝ => A a i j) alpha :=
    analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hA i) j
  have hofReal :
      AnalyticAt ℝ (fun x : ℝ => (x : ℂ)) (A alpha i j) := by
    simpa using
      ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ).analyticAt (A alpha i j))
  have hAij_complex : AnalyticAt ℝ (fun a : ℝ => (A a i j : ℂ)) alpha :=
    AnalyticAt.comp_of_eq' (𝕜 := ℝ)
      (g := fun x : ℝ => (x : ℂ)) (f := fun a : ℝ => A a i j)
      (y := A alpha i j) (x := alpha) hofReal hAij rfl
  exact analyticAt_const.sub hAij_complex

/-- The determinant of a finite complex matrix is analytic in analytic matrix
entries. -/
theorem complexMatrix_det_analyticAt_alpha [DecidableEq Node]
    (M : ℝ → ComplexNodeMatrix Node) {alpha : ℝ}
    (hM : ∀ i j : Node, AnalyticAt ℝ (fun a : ℝ => M a i j) alpha) :
    AnalyticAt ℝ (fun a : ℝ => Matrix.det (M a)) alpha := by
  classical
  simpa [Matrix.det_apply'] using
    Finset.analyticAt_fun_sum
      (Finset.univ : Finset (Equiv.Perm Node)) (fun σ _hσ =>
      analyticAt_const.mul
        (Finset.analyticAt_fun_prod Finset.univ (fun i _hi =>
          hM (σ i) i)))

/-- Each adjugate entry of a finite complex matrix is analytic in analytic
matrix entries. -/
theorem complexMatrix_adjugate_entry_analyticAt_alpha [DecidableEq Node]
    (M : ℝ → ComplexNodeMatrix Node) {alpha : ℝ}
    (hM : ∀ i j : Node, AnalyticAt ℝ (fun a : ℝ => M a i j) alpha)
    (i j : Node) :
    AnalyticAt ℝ (fun a : ℝ => Matrix.adjugate (M a) i j) alpha := by
  classical
  simpa [Matrix.adjugate_apply] using
    (complexMatrix_det_analyticAt_alpha (Node := Node)
      (fun a : ℝ => (M a).updateRow j (Pi.single i (1 : ℂ)))
      (alpha := alpha) (by
        intro r c
        by_cases hr : r = j
        · subst r
          simpa [Matrix.updateRow] using
            (analyticAt_const (𝕜 := ℝ) (E := ℝ) (F := ℂ)
              (v := ((Pi.single i (1 : ℂ) : Node → ℂ) c)) (x := alpha))
        · simpa [Matrix.updateRow, hr] using hM r c))

/-- Each entry of the finite-dimensional complex matrix inverse is analytic,
proved through Mathlib's adjugate-over-determinant inverse formula. -/
theorem complexMatrix_inv_entry_analyticAt_alpha_of_det_ne_zero
    [DecidableEq Node]
    (M : ℝ → ComplexNodeMatrix Node) {alpha : ℝ}
    (hM : ∀ i j : Node, AnalyticAt ℝ (fun a : ℝ => M a i j) alpha)
    (hdet : Matrix.det (M alpha) ≠ 0) (i j : Node) :
    AnalyticAt ℝ (fun a : ℝ => (M a)⁻¹ i j) alpha := by
  classical
  have hdet_analytic :
      AnalyticAt ℝ (fun a : ℝ => Matrix.det (M a)) alpha :=
    complexMatrix_det_analyticAt_alpha (Node := Node) M hM
  have hinv_base :
      AnalyticAt ℝ (fun x : ℂ => x⁻¹) (Matrix.det (M alpha)) :=
    analyticAt_inv hdet
  have hinv_det :
      AnalyticAt ℝ (fun a : ℝ => (Matrix.det (M a))⁻¹) alpha :=
    AnalyticAt.comp_of_eq' (𝕜 := ℝ)
      (g := fun x : ℂ => x⁻¹)
      (f := fun a : ℝ => Matrix.det (M a))
      (y := Matrix.det (M alpha)) (x := alpha)
      hinv_base hdet_analytic rfl
  have hentry :
      AnalyticAt ℝ
        (fun a : ℝ =>
          (Matrix.det (M a))⁻¹ * Matrix.adjugate (M a) i j) alpha :=
    hinv_det.mul
      (complexMatrix_adjugate_entry_analyticAt_alpha (Node := Node) M hM i j)
  simpa [Matrix.inv_def, Pi.smul_apply, smul_eq_mul, Ring.inverse_eq_inv'] using
    hentry

/-- Complex-parameter version of determinant analyticity for finite complex
matrices. -/
theorem complexMatrix_det_analyticAt_z [DecidableEq Node]
    (M : ℂ → ComplexNodeMatrix Node) {z0 : ℂ}
    (hM : ∀ i j : Node, AnalyticAt ℂ (fun z : ℂ => M z i j) z0) :
    AnalyticAt ℂ (fun z : ℂ => Matrix.det (M z)) z0 := by
  classical
  simpa [Matrix.det_apply'] using
    Finset.analyticAt_fun_sum
      (Finset.univ : Finset (Equiv.Perm Node)) (fun σ _hσ =>
      analyticAt_const.mul
        (Finset.analyticAt_fun_prod Finset.univ (fun i _hi =>
          hM (σ i) i)))

theorem complexMatrix_adjugate_entry_analyticAt_z [DecidableEq Node]
    (M : ℂ → ComplexNodeMatrix Node) {z0 : ℂ}
    (hM : ∀ i j : Node, AnalyticAt ℂ (fun z : ℂ => M z i j) z0)
    (i j : Node) :
    AnalyticAt ℂ (fun z : ℂ => Matrix.adjugate (M z) i j) z0 := by
  classical
  simpa [Matrix.adjugate_apply] using
    (complexMatrix_det_analyticAt_z (Node := Node)
      (fun z : ℂ => (M z).updateRow j (Pi.single i (1 : ℂ)))
      (z0 := z0) (by
        intro r c
        by_cases hr : r = j
        · subst r
          simpa [Matrix.updateRow] using
            (analyticAt_const (𝕜 := ℂ) (E := ℂ) (F := ℂ)
              (v := ((Pi.single i (1 : ℂ) : Node → ℂ) c)) (x := z0))
        · simpa [Matrix.updateRow, hr] using hM r c))

theorem complexMatrix_inv_entry_analyticAt_z_of_det_ne_zero
    [DecidableEq Node]
    (M : ℂ → ComplexNodeMatrix Node) {z0 : ℂ}
    (hM : ∀ i j : Node, AnalyticAt ℂ (fun z : ℂ => M z i j) z0)
    (hdet : Matrix.det (M z0) ≠ 0) (i j : Node) :
    AnalyticAt ℂ (fun z : ℂ => (M z)⁻¹ i j) z0 := by
  classical
  have hdet_analytic :
      AnalyticAt ℂ (fun z : ℂ => Matrix.det (M z)) z0 :=
    complexMatrix_det_analyticAt_z (Node := Node) M hM
  have hinv_base :
      AnalyticAt ℂ (fun x : ℂ => x⁻¹) (Matrix.det (M z0)) :=
    analyticAt_inv hdet
  have hinv_det :
      AnalyticAt ℂ (fun z : ℂ => (Matrix.det (M z))⁻¹) z0 :=
    AnalyticAt.comp_of_eq' (𝕜 := ℂ)
      (g := fun x : ℂ => x⁻¹)
      (f := fun z : ℂ => Matrix.det (M z))
      (y := Matrix.det (M z0)) (x := z0)
      hinv_base hdet_analytic rfl
  have hentry :
      AnalyticAt ℂ
        (fun z : ℂ =>
          (Matrix.det (M z))⁻¹ * Matrix.adjugate (M z) i j) z0 :=
    hinv_det.mul
      (complexMatrix_adjugate_entry_analyticAt_z (Node := Node) M hM i j)
  simpa [Matrix.inv_def, Pi.smul_apply, smul_eq_mul, Ring.inverse_eq_inv'] using
    hentry

theorem complexResolventMatrix_entry_analyticAt_z
    (A0 : NodeMatrix Node) {z0 : ℂ} (i j : Node) :
    AnalyticAt ℂ
      (fun z : ℂ => complexResolventMatrix (Node := Node) A0 z i j) z0 := by
  classical
  have hlinear :
      AnalyticAt ℂ
        (fun z : ℂ =>
          z * complexIdentityMatrix (Node := Node) i j - (A0 i j : ℂ)) z0 :=
    (analyticAt_id.mul analyticAt_const).sub analyticAt_const
  simpa [complexResolventMatrix, complexMatrixSub, complexOfRealMatrix] using
    hlinear

theorem complex_resolvent_inv_entry_differentiableAt_z_of_det_ne_zero
    [DecidableEq Node]
    (A0 : NodeMatrix Node) {z0 : ℂ}
    (hdet : Matrix.det (complexResolventMatrix (Node := Node) A0 z0) ≠ 0)
    (i j : Node) :
    DifferentiableAt ℂ
      (fun z : ℂ => (complexResolventMatrix (Node := Node) A0 z)⁻¹ i j) z0 := by
  classical
  exact (complexMatrix_inv_entry_analyticAt_z_of_det_ne_zero
    (Node := Node) (fun z : ℂ => complexResolventMatrix (Node := Node) A0 z)
    (z0 := z0)
    (by
      intro r c
      exact complexResolventMatrix_entry_analyticAt_z
        (Node := Node) A0 (z0 := z0) r c)
    hdet i j).differentiableAt

/-- For fixed `z` outside the point spectrum at `alpha`, each canonical
inverse-resolvent entry depends analytically on the real parameter. -/
theorem complexResolventInverse_entry_analyticAt_alpha_of_not_eigen
    [DecidableEq Node]
    (A : ℝ → NodeMatrix Node) {alpha : ℝ} (z : ℂ)
    (hA : AnalyticAt ℝ A alpha)
    (hnot :
      ¬ IsComplexRightEigenvalue (Node := Node) (A alpha) z) (i j : Node) :
    AnalyticAt ℝ
      (fun a : ℝ =>
      (complexResolventMatrix (Node := Node) (A a) z)⁻¹ i j)
      alpha := by
  classical
  exact complexMatrix_inv_entry_analyticAt_alpha_of_det_ne_zero (Node := Node)
    (fun a : ℝ => complexResolventMatrix (Node := Node) (A a) z)
    (alpha := alpha)
    (by
      intro p q
      exact complexResolventMatrix_entry_analyticAt_alpha (Node := Node)
        A z hA p q)
    (complexResolvent_det_ne_zero_of_not_eigen (Node := Node)
      (A alpha) z hnot) i j

/-- Complex matrix action as a continuous linear map on the finite coordinate
space. -/
noncomputable def complexMatrixContinuousLinearMap
    (A : ComplexNodeMatrix Node) :
    ComplexRowVector Node →L[ℂ] ComplexRowVector Node :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)

/-- Operator norm for complex node matrices, using Mathlib's continuous
linear-map norm for the finite complex scalar extension. -/
noncomputable def complexMatrixOperatorNorm
    (A : ComplexNodeMatrix Node) : ℝ :=
  ‖complexMatrixContinuousLinearMap (Node := Node) A‖

theorem complexMatrixOperatorNorm_spec (A : ComplexNodeMatrix Node) :
    0 ≤ complexMatrixOperatorNorm (Node := Node) A ∧
      ∀ x : ComplexRowVector Node,
        ‖complexNodeMatrixMulVector (Node := Node) A x‖ ≤
          complexMatrixOperatorNorm (Node := Node) A * ‖x‖ := by
  constructor
  · exact norm_nonneg _
  · intro x
    simpa [complexMatrixOperatorNorm, complexMatrixContinuousLinearMap,
      complexNodeMatrixMulVector] using
      (ContinuousLinearMap.le_opNorm
        (complexMatrixContinuousLinearMap (Node := Node) A) x)

/-- The canonical complex operator norm is submultiplicative for the concrete
matrix product used in the resolvent identities. -/
theorem complexMatrixOperatorNorm_mul
    (A B : ComplexNodeMatrix Node) :
    complexMatrixOperatorNorm (Node := Node)
      (complexMatrixMul (Node := Node) A B) ≤
      complexMatrixOperatorNorm (Node := Node) A *
        complexMatrixOperatorNorm (Node := Node) B := by
  classical
  have hmap :
      complexMatrixContinuousLinearMap (Node := Node)
          (complexMatrixMul (Node := Node) A B) =
        (complexMatrixContinuousLinearMap (Node := Node) A).comp
          (complexMatrixContinuousLinearMap (Node := Node) B) := by
    ext v i
    simp [complexMatrixContinuousLinearMap, complexMatrixMul,
      Matrix.mulVec_mulVec]
  simpa [complexMatrixOperatorNorm, hmap] using
    (ContinuousLinearMap.opNorm_comp_le
      (complexMatrixContinuousLinearMap (Node := Node) A)
      (complexMatrixContinuousLinearMap (Node := Node) B))

/-- Submultiplicativity in Mathlib's native matrix product notation. -/
theorem complexMatrixOperatorNorm_matrix_mul
    (A B : ComplexNodeMatrix Node) :
    complexMatrixOperatorNorm (Node := Node) (A * B) ≤
      complexMatrixOperatorNorm (Node := Node) A *
        complexMatrixOperatorNorm (Node := Node) B := by
  simpa [complexMatrixMul] using
    complexMatrixOperatorNorm_mul (Node := Node) A B

/-- Geometric operator-norm control for powers of a complex node matrix. -/
theorem complexMatrixOperatorNorm_pow_le
    [DecidableEq Node]
    (A : ComplexNodeMatrix Node) :
    ∀ n : ℕ,
      complexMatrixOperatorNorm (Node := Node) (A ^ n) ≤
        complexMatrixOperatorNorm (Node := Node) A ^ n
    := by
  intro n
  induction n with
  | zero =>
      have hmap :
          complexMatrixContinuousLinearMap (Node := Node)
              (1 : ComplexNodeMatrix Node) =
            ContinuousLinearMap.id ℂ (ComplexRowVector Node) := by
        ext v i
        simp [complexMatrixContinuousLinearMap]
      simpa [complexMatrixOperatorNorm, hmap] using
        (ContinuousLinearMap.norm_id_le
          (𝕜 := ℂ) (E := ComplexRowVector Node))
  | succ n ih =>
      calc
        complexMatrixOperatorNorm (Node := Node) (A ^ (n + 1)) =
            complexMatrixOperatorNorm (Node := Node) (A ^ n * A) := by
              rw [pow_succ]
        _ ≤ complexMatrixOperatorNorm (Node := Node) (A ^ n) *
              complexMatrixOperatorNorm (Node := Node) A :=
              complexMatrixOperatorNorm_matrix_mul (Node := Node) (A ^ n) A
        _ ≤ complexMatrixOperatorNorm (Node := Node) A ^ n *
              complexMatrixOperatorNorm (Node := Node) A := by
              exact mul_le_mul_of_nonneg_right ih
                (complexMatrixOperatorNorm_spec (Node := Node) A).1
        _ = complexMatrixOperatorNorm (Node := Node) A ^ (n + 1) := by
              rw [pow_succ]

/-- Every matrix entry is bounded by the canonical complex operator norm. -/
theorem complexMatrix_entry_norm_le_operatorNorm
    (R : ComplexNodeMatrix Node) (i j : Node) :
    ‖R i j‖ ≤ complexMatrixOperatorNorm (Node := Node) R := by
  classical
  have haction :=
    (complexMatrixOperatorNorm_spec (Node := Node) R).2
      ((Pi.single j (1 : ℂ) : ComplexRowVector Node))
  have hsingle : ‖(Pi.single j (1 : ℂ) : ComplexRowVector Node)‖ = 1 := by
    simpa using
      (Pi.norm_single (G := fun _ : Node => ℂ) (i := j) (1 : ℂ))
  have haction_le :
      ‖complexNodeMatrixMulVector (Node := Node) R
          ((Pi.single j (1 : ℂ) : ComplexRowVector Node))‖ ≤
        complexMatrixOperatorNorm (Node := Node) R := by
    simpa [hsingle] using haction
  have hcoord :
      ‖R i j‖ ≤
        ‖complexNodeMatrixMulVector (Node := Node) R
          ((Pi.single j (1 : ℂ) : ComplexRowVector Node))‖ := by
    have happly :
        complexNodeMatrixMulVector (Node := Node) R
            ((Pi.single j (1 : ℂ) : ComplexRowVector Node)) i = R i j := by
      rw [complexNodeMatrixMulVector_apply]
      calc
        (∑ j_1 : Node,
            R i j_1 *
              ((Pi.single j (1 : ℂ) : ComplexRowVector Node) j_1)) =
            R i j *
              ((Pi.single j (1 : ℂ) : ComplexRowVector Node) j) := by
          refine Finset.sum_eq_single j ?_ ?_
          · intro b _ hb
            rw [Pi.single_eq_of_ne hb, mul_zero]
          · intro hjnot
            simp at hjnot
        _ = R i j := by simp
    simpa [happly] using
      (norm_le_pi_norm
        (complexNodeMatrixMulVector (Node := Node) R
          ((Pi.single j (1 : ℂ) : ComplexRowVector Node))) i)
  exact le_trans hcoord haction_le

/-- Mathlib's native finite-matrix norm is controlled by the canonical
operator norm used for the local Neumann contraction. -/
theorem complexMatrix_norm_le_operatorNorm
    [DecidableEq Node]
    (R : ComplexNodeMatrix Node) :
    ‖R‖ ≤ complexMatrixOperatorNorm (Node := Node) R := by
  classical
  rw [Matrix.linfty_opNorm_eq_opNorm]
  rfl

/-- The map sending a complex matrix to its induced continuous linear operator
on finite node vectors is continuous. -/
theorem complexMatrixContinuousLinearMap_continuous :
    Continuous
      (fun A : ComplexNodeMatrix Node =>
        complexMatrixContinuousLinearMap (Node := Node) A) := by
  classical
  let L : ComplexNodeMatrix Node →ₗ[ℂ]
      (ComplexRowVector Node →L[ℂ] ComplexRowVector Node) :=
    { toFun := fun A => complexMatrixContinuousLinearMap (Node := Node) A
      map_add' := by
        intro A B
        ext x i
        simp [complexMatrixContinuousLinearMap, Matrix.add_mulVec]
      map_smul' := by
        intro c A
        ext x i
        simp [complexMatrixContinuousLinearMap, Matrix.smul_mulVec] }
  change Continuous L
  exact L.continuous_of_finiteDimensional

/-- The finite-dimensional algebra equivalence between complex node matrices
and their induced continuous endomorphisms. -/
noncomputable def complexMatrixOperatorAlgEquiv [DecidableEq Node] :
    ComplexNodeMatrix Node ≃ₐ[ℂ]
      (ComplexRowVector Node →L[ℂ] ComplexRowVector Node) :=
  (Matrix.toLinAlgEquiv' :
      ComplexNodeMatrix Node ≃ₐ[ℂ]
        (ComplexRowVector Node →ₗ[ℂ] ComplexRowVector Node)).trans
    (Module.End.toContinuousLinearMap (𝕜 := ℂ) (ComplexRowVector Node))

@[simp]
theorem complexMatrixOperatorAlgEquiv_apply [DecidableEq Node]
    (A : ComplexNodeMatrix Node) :
    complexMatrixOperatorAlgEquiv (Node := Node) A =
      complexMatrixContinuousLinearMap (Node := Node) A := by
  rfl

/-- The matrix action equivalence, viewed as a continuous complex-algebra
representation. -/
noncomputable def complexMatrixOperatorAlgHom [DecidableEq Node] :
    ComplexNodeMatrix Node →A[ℂ]
      (ComplexRowVector Node →L[ℂ] ComplexRowVector Node) where
  toAlgHom := (complexMatrixOperatorAlgEquiv (Node := Node)).toAlgHom
  cont := by
    simpa only [complexMatrixOperatorAlgEquiv_apply] using
      (complexMatrixContinuousLinearMap_continuous (Node := Node))

@[simp]
theorem complexMatrixOperatorAlgHom_apply [DecidableEq Node]
    (A : ComplexNodeMatrix Node) :
    complexMatrixOperatorAlgHom (Node := Node) A =
      complexMatrixContinuousLinearMap (Node := Node) A := by
  rfl

/-- Recover a matrix continuously from its finite-dimensional continuous
endomorphism. -/
noncomputable def complexOperatorMatrixContinuousLinearMap [DecidableEq Node] :
    (ComplexRowVector Node →L[ℂ] ComplexRowVector Node) →L[ℂ]
      ComplexNodeMatrix Node :=
  LinearMap.toContinuousLinearMap
    (complexMatrixOperatorAlgEquiv (Node := Node)).symm.toLinearMap

@[simp]
theorem complexOperatorMatrixContinuousLinearMap_apply_matrix
    [DecidableEq Node] (A : ComplexNodeMatrix Node) :
    complexOperatorMatrixContinuousLinearMap (Node := Node)
        (complexMatrixOperatorAlgHom (Node := Node) A) = A := by
  exact (complexMatrixOperatorAlgEquiv (Node := Node)).symm_apply_apply A

/-- The matrix/operator algebra equivalence preserves the total ring inverse. -/
theorem complexMatrixOperatorAlgEquiv_map_ringInverse [DecidableEq Node]
    (A : ComplexNodeMatrix Node) :
    complexMatrixOperatorAlgEquiv (Node := Node) (Ring.inverse A) =
      Ring.inverse (complexMatrixOperatorAlgEquiv (Node := Node) A) := by
  let e := complexMatrixOperatorAlgEquiv (Node := Node)
  change e (Ring.inverse A) = Ring.inverse (e A)
  by_cases hA : IsUnit A
  · have heA : IsUnit (e A) := hA.map e.toRingEquiv.toRingHom
    have hright : e (Ring.inverse A) * e A = 1 := by
      rw [← map_mul, Ring.inverse_mul_cancel A hA, map_one]
    have h :=
      (Ring.eq_mul_inverse_iff_mul_eq
        (e (Ring.inverse A)) 1 (e A) heA).2 hright
    simpa using h
  · have heA : ¬ IsUnit (e A) := by
      intro h
      have h' : IsUnit (e.symm (e A)) :=
        h.map e.symm.toRingEquiv.toRingHom
      exact hA (by simpa using h')
    rw [Ring.inverse_non_unit A hA, Ring.inverse_non_unit (e A) heA, map_zero]

/-- Continuity of the canonical complex operator norm used for Appendix A's
resolvent bound. -/
theorem complexMatrixOperatorNorm_continuous :
    Continuous
      (fun A : ComplexNodeMatrix Node =>
        complexMatrixOperatorNorm (Node := Node) A) := by
  simpa [complexMatrixOperatorNorm] using
    (continuous_norm.comp
      (complexMatrixContinuousLinearMap_continuous (Node := Node)))

/-- Uniform boundedness of the complex resolvent on the source contour
`|z| = theta`, for all admissible parameters. -/
def UniformComplexResolventBoundOnCircle
    (F : ℝ → NodeMatrix Node) (alpha0 theta M : ℝ) : Prop :=
  ∀ alpha : ℝ, |alpha| ≤ alpha0 →
    ∀ z : ℂ, ‖z‖ = theta →
      ∃ R : ComplexNodeMatrix Node,
        HasComplexResolvent (Node := Node) (F alpha) z R ∧
          complexMatrixOperatorNorm (Node := Node) R ≤ M

/-- If a matrix family is analytic on a radius strictly larger than a closed
interval, then it is continuous on that closed interval.  Appendix A uses this
strict-margin form when it shrinks the parameter interval before applying
compactness to the resolvent. -/
theorem analytic_matrixFamily_continuousOn_Icc_of_lt
    (F : ℝ → NodeMatrix Node) (alpha0 alphaAnalytic : ℝ)
    (hFanalytic :
      ∀ alpha : ℝ, |alpha| < alphaAnalytic → AnalyticAt ℝ F alpha)
    (hmargin : alpha0 < alphaAnalytic) :
    ContinuousOn F (Set.Icc (-alpha0) alpha0) := by
  intro alpha halpha
  have habs : |alpha| ≤ alpha0 := abs_le.mpr halpha
  exact (hFanalytic alpha (lt_of_le_of_lt habs hmargin)).continuousAt.continuousWithinAt

/-- Continuity of the concrete resolvent matrix `zI-F(alpha)` on a compact
parameter-contour product. -/
theorem complexResolventMatrix_continuousOn_contour
    (F : ℝ → NodeMatrix Node) (alpha0 theta : ℝ)
    (hFcontinuousOn : ContinuousOn F (Set.Icc (-alpha0) alpha0)) :
    ContinuousOn
      (fun p : ℝ × ℂ =>
        complexResolventMatrix (Node := Node) (F p.1) p.2)
      (Set.Icc (-alpha0) alpha0 ×ˢ Metric.sphere (0 : ℂ) theta) := by
  classical
  change ContinuousOn
      (fun p : ℝ × ℂ => fun i : Node => fun j : Node =>
        complexResolventMatrix (Node := Node) (F p.1) p.2 i j)
      (Set.Icc (-alpha0) alpha0 ×ˢ Metric.sphere (0 : ℂ) theta)
  rw [continuousOn_pi]
  intro i
  rw [continuousOn_pi]
  intro j
  intro p hp
  unfold complexResolventMatrix complexMatrixSub complexOfRealMatrix
  simp only [Pi.sub_apply]
  have hFij : ContinuousWithinAt
      (fun q : ℝ × ℂ => (F q.1 i j : ℂ))
      (Set.Icc (-alpha0) alpha0 ×ˢ Metric.sphere (0 : ℂ) theta) p := by
    have hF_at : ContinuousWithinAt F (Set.Icc (-alpha0) alpha0) p.1 :=
      hFcontinuousOn p.1 hp.1
    have hFi : ContinuousWithinAt (fun a : ℝ => F a i)
        (Set.Icc (-alpha0) alpha0) p.1 :=
      (continuous_apply i).continuousAt.comp_continuousWithinAt hF_at
    have hFij_real : ContinuousWithinAt (fun a : ℝ => F a i j)
        (Set.Icc (-alpha0) alpha0) p.1 :=
      (continuous_apply j).continuousAt.comp_continuousWithinAt hFi
    exact Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt
      (hFij_real.comp continuousWithinAt_fst fun q hq => hq.1)
  have hz : ContinuousWithinAt
      (fun q : ℝ × ℂ => q.2 * complexIdentityMatrix (Node := Node) i j)
      (Set.Icc (-alpha0) alpha0 ×ˢ Metric.sphere (0 : ℂ) theta) p :=
    continuousWithinAt_snd.mul continuousWithinAt_const
  exact hz.sub hFij

/-- The concrete resolvent matrix is nonsingular at every point of the
parameter-contour product when the contour contains no point spectrum. -/
theorem complexResolventMatrix_det_ne_zero_on_contour [DecidableEq Node]
    (F : ℝ → NodeMatrix Node) (alpha0 theta : ℝ)
    (hcircleNoEigen : ∀ alpha : ℝ, |alpha| ≤ alpha0 →
      ∀ z : ℂ, ‖z‖ = theta →
        ¬ IsComplexRightEigenvalue (Node := Node) (F alpha) z) :
    ∀ p : ℝ × ℂ,
      p ∈ Set.Icc (-alpha0) alpha0 ×ˢ Metric.sphere (0 : ℂ) theta →
        Matrix.det
          (complexResolventMatrix (Node := Node) (F p.1) p.2) ≠ 0 := by
  classical
  intro p hp
  have halpha : |p.1| ≤ alpha0 := abs_le.mpr hp.1
  have hz : ‖p.2‖ = theta := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hp.2
  exact complexResolvent_det_ne_zero_of_not_eigen (Node := Node)
    (F p.1) p.2 (hcircleNoEigen p.1 halpha p.2 hz)

/-- Continuity of the canonical nonsingular inverse of the resolvent on the
source contour. -/
theorem complexResolventInverse_continuousOn_contour [DecidableEq Node]
    (F : ℝ → NodeMatrix Node) (alpha0 theta : ℝ)
    (hFcontinuousOn : ContinuousOn F (Set.Icc (-alpha0) alpha0))
    (hcircleNoEigen : ∀ alpha : ℝ, |alpha| ≤ alpha0 →
      ∀ z : ℂ, ‖z‖ = theta →
        ¬ IsComplexRightEigenvalue (Node := Node) (F alpha) z) :
    ContinuousOn
      (fun p : ℝ × ℂ =>
        (complexResolventMatrix (Node := Node) (F p.1) p.2)⁻¹)
      (Set.Icc (-alpha0) alpha0 ×ˢ Metric.sphere (0 : ℂ) theta) := by
  classical
  intro p hp
  have hresCont : ContinuousWithinAt
      (fun q : ℝ × ℂ =>
        complexResolventMatrix (Node := Node) (F q.1) q.2)
      (Set.Icc (-alpha0) alpha0 ×ˢ Metric.sphere (0 : ℂ) theta) p :=
    complexResolventMatrix_continuousOn_contour (Node := Node)
      F alpha0 theta hFcontinuousOn p hp
  have hdet :
      Matrix.det
        (complexResolventMatrix (Node := Node) (F p.1) p.2) ≠ 0 :=
    complexResolventMatrix_det_ne_zero_on_contour (Node := Node)
      F alpha0 theta hcircleNoEigen p hp
  have hdetInverse :
      ContinuousAt Ring.inverse
        (Matrix.det
          (complexResolventMatrix (Node := Node) (F p.1) p.2)) := by
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hdet
  have hinvAt : ContinuousAt
      (fun M : ComplexNodeMatrix Node => M⁻¹)
      (complexResolventMatrix (Node := Node) (F p.1) p.2) :=
    continuousAt_matrix_inv
      (complexResolventMatrix (Node := Node) (F p.1) p.2)
      hdetInverse
  exact ContinuousAt.comp_continuousWithinAt
    (f := fun q : ℝ × ℂ =>
      complexResolventMatrix (Node := Node) (F q.1) q.2)
    hinvAt hresCont

/-- Continuity of the inverse-resolvent operator norm on the compact contour. -/
theorem complexResolventOperatorNorm_continuousOn_contour [DecidableEq Node]
    (F : ℝ → NodeMatrix Node) (alpha0 theta : ℝ)
    (hFcontinuousOn : ContinuousOn F (Set.Icc (-alpha0) alpha0))
    (hcircleNoEigen : ∀ alpha : ℝ, |alpha| ≤ alpha0 →
      ∀ z : ℂ, ‖z‖ = theta →
        ¬ IsComplexRightEigenvalue (Node := Node) (F alpha) z) :
    ContinuousOn
      (fun p : ℝ × ℂ =>
        complexMatrixOperatorNorm (Node := Node)
          ((complexResolventMatrix (Node := Node) (F p.1) p.2)⁻¹))
      (Set.Icc (-alpha0) alpha0 ×ˢ Metric.sphere (0 : ℂ) theta) := by
  exact complexMatrixOperatorNorm_continuous (Node := Node)
    |>.comp_continuousOn
      (complexResolventInverse_continuousOn_contour (Node := Node)
        F alpha0 theta hFcontinuousOn hcircleNoEigen)

/-- Continuity of the concrete resolvent matrix on a compact shifted contour.

This is the fixed-circle analogue needed for the unit-eigenvalue contour
`‖z - 1‖ = baseRadius` in Appendix A. -/
theorem complexResolventMatrix_continuousOn_shifted_contour
    (F : ℝ → NodeMatrix Node) (alpha0 : ℝ) (center : ℂ) (radius : ℝ)
    (hFcontinuousOn : ContinuousOn F (Set.Icc (-alpha0) alpha0)) :
    ContinuousOn
      (fun p : ℝ × ℂ =>
        complexResolventMatrix (Node := Node) (F p.1) p.2)
      (Set.Icc (-alpha0) alpha0 ×ˢ Metric.sphere center radius) := by
  classical
  change ContinuousOn
      (fun p : ℝ × ℂ => fun i : Node => fun j : Node =>
        complexResolventMatrix (Node := Node) (F p.1) p.2 i j)
      (Set.Icc (-alpha0) alpha0 ×ˢ Metric.sphere center radius)
  rw [continuousOn_pi]
  intro i
  rw [continuousOn_pi]
  intro j
  intro p hp
  unfold complexResolventMatrix complexMatrixSub complexOfRealMatrix
  simp only [Pi.sub_apply]
  have hFij : ContinuousWithinAt
      (fun q : ℝ × ℂ => (F q.1 i j : ℂ))
      (Set.Icc (-alpha0) alpha0 ×ˢ Metric.sphere center radius) p := by
    have hF_at : ContinuousWithinAt F (Set.Icc (-alpha0) alpha0) p.1 :=
      hFcontinuousOn p.1 hp.1
    have hFi : ContinuousWithinAt (fun a : ℝ => F a i)
        (Set.Icc (-alpha0) alpha0) p.1 :=
      (continuous_apply i).continuousAt.comp_continuousWithinAt hF_at
    have hFij_real : ContinuousWithinAt (fun a : ℝ => F a i j)
        (Set.Icc (-alpha0) alpha0) p.1 :=
      (continuous_apply j).continuousAt.comp_continuousWithinAt hFi
    exact Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt
      (hFij_real.comp continuousWithinAt_fst fun q hq => hq.1)
  have hz : ContinuousWithinAt
      (fun q : ℝ × ℂ => q.2 * complexIdentityMatrix (Node := Node) i j)
      (Set.Icc (-alpha0) alpha0 ×ˢ Metric.sphere center radius) p :=
    continuousWithinAt_snd.mul continuousWithinAt_const
  exact hz.sub hFij

/-- Nonvanishing determinant of the resolvent matrix on a shifted contour,
assuming that contour contains no point spectrum. -/
theorem complexResolventMatrix_det_ne_zero_on_shifted_contour
    [DecidableEq Node]
    (F : ℝ → NodeMatrix Node) (alpha0 : ℝ) (center : ℂ) (radius : ℝ)
    (hcircleNoEigen : ∀ alpha : ℝ, |alpha| ≤ alpha0 →
      ∀ z : ℂ, ‖z - center‖ = radius →
        ¬ IsComplexRightEigenvalue (Node := Node) (F alpha) z) :
    ∀ p : ℝ × ℂ,
      p ∈ Set.Icc (-alpha0) alpha0 ×ˢ Metric.sphere center radius →
        Matrix.det
          (complexResolventMatrix (Node := Node) (F p.1) p.2) ≠ 0 := by
  classical
  intro p hp
  have halpha : |p.1| ≤ alpha0 := abs_le.mpr hp.1
  have hz : ‖p.2 - center‖ = radius := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hp.2
  exact complexResolvent_det_ne_zero_of_not_eigen (Node := Node)
    (F p.1) p.2 (hcircleNoEigen p.1 halpha p.2 hz)

/-- Continuity of the determinant of the shifted resolvent matrix on the
parameter-contour product. -/
theorem complexResolventDet_continuousOn_shifted_contour
    [DecidableEq Node]
    (F : ℝ → NodeMatrix Node) (alpha0 : ℝ) (center : ℂ) (radius : ℝ)
    (hFcontinuousOn : ContinuousOn F (Set.Icc (-alpha0) alpha0)) :
    ContinuousOn
      (fun p : ℝ × ℂ =>
        Matrix.det (complexResolventMatrix (Node := Node) (F p.1) p.2))
      (Set.Icc (-alpha0) alpha0 ×ˢ Metric.sphere center radius) := by
  exact (Continuous.matrix_det continuous_id).comp_continuousOn
    (complexResolventMatrix_continuousOn_shifted_contour (Node := Node)
      F alpha0 center radius hFcontinuousOn)

/-- Continuity of the canonical nonsingular inverse of the resolvent on a
shifted contour. -/
theorem complexResolventInverse_continuousOn_shifted_contour
    [DecidableEq Node]
    (F : ℝ → NodeMatrix Node) (alpha0 : ℝ) (center : ℂ) (radius : ℝ)
    (hFcontinuousOn : ContinuousOn F (Set.Icc (-alpha0) alpha0))
    (hcircleNoEigen : ∀ alpha : ℝ, |alpha| ≤ alpha0 →
      ∀ z : ℂ, ‖z - center‖ = radius →
        ¬ IsComplexRightEigenvalue (Node := Node) (F alpha) z) :
    ContinuousOn
      (fun p : ℝ × ℂ =>
        (complexResolventMatrix (Node := Node) (F p.1) p.2)⁻¹)
      (Set.Icc (-alpha0) alpha0 ×ˢ Metric.sphere center radius) := by
  classical
  intro p hp
  have hresCont : ContinuousWithinAt
      (fun q : ℝ × ℂ =>
        complexResolventMatrix (Node := Node) (F q.1) q.2)
      (Set.Icc (-alpha0) alpha0 ×ˢ Metric.sphere center radius) p :=
    complexResolventMatrix_continuousOn_shifted_contour (Node := Node)
      F alpha0 center radius hFcontinuousOn p hp
  have hdet :
      Matrix.det
        (complexResolventMatrix (Node := Node) (F p.1) p.2) ≠ 0 :=
    complexResolventMatrix_det_ne_zero_on_shifted_contour (Node := Node)
      F alpha0 center radius hcircleNoEigen p hp
  have hdetInverse :
      ContinuousAt Ring.inverse
        (Matrix.det
          (complexResolventMatrix (Node := Node) (F p.1) p.2)) := by
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hdet
  have hinvAt : ContinuousAt
      (fun M : ComplexNodeMatrix Node => M⁻¹)
      (complexResolventMatrix (Node := Node) (F p.1) p.2) :=
    continuousAt_matrix_inv
      (complexResolventMatrix (Node := Node) (F p.1) p.2)
      hdetInverse
  exact ContinuousAt.comp_continuousWithinAt
    (f := fun q : ℝ × ℂ =>
      complexResolventMatrix (Node := Node) (F q.1) q.2)
    hinvAt hresCont

/-- Continuity of the inverse-resolvent operator norm on a shifted contour. -/
theorem complexResolventOperatorNorm_continuousOn_shifted_contour
    [DecidableEq Node]
    (F : ℝ → NodeMatrix Node) (alpha0 : ℝ) (center : ℂ) (radius : ℝ)
    (hFcontinuousOn : ContinuousOn F (Set.Icc (-alpha0) alpha0))
    (hcircleNoEigen : ∀ alpha : ℝ, |alpha| ≤ alpha0 →
      ∀ z : ℂ, ‖z - center‖ = radius →
        ¬ IsComplexRightEigenvalue (Node := Node) (F alpha) z) :
    ContinuousOn
      (fun p : ℝ × ℂ =>
        complexMatrixOperatorNorm (Node := Node)
          ((complexResolventMatrix (Node := Node) (F p.1) p.2)⁻¹))
      (Set.Icc (-alpha0) alpha0 ×ˢ Metric.sphere center radius) := by
  exact complexMatrixOperatorNorm_continuous (Node := Node)
    |>.comp_continuousOn
      (complexResolventInverse_continuousOn_shifted_contour (Node := Node)
        F alpha0 center radius hFcontinuousOn hcircleNoEigen)

/-- Uniform boundedness of the complex resolvent on a shifted source contour,
once absence of point spectrum has already been established there. -/
theorem complexResolventNorm_uniform_on_shifted_circle
    [DecidableEq Node]
    (F : ℝ → NodeMatrix Node) (alpha0 alphaAnalytic : ℝ)
    (center : ℂ) (radius : ℝ)
    (hFanalytic :
      ∀ alpha : ℝ, |alpha| < alphaAnalytic → AnalyticAt ℝ F alpha)
    (hmargin : alpha0 < alphaAnalytic)
    (hcircleNoEigen : ∀ alpha : ℝ, |alpha| ≤ alpha0 →
      ∀ z : ℂ, ‖z - center‖ = radius →
        ¬ IsComplexRightEigenvalue (Node := Node) (F alpha) z) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ alpha : ℝ, |alpha| ≤ alpha0 →
        ∀ z : ℂ, ‖z - center‖ = radius →
          ∃ R : ComplexNodeMatrix Node,
            HasComplexResolvent (Node := Node) (F alpha) z R ∧
              complexMatrixOperatorNorm (Node := Node) R ≤ M := by
  classical
  let contourSet : Set (ℝ × ℂ) :=
    Set.Icc (-alpha0) alpha0 ×ˢ Metric.sphere center radius
  let resolventNormOnContour : ℝ × ℂ → ℝ := fun p =>
    complexMatrixOperatorNorm (Node := Node)
      ((complexResolventMatrix (Node := Node) (F p.1) p.2)⁻¹)
  have hcompact : IsCompact contourSet := by
    simpa [contourSet] using
      (isCompact_Icc.prod (isCompact_sphere center radius))
  have hFcontinuousOn : ContinuousOn F (Set.Icc (-alpha0) alpha0) :=
    analytic_matrixFamily_continuousOn_Icc_of_lt (Node := Node)
      F alpha0 alphaAnalytic hFanalytic hmargin
  have hcont : ContinuousOn resolventNormOnContour contourSet := by
    simpa [resolventNormOnContour, contourSet] using
      complexResolventOperatorNorm_continuousOn_shifted_contour (Node := Node)
        F alpha0 center radius hFcontinuousOn hcircleNoEigen
  obtain ⟨M, hM_nonneg, hM_bound⟩ :=
    exists_nonneg_norm_bound_of_isCompact_of_continuousOn
      resolventNormOnContour hcompact hcont
  refine ⟨M, hM_nonneg, ?_⟩
  intro alpha halpha z hz
  let R : ComplexNodeMatrix Node :=
    (complexResolventMatrix (Node := Node) (F alpha) z)⁻¹
  refine ⟨R, ?_, ?_⟩
  · exact complexResolvent_nonsing_inv_spec_of_not_eigen (Node := Node)
      (F alpha) z (hcircleNoEigen alpha halpha z hz)
  · have halphaIcc : alpha ∈ Set.Icc (-alpha0) alpha0 := by
      exact abs_le.mp halpha
    have hzSphere : z ∈ Metric.sphere center radius := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hp : (alpha, z) ∈ contourSet := by
      exact ⟨halphaIcc, hzSphere⟩
    have hbound := hM_bound (alpha, z) hp
    have hle_abs :
        complexMatrixOperatorNorm (Node := Node) R ≤
          ‖complexMatrixOperatorNorm (Node := Node) R‖ :=
      le_abs_self _
    exact le_trans hle_abs (by
      simpa [resolventNormOnContour, R] using hbound)

theorem circleMap_deriv_continuous (center : ℂ) (radius : ℝ) :
    Continuous (fun theta : ℝ => deriv (circleMap center radius) theta) := by
  have hfun :
      (fun theta : ℝ => deriv (circleMap center radius) theta) =
        fun theta : ℝ => circleMap (0 : ℂ) radius theta * Complex.I := by
    funext theta
    exact deriv_circleMap center radius theta
  rw [hfun]
  have hI : Continuous (fun _ : ℝ => (Complex.I : ℂ)) := continuous_const
  exact (continuous_circleMap (0 : ℂ) radius).mul hI

/-- Joint continuity of the scaled fixed-contour interval integrand.

This is the compact-contour continuity layer below the missing
analytic-under-integral step: after shrinking to a parameter interval where
the fixed shifted circle contains no spectrum, the inverse resolvent entry
composed with the circle parametrization is continuous jointly in the real
parameter and contour angle. -/
theorem fixedCircle_scaledResolvent_intervalIntegrand_continuousOn
    [DecidableEq Node]
    (A : ℝ → NodeMatrix Node) (alpha0 alphaAnalytic : ℝ)
    (center : ℂ) (radius : ℝ)
    (hradius_nonneg : 0 ≤ radius)
    (hAanalytic :
      ∀ alpha : ℝ, |alpha| < alphaAnalytic → AnalyticAt ℝ A alpha)
    (hmargin : alpha0 < alphaAnalytic)
    (hcircleNoEigen : ∀ alpha : ℝ, |alpha| ≤ alpha0 →
      ∀ z : ℂ, ‖z - center‖ = radius →
        ¬ IsComplexRightEigenvalue (Node := Node) (A alpha) z)
    (i j : Node) :
    ContinuousOn
      (fun p : ℝ × ℝ =>
        deriv (circleMap center radius) p.2 *
          ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
            (complexResolventMatrix (Node := Node) (A p.1)
              (circleMap center radius p.2))⁻¹ i j))
      (Set.Icc (-alpha0) alpha0 ×ˢ
        Set.Icc (0 : ℝ) (2 * Real.pi)) := by
  classical
  let parameterThetaSet : Set (ℝ × ℝ) :=
    Set.Icc (-alpha0) alpha0 ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)
  let parameterContourSet : Set (ℝ × ℂ) :=
    Set.Icc (-alpha0) alpha0 ×ˢ Metric.sphere center radius
  have hAcontinuousOn : ContinuousOn A (Set.Icc (-alpha0) alpha0) :=
    analytic_matrixFamily_continuousOn_Icc_of_lt (Node := Node)
      A alpha0 alphaAnalytic hAanalytic hmargin
  have hinvContour : ContinuousOn
      (fun p : ℝ × ℂ =>
        (complexResolventMatrix (Node := Node) (A p.1) p.2)⁻¹)
      parameterContourSet := by
    simpa [parameterContourSet] using
      complexResolventInverse_continuousOn_shifted_contour (Node := Node)
        A alpha0 center radius hAcontinuousOn hcircleNoEigen
  have hpathMaps :
      Set.MapsTo
        (fun p : ℝ × ℝ => (p.1, circleMap center radius p.2))
        parameterThetaSet parameterContourSet := by
    intro p hp
    have hcircle :
        circleMap center radius p.2 ∈ Metric.sphere center radius :=
      circleMap_mem_sphere center hradius_nonneg p.2
    exact ⟨hp.1, hcircle⟩
  have hpathContinuous : ContinuousOn
      (fun p : ℝ × ℝ => (p.1, circleMap center radius p.2))
      parameterThetaSet := by
    fun_prop
  have hinvTheta : ContinuousOn
      (fun p : ℝ × ℝ =>
        (complexResolventMatrix (Node := Node) (A p.1)
          (circleMap center radius p.2))⁻¹)
      parameterThetaSet := by
    simpa using hinvContour.comp hpathContinuous hpathMaps
  have hentry : ContinuousOn
      (fun p : ℝ × ℝ =>
        (complexResolventMatrix (Node := Node) (A p.1)
          (circleMap center radius p.2))⁻¹ i j)
      parameterThetaSet :=
    (continuous_apply j).comp_continuousOn
      ((continuous_apply i).comp_continuousOn hinvTheta)
  have hscaled : ContinuousOn
      (fun p : ℝ × ℝ =>
        (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
          (complexResolventMatrix (Node := Node) (A p.1)
            (circleMap center radius p.2))⁻¹ i j)
      parameterThetaSet :=
    continuousOn_const.mul hentry
  have hderivTheta :
      Continuous (fun theta : ℝ => deriv (circleMap center radius) theta) := by
    exact circleMap_deriv_continuous center radius
  have hderiv : ContinuousOn
      (fun p : ℝ × ℝ => deriv (circleMap center radius) p.2)
      parameterThetaSet := by
    fun_prop
  simpa only [parameterThetaSet] using hderiv.mul hscaled

/-- Continuous linear functional obtained by integrating a continuous function
on a compact real interval.  The definition is intentionally stated on the
interval subtype; callers can use `MeasureTheory.integral_subtype` to rewrite
back to an ambient `Set.Icc` integral. -/
noncomputable def continuousMap_Icc_setIntegral_clm (l u : ℝ) :
    ContinuousMap (Set.Icc l u) ℂ →L[ℝ] ℂ := by
  classical
  let K : Type := Set.Icc l u
  let μK : Measure K := Measure.comap (Subtype.val : K → ℝ) volume
  have hμK_univ_lt_top : μK (Set.univ : Set K) < ⊤ := by
    dsimp [μK, K]
    rw [comap_subtype_coe_apply isCompact_Icc.measurableSet]
    simpa using (isCompact_Icc (a := l) (b := u)).measure_lt_top
  let L : ContinuousMap K ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ x in (Set.univ : Set K), f x ∂μK
      map_add' := by
        intro f g
        have hf : Integrable (fun x : K => f x) μK := by
          simpa [IntegrableOn] using
            (f.continuous.continuousOn.integrableOn_of_subset_isCompact
              (μ := μK) (K := Set.univ) isCompact_univ MeasurableSet.univ
              (fun x hx => hx) (ne_of_lt hμK_univ_lt_top))
        have hg : Integrable (fun x : K => g x) μK := by
          simpa [IntegrableOn] using
            (g.continuous.continuousOn.integrableOn_of_subset_isCompact
              (μ := μK) (K := Set.univ) isCompact_univ MeasurableSet.univ
              (fun x hx => hx) (ne_of_lt hμK_univ_lt_top))
        simpa [Pi.add_apply] using
          (MeasureTheory.integral_add
            (μ := μK) (f := fun x : K => f x)
            (g := fun x : K => g x) hf hg)
      map_smul' := by
        intro c f
        simpa [Pi.smul_apply] using
          (MeasureTheory.integral_smul
            (μ := μK) (𝕜 := ℂ) (G := ℂ) c (fun x : K => f x)) }
  let Lc : ContinuousMap K ℂ →L[ℂ] ℂ :=
    LinearMap.mkContinuous L (μK.real (Set.univ : Set K)) (by
    intro f
    change
      ‖∫ x in (Set.univ : Set K), f x ∂μK‖ ≤
        μK.real (Set.univ : Set K) * ‖f‖
    have hbound :
        ‖∫ x in (Set.univ : Set K), f x ∂μK‖ ≤
          ‖f‖ * μK.real (Set.univ : Set K) :=
      MeasureTheory.norm_setIntegral_le_of_norm_le_const
        (μ := μK) (s := (Set.univ : Set K))
        (f := fun x : K => f x) hμK_univ_lt_top
        (fun x _hx => ContinuousMap.norm_coe_le_norm f x)
    simpa only [mul_comm] using hbound)
  exact Lc.restrictScalars ℝ

/-- Applying the interval integration CLM preserves real analyticity. -/
theorem continuousMap_Icc_setIntegral_clm_apply_analyticAt
    (l u alpha : ℝ) (F : ℝ → ContinuousMap (Set.Icc l u) ℂ)
    (hF : AnalyticAt ℝ F alpha) :
    AnalyticAt ℝ
      (fun a : ℝ => continuousMap_Icc_setIntegral_clm l u (F a))
      alpha := by
  exact ((continuousMap_Icc_setIntegral_clm l u).analyticAt (F alpha)).comp' hF

/-- If a locally analytic continuous-map-valued interval integrand agrees
eventually with an ambient integrand, the interval integration CLM gives the
ambient `Set.Icc` integral. -/
theorem continuousMap_Icc_setIntegral_clm_apply_eventually_eq_ambient_integral
    (l u alpha : ℝ) (F : ℝ → ContinuousMap (Set.Icc l u) ℂ)
    (f : ℝ → ℝ → ℂ)
    (hFint :
      AnalyticAt ℝ
        (fun a : ℝ => continuousMap_Icc_setIntegral_clm l u (F a))
        alpha)
    (hF_eq :
      ∀ᶠ a in 𝓝 alpha, ∀ x : Set.Icc l u, F a x = f a x.1) :
    AnalyticAt ℝ (fun a : ℝ => ∫ x in Set.Icc l u, f a x) alpha := by
  refine hFint.congr ?_
  filter_upwards [hF_eq] with a ha
  let K : Type := Set.Icc l u
  let μK : Measure K := Measure.comap (Subtype.val : K → ℝ) volume
  have hsubtype :
      (∫ x in (Set.univ : Set K), F a x ∂μK) =
        ∫ x in Set.Icc l u, f a x := by
    have hpoint :
        (∫ x in (Set.univ : Set K), F a x ∂μK) =
          ∫ x : K, f a x.1 ∂μK := by
      simp [ha, K]
    have hcomap :
        (∫ x : K, f a x.1 ∂μK) =
          ∫ x in Set.Icc l u, f a x := by
      simpa [K, μK] using
      (MeasureTheory.integral_subtype_comap
          (μ := volume) isCompact_Icc.measurableSet (f a))
    exact hpoint.trans hcomap
  simpa [continuousMap_Icc_setIntegral_clm, K, μK] using hsubtype

/-- The base inverse resolvent is continuous as a function of the circle
parameter on the fixed interval. -/
theorem fixed_contour_base_resolventInverse_continuousOn_Icc
    [DecidableEq Node]
    (Aalpha : NodeMatrix Node) (center : ℂ) (radius : ℝ)
    (hradius_nonneg : 0 ≤ radius)
    (hnotEigen :
      ∀ z : ℂ, ‖z - center‖ = radius →
        ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z) :
    ContinuousOn
      (fun theta : ℝ =>
        (complexResolventMatrix (Node := Node) Aalpha
          (circleMap center radius theta))⁻¹)
      (Set.Icc (0 : ℝ) (2 * Real.pi)) := by
  classical
  let F : ℝ → NodeMatrix Node := fun _ => Aalpha
  have hFcont : ContinuousOn F (Set.Icc (-(0 : ℝ)) 0) :=
    continuousOn_const
  have hcircle :
      ∀ beta : ℝ, |beta| ≤ (0 : ℝ) →
        ∀ z : ℂ, ‖z - center‖ = radius →
          ¬ IsComplexRightEigenvalue (Node := Node) (F beta) z := by
    intro beta _ z hz
    exact hnotEigen z hz
  have hinvProd :
      ContinuousOn
        (fun p : ℝ × ℂ =>
          (complexResolventMatrix (Node := Node) (F p.1) p.2)⁻¹)
        (Set.Icc (-(0 : ℝ)) 0 ×ˢ Metric.sphere center radius) :=
    complexResolventInverse_continuousOn_shifted_contour (Node := Node)
      F 0 center radius hFcont hcircle
  have hpath :
      ContinuousOn
        (fun theta : ℝ => ((0 : ℝ), circleMap center radius theta))
        (Set.Icc (0 : ℝ) (2 * Real.pi)) := by
    fun_prop
  have hmaps :
      Set.MapsTo
        (fun theta : ℝ => ((0 : ℝ), circleMap center radius theta))
        (Set.Icc (0 : ℝ) (2 * Real.pi))
        (Set.Icc (-(0 : ℝ)) 0 ×ˢ Metric.sphere center radius) := by
    intro theta _htheta
    constructor
    · simp
    · simpa [Metric.mem_sphere, dist_eq_norm] using
        circleMap_mem_sphere center hradius_nonneg theta
  simpa [F] using hinvProd.comp hpath hmaps

/-- The analytic matrix-family perturbation `A a - A alpha`, coerced to the
complex matrix algebra used by the fixed-contour Neumann expansion. -/
theorem fixed_contour_matrix_delta_analyticAt
    (A : ℝ → NodeMatrix Node) (alpha : ℝ)
    (hAanalytic : AnalyticAt ℝ A alpha) :
    AnalyticAt ℝ
      (fun a : ℝ =>
        complexOfRealMatrix (Node := Node)
      (matrixSub (Node := Node) (A a) (A alpha)))
      alpha := by
  classical
  letI : NormedSpace ℝ
      (ComplexRowVector Node →L[ℂ] ComplexRowVector Node) :=
    NormedSpace.restrictScalars ℝ ℂ _
  letI : IsBoundedSMul ℝ
      (ComplexRowVector Node →L[ℂ] ComplexRowVector Node) :=
    IsBoundedSMul.of_norm_smul_le NormedSpace.norm_smul_le
  letI : ContinuousSMul ℝ
      (ComplexRowVector Node →L[ℂ] ComplexRowVector Node) :=
    IsBoundedSMul.continuousSMul
  letI : NormedSpace ℝ (ComplexNodeMatrix Node) :=
    NormedSpace.restrictScalars ℝ ℂ _
  letI : IsBoundedSMul ℝ (ComplexNodeMatrix Node) :=
    IsBoundedSMul.of_norm_smul_le NormedSpace.norm_smul_le
  letI : ContinuousSMul ℝ (ComplexNodeMatrix Node) :=
    IsBoundedSMul.continuousSMul
  let toOpLin : NodeMatrix Node →ₗ[ℝ]
      (ComplexRowVector Node →L[ℂ] ComplexRowVector Node) :=
    { toFun := fun B =>
        complexMatrixContinuousLinearMap (Node := Node)
          (complexOfRealMatrix (Node := Node) B)
      map_add' := by
        intro B C
        ext x i
        change
          (fun j => ((B + C) i j : ℂ)) ⬝ᵥ x =
            (fun j => (B i j : ℂ)) ⬝ᵥ x +
              (fun j => (C i j : ℂ)) ⬝ᵥ x
        simpa only [Pi.add_apply, Complex.ofReal_add] using
          (add_dotProduct (fun j => (B i j : ℂ))
            (fun j => (C i j : ℂ)) x)
      map_smul' := by
        intro r B
        ext x i
        change
          (fun j => ((r • B) i j : ℂ)) ⬝ᵥ x =
            (r : ℂ) * ((fun j => (B i j : ℂ)) ⬝ᵥ x)
        simpa only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul] using
          (smul_dotProduct (r : ℂ) (fun j => (B i j : ℂ)) x) }
  let toOp : NodeMatrix Node →L[ℝ]
      (ComplexRowVector Node →L[ℂ] ComplexRowVector Node) :=
    LinearMap.toContinuousLinearMap toOpLin
  let fromOp :
      (ComplexRowVector Node →L[ℂ] ComplexRowVector Node) →L[ℝ]
        ComplexNodeMatrix Node :=
    (complexOperatorMatrixContinuousLinearMap (Node := Node)).restrictScalars ℝ
  let C : NodeMatrix Node →L[ℝ] ComplexNodeMatrix Node := fromOp.comp toOp
  have hdelta : AnalyticAt ℝ
      (fun a : ℝ => matrixSub (Node := Node) (A a) (A alpha)) alpha := by
    simpa [matrixSub] using hAanalytic.sub analyticAt_const
  have hmapped : AnalyticAt ℝ
      (fun a : ℝ => C (matrixSub (Node := Node) (A a) (A alpha))) alpha :=
    (C.analyticAt _).comp' hdelta
  have hrecover (B : NodeMatrix Node) :
      C B = complexOfRealMatrix (Node := Node) B := by
    change complexOperatorMatrixContinuousLinearMap (Node := Node)
        (complexMatrixContinuousLinearMap (Node := Node)
          (complexOfRealMatrix (Node := Node) B)) =
      complexOfRealMatrix (Node := Node) B
    rw [← complexMatrixOperatorAlgHom_apply]
    exact complexOperatorMatrixContinuousLinearMap_apply_matrix
      (Node := Node) (complexOfRealMatrix (Node := Node) B)
  simpa only [hrecover] using hmapped

/-- At the base point the complex perturbation matrix vanishes. -/
theorem fixed_contour_matrix_delta_self
    (Aalpha : NodeMatrix Node) :
    complexOfRealMatrix (Node := Node)
      (matrixSub (Node := Node) Aalpha Aalpha) =
      (0 : ComplexNodeMatrix Node) := by
  ext r s
  simp [complexOfRealMatrix, matrixSub]

/-- ContinuousMap-valued analytic perturbation operator for the fixed contour:
`X(a)(theta) = R0(theta) * (A(a)-A(alpha))`.

This isolates the first Banach-valued step of the Appendix A Neumann route
before applying the analytic inverse map. -/
theorem fixed_contour_matrix_delta_to_continuousMap_analyticAt
    [DecidableEq Node]
    (A : ℝ → NodeMatrix Node) (center : ℂ) (radius : ℝ) (alpha : ℝ)
    (hradius_nonneg : 0 ≤ radius)
    (hAanalytic : AnalyticAt ℝ A alpha)
    (hnotEigenAlpha :
      ∀ z : ℂ, ‖z - center‖ = radius →
        ¬ IsComplexRightEigenvalue (Node := Node) (A alpha) z) :
    ∃ X : ℝ →
        ContinuousMap (Set.Icc (0 : ℝ) (2 * Real.pi))
          (ComplexNodeMatrix Node),
      AnalyticAt ℝ X alpha ∧
        (∀ a : ℝ, ∀ theta : Set.Icc (0 : ℝ) (2 * Real.pi),
          X a theta =
            ((complexResolventMatrix (Node := Node) (A alpha)
                (circleMap center radius theta.1))⁻¹) *
              complexOfRealMatrix (Node := Node)
                (matrixSub (Node := Node) (A a) (A alpha))) ∧
        X alpha = 0 := by
  classical
  letI : NormedSpace ℝ (ComplexNodeMatrix Node) :=
    NormedSpace.restrictScalars ℝ ℂ _
  letI : IsBoundedSMul ℝ (ComplexNodeMatrix Node) :=
    IsBoundedSMul.of_norm_smul_le NormedSpace.norm_smul_le
  letI : ContinuousSMul ℝ (ComplexNodeMatrix Node) :=
    IsBoundedSMul.continuousSMul
  let K : Type := Set.Icc (0 : ℝ) (2 * Real.pi)
  let R0 : K → ComplexNodeMatrix Node := fun theta =>
    (complexResolventMatrix (Node := Node) (A alpha)
      (circleMap center radius theta.1))⁻¹
  have hR0cont : Continuous R0 := by
    have hbase :=
      fixed_contour_base_resolventInverse_continuousOn_Icc
        (Node := Node) (A alpha) center radius hradius_nonneg
        hnotEigenAlpha
    simpa [R0, K] using
      (continuousOn_iff_continuous_restrict.mp hbase)
  let L : ComplexNodeMatrix Node →ₗ[ℝ] ContinuousMap K (ComplexNodeMatrix Node) :=
    { toFun := fun D =>
        ⟨fun theta : K => R0 theta * D,
          by
            simpa using hR0cont.mul continuous_const⟩
      map_add' := by
        intro D E
        ext theta r s
        simp [Matrix.mul_add]
      map_smul' := by
        intro c D
        ext theta r s
        simp [Matrix.mul_apply, Finset.mul_sum, mul_assoc, smul_eq_mul] }
  let Lc : ComplexNodeMatrix Node →L[ℝ]
      ContinuousMap K (ComplexNodeMatrix Node) :=
    LinearMap.toContinuousLinearMap L
  let D : ℝ → ComplexNodeMatrix Node := fun a =>
    complexOfRealMatrix (Node := Node)
      (matrixSub (Node := Node) (A a) (A alpha))
  let X : ℝ → ContinuousMap K (ComplexNodeMatrix Node) := fun a => Lc (D a)
  refine ⟨X, ?_, ?_, ?_⟩
  · have hD : AnalyticAt ℝ D alpha := by
      simpa [D] using
        fixed_contour_matrix_delta_analyticAt (Node := Node) A alpha
          hAanalytic
    simpa [X, Lc] using (Lc.analyticAt (D alpha)).comp' hD
  · intro a theta
    simp [X, Lc, L, D, R0]
  · ext theta r s
    simp [X, Lc, L, D, fixed_contour_matrix_delta_self]

/-- Analyticity of the fixed-contour inverse branch in the continuous-map
Banach algebra.  The branch is written with `Ring.inverse`, since the
continuous-map algebra has no global `Inv` instance for matrix-valued maps. -/
theorem continuousMap_one_sub_ringInverse_analyticAt_of_zero
    [DecidableEq Node] {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (X : ℝ → ContinuousMap K (ComplexNodeMatrix Node)) {alpha : ℝ}
    (hXanalytic : AnalyticAt ℝ X alpha) (hX_alpha : X alpha = 0) :
    AnalyticAt ℝ
      (fun a : ℝ =>
        Ring.inverse
          ((1 : ContinuousMap K (ComplexNodeMatrix Node)) - X a))
      alpha := by
  letI : NormedSpace ℝ (ComplexNodeMatrix Node) :=
    NormedSpace.restrictScalars ℝ ℂ _
  letI : IsBoundedSMul ℝ (ComplexNodeMatrix Node) :=
    IsBoundedSMul.of_norm_smul_le NormedSpace.norm_smul_le
  letI : ContinuousSMul ℝ (ComplexNodeMatrix Node) :=
    IsBoundedSMul.continuousSMul
  letI hmatrixComplete : CompleteSpace (ComplexNodeMatrix Node) :=
    FiniteDimensional.complete ℂ _
  have hcmComplete :
      CompleteSpace (ContinuousMap K (ComplexNodeMatrix Node)) :=
    (ContinuousMap.isometryEquivBoundedOfCompact K
      (ComplexNodeMatrix Node)).completeSpace
  letI := hcmComplete
  letI hgeom : HasSummableGeomSeries
      (ContinuousMap K (ComplexNodeMatrix Node)) :=
    @instHasSummableGeomSeriesOfCompleteSpace
      (ContinuousMap K (ComplexNodeMatrix Node)) _ hcmComplete
  have hinv : AnalyticAt ℝ
      (fun Y : ContinuousMap K (ComplexNodeMatrix Node) =>
        Ring.inverse (1 - Y)) 0 :=
    analyticAt_inverse_one_sub ℝ _
  rw [← hX_alpha] at hinv
  simpa only [Function.comp_apply] using
    AnalyticAt.comp hinv hXanalytic

/-- Local ContinuousMap-valued analytic bridge for the fixed contour integrand.

This is the Banach-valued Neumann-series step in Appendix A: the scalar
resolvent integrand is represented near `alpha` by a geometrically dominated
Neumann expansion, yielding a locally analytic map into continuous functions
on the fixed interval. -/
theorem fixed_contour_integrand_continuousMap_analyticAt_from_neumann
    [DecidableEq Node]
    (A : ℝ → NodeMatrix Node) (center : ℂ) (radius : ℝ)
    (alpha epsN qN M : ℝ) (c : ℂ) (i j : Node)
    (scaledIntegrand : ℝ → ℝ → ℂ)
    (hradius_nonneg : 0 ≤ radius)
    (hepsN_pos : 0 < epsN)
    (hqN_nonneg : 0 ≤ qN) (hqN_lt_one : qN < 1)
    (hAanalytic : AnalyticAt ℝ A alpha)
    (hnotEigenAlpha :
      ∀ z : ℂ, ‖z - center‖ = radius →
        ¬ IsComplexRightEigenvalue (Node := Node) (A alpha) z)
    (hcanonicalResolventBound :
      ∀ z : ℂ, ‖z - center‖ = radius →
        complexMatrixOperatorNorm (Node := Node)
          ((complexResolventMatrix (Node := Node) (A alpha) z)⁻¹) ≤ M)
    (hlocalNeumannPowerBound :
      ∀ a : ℝ, |a - alpha| < epsN →
        ∀ z : ℂ, ‖z - center‖ = radius →
          ∀ n : ℕ,
            complexMatrixOperatorNorm (Node := Node)
              ((((complexResolventMatrix (Node := Node) (A alpha) z)⁻¹) *
                  complexOfRealMatrix (Node := Node)
                    (matrixSub (Node := Node) (A a) (A alpha))) ^ n) ≤
              qN ^ n)
    (hscaledIntegrand_neumann :
      ∀ a : ℝ, |a - alpha| < epsN →
        ∀ theta : ℝ,
          scaledIntegrand a theta =
            deriv (circleMap center radius) theta *
              (c *
                (((∑' n : ℕ,
                  ((((complexResolventMatrix (Node := Node) (A alpha)
                    (circleMap center radius theta))⁻¹) *
                    complexOfRealMatrix (Node := Node)
                      (matrixSub (Node := Node) (A a) (A alpha))) ^ n))) *
                  (complexResolventMatrix (Node := Node) (A alpha)
                    (circleMap center radius theta))⁻¹) i j))
    (hneumannTermEntryBound :
      ∀ a : ℝ, |a - alpha| < epsN →
        ∀ theta : ℝ, theta ∈ Set.Icc (0 : ℝ) (2 * Real.pi) →
          ∀ n : ℕ,
            ‖(((((complexResolventMatrix (Node := Node) (A alpha)
                    (circleMap center radius theta))⁻¹) *
                  complexOfRealMatrix (Node := Node)
                    (matrixSub (Node := Node) (A a) (A alpha))) ^ n *
                (complexResolventMatrix (Node := Node) (A alpha)
                  (circleMap center radius theta))⁻¹) i j)‖ ≤
              qN ^ n * M) :
    ∃ G : ℝ → ContinuousMap (Set.Icc (0 : ℝ) (2 * Real.pi)) ℂ,
      AnalyticAt ℝ G alpha ∧
        ∀ᶠ a in 𝓝 alpha,
          ∀ theta : Set.Icc (0 : ℝ) (2 * Real.pi),
            G a theta = scaledIntegrand a theta.1 := by
  classical
  let K : Type := Set.Icc (0 : ℝ) (2 * Real.pi)
  letI : NormedSpace ℝ ℂ :=
    NormedSpace.restrictScalars ℝ ℂ _
  letI : IsBoundedSMul ℝ ℂ :=
    IsBoundedSMul.of_norm_smul_le NormedSpace.norm_smul_le
  letI : ContinuousSMul ℝ ℂ :=
    IsBoundedSMul.continuousSMul
  letI : NormedSpace ℝ (ComplexNodeMatrix Node) :=
    NormedSpace.restrictScalars ℝ ℂ _
  letI : IsBoundedSMul ℝ (ComplexNodeMatrix Node) :=
    IsBoundedSMul.of_norm_smul_le NormedSpace.norm_smul_le
  letI : ContinuousSMul ℝ (ComplexNodeMatrix Node) :=
    IsBoundedSMul.continuousSMul
  letI hmatrixComplete : CompleteSpace (ComplexNodeMatrix Node) :=
    FiniteDimensional.complete ℂ _
  have hcmComplete :
      CompleteSpace (ContinuousMap K (ComplexNodeMatrix Node)) :=
    (ContinuousMap.isometryEquivBoundedOfCompact K
      (ComplexNodeMatrix Node)).completeSpace
  letI := hcmComplete
  letI hgeom : HasSummableGeomSeries
      (ContinuousMap K (ComplexNodeMatrix Node)) :=
    @instHasSummableGeomSeriesOfCompleteSpace
      (ContinuousMap K (ComplexNodeMatrix Node)) _ hcmComplete
  rcases
    fixed_contour_matrix_delta_to_continuousMap_analyticAt
      (Node := Node) A center radius alpha hradius_nonneg hAanalytic
      hnotEigenAlpha
    with ⟨X, hXanalytic, hX_eval, hX_alpha⟩
  /-
  Remaining direct subgoal: project
  `(Ring.inverse (1 - X a) * R0)` to the scaled scalar entry, and use the
  local Neumann equality hypotheses to identify the resulting branch with
  `scaledIntegrand` eventually.  The `Ring.inverse` branch below is the
  ContinuousMap-valued inverse supplied by the Banach-algebra inverse API.
  -/
  have hXinvanalytic :
      AnalyticAt ℝ
        (fun a : ℝ =>
          Ring.inverse
            ((1 : ContinuousMap K (ComplexNodeMatrix Node)) - X a))
        alpha :=
    continuousMap_one_sub_ringInverse_analyticAt_of_zero
      (Node := Node) (K := K) X hXanalytic hX_alpha
  let R0cm : ContinuousMap K (ComplexNodeMatrix Node) :=
    ⟨fun theta : K =>
        (complexResolventMatrix (Node := Node) (A alpha)
          (circleMap center radius theta.1))⁻¹,
      by
        have hbase :=
          fixed_contour_base_resolventInverse_continuousOn_Icc
            (Node := Node) (A alpha) center radius hradius_nonneg
            hnotEigenAlpha
        simpa [K] using
          (continuousOn_iff_continuous_restrict.mp hbase)⟩
  let H : ℝ → ContinuousMap K (ComplexNodeMatrix Node) :=
    fun a =>
      Ring.inverse
        ((1 : ContinuousMap K (ComplexNodeMatrix Node)) - X a) * R0cm
  have hHanalytic : AnalyticAt ℝ H alpha := by
    simpa [H] using hXinvanalytic.mul analyticAt_const
  let entryLin : ComplexNodeMatrix Node →ₗ[ℝ] ℂ :=
    { toFun := fun Y => Y i j
      map_add' := by intro Y Z; simp
      map_smul' := by intro r Y; simp [smul_eq_mul] }
  let entryCLM : ComplexNodeMatrix Node →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap entryLin
  let entryMap :
      ContinuousMap K (ComplexNodeMatrix Node) →L[ℝ] ContinuousMap K ℂ :=
    ContinuousLinearMap.compLeftContinuous ℝ K entryCLM
  have hEntryAnalytic :
      AnalyticAt ℝ (fun a : ℝ => entryMap (H a)) alpha := by
    simpa using (entryMap.analyticAt (H alpha)).comp' hHanalytic
  let coeff : ContinuousMap K ℂ :=
    ⟨fun theta : K => deriv (circleMap center radius) theta.1 * c,
      by
        have hderivTheta :
            Continuous (fun theta : ℝ =>
              deriv (circleMap center radius) theta) := by
          exact circleMap_deriv_continuous center radius
        exact (hderivTheta.comp continuous_subtype_val).mul continuous_const⟩
  let G : ℝ → ContinuousMap K ℂ := fun a => coeff * entryMap (H a)
  have hGanalytic : AnalyticAt ℝ G alpha := by
    simpa [G] using analyticAt_const.mul hEntryAnalytic
  refine ⟨G, hGanalytic, ?_⟩
  have hnear : ∀ᶠ a in 𝓝 alpha, |a - alpha| < epsN := by
    have hball : Metric.ball alpha epsN ∈ 𝓝 alpha :=
      Metric.ball_mem_nhds alpha hepsN_pos
    filter_upwards [hball] with a ha
    simpa [Metric.mem_ball, Real.dist_eq] using ha
  filter_upwards [hnear] with a ha theta
  have hRingInverse_neumann :
      Ring.inverse
          ((1 : ContinuousMap K (ComplexNodeMatrix Node)) - X a) theta =
        (∑' n : ℕ, (X a theta) ^ n) := by
    have hXpoint_le : ∀ theta : K, ‖X a theta‖ ≤ qN := by
      intro theta
      have hz : ‖circleMap center radius theta.1 - center‖ = radius := by
        simpa [Metric.mem_sphere, dist_eq_norm] using
          circleMap_mem_sphere center hradius_nonneg theta.1
      have hop_le :
          complexMatrixOperatorNorm (Node := Node) (X a theta) ≤ qN := by
        have hpow := hlocalNeumannPowerBound a ha
          (circleMap center radius theta.1) hz 1
        simpa [hX_eval a theta] using hpow
      exact le_trans
        (complexMatrix_norm_le_operatorNorm (Node := Node) (X a theta))
        hop_le
    have hXnorm_le : ‖X a‖ ≤ qN := by
      exact (ContinuousMap.norm_le (X a) hqN_nonneg).2 hXpoint_le
    have hXnorm : ‖X a‖ < 1 := lt_of_le_of_lt hXnorm_le hqN_lt_one
    have hcmGeom :
        (∑' n : ℕ, (X a) ^ n) =
          Ring.inverse
            ((1 : ContinuousMap K (ComplexNodeMatrix Node)) - X a) := by
      simpa using geom_series_eq_inverse (X a) hXnorm
    have h_eval_tsum :
        (∑' n : ℕ, (X a) ^ n) theta =
          ∑' n : ℕ, (X a theta) ^ n := by
      let ev :
          ContinuousMap K (ComplexNodeMatrix Node) →L[ℝ]
            ComplexNodeMatrix Node :=
        ContinuousMap.evalCLM ℝ theta
      have hsumm : Summable (fun n : ℕ => (X a) ^ n) :=
        summable_geometric_of_norm_lt_one hXnorm
      have hmap := ev.map_tsum hsumm
      simpa [ev] using hmap
    calc
      Ring.inverse
          ((1 : ContinuousMap K (ComplexNodeMatrix Node)) - X a) theta =
          (∑' n : ℕ, (X a) ^ n) theta := by
            exact congrArg
              (fun f : ContinuousMap K (ComplexNodeMatrix Node) => f theta)
              hcmGeom.symm
      _ = (∑' n : ℕ, (X a theta) ^ n) := h_eval_tsum
  have hscaled := hscaledIntegrand_neumann a ha theta.1
  rw [hscaled]
  simp [G, coeff, entryMap, entryCLM, entryLin, H, R0cm,
    hRingInverse_neumann, hX_eval]
  ring

/-- Source-specific fixed-contour analytic integration bridge for Appendix A.

This is the real analytic step behind Lemma A.1's sentence that compactness
and the resolvent identity make the fixed Riesz projection analytic.  The
statement deliberately keeps the fixed-circle no-eigen hypothesis and analytic
matrix family in the interface, rather than reducing the problem to the false
generic shape "pointwise analytic plus joint continuous". -/
theorem fixed_contour_resolvent_integral_analytic_via_neumann_identity
    [DecidableEq Node]
    (A : ℝ → NodeMatrix Node) (rho : ℝ) (center : ℂ) (radius : ℝ)
    (hrho_pos : 0 < rho)
    (hradius_nonneg : 0 ≤ radius)
    (hAanalytic :
      ∀ alpha : ℝ, |alpha| < rho → AnalyticAt ℝ A alpha)
    (hcircleNoEigen : ∀ alpha : ℝ, |alpha| ≤ rho / 2 →
      ∀ z : ℂ, ‖z - center‖ = radius →
        ¬ IsComplexRightEigenvalue (Node := Node) (A alpha) z)
    (alpha : ℝ) (halpha : |alpha| < rho / 2) (i j : Node) :
    AnalyticAt ℝ
      (fun a : ℝ =>
        ∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
          deriv (circleMap center radius) theta *
            ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
              (complexResolventMatrix (Node := Node) (A a)
                (circleMap center radius theta))⁻¹ i j))
      alpha := by
  classical
  let c : ℂ := (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹)
  let scaledIntegrand : ℝ → ℝ → ℂ := fun a theta =>
    deriv (circleMap center radius) theta *
      (c *
        (complexResolventMatrix (Node := Node) (A a)
          (circleMap center radius theta))⁻¹ i j)
  have hhalf_lt : rho / 2 < rho := by nlinarith
  have halpha_rho : |alpha| < rho := lt_trans halpha hhalf_lt
  have hscaledResolventEntryAnalytic :
      ∀ z : ℂ, ‖z - center‖ = radius →
        ∀ p q : Node,
          AnalyticAt ℝ
            (fun a : ℝ =>
              c *
                (complexResolventMatrix (Node := Node) (A a) z)⁻¹ p q)
            alpha := by
    intro z hz p q
    have hnot :
        ¬ IsComplexRightEigenvalue (Node := Node) (A alpha) z :=
      hcircleNoEigen alpha (le_of_lt halpha) z hz
    exact analyticAt_const.mul
      (complexResolventInverse_entry_analyticAt_alpha_of_not_eigen
        (Node := Node) A z (hAanalytic alpha halpha_rho) hnot p q)
  have hpointwise :
      ∀ theta : ℝ,
        AnalyticAt ℝ (fun a : ℝ => scaledIntegrand a theta) alpha := by
    intro theta
    exact fixedCircle_scaledResolvent_intervalIntegrand_analyticAt
      (Node := Node) A (center := center) (radius := radius)
      (alpha := alpha) hradius_nonneg hscaledResolventEntryAnalytic
      theta i j
  have hjoint :
      ContinuousOn
        (fun p : ℝ × ℝ => scaledIntegrand p.1 p.2)
        (Set.Icc (-(rho / 2)) (rho / 2) ×ˢ
          Set.Icc (0 : ℝ) (2 * Real.pi)) := by
    simpa [scaledIntegrand, c] using
      fixedCircle_scaledResolvent_intervalIntegrand_continuousOn
        (Node := Node) A (rho / 2) rho center radius
        hradius_nonneg hAanalytic hhalf_lt hcircleNoEigen i j
  have huniformResolvent :
      ∃ M : ℝ, 0 ≤ M ∧
        ∀ beta : ℝ, |beta| ≤ rho / 2 →
          ∀ z : ℂ, ‖z - center‖ = radius →
            ∃ R : ComplexNodeMatrix Node,
              HasComplexResolvent (Node := Node) (A beta) z R ∧
                complexMatrixOperatorNorm (Node := Node) R ≤ M :=
    complexResolventNorm_uniform_on_shifted_circle (Node := Node)
      A (rho / 2) rho center radius hAanalytic hhalf_lt hcircleNoEigen
  rcases huniformResolvent with ⟨M, hM_nonneg, hM⟩
  have hcanonicalResolventBound :
      ∀ beta : ℝ, |beta| ≤ rho / 2 →
        ∀ z : ℂ, ‖z - center‖ = radius →
          complexMatrixOperatorNorm (Node := Node)
            ((complexResolventMatrix (Node := Node) (A beta) z)⁻¹) ≤ M := by
    intro beta hbeta z hz
    rcases hM beta hbeta z hz with ⟨R, hRspec, hRbound⟩
    have hR_eq :
        (complexResolventMatrix (Node := Node) (A beta) z)⁻¹ = R := by
      exact Matrix.inv_eq_right_inv (by
        simpa [complexMatrixMul, complexIdentityMatrix_eq_one] using hRspec.1)
    simpa [hR_eq] using hRbound
  have hcanonicalEntryBound :
      ∀ beta : ℝ, |beta| ≤ rho / 2 →
        ∀ z : ℂ, ‖z - center‖ = radius →
          ‖((complexResolventMatrix (Node := Node) (A beta) z)⁻¹ i j)‖ ≤ M := by
    intro beta hbeta z hz
    let R : ComplexNodeMatrix Node :=
      (complexResolventMatrix (Node := Node) (A beta) z)⁻¹
    have hop := hcanonicalResolventBound beta hbeta z hz
    exact le_trans
      (complexMatrix_entry_norm_le_operatorNorm (Node := Node) R i j)
      (by simpa [R] using hop)
  have hlocalContraction :
      ∃ eps q : ℝ, 0 < eps ∧ 0 ≤ q ∧ q < 1 ∧
        ∀ a : ℝ, |a - alpha| < eps →
          |a| ≤ rho / 2 ∧
            ∀ z : ℂ, ‖z - center‖ = radius →
              complexMatrixOperatorNorm (Node := Node)
                (((complexResolventMatrix (Node := Node) (A alpha) z)⁻¹) *
                  complexOfRealMatrix (Node := Node)
                    (matrixSub (Node := Node) (A a) (A alpha))) ≤ q := by
    let delta : ℝ := (2 * (M + 1))⁻¹
    have hM_plus_pos : 0 < M + 1 := by nlinarith
    have hden_pos : 0 < 2 * (M + 1) := by positivity
    have hdelta_pos : 0 < delta := by
      dsimp [delta]
      positivity
    let deltaNorm : ℝ → ℝ := fun a =>
      complexMatrixOperatorNorm (Node := Node)
        (complexOfRealMatrix (Node := Node)
          (matrixSub (Node := Node) (A a) (A alpha)))
    have hAcont : ContinuousAt A alpha :=
      (hAanalytic alpha halpha_rho).continuousAt
    have hdiffCont :
        ContinuousAt
          (fun a : ℝ =>
            complexOfRealMatrix (Node := Node)
              (matrixSub (Node := Node) (A a) (A alpha))) alpha := by
      change ContinuousAt
        (fun a : ℝ => fun r : Node => fun s : Node =>
          ((A a r s - A alpha r s : ℝ) : ℂ)) alpha
      rw [continuousAt_pi]
      intro r
      rw [continuousAt_pi]
      intro s
      have hAr : ContinuousAt (fun a : ℝ => A a r) alpha :=
        (continuous_apply r).continuousAt.comp hAcont
      have hArs : ContinuousAt (fun a : ℝ => A a r s) alpha :=
        (continuous_apply s).continuousAt.comp hAr
      exact Complex.continuous_ofReal.continuousAt.comp
        (hArs.sub continuousAt_const)
    have hdeltaNormCont : ContinuousAt deltaNorm alpha :=
      (complexMatrixOperatorNorm_continuous (Node := Node)).continuousAt.comp
        hdiffCont
    have hdeltaNorm_zero : deltaNorm alpha = 0 := by
      have hzeroMatrix :
          complexOfRealMatrix (Node := Node)
              (matrixSub (Node := Node) (A alpha) (A alpha)) =
            (0 : ComplexNodeMatrix Node) := by
        ext r s
        simp [complexOfRealMatrix, matrixSub]
      have hzeroCLM :
          complexMatrixContinuousLinearMap (Node := Node)
              (0 : ComplexNodeMatrix Node) =
            (0 : ComplexRowVector Node →L[ℂ] ComplexRowVector Node) := by
        ext v r
        simp [complexMatrixContinuousLinearMap]
      simp [deltaNorm, hzeroMatrix, complexMatrixOperatorNorm, hzeroCLM]
    have hsmallEventually : ∀ᶠ a in 𝓝 alpha, deltaNorm a < delta := by
      have hlim : Tendsto deltaNorm (𝓝 alpha) (𝓝 (0 : ℝ)) := by
        simpa [ContinuousAt, hdeltaNorm_zero] using hdeltaNormCont
      exact hlim (Iio_mem_nhds hdelta_pos)
    rcases Metric.eventually_nhds_iff.mp hsmallEventually with
      ⟨epsDelta, hepsDelta_pos, hDeltaSmall⟩
    let epsParam : ℝ := (rho / 2 - |alpha|) / 2
    have hepsParam_pos : 0 < epsParam := by
      dsimp [epsParam]
      nlinarith
    refine ⟨min epsParam epsDelta, (1 : ℝ) / 2, ?_, by norm_num,
      by norm_num, ?_⟩
    · exact lt_min hepsParam_pos hepsDelta_pos
    · intro a haeps
      have haepsParam : |a - alpha| < epsParam :=
        lt_of_lt_of_le haeps (min_le_left epsParam epsDelta)
      have haepsDelta : |a - alpha| < epsDelta :=
        lt_of_lt_of_le haeps (min_le_right epsParam epsDelta)
      have ha_half : |a| ≤ rho / 2 := by
        have hre : a = alpha + (a - alpha) := by ring
        have habs_le : |a| ≤ |alpha| + |a - alpha| := by
          calc
            |a| = |alpha + (a - alpha)| := by
              rw [show alpha + (a - alpha) = a by ring]
            _ ≤ |alpha| + |a - alpha| := abs_add_le alpha (a - alpha)
        have hlt : |alpha| + |a - alpha| < rho / 2 := by
          dsimp [epsParam] at haepsParam
          nlinarith
        exact le_of_lt (lt_of_le_of_lt habs_le hlt)
      refine ⟨ha_half, ?_⟩
      intro z hz
      let R0 : ComplexNodeMatrix Node :=
        (complexResolventMatrix (Node := Node) (A alpha) z)⁻¹
      let D : ComplexNodeMatrix Node :=
        complexOfRealMatrix (Node := Node)
          (matrixSub (Node := Node) (A a) (A alpha))
      have hDelta_lt : complexMatrixOperatorNorm (Node := Node) D < delta := by
        have hdist : dist a alpha < epsDelta := by
          simpa [Real.dist_eq] using haepsDelta
        simpa [deltaNorm, D] using hDeltaSmall (y := a) hdist
      have hDelta_le :
          complexMatrixOperatorNorm (Node := Node) D ≤ delta :=
        le_of_lt hDelta_lt
      have hR0_le :
          complexMatrixOperatorNorm (Node := Node) R0 ≤ M := by
        simpa [R0] using
          hcanonicalResolventBound alpha (le_of_lt halpha) z hz
      have hmul :
          complexMatrixOperatorNorm (Node := Node) (R0 * D) ≤
            complexMatrixOperatorNorm (Node := Node) R0 *
              complexMatrixOperatorNorm (Node := Node) D :=
        complexMatrixOperatorNorm_matrix_mul (Node := Node) R0 D
      have hprod :
          complexMatrixOperatorNorm (Node := Node) R0 *
              complexMatrixOperatorNorm (Node := Node) D ≤
            M * delta := by
        exact mul_le_mul hR0_le hDelta_le
          (complexMatrixOperatorNorm_spec (Node := Node) D).1 hM_nonneg
      have hMdelta_le : M * delta ≤ (1 : ℝ) / 2 := by
        dsimp [delta]
        field_simp [hden_pos.ne']
        nlinarith
      exact le_trans hmul (le_trans hprod hMdelta_le)
  rcases hlocalContraction with
    ⟨epsN, qN, hepsN_pos, hqN_nonneg, hqN_lt_one, hcontractN⟩
  have hlocalNeumannPowerBound :
      ∀ a : ℝ, |a - alpha| < epsN →
        |a| ≤ rho / 2 ∧
          ∀ z : ℂ, ‖z - center‖ = radius →
            ∀ n : ℕ,
              complexMatrixOperatorNorm (Node := Node)
                ((((complexResolventMatrix (Node := Node) (A alpha) z)⁻¹) *
                    complexOfRealMatrix (Node := Node)
                      (matrixSub (Node := Node) (A a) (A alpha))) ^ n) ≤
                qN ^ n := by
    intro a ha
    have hcontract_a := hcontractN a ha
    refine ⟨hcontract_a.1, ?_⟩
    intro z hz n
    let X : ComplexNodeMatrix Node :=
      ((complexResolventMatrix (Node := Node) (A alpha) z)⁻¹) *
        complexOfRealMatrix (Node := Node)
          (matrixSub (Node := Node) (A a) (A alpha))
    have hX_le : complexMatrixOperatorNorm (Node := Node) X ≤ qN := by
      simpa [X] using hcontract_a.2 z hz
    have hpow :
        complexMatrixOperatorNorm (Node := Node) (X ^ n) ≤
          complexMatrixOperatorNorm (Node := Node) X ^ n :=
      complexMatrixOperatorNorm_pow_le (Node := Node) X n
    have hgeom :
        complexMatrixOperatorNorm (Node := Node) X ^ n ≤ qN ^ n :=
      pow_le_pow_left₀
        (complexMatrixOperatorNorm_spec (Node := Node) X).1 hX_le n
    exact le_trans hpow hgeom
  have hnativeContraction :
      ∀ a : ℝ, |a - alpha| < epsN →
        |a| ≤ rho / 2 ∧
          ∀ z : ℂ, ‖z - center‖ = radius →
            ‖(((complexResolventMatrix (Node := Node) (A alpha) z)⁻¹) *
                complexOfRealMatrix (Node := Node)
                  (matrixSub (Node := Node) (A a) (A alpha)))‖ < 1 := by
    intro a ha
    have hcontract_a := hcontractN a ha
    refine ⟨hcontract_a.1, ?_⟩
    intro z hz
    let X : ComplexNodeMatrix Node :=
      ((complexResolventMatrix (Node := Node) (A alpha) z)⁻¹) *
        complexOfRealMatrix (Node := Node)
          (matrixSub (Node := Node) (A a) (A alpha))
    have hnative_le :
        ‖X‖ ≤ complexMatrixOperatorNorm (Node := Node) X :=
      complexMatrix_norm_le_operatorNorm (Node := Node) X
    have hop_le : complexMatrixOperatorNorm (Node := Node) X ≤ qN := by
      simpa [X] using hcontract_a.2 z hz
    exact lt_of_le_of_lt (le_trans hnative_le hop_le) hqN_lt_one
  have hneumannTsumInverse :
      ∀ a : ℝ, |a - alpha| < epsN →
        ∀ z : ℂ, ‖z - center‖ = radius →
          (∑' n : ℕ,
            ((((complexResolventMatrix (Node := Node) (A alpha) z)⁻¹) *
              complexOfRealMatrix (Node := Node)
                (matrixSub (Node := Node) (A a) (A alpha))) ^ n)) =
            (1 -
              (((complexResolventMatrix (Node := Node) (A alpha) z)⁻¹) *
                complexOfRealMatrix (Node := Node)
                  (matrixSub (Node := Node) (A a) (A alpha))))⁻¹ := by
    intro a ha z hz
    let X : ComplexNodeMatrix Node :=
      ((complexResolventMatrix (Node := Node) (A alpha) z)⁻¹) *
        complexOfRealMatrix (Node := Node)
          (matrixSub (Node := Node) (A a) (A alpha))
    have hXnorm : ‖X‖ < 1 := by
      simpa [X] using (hnativeContraction a ha).2 z hz
    simpa [X, Matrix.nonsing_inv_eq_ringInverse] using
      geom_series_eq_inverse X hXnorm
  have hneumannRightInverse :
      ∀ a : ℝ, |a - alpha| < epsN →
        ∀ z : ℂ, ‖z - center‖ = radius →
          complexResolventMatrix (Node := Node) (A a) z *
            (((∑' n : ℕ,
              ((((complexResolventMatrix (Node := Node) (A alpha) z)⁻¹) *
                complexOfRealMatrix (Node := Node)
                  (matrixSub (Node := Node) (A a) (A alpha))) ^ n))) *
              (complexResolventMatrix (Node := Node) (A alpha) z)⁻¹) =
            1 := by
    intro a ha z hz
    let Rα : ComplexNodeMatrix Node :=
      complexResolventMatrix (Node := Node) (A alpha) z
    let Rαinv : ComplexNodeMatrix Node := Rα⁻¹
    let D : ComplexNodeMatrix Node :=
      complexOfRealMatrix (Node := Node)
        (matrixSub (Node := Node) (A a) (A alpha))
    let X : ComplexNodeMatrix Node := Rαinv * D
    have hnotα :
        ¬ IsComplexRightEigenvalue (Node := Node) (A alpha) z :=
      hcircleNoEigen alpha (le_of_lt halpha) z hz
    have hRα_right : Rα * Rαinv = 1 := by
      have hspec :=
        complexResolvent_nonsing_inv_spec_of_not_eigen (Node := Node)
          (A alpha) z hnotα
      simpa [Rα, Rαinv, HasComplexResolvent, ComplexMatrixInverseSpec,
        complexMatrixMul, complexIdentityMatrix_eq_one] using hspec.1
    have hRα_right' : Rα * Rα⁻¹ = 1 := by
      simpa [Rαinv] using hRα_right
    have hRD : Rα * (Rα⁻¹ * D) = D := by
      rw [← Matrix.mul_assoc, hRα_right', Matrix.one_mul]
    have hresolvent_sub :
        complexResolventMatrix (Node := Node) (A a) z = Rα - D := by
      ext r s
      simp [Rα, D, complexResolventMatrix, complexMatrixSub,
        complexOfRealMatrix, matrixSub]
    have hfactor :
        complexResolventMatrix (Node := Node) (A a) z = Rα * (1 - X) := by
      calc
        complexResolventMatrix (Node := Node) (A a) z = Rα - D :=
          hresolvent_sub
        _ = Rα * (1 - X) := by
          rw [← hRD]
          simp [X, Rαinv, Matrix.mul_sub]
    have hXnorm : ‖X‖ < 1 := by
      simpa [X, Rα, Rαinv, D] using (hnativeContraction a ha).2 z hz
    have hgeom_left : (1 - X) * (∑' n : ℕ, X ^ n) = 1 :=
      mul_neg_geom_series X hXnorm
    calc
      complexResolventMatrix (Node := Node) (A a) z *
          (((∑' n : ℕ,
            ((((complexResolventMatrix (Node := Node) (A alpha) z)⁻¹) *
              complexOfRealMatrix (Node := Node)
                (matrixSub (Node := Node) (A a) (A alpha))) ^ n))) *
            (complexResolventMatrix (Node := Node) (A alpha) z)⁻¹)
          =
        (Rα * (1 - X)) * ((∑' n : ℕ, X ^ n) * Rαinv) := by
          simp [hfactor, X, Rα, Rαinv, D]
      _ = Rα * ((1 - X) * (∑' n : ℕ, X ^ n)) * Rαinv := by
          simp [Matrix.mul_assoc]
      _ = 1 := by
          simp [hgeom_left, hRα_right, Matrix.mul_assoc]
  have hneumannInverseEquality :
      ∀ a : ℝ, |a - alpha| < epsN →
        ∀ z : ℂ, ‖z - center‖ = radius →
          (complexResolventMatrix (Node := Node) (A a) z)⁻¹ =
            ((∑' n : ℕ,
              ((((complexResolventMatrix (Node := Node) (A alpha) z)⁻¹) *
                complexOfRealMatrix (Node := Node)
                  (matrixSub (Node := Node) (A a) (A alpha))) ^ n))) *
              (complexResolventMatrix (Node := Node) (A alpha) z)⁻¹ := by
    intro a ha z hz
    exact Matrix.inv_eq_right_inv (hneumannRightInverse a ha z hz)
  have hscaledIntegrand_neumann :
      ∀ a : ℝ, |a - alpha| < epsN →
        ∀ theta : ℝ,
          scaledIntegrand a theta =
            deriv (circleMap center radius) theta *
              (c *
                (((∑' n : ℕ,
                  ((((complexResolventMatrix (Node := Node) (A alpha)
                    (circleMap center radius theta))⁻¹) *
                    complexOfRealMatrix (Node := Node)
                      (matrixSub (Node := Node) (A a) (A alpha))) ^ n))) *
                  (complexResolventMatrix (Node := Node) (A alpha)
                    (circleMap center radius theta))⁻¹) i j) := by
    intro a ha theta
    have hz :
        ‖circleMap center radius theta - center‖ = radius := by
      simpa [Metric.mem_sphere, dist_eq_norm] using
        circleMap_mem_sphere center hradius_nonneg theta
    have hinv := hneumannInverseEquality a ha
      (circleMap center radius theta) hz
    simp [scaledIntegrand, hinv]
  have hneumannTermEntryBound :
      ∀ a : ℝ, |a - alpha| < epsN →
        ∀ theta : ℝ, theta ∈ Set.Icc (0 : ℝ) (2 * Real.pi) →
          ∀ n : ℕ,
            ‖(((((complexResolventMatrix (Node := Node) (A alpha)
                    (circleMap center radius theta))⁻¹) *
                  complexOfRealMatrix (Node := Node)
                    (matrixSub (Node := Node) (A a) (A alpha))) ^ n *
                (complexResolventMatrix (Node := Node) (A alpha)
                  (circleMap center radius theta))⁻¹) i j)‖ ≤
              qN ^ n * M := by
    intro a ha theta _htheta n
    let z : ℂ := circleMap center radius theta
    let R0 : ComplexNodeMatrix Node :=
      (complexResolventMatrix (Node := Node) (A alpha) z)⁻¹
    let D : ComplexNodeMatrix Node :=
      complexOfRealMatrix (Node := Node)
        (matrixSub (Node := Node) (A a) (A alpha))
    let X : ComplexNodeMatrix Node := R0 * D
    have hz : ‖z - center‖ = radius :=
      by
        simpa [z, Metric.mem_sphere, dist_eq_norm] using
          circleMap_mem_sphere center hradius_nonneg theta
    have hentry :
        ‖((X ^ n * R0) i j)‖ ≤
          complexMatrixOperatorNorm (Node := Node) (X ^ n * R0) :=
      complexMatrix_entry_norm_le_operatorNorm (Node := Node) (X ^ n * R0) i j
    have hmul :
        complexMatrixOperatorNorm (Node := Node) (X ^ n * R0) ≤
          complexMatrixOperatorNorm (Node := Node) (X ^ n) *
            complexMatrixOperatorNorm (Node := Node) R0 :=
      complexMatrixOperatorNorm_matrix_mul (Node := Node) (X ^ n) R0
    have hpow :
        complexMatrixOperatorNorm (Node := Node) (X ^ n) ≤ qN ^ n := by
      simpa [X, R0, D, z] using
        (hlocalNeumannPowerBound a ha).2 z hz n
    have hR0_le :
        complexMatrixOperatorNorm (Node := Node) R0 ≤ M := by
      simpa [R0, z] using
        hcanonicalResolventBound alpha (le_of_lt halpha) z hz
    have hprod :
        complexMatrixOperatorNorm (Node := Node) (X ^ n) *
            complexMatrixOperatorNorm (Node := Node) R0 ≤
          qN ^ n * M := by
      exact mul_le_mul hpow hR0_le
        (complexMatrixOperatorNorm_spec (Node := Node) R0).1
        (pow_nonneg hqN_nonneg n)
    exact le_trans hentry (le_trans hmul hprod)
  rcases
    fixed_contour_integrand_continuousMap_analyticAt_from_neumann
      (Node := Node) A center radius alpha epsN qN M c i j
      scaledIntegrand hradius_nonneg hepsN_pos hqN_nonneg hqN_lt_one
      (hAanalytic alpha halpha_rho)
      (fun z hz => hcircleNoEigen alpha (le_of_lt halpha) z hz)
      (fun z hz => hcanonicalResolventBound alpha (le_of_lt halpha) z hz)
      (fun a ha z hz n => (hlocalNeumannPowerBound a ha).2 z hz n)
      hscaledIntegrand_neumann hneumannTermEntryBound
    with ⟨G, hGanalytic, hG_eq⟩
  have hGint :
      AnalyticAt ℝ
        (fun a : ℝ =>
          continuousMap_Icc_setIntegral_clm (0 : ℝ) (2 * Real.pi) (G a))
        alpha :=
    continuousMap_Icc_setIntegral_clm_apply_analyticAt
      (0 : ℝ) (2 * Real.pi) alpha G hGanalytic
  have hambient :
      AnalyticAt ℝ
        (fun a : ℝ =>
          ∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
            scaledIntegrand a theta)
        alpha :=
    continuousMap_Icc_setIntegral_clm_apply_eventually_eq_ambient_integral
      (0 : ℝ) (2 * Real.pi) alpha G scaledIntegrand hGint hG_eq
  simpa [scaledIntegrand, c] using hambient

/-- Entrywise analyticity of the fixed complex contour projection from the
source-specific fixed-contour resolvent bridge.

This reduces the contour projection entry to the interval integral of the
scaled resolvent integrand, then delegates only the genuinely source-specific
analytic integration step. -/
theorem complexRieszProjectionOnCircle_entries_analyticAt_of_fixed_interval_integrand
    [DecidableEq Node]
    (A : ℝ → NodeMatrix Node) (rho : ℝ) (center : ℂ) (radius : ℝ)
    (hrho_pos : 0 < rho)
    (hradius_nonneg : 0 ≤ radius)
    (hAanalytic :
      ∀ alpha : ℝ, |alpha| < rho → AnalyticAt ℝ A alpha)
    (hcircleNoEigen : ∀ alpha : ℝ, |alpha| ≤ rho / 2 →
      ∀ z : ℂ, ‖z - center‖ = radius →
        ¬ IsComplexRightEigenvalue (Node := Node) (A alpha) z)
    (hcontourEntryIcc :
      ∀ alpha : ℝ, ∀ i j : Node,
        complexRieszProjectionOnCircle (Node := Node)
            (A alpha) center radius i j =
          (letI : DecidableEq Node := Classical.decEq Node;
            (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
                  (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
                    deriv (circleMap center radius) theta •
                      ((complexResolventMatrix (Node := Node) (A alpha)
                        (circleMap center radius theta))⁻¹) i j))) :
    ∀ alpha : ℝ, |alpha| < rho / 2 →
      ∀ i j : Node,
        AnalyticAt ℝ
          (fun a : ℝ =>
            complexRieszProjectionOnCircle (Node := Node)
              (A a) center radius i j)
          alpha := by
  classical
  intro alpha halpha i j
  let c : ℂ := (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹)
  let scaledIntegrand : ℝ → ℝ → ℂ := fun a theta =>
    deriv (circleMap center radius) theta *
      (c *
        (complexResolventMatrix (Node := Node) (A a)
          (circleMap center radius theta))⁻¹ i j)
  let unscaledIntegrand : ℝ → ℝ → ℂ := fun a theta =>
    deriv (circleMap center radius) theta •
      ((complexResolventMatrix (Node := Node) (A a)
        (circleMap center radius theta))⁻¹) i j
  have hcontourAnalytic :
      AnalyticAt ℝ
        (fun a : ℝ =>
          c *
            (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
              unscaledIntegrand a theta))
        alpha := by
    have hscaledIntegralEq :
        (fun a : ℝ =>
          c *
            (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
              unscaledIntegrand a theta)) =
          fun a : ℝ =>
            ∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
              scaledIntegrand a theta := by
      funext a
      calc
        c *
            (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
              unscaledIntegrand a theta) =
            ∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
              c * unscaledIntegrand a theta := by
          exact (MeasureTheory.integral_const_mul
            (μ := volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi)))
            c (fun theta : ℝ => unscaledIntegrand a theta)).symm
        _ = ∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
              scaledIntegrand a theta := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with theta
          simp only [scaledIntegrand, unscaledIntegrand, smul_eq_mul]
          rw [← mul_assoc, mul_comm c (deriv (circleMap center radius) theta),
            mul_assoc]
    have hscaledIntegralAnalytic :
        AnalyticAt ℝ
          (fun a : ℝ =>
            ∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
              scaledIntegrand a theta)
          alpha := by
      simpa [scaledIntegrand, c] using
        fixed_contour_resolvent_integral_analytic_via_neumann_identity
          (Node := Node) A rho center radius hrho_pos hradius_nonneg
          hAanalytic hcircleNoEigen alpha halpha i j
    rw [hscaledIntegralEq]
    exact hscaledIntegralAnalytic
  have hentry_eq :
      (fun a : ℝ =>
        complexRieszProjectionOnCircle (Node := Node)
          (A a) center radius i j) =
        fun a : ℝ =>
          c *
            (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
              unscaledIntegrand a theta) := by
    funext a
    have hraw_supplied := hcontourEntryIcc a i j
    have hdec : (Classical.decEq Node) = (inferInstance : DecidableEq Node) :=
      Subsingleton.elim _ _
    rw [hdec] at hraw_supplied
    simpa [c, unscaledIntegrand] using hraw_supplied
  simpa [hentry_eq] using hcontourAnalytic

/-- The base resolvent determinant has a positive lower bound on a shifted
circle when the circle contains no point spectrum. -/
theorem complexResolvent_base_det_pos_lower_bound_on_shifted_circle
    [DecidableEq Node]
    (A0 : NodeMatrix Node) (center : ℂ) (radius : ℝ)
    (hradius_pos : 0 < radius)
    (hbaseCircle : ∀ z : ℂ, ‖z - center‖ = radius →
      ¬ IsComplexRightEigenvalue (Node := Node) A0 z) :
    ∃ m : ℝ, 0 < m ∧
      ∀ z : ℂ, ‖z - center‖ = radius →
        m ≤ ‖Matrix.det
          (complexResolventMatrix (Node := Node) A0 z)‖ := by
  classical
  let s : Set ℂ := Metric.sphere center radius
  have hscompact : IsCompact s := isCompact_sphere center radius
  have hsne : s.Nonempty := by
    refine ⟨center + (radius : ℂ), ?_⟩
    have hsub : center + (radius : ℂ) - center = (radius : ℂ) := by ring
    have hnorm : ‖(radius : ℂ)‖ = radius := by
      have hsq :
          ‖(radius : ℂ)‖ ^ 2 = radius ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
        ring
      exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq |>.elim id (fun hneg => by
        have hnorm_nonneg : 0 ≤ ‖(radius : ℂ)‖ := norm_nonneg _
        nlinarith)
    have hradius_nonneg : 0 ≤ radius := le_of_lt hradius_pos
    simpa [s, Metric.mem_sphere, dist_eq_norm, hsub, hnorm, hradius_nonneg]
  have hcont : ContinuousOn
      (fun z : ℂ =>
        ‖Matrix.det (complexResolventMatrix (Node := Node) A0 z)‖) s :=
    (complexResolventDet_continuous_z (Node := Node) A0).continuousOn.norm
  rcases hscompact.exists_isMinOn hsne hcont with ⟨zmin, hzmin_s, hzmin⟩
  refine ⟨‖Matrix.det
      (complexResolventMatrix (Node := Node) A0 zmin)‖, ?_, ?_⟩
  · have hzmin_circle : ‖zmin - center‖ = radius := by
      simpa [s, Metric.mem_sphere, dist_eq_norm] using hzmin_s
    have hdet_ne :
        Matrix.det (complexResolventMatrix (Node := Node) A0 zmin) ≠ 0 :=
      complexResolvent_det_ne_zero_of_not_eigen (Node := Node) A0 zmin
        (hbaseCircle zmin hzmin_circle)
    exact norm_pos_iff.mpr hdet_ne
  · intro z hz
    exact hzmin (by simpa [s, Metric.mem_sphere, dist_eq_norm] using hz)

/-- Fixed-circle resolvent persistence near the origin.

This is the determinant/non-eigen compactness part of Appendix A, Lemma A.1:
if the base circle around `1` avoids the point spectrum of `A 0`, then after
shrinking the analytic parameter interval the same fixed circle avoids the
point spectrum of `A alpha`. -/
theorem fixed_circle_resolvent_persistence_near_zero
    [DecidableEq Node]
    (A : ℝ → NodeMatrix Node) (alpha1 baseRadius : ℝ)
    (hanalytic : RealAnalyticMatrixFamilyNear (Node := Node) A alpha1)
    (hbaseRadius_pos : 0 < baseRadius)
    (hbaseCircle : ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
      ¬ IsComplexRightEigenvalue (Node := Node) (A 0) z) :
    ∃ eps : ℝ,
      eps ≤ alpha1 ∧ 0 < eps ∧
        ∀ alpha : ℝ, |alpha| ≤ eps →
          ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
            ¬ IsComplexRightEigenvalue (Node := Node) (A alpha) z := by
  classical
  let center : ℂ := 1
  obtain ⟨m, hm_pos, hm_bound⟩ :=
    complexResolvent_base_det_pos_lower_bound_on_shifted_circle
      (Node := Node) (A 0) center baseRadius hbaseRadius_pos
      (by
        intro z hz
        exact hbaseCircle z (by simpa [center] using hz))
  let alpha0 : ℝ := alpha1 / 2
  have halpha0_pos : 0 < alpha0 := by
    dsimp [alpha0]
    nlinarith [hanalytic.1]
  have halpha0_lt : alpha0 < alpha1 := by
    dsimp [alpha0]
    nlinarith [hanalytic.1]
  have hFcontinuousOn : ContinuousOn A (Set.Icc (-alpha0) alpha0) :=
    analytic_matrixFamily_continuousOn_Icc_of_lt (Node := Node)
      A alpha0 alpha1 hanalytic.2 halpha0_lt
  let contourSet : Set (ℝ × ℂ) :=
    Set.Icc (-alpha0) alpha0 ×ˢ Metric.sphere center baseRadius
  let detOnContour : ℝ × ℂ → ℂ := fun p =>
    Matrix.det (complexResolventMatrix (Node := Node) (A p.1) p.2)
  have hcompact : IsCompact contourSet := by
    simpa [contourSet] using
      (isCompact_Icc.prod (isCompact_sphere center baseRadius))
  have hdetContinuousOn : ContinuousOn detOnContour contourSet := by
    simpa [detOnContour, contourSet] using
      complexResolventDet_continuousOn_shifted_contour (Node := Node)
        A alpha0 center baseRadius hFcontinuousOn
  have hunif : UniformContinuousOn detOnContour contourSet :=
    hcompact.uniformContinuousOn_of_continuous hdetContinuousOn
  rcases (Metric.uniformContinuousOn_iff.mp hunif) (m / 2) (half_pos hm_pos) with
    ⟨delta, hdelta_pos, hdelta⟩
  let eps : ℝ := min alpha0 (delta / 2)
  refine ⟨eps, ?_, ?_, ?_⟩
  · exact le_trans (min_le_left alpha0 (delta / 2)) (le_of_lt halpha0_lt)
  · exact lt_min halpha0_pos (half_pos hdelta_pos)
  · intro alpha halpha z hz
    have heps_le_alpha0 : eps ≤ alpha0 := min_le_left alpha0 (delta / 2)
    have heps_le_delta_half : eps ≤ delta / 2 := min_le_right alpha0 (delta / 2)
    have halpha_alpha0 : |alpha| ≤ alpha0 := le_trans halpha heps_le_alpha0
    have hzSphere : z ∈ Metric.sphere center baseRadius := by
      simpa [center, Metric.mem_sphere, dist_eq_norm] using hz
    have hp : (alpha, z) ∈ contourSet := by
      exact ⟨abs_le.mp halpha_alpha0, hzSphere⟩
    have hq : ((0 : ℝ), z) ∈ contourSet := by
      refine ⟨?_, hzSphere⟩
      constructor <;> nlinarith [halpha0_pos]
    have hdist_arg : dist (alpha, z) ((0 : ℝ), z) < delta := by
      rw [dist_prod_same_right, Real.dist_eq]
      have habs_delta_half : |alpha| ≤ delta / 2 :=
        le_trans halpha heps_le_delta_half
      have habs_delta : |alpha| < delta := by
        nlinarith [hdelta_pos, habs_delta_half]
      simpa using habs_delta
    have hclose :
        dist (detOnContour (alpha, z)) (detOnContour ((0 : ℝ), z)) < m / 2 :=
      hdelta (alpha, z) hp ((0 : ℝ), z) hq hdist_arg
    have hbaseLower :
        m ≤ ‖Matrix.det
          (complexResolventMatrix (Node := Node) (A 0) z)‖ :=
      hm_bound z (by simpa [center] using hz)
    have hdet_ne :
        Matrix.det
          (complexResolventMatrix (Node := Node) (A alpha) z) ≠ 0 := by
      intro hzero
      have hclose_norm :
          ‖Matrix.det
            (complexResolventMatrix (Node := Node) (A 0) z)‖ < m / 2 := by
        simpa [detOnContour, hzero, dist_eq_norm, norm_neg] using hclose
      nlinarith [hm_pos, hbaseLower, hclose_norm]
    exact not_isComplexRightEigenvalue_of_complexResolvent_det_ne_zero
      (Node := Node) (A alpha) z hdet_ne


def boolUnitStableMatrix : NodeMatrix Bool :=
  fun i j => if i = false then if j = false then 1 else 0 else 0

def boolStableVector : RowVector Bool :=
  fun i => if i = true then 1 else 0

def boolStableProjection : NodeMatrix Bool :=
  fun i j => boolStableVector i * boolStableVector j

theorem boolUnitStableMatrix_eigenvalue_eq_zero_or_one
    {z : ℂ}
    (hz : IsComplexRightEigenvalue (Node := Bool) boolUnitStableMatrix z) :
    z = 0 ∨ z = 1 := by
  rcases hz with ⟨v, hvne, hmul⟩
  have hfalse := congrFun hmul false
  have htrue := congrFun hmul true
  simp [complexMatrixMulVector, boolUnitStableMatrix] at hfalse htrue
  by_cases hvf : v false = 0
  · rcases htrue with hz0 | hvt
    · exact Or.inl hz0
    · exfalso
      apply hvne
      funext i
      cases i <;> simp [hvf, hvt]
  · right
    have hmulzero : (z - 1) * v false = 0 := by
      rw [sub_mul, one_mul, ← hfalse]
      ring
    have hzminus : z - 1 = 0 :=
      (mul_eq_zero.mp hmulzero).resolve_right hvf
    exact sub_eq_zero.mp hzminus

/-- Typed obstruction for the retired local unit-projection surrogate.

The old surface recorded rank one plus a separating circle, but did not
identify the contour projection. For the diagonal matrix with unit eigenspace at
`false` and stable eigenspace at `true`, the projection onto the stable
eigenspace satisfies that retired surrogate while it is not the unit spectral
projection (`A P ≠ P`). The corrected `IsUnitRieszProjection` in `Part002`
therefore includes the full `RieszProjectionAtEigenvalueSpec`. -/
theorem isUnitRieszProjection_wrong_eigenspace_counterexample :
    ∃ A : ℝ → NodeMatrix Bool, ∃ P : NodeMatrix Bool,
      (RankOneProjection (Node := Bool) P ∧
          (∃ radius : ℝ, 0 < radius ∧
            ∀ z : ℂ, ‖z - (1 : ℂ)‖ = radius →
              ¬ IsComplexRightEigenvalue (Node := Bool) (A 0) z)) ∧
        matrixMul (Node := Bool) (A 0) P ≠ P := by
  refine ⟨fun _ : ℝ => boolUnitStableMatrix, boolStableProjection, ?_, ?_⟩
  · refine ⟨?_, 1 / 2, by norm_num, ?_⟩
    · unfold boolStableProjection
      apply normalized_outer_product_rankOneProjection (Node := Bool)
        boolStableVector boolStableVector
      · intro h
        have := congrFun h true
        norm_num [boolStableVector] at this
      · intro h
        have := congrFun h true
        norm_num [boolStableVector] at this
      · norm_num [rowDot, boolStableVector]
    · intro z hzCircle hzEig
      have hz01 := boolUnitStableMatrix_eigenvalue_eq_zero_or_one hzEig
      rcases hz01 with hz0 | hz1
      · subst z
        norm_num at hzCircle
      · subst z
        norm_num at hzCircle
  · intro h
    have hh := congrFun (congrFun h true) true
    norm_num [matrixMul, boolUnitStableMatrix, boolStableProjection,
      boolStableVector] at hh

theorem complexMatrixMulVector_matrixMul_real
    (A B : NodeMatrix Node) (v : ComplexRowVector Node) :
    complexMatrixMulVector (Node := Node) (matrixMul (Node := Node) A B) v =
      complexMatrixMulVector (Node := Node) A
        (complexMatrixMulVector (Node := Node) B v) := by
  classical
  have hmul :
      complexOfRealMatrix (Node := Node) (matrixMul (Node := Node) A B) =
        complexMatrixMul (Node := Node)
          (complexOfRealMatrix (Node := Node) A)
          (complexOfRealMatrix (Node := Node) B) := by
    ext i k
    simp only [complexOfRealMatrix, matrixMul, complexMatrixMul,
      Matrix.mul_apply, dotProduct]
    norm_cast
  calc
    complexMatrixMulVector (Node := Node) (matrixMul (Node := Node) A B) v =
        complexNodeMatrixMulVector (Node := Node)
          (complexOfRealMatrix (Node := Node) (matrixMul (Node := Node) A B)) v := by
          rw [complexNodeMatrixMulVector_complexOfRealMatrix]
    _ = complexNodeMatrixMulVector (Node := Node)
          (complexMatrixMul (Node := Node)
            (complexOfRealMatrix (Node := Node) A)
            (complexOfRealMatrix (Node := Node) B)) v := by
          rw [hmul]
    _ = complexNodeMatrixMulVector (Node := Node)
          (complexOfRealMatrix (Node := Node) A)
          (complexNodeMatrixMulVector (Node := Node)
            (complexOfRealMatrix (Node := Node) B) v) := by
          simp [complexNodeMatrixMulVector, complexMatrixMul,
            Matrix.mulVec_mulVec]
    _ = complexMatrixMulVector (Node := Node) A
          (complexMatrixMulVector (Node := Node) B v) := by
          rw [complexNodeMatrixMulVector_complexOfRealMatrix]
          rw [complexNodeMatrixMulVector_complexOfRealMatrix]

theorem complexMatrixMulVector_matrixSub_real
    (A B : NodeMatrix Node) (v : ComplexRowVector Node) :
    complexMatrixMulVector (Node := Node) (matrixSub (Node := Node) A B) v =
      complexMatrixMulVector (Node := Node) A v -
        complexMatrixMulVector (Node := Node) B v := by
  classical
  funext i
  simp only [complexMatrixMulVector, matrixSub, Pi.sub_apply]
  calc
    (∑ j : Node, ((A i j - B i j : ℝ) : ℂ) * v j) =
        ∑ j : Node, (((A i j : ℂ) - (B i j : ℂ)) * v j) := by
          apply Finset.sum_congr rfl
          intro j _
          norm_num
    _ = (∑ j : Node, (A i j : ℂ) * v j) -
        ∑ j : Node, (B i j : ℂ) * v j := by
          simp_rw [sub_mul]
          rw [Finset.sum_sub_distrib]

theorem complexMatrixMulVector_smul_vector
    (A : NodeMatrix Node) (c : ℂ) (v : ComplexRowVector Node) :
    complexMatrixMulVector (Node := Node) A (c • v) =
      c • complexMatrixMulVector (Node := Node) A v := by
  classical
  change Matrix.mulVec (complexOfRealMatrix (Node := Node) A) (c • v) =
    c • Matrix.mulVec (complexOfRealMatrix (Node := Node) A) v
  exact Matrix.mulVec_smul (complexOfRealMatrix (Node := Node) A) c v

/-- The real part of a real matrix acting on a complex vector is the same
real matrix acting on the vector of real parts. -/
theorem complexMatrixMulVector_re_eq_leftMul
    (A : NodeMatrix Node) (v : ComplexRowVector Node) :
    (fun i : Node => (complexMatrixMulVector (Node := Node) A v i).re) =
      leftMul (Node := Node) (E := ℝ) A
        (fun i : Node => (v i).re) := by
  classical
  funext i
  simp [complexMatrixMulVector, leftMul]

/-- The imaginary part of a real matrix acting on a complex vector is the same
real matrix acting on the vector of imaginary parts. -/
theorem complexMatrixMulVector_im_eq_leftMul
    (A : NodeMatrix Node) (v : ComplexRowVector Node) :
    (fun i : Node => (complexMatrixMulVector (Node := Node) A v i).im) =
      leftMul (Node := Node) (E := ℝ) A
        (fun i : Node => (v i).im) := by
  classical
  funext i
  simp [complexMatrixMulVector, leftMul]

theorem complexMatrixMulVector_stableComplement_one
    (A P : NodeMatrix Node) (v : ComplexRowVector Node) :
    complexMatrixMulVector (Node := Node)
        (stableComplementMatrix (Node := Node) A 1 P) v =
      complexMatrixMulVector (Node := Node) A v -
        complexMatrixMulVector (Node := Node) P v := by
  simpa [stableComplementMatrix] using
    complexMatrixMulVector_matrixSub_real (Node := Node) A P v

theorem complex_normalized_outer_product_apply
    (right left : RowVector Node) (v : ComplexRowVector Node) :
    complexMatrixMulVector (Node := Node)
        (fun i j : Node => right i * left j) v =
      (∑ j : Node, (left j : ℂ) * v j) •
        complexOfRealRow (Node := Node) right := by
  classical
  funext i
  simp only [complexMatrixMulVector, Pi.smul_apply, complexOfRealRow]
  calc
    (∑ j : Node, ((right i * left j : ℝ) : ℂ) * v j) =
        (right i : ℂ) * ∑ j : Node, (left j : ℂ) * v j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          norm_num
          ring
    _ = (∑ j : Node, (left j : ℂ) * v j) * (right i : ℂ) := by
          ring

theorem complex_normalized_outer_product_fixed_of_unit_eigen
    (A0 : NodeMatrix Node) (right left : RowVector Node)
    (hnormalized : rowDot (Node := Node) left right = 1)
    (halgebraicallySimple :
      UnitEigenvalueAlgebraicallySimple (Node := Node) A0 right)
    (v : ComplexRowVector Node)
    (hv_unit :
      complexMatrixMulVector (Node := Node) A0 v = (1 : ℂ) • v) :
    complexMatrixMulVector (Node := Node)
        (fun i j : Node => right i * left j) v = v := by
  classical
  obtain ⟨c, hc⟩ := halgebraicallySimple.1 v hv_unit
  subst v
  have hnormalized_complex :
      (∑ j : Node, (left j : ℂ) * (right j : ℂ)) = 1 := by
    have hcast := congrArg Complex.ofReal hnormalized
    simpa [rowDot] using hcast
  rw [complex_normalized_outer_product_apply]
  funext i
  simp only [Pi.smul_apply, complexOfRealRow]
  have hdot :
      (∑ j : Node, (left j : ℂ) *
          ((c • complexOfRealRow (Node := Node) right) j)) = c := by
    simp only [Pi.smul_apply, complexOfRealRow, smul_eq_mul]
    calc
      (∑ j : Node, (left j : ℂ) * (c * (right j : ℂ))) =
          c * ∑ j : Node, (left j : ℂ) * (right j : ℂ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = c := by rw [hnormalized_complex, mul_one]
  have hdot' :
      (∑ j : Node, (left j : ℂ) * (c * (right j : ℂ))) = c := by
    simpa [Pi.smul_apply, complexOfRealRow, smul_eq_mul] using hdot
  change (∑ j : Node, (left j : ℂ) * (c * (right j : ℂ))) *
      (right i : ℂ) = c * (right i : ℂ)
  rw [hdot']

/-- Base-point spectrum of the stable complement in Lemma A.1.

Once the contour projection is identified with the normalized unit Riesz
projection, every nonzero complement eigenvalue is a non-unit eigenvalue of
`A0`; the possible zero eigenvalue is harmless.  This is the algebraic input
for the later spectral upper-semicontinuity shrink. -/
theorem stableComplementMatrix_base_spectrum_le_of_riesz
    (A0 : NodeMatrix Node) (r0 : ℝ) (right left : RowVector Node)
    (P0 : NodeMatrix Node)
    (hspectrum :
      SimpleIsolatedUnitEigenvalueStableSpectrum (Node := Node) A0 r0 right left)
    (hRieszAtBase :
      IsRieszProjectionAtEigenvalue (Node := Node) A0 1 P0)
    (hP0 : P0 = (fun i j : Node => right i * left j)) :
    ∀ z : ℂ,
      IsComplexRightEigenvalue (Node := Node)
        (stableComplementMatrix (Node := Node) A0 1 P0) z →
        ‖z‖ ≤ r0 := by
  classical
  intro z hzEig
  by_cases hz0 : z = 0
  · subst z
    simpa using hspectrum.1
  · obtain ⟨v, hvne, hFv⟩ := hzEig
    have halg :=
      rieszProjection_stableComplementMatrix_algebra (Node := Node)
        A0 1 P0 hRieszAtBase
    let F0 : NodeMatrix Node := stableComplementMatrix (Node := Node) A0 1 P0
    have hPF_zero : matrixMul (Node := Node) P0 F0 = 0 := by
      simpa [F0] using halg.2.1
    have hPFv_zero :
        complexMatrixMulVector (Node := Node) P0
            (complexMatrixMulVector (Node := Node) F0 v) = 0 := by
      calc
        complexMatrixMulVector (Node := Node) P0
            (complexMatrixMulVector (Node := Node) F0 v) =
            complexMatrixMulVector (Node := Node)
              (matrixMul (Node := Node) P0 F0) v := by
                rw [complexMatrixMulVector_matrixMul_real]
        _ = 0 := by
                rw [hPF_zero]
                funext i
                simp [complexMatrixMulVector]
    have hPv_zero :
        complexMatrixMulVector (Node := Node) P0 v = 0 := by
      have hzPv :
          z • complexMatrixMulVector (Node := Node) P0 v = 0 := by
        rw [← complexMatrixMulVector_smul_vector]
        rw [← hFv]
        exact hPFv_zero
      exact (smul_eq_zero.mp hzPv).resolve_left hz0
    have hF_action :
        complexMatrixMulVector (Node := Node) F0 v =
          complexMatrixMulVector (Node := Node) A0 v -
            complexMatrixMulVector (Node := Node) P0 v := by
      simpa [F0] using
        complexMatrixMulVector_stableComplement_one (Node := Node) A0 P0 v
    have hAeig :
        complexMatrixMulVector (Node := Node) A0 v = z • v := by
      have htmp := hF_action
      rw [hPv_zero, sub_zero] at htmp
      rw [← htmp]
      exact hFv
    have hz_ne_one : z ≠ (1 : ℂ) := by
      intro hz1
      have hunit :
          complexMatrixMulVector (Node := Node) A0 v = (1 : ℂ) • v := by
        simpa [hz1] using hAeig
      have hPfix :
          complexMatrixMulVector (Node := Node) P0 v = v := by
        rw [hP0]
        exact complex_normalized_outer_product_fixed_of_unit_eigen
          (Node := Node) A0 right left hspectrum.2.2.2.2.1
          hspectrum.2.2.2.2.2.1 v hunit
      apply hvne
      rw [← hPfix, hPv_zero]
    exact hspectrum.2.2.2.2.2.2 z ⟨v, hvne, hAeig⟩ hz_ne_one

/-- Convert an eventual neighborhood statement at the origin into a symmetric
absolute-value radius, optionally capped by a positive ambient radius. -/
theorem eventually_nhds_zero_abs_radius_of_pos
    {p : ℝ → Prop} {alpha1 : ℝ} (halpha1 : 0 < alpha1)
    (hp : ∀ᶠ alpha : ℝ in 𝓝 0, p alpha) :
    ∃ eps : ℝ,
      eps ≤ alpha1 ∧ 0 < eps ∧
        ∀ alpha : ℝ, |alpha| < eps → p alpha := by
  rcases (Metric.eventually_nhds_iff.mp hp) with ⟨delta, hdelta_pos, hdelta⟩
  refine ⟨min alpha1 (delta / 2), min_le_left _ _, ?_, ?_⟩
  · exact lt_min halpha1 (half_pos hdelta_pos)
  · intro alpha halpha
    apply hdelta
    have hlt_half : |alpha| < delta / 2 :=
      lt_of_lt_of_le halpha (min_le_right alpha1 (delta / 2))
    have hlt_delta : |alpha| < delta := by
      nlinarith
    simpa [Real.dist_eq, abs_sub_comm] using hlt_delta

/-- Strong form of the source small-contour choice in Lemma A.1.

The read-only Part002 producer already chooses `(1 - r0) / 2`, but exports
only boundary avoidance.  The contour branch also needs the source fact that
this circle lies strictly inside the spectral gap from the remaining
eigenvalues. -/
theorem exists_unit_spectral_separating_circle_strong
    (A0 : NodeMatrix Node) (r0 : ℝ) (right left : RowVector Node)
    (hspectrum :
      SimpleIsolatedUnitEigenvalueStableSpectrum
        (Node := Node) A0 r0 right left) :
    ∃ radius : ℝ, 0 < radius ∧ radius < 1 - r0 ∧
      (∀ z : ℂ, ‖z - 1‖ = radius →
        ¬ IsComplexRightEigenvalue (Node := Node) A0 z) ∧
      (∀ z : ℂ, IsComplexRightEigenvalue (Node := Node) A0 z →
        z ≠ (1 : ℂ) → radius < ‖z - 1‖) := by
  classical
  rcases hspectrum with
    ⟨hr0_nonneg, hr0_lt_one, hright, hleft, hnormalized,
      halgebraic, hstable⟩
  refine ⟨(1 - r0) / 2, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · intro z hz heigen
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
  · intro z heigen hz_ne_one
    have hznorm : ‖z‖ ≤ r0 := hstable z heigen hz_ne_one
    have htriangle : (1 : ℝ) ≤ ‖z‖ + ‖z - 1‖ := by
      have h := norm_sub_le z (z - 1)
      convert h using 1 <;> norm_num <;> ring
    linarith

theorem isComplexRightEigenvalue_of_real_eigenpair_rowDot_one
    (Aalpha : NodeMatrix Node) (lambda : ℝ)
    (right left : RowVector Node)
    (heigen :
      matrixMulVector (Node := Node) Aalpha right = lambda • right)
    (hnormalized : rowDot (Node := Node) left right = 1) :
    IsComplexRightEigenvalue (Node := Node) Aalpha (lambda : ℂ) := by
  classical
  refine ⟨complexOfRealRow (Node := Node) right, ?_, ?_⟩
  · intro hzero
    have hright_zero : right = 0 := by
      funext i
      have hi : (right i : ℂ) = 0 := by
        simpa [complexOfRealRow] using congrFun hzero i
      exact Complex.ofReal_eq_zero.mp hi
    rw [hright_zero] at hnormalized
    simp [rowDot] at hnormalized
  · funext i
    have hi := congrFun heigen i
    simp only [complexMatrixMulVector, complexOfRealRow, Pi.smul_apply,
      smul_eq_mul]
    exact_mod_cast hi

theorem eigenbranch_stays_inside_fixed_circle_of_no_boundary
    (A : ℝ → NodeMatrix Node) (gamma : ℝ → ℝ)
    (rho branchRadius baseRadius : ℝ)
    (hgamma0 : gamma 0 = 1)
    (hbaseRadius_pos : 0 < baseRadius)
    (hrho_lt_branch : rho < branchRadius)
    (hgammaAnalytic :
      ∀ alpha : ℝ, |alpha| < branchRadius → AnalyticAt ℝ gamma alpha)
    (hgammaEigen :
      ∀ alpha : ℝ, |alpha| < branchRadius →
        IsComplexRightEigenvalue (Node := Node) (A alpha) (gamma alpha : ℂ))
    (hnoBoundary :
      ∀ alpha : ℝ, |alpha| ≤ rho →
        ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
          ¬ IsComplexRightEigenvalue (Node := Node) (A alpha) z) :
    ∀ alpha : ℝ, |alpha| ≤ rho →
      ‖(gamma alpha : ℂ) - (1 : ℂ)‖ < baseRadius := by
  classical
  let distToUnit : ℝ → ℝ := fun a => ‖(gamma a : ℂ) - (1 : ℂ)‖
  intro alpha halpha
  by_contra hnot_lt
  have hge : baseRadius ≤ distToUnit alpha := le_of_not_gt hnot_lt
  have hdist0 : distToUnit 0 = 0 := by
    simp [distToUnit, hgamma0]
  have hcont :
      ContinuousOn distToUnit (Set.uIcc (0 : ℝ) alpha) := by
    intro beta hbeta
    have hbeta_abs : |beta| ≤ |alpha| := by
      have h := Set.abs_sub_left_of_mem_uIcc
        (a := (0 : ℝ)) (b := alpha) (c := beta) hbeta
      simpa using h
    have hbeta_branch : |beta| < branchRadius :=
      lt_of_le_of_lt (le_trans hbeta_abs halpha) hrho_lt_branch
    have hgamma_cont :
        ContinuousAt gamma beta :=
      (hgammaAnalytic beta hbeta_branch).continuousAt
    have hcomplex_cont :
        ContinuousAt (fun a : ℝ => (gamma a : ℂ)) beta :=
      Complex.continuous_ofReal.continuousAt.comp hgamma_cont
    exact ((hcomplex_cont.sub continuousAt_const).norm).continuousWithinAt
  have htarget_mem :
      baseRadius ∈ Set.uIcc (distToUnit 0) (distToUnit alpha) := by
    rw [hdist0]
    exact Set.mem_uIcc_of_le (le_of_lt hbaseRadius_pos) hge
  rcases intermediate_value_uIcc hcont htarget_mem with
    ⟨beta, hbeta_mem, hbeta_eq⟩
  have hbeta_abs : |beta| ≤ |alpha| := by
    have h := Set.abs_sub_left_of_mem_uIcc
      (a := (0 : ℝ)) (b := alpha) (c := beta) hbeta_mem
    simpa using h
  have hbeta_rho : |beta| ≤ rho := le_trans hbeta_abs halpha
  have hbeta_branch : |beta| < branchRadius :=
    lt_of_le_of_lt hbeta_rho hrho_lt_branch
  exact (hnoBoundary beta hbeta_rho (gamma beta : ℂ)
    (by simpa [distToUnit] using hbeta_eq)) (hgammaEigen beta hbeta_branch)

/-- The source separating circle around the base unit eigenvalue encloses no
other point spectrum.

This is the spectral-topology part of the fixed-contour Riesz argument before
any contour integration is used: every base eigenvalue in the closed disk
`|z - 1| <= baseRadius` is the unit eigenvalue. -/
theorem fixed_circle_base_enclosed_spectrum_singleton
    (A0 : NodeMatrix Node) (baseRadius : ℝ)
    (hbaseRadius_pos : 0 < baseRadius)
    (hunit :
      IsComplexRightEigenvalue (Node := Node) A0 (1 : ℂ))
    (hbaseInteriorSeparates :
      ∀ z : ℂ, IsComplexRightEigenvalue (Node := Node) A0 z →
        z ≠ (1 : ℂ) → baseRadius < ‖z - (1 : ℂ)‖) :
    IsComplexRightEigenvalue (Node := Node) A0 (1 : ℂ) ∧
      ∀ z : ℂ, IsComplexRightEigenvalue (Node := Node) A0 z →
        (‖z - (1 : ℂ)‖ < baseRadius ↔ z = (1 : ℂ)) ∧
          (‖z - (1 : ℂ)‖ ≤ baseRadius ↔ z = (1 : ℂ)) := by
  classical
  refine ⟨hunit, ?_⟩
  intro z hz
  constructor
  · constructor
    · intro hinside
      by_contra hne
      have houtside := hbaseInteriorSeparates z hz hne
      linarith
    · intro hz1
      subst z
      simpa using hbaseRadius_pos
  · constructor
    · intro hclosed
      by_contra hne
      have houtside := hbaseInteriorSeparates z hz hne
      linarith
    · intro hz1
      subst z
      exact le_of_lt (by simpa using hbaseRadius_pos)

/-- The scalar simple-pole contribution of the unit eigenvalue on the fixed
circle. -/
theorem fixed_circle_simple_pole_entry_integral_eq
    (baseRadius : ℝ) (hbaseRadius_pos : 0 < baseRadius) (c : ℂ) :
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ z in C((1 : ℂ), baseRadius), (z - (1 : ℂ))⁻¹ * c) = c := by
  classical
  have hmem : (1 : ℂ) ∈ Metric.ball (1 : ℂ) baseRadius := by
    simpa [Metric.mem_ball, dist_self] using hbaseRadius_pos
  have hinv :
      (∮ z in C((1 : ℂ), baseRadius), (z - (1 : ℂ))⁻¹) =
        (2 : ℂ) * (Real.pi : ℂ) * Complex.I :=
    circleIntegral.integral_sub_inv_of_mem_ball
      (c := (1 : ℂ)) (w := (1 : ℂ)) (R := baseRadius) hmem
  have hconst :
      (∮ z in C((1 : ℂ), baseRadius), (z - (1 : ℂ))⁻¹ * c) =
        c * (∮ z in C((1 : ℂ), baseRadius), (z - (1 : ℂ))⁻¹) := by
    rw [show (fun z : ℂ => (z - (1 : ℂ))⁻¹ * c) =
        fun z : ℂ => c * (z - (1 : ℂ))⁻¹ by
          funext z
          ring]
    exact circleIntegral.integral_const_mul c
      (fun z : ℂ => (z - (1 : ℂ))⁻¹) (1 : ℂ) baseRadius
  rw [hconst, hinv]
  rw [mul_comm c ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)]
  rw [← mul_assoc, inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_mul]

theorem circleIntegral_sub_inv_mul_const_eq_of_mem_ball
    {center pole : ℂ} {radius : ℝ}
    (hpole : pole ∈ Metric.ball center radius) (c : ℂ) :
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ z in C(center, radius), (z - pole)⁻¹ * c) = c := by
  classical
  have hinv :
      (∮ z in C(center, radius), (z - pole)⁻¹) =
        (2 : ℂ) * (Real.pi : ℂ) * Complex.I :=
    circleIntegral.integral_sub_inv_of_mem_ball
      (c := center) (w := pole) (R := radius) hpole
  have hconst :
      (∮ z in C(center, radius), (z - pole)⁻¹ * c) =
        c * (∮ z in C(center, radius), (z - pole)⁻¹) := by
    rw [show (fun z : ℂ => (z - pole)⁻¹ * c) =
        fun z : ℂ => c * (z - pole)⁻¹ by
          funext z
          ring]
    exact circleIntegral.integral_const_mul c
      (fun z : ℂ => (z - pole)⁻¹) center radius
  rw [hconst, hinv]
  rw [mul_comm c ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)]
  rw [← mul_assoc, inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_mul]

theorem circleIntegral_w_sub_inv_mul_const_eq_neg_of_mem_ball
    {center pole : ℂ} {radius : ℝ}
    (hpole : pole ∈ Metric.ball center radius) (c : ℂ) :
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ z in C(center, radius), (pole - z)⁻¹ * c) = -c := by
  classical
  have hrewrite :
      (∮ z in C(center, radius), (pole - z)⁻¹ * c) =
        ∮ z in C(center, radius), (z - pole)⁻¹ * (-c) := by
    have hradius_pos : 0 < radius := by
      have hdist_nonneg : 0 ≤ dist pole center := dist_nonneg
      have hdist_lt : dist pole center < radius := Metric.mem_ball.mp hpole
      linarith
    refine circleIntegral.integral_congr
      (le_of_lt hradius_pos) ?_
    intro z _hz
    change (pole - z)⁻¹ * c = (z - pole)⁻¹ * (-c)
    have hneg : pole - z = -(z - pole) := by ring
    rw [hneg]
    rw [inv_neg]
    ring
  rw [hrewrite]
  simpa using
    circleIntegral_sub_inv_mul_const_eq_of_mem_ball
      (center := center) (pole := pole) (radius := radius) hpole (-c)

theorem circleIntegral_sub_inv_eq_zero_of_not_mem_closedBall
    {center pole : ℂ} {radius : ℝ} (hradius_nonneg : 0 ≤ radius)
    (hpole : pole ∉ Metric.closedBall center radius) :
    (∮ z in C(center, radius), (z - pole)⁻¹) = 0 := by
  classical
  refine
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
      hradius_nonneg (s := (∅ : Set ℂ)) Set.countable_empty ?_ ?_
  · intro z hz
    have hzw : z ≠ pole := by
      intro hzp
      exact hpole (by simpa [hzp] using hz)
    have hsub_ne : z - pole ≠ 0 := sub_ne_zero.mpr hzw
    have hsub_diff :
        DifferentiableAt ℂ (fun y : ℂ => y - pole) z :=
      differentiableAt_id.sub
        (differentiableAt_const (𝕜 := ℂ) (c := pole) (x := z))
    exact
      ((differentiableAt_inv hsub_ne).comp z hsub_diff).continuousAt.continuousWithinAt
  · intro z hz
    have hzclosed : z ∈ Metric.closedBall center radius :=
      Metric.mem_closedBall.2 (le_of_lt (Metric.mem_ball.mp hz.1))
    have hzw : z ≠ pole := by
      intro hzp
      exact hpole (by simpa [hzp] using hzclosed)
    have hsub_ne : z - pole ≠ 0 := sub_ne_zero.mpr hzw
    have hsub_diff :
        DifferentiableAt ℂ (fun y : ℂ => y - pole) z :=
      differentiableAt_id.sub
        (differentiableAt_const (𝕜 := ℂ) (c := pole) (x := z))
    exact (differentiableAt_inv hsub_ne).comp z hsub_diff

theorem circleIntegral_sub_inv_mul_const_eq_zero_of_not_mem_closedBall
    {center pole : ℂ} {radius : ℝ} (hradius_nonneg : 0 ≤ radius)
    (hpole : pole ∉ Metric.closedBall center radius) (c : ℂ) :
    (∮ z in C(center, radius), (z - pole)⁻¹ * c) = 0 := by
  classical
  have hconst :
      (∮ z in C(center, radius), (z - pole)⁻¹ * c) =
        c * (∮ z in C(center, radius), (z - pole)⁻¹) := by
    rw [show (fun z : ℂ => (z - pole)⁻¹ * c) =
        fun z : ℂ => c * (z - pole)⁻¹ by
          funext z
          ring]
    exact circleIntegral.integral_const_mul c
      (fun z : ℂ => (z - pole)⁻¹) center radius
  rw [hconst,
    circleIntegral_sub_inv_eq_zero_of_not_mem_closedBall
      hradius_nonneg hpole]
  simp

theorem circleIntegral_w_sub_inv_mul_const_eq_zero_of_not_mem_closedBall
    {center pole : ℂ} {radius : ℝ} (hradius_nonneg : 0 ≤ radius)
    (hpole : pole ∉ Metric.closedBall center radius) (c : ℂ) :
    (∮ z in C(center, radius), (pole - z)⁻¹ * c) = 0 := by
  classical
  have hrewrite :
      (∮ z in C(center, radius), (pole - z)⁻¹ * c) =
        ∮ z in C(center, radius), (z - pole)⁻¹ * (-c) := by
    refine circleIntegral.integral_congr hradius_nonneg ?_
    intro z _hz
    change (pole - z)⁻¹ * c = (z - pole)⁻¹ * (-c)
    have hneg : pole - z = -(z - pole) := by ring
    rw [hneg, inv_neg]
    ring
  rw [hrewrite]
  exact circleIntegral_sub_inv_mul_const_eq_zero_of_not_mem_closedBall
    hradius_nonneg hpole (-c)

theorem complex_resolvent_inv_entry_circleIntegral_eq_of_no_eigen_annulus
    [DecidableEq Node]
    (Aalpha : NodeMatrix Node) {innerRadius outerRadius : ℝ}
    (hinner_pos : 0 < innerRadius) (hradii : innerRadius ≤ outerRadius)
    (hnoAnnulus :
      ∀ z : ℂ, innerRadius ≤ ‖z - (1 : ℂ)‖ →
        ‖z - (1 : ℂ)‖ ≤ outerRadius →
          ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z)
    (i j : Node) :
    (∮ z in C((1 : ℂ), outerRadius),
        ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i j) =
      ∮ z in C((1 : ℂ), innerRadius),
        ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i j := by
  classical
  refine
    Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
      (c := (1 : ℂ)) hinner_pos hradii (s := (∅ : Set ℂ))
      Set.countable_empty ?_ ?_
  · intro z hz
    rcases hz with ⟨hzclosed, hznotball⟩
    have hlower : innerRadius ≤ ‖z - (1 : ℂ)‖ := by
      have hnotlt : ¬ dist z (1 : ℂ) < innerRadius := by
        intro hlt
        exact hznotball (Metric.mem_ball.2 hlt)
      simpa [dist_eq_norm] using le_of_not_gt hnotlt
    have hupper : ‖z - (1 : ℂ)‖ ≤ outerRadius := by
      simpa [dist_eq_norm] using (Metric.mem_closedBall.mp hzclosed)
    have hdet :
        Matrix.det (complexResolventMatrix (Node := Node) Aalpha z) ≠ 0 :=
      complexResolvent_det_ne_zero_of_not_eigen (Node := Node) Aalpha z
        (hnoAnnulus z hlower hupper)
    exact
      (complex_resolvent_inv_entry_differentiableAt_z_of_det_ne_zero
        (Node := Node) Aalpha hdet i j).continuousAt.continuousWithinAt
  · intro z hz
    rcases hz with ⟨⟨hzball, hznotclosed⟩, _hznotempty⟩
    have hlower : innerRadius ≤ ‖z - (1 : ℂ)‖ := by
      have hnotle : ¬ dist z (1 : ℂ) ≤ innerRadius := by
        intro hle
        exact hznotclosed (Metric.mem_closedBall.2 hle)
      exact le_of_lt (by
        simpa [dist_eq_norm] using lt_of_not_ge hnotle)
    have hupper : ‖z - (1 : ℂ)‖ ≤ outerRadius := by
      exact le_of_lt (by
        simpa [dist_eq_norm] using (Metric.mem_ball.mp hzball))
    have hdet :
        Matrix.det (complexResolventMatrix (Node := Node) Aalpha z) ≠ 0 :=
      complexResolvent_det_ne_zero_of_not_eigen (Node := Node) Aalpha z
        (hnoAnnulus z hlower hupper)
    exact complex_resolvent_inv_entry_differentiableAt_z_of_det_ne_zero
      (Node := Node) Aalpha hdet i j

theorem complexRieszProjectionOnCircle_eq_of_no_eigen_annulus
    [DecidableEq Node]
    (Aalpha : NodeMatrix Node) {innerRadius outerRadius : ℝ}
    (hinner_pos : 0 < innerRadius) (hradii : innerRadius ≤ outerRadius)
    (hnoAnnulus :
      ∀ z : ℂ, innerRadius ≤ ‖z - (1 : ℂ)‖ →
        ‖z - (1 : ℂ)‖ ≤ outerRadius →
          ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z) :
    complexRieszProjectionOnCircle (Node := Node)
        Aalpha (1 : ℂ) outerRadius =
      complexRieszProjectionOnCircle (Node := Node)
        Aalpha (1 : ℂ) innerRadius := by
  classical
  letI : DecidableEq Node := Classical.decEq Node
  ext i j
  simp only [complexRieszProjectionOnCircle]
  exact congrArg
    (fun x : ℂ => (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) * x)
    (complex_resolvent_inv_entry_circleIntegral_eq_of_no_eigen_annulus
      (Node := Node) Aalpha hinner_pos hradii hnoAnnulus i j)

theorem mem_cthickening_sphere_of_abs_norm_sub_le
    {center z : ℂ} {radius delta : ℝ}
    (hradius_pos : 0 < radius) (hdelta_nonneg : 0 ≤ delta)
    (hdelta_lt_radius : delta < radius)
    (hz : |‖z - center‖ - radius| ≤ delta) :
    z ∈ Metric.cthickening delta (Metric.sphere center radius) := by
  classical
  let d : ℝ := ‖z - center‖
  have hd_pos : 0 < d := by
    have hleft : -delta ≤ d - radius := (abs_le.mp hz).1
    dsimp [d]
    nlinarith [hradius_pos, hdelta_lt_radius, hleft]
  let y : ℂ := center + ((radius / d : ℝ) : ℂ) * (z - center)
  have hy_sphere : y ∈ Metric.sphere center radius := by
    have hy_sub : y - center = ((radius / d : ℝ) : ℂ) * (z - center) := by
      simp [y]
    have hnorm :
        ‖((radius / d : ℝ) : ℂ) * (z - center)‖ = radius := by
      have hdiv_nonneg : 0 ≤ radius / d := div_nonneg
        (le_of_lt hradius_pos) (le_of_lt hd_pos)
      rw [norm_mul, Complex.norm_of_nonneg hdiv_nonneg]
      rw [show ‖z - center‖ = d by rfl]
      field_simp [ne_of_gt hd_pos]
    exact Metric.mem_sphere.mpr (by
      simpa [dist_eq_norm, hy_sub] using hnorm)
  have hdist_le : dist z y ≤ delta := by
    have hz_sub :
        z - y = (1 - ((radius / d : ℝ) : ℂ)) * (z - center) := by
      simp [y]
      ring
    have hnorm :
        ‖(1 - ((radius / d : ℝ) : ℂ)) * (z - center)‖ =
          |d - radius| := by
      rw [norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub,
        Complex.norm_real]
      rw [show ‖z - center‖ = d by rfl]
      have hfactor :
          |(1 : ℝ) - radius / d| * d = |d - radius| := by
        have hd_ne : d ≠ 0 := ne_of_gt hd_pos
        calc
          |(1 : ℝ) - radius / d| * d =
              |(d - radius) / d| * d := by
                congr 1
                field_simp [hd_ne]
          _ = (|d - radius| / d) * d := by
                rw [abs_div, abs_of_pos hd_pos]
          _ = |d - radius| := by
                field_simp [hd_ne]
      simpa [d] using hfactor
    have hdist : dist z y = |d - radius| := by
      simpa [dist_eq_norm, hz_sub] using hnorm
    simpa [d, hdist] using hz
  exact Metric.mem_cthickening_of_dist_le z y delta
    (Metric.sphere center radius) hy_sphere hdist_le

theorem exists_no_eigen_annulus_around_fixed_circle
    [DecidableEq Node]
    (Aalpha : NodeMatrix Node) (baseRadius : ℝ)
    (hbaseRadius_pos : 0 < baseRadius)
    (hnoBoundary :
      ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
        ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z) :
    ∃ innerRadius outerRadius : ℝ,
      0 < innerRadius ∧ innerRadius < baseRadius ∧
      baseRadius < outerRadius ∧
      (∀ z : ℂ, innerRadius ≤ ‖z - (1 : ℂ)‖ →
        ‖z - (1 : ℂ)‖ ≤ outerRadius →
          ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z) := by
  classical
  let center : ℂ := 1
  let sphere : Set ℂ := Metric.sphere center baseRadius
  let detFun : ℂ → ℂ := fun z =>
    Matrix.det (complexResolventMatrix (Node := Node) Aalpha z)
  let U : Set ℂ := {z : ℂ | detFun z ≠ 0}
  have hscompact : IsCompact sphere := by
    simpa [sphere] using isCompact_sphere center baseRadius
  have hUopen : IsOpen U := by
    have hclosed : IsClosed (detFun ⁻¹' ({0} : Set ℂ)) := by
      exact isClosed_singleton.preimage
        ((complexResolventDet_continuous_z (Node := Node) Aalpha))
    simpa [U, detFun, Set.preimage, Set.compl_setOf] using hclosed.isOpen_compl
  have hs_subset_U : sphere ⊆ U := by
    intro z hz
    have hzboundary : ‖z - (1 : ℂ)‖ = baseRadius := by
      simpa [sphere, center, Metric.mem_sphere, dist_eq_norm] using hz
    exact complexResolvent_det_ne_zero_of_not_eigen
      (Node := Node) Aalpha z (hnoBoundary z hzboundary)
  rcases hscompact.exists_cthickening_subset_open hUopen hs_subset_U with
    ⟨delta, hdelta_pos, hdelta_subset⟩
  let eta : ℝ := min (delta / 2) (baseRadius / 2)
  have heta_pos : 0 < eta := by
    exact lt_min (half_pos hdelta_pos) (half_pos hbaseRadius_pos)
  have heta_nonneg : 0 ≤ eta := le_of_lt heta_pos
  have heta_le_delta : eta ≤ delta := by
    exact le_trans (min_le_left (delta / 2) (baseRadius / 2)) (by linarith)
  have heta_lt_radius : eta < baseRadius := by
    exact lt_of_le_of_lt (min_le_right (delta / 2) (baseRadius / 2)) (by linarith)
  refine ⟨baseRadius - eta, baseRadius + eta, ?_, ?_, ?_, ?_⟩
  · nlinarith [heta_lt_radius]
  · nlinarith [heta_pos]
  · nlinarith [heta_pos]
  · intro z hzinner hzouter
    have hz_abs : |‖z - (1 : ℂ)‖ - baseRadius| ≤ eta := by
      rw [abs_sub_le_iff]
      constructor <;> nlinarith [hzinner, hzouter]
    have hz_cthick_eta :
        z ∈ Metric.cthickening eta sphere := by
      exact mem_cthickening_sphere_of_abs_norm_sub_le
        (center := center) (radius := baseRadius) hbaseRadius_pos
        heta_nonneg heta_lt_radius (by simpa [center] using hz_abs)
    have hz_cthick_delta :
        z ∈ Metric.cthickening delta sphere :=
      Metric.cthickening_mono heta_le_delta sphere hz_cthick_eta
    have hdet_ne : detFun z ≠ 0 := hdelta_subset hz_cthick_delta
    exact not_isComplexRightEigenvalue_of_complexResolvent_det_ne_zero
      (Node := Node) Aalpha z (by simpa [detFun] using hdet_ne)

theorem complexOfRealMatrix_matrixMul
    (A B : NodeMatrix Node) :
    complexOfRealMatrix (Node := Node) (matrixMul (Node := Node) A B) =
      complexMatrixMul (Node := Node)
        (complexOfRealMatrix (Node := Node) A)
        (complexOfRealMatrix (Node := Node) B) := by
  classical
  ext i k
  simp only [complexOfRealMatrix, matrixMul, complexMatrixMul,
    Matrix.mul_apply, dotProduct]
  norm_cast

theorem complexified_base_riesz_projection_algebra
    (A0 P0 : NodeMatrix Node)
    (hrank : RankOneProjection (Node := Node) P0)
    (hAP : matrixMul (Node := Node) A0 P0 = (1 : ℝ) • P0)
    (hPA : matrixMul (Node := Node) P0 A0 = (1 : ℝ) • P0) :
    let Ac : ComplexNodeMatrix Node := complexOfRealMatrix (Node := Node) A0
    let Pc : ComplexNodeMatrix Node := complexOfRealMatrix (Node := Node) P0
    Pc * Pc = Pc ∧ Ac * Pc = Pc ∧ Pc * Ac = Pc := by
  classical
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · have h := congrArg (complexOfRealMatrix (Node := Node)) hrank.1
    rw [complexOfRealMatrix_matrixMul] at h
    simpa [complexMatrixMul] using h
  · have h := congrArg (complexOfRealMatrix (Node := Node)) hAP
    rw [complexOfRealMatrix_matrixMul] at h
    simpa [complexMatrixMul, complexOfRealMatrix] using h
  · have h := congrArg (complexOfRealMatrix (Node := Node)) hPA
    rw [complexOfRealMatrix_matrixMul] at h
    simpa [complexMatrixMul, complexOfRealMatrix] using h

theorem fixed_circle_base_resolvent_det_ne_zero_of_ne_unit
    [DecidableEq Node]
    (A0 : NodeMatrix Node) (baseRadius : ℝ)
    (hbaseEnclosedSpectrum :
      IsComplexRightEigenvalue (Node := Node) A0 (1 : ℂ) ∧
        ∀ z : ℂ, IsComplexRightEigenvalue (Node := Node) A0 z →
          (‖z - (1 : ℂ)‖ < baseRadius ↔ z = (1 : ℂ)) ∧
            (‖z - (1 : ℂ)‖ ≤ baseRadius ↔ z = (1 : ℂ)))
    (z : ℂ) (hzclosed : ‖z - (1 : ℂ)‖ ≤ baseRadius)
    (hz_ne_one : z ≠ (1 : ℂ)) :
    Matrix.det (complexResolventMatrix (Node := Node) A0 z) ≠ 0 := by
  classical
  exact complexResolvent_det_ne_zero_of_not_eigen (Node := Node) A0 z (by
    intro heig
    exact hz_ne_one ((hbaseEnclosedSpectrum.2 z heig).2.1 hzclosed))

theorem fixed_circle_base_resolvent_det_ne_zero_on_boundary
    [DecidableEq Node]
    (A0 : NodeMatrix Node) (baseRadius : ℝ)
    (hbaseNoBoundary :
      ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
        ¬ IsComplexRightEigenvalue (Node := Node) A0 z)
    (z : ℂ) (hzboundary : ‖z - (1 : ℂ)‖ = baseRadius) :
    Matrix.det (complexResolventMatrix (Node := Node) A0 z) ≠ 0 := by
  classical
  exact complexResolvent_det_ne_zero_of_not_eigen (Node := Node) A0 z
    (hbaseNoBoundary z hzboundary)

theorem complex_resolvent_inverse_identity_two_points
    [DecidableEq Node]
    (A0 : NodeMatrix Node) (z w : ℂ)
    (hz : ¬ IsComplexRightEigenvalue (Node := Node) A0 z)
    (hw : ¬ IsComplexRightEigenvalue (Node := Node) A0 w) :
    (complexResolventMatrix (Node := Node) A0 z)⁻¹ -
        (complexResolventMatrix (Node := Node) A0 w)⁻¹ =
      (w - z) •
        ((complexResolventMatrix (Node := Node) A0 z)⁻¹ *
          (complexResolventMatrix (Node := Node) A0 w)⁻¹) := by
  classical
  let Mz : ComplexNodeMatrix Node := complexResolventMatrix (Node := Node) A0 z
  let Mw : ComplexNodeMatrix Node := complexResolventMatrix (Node := Node) A0 w
  have hdetz : Matrix.det Mz ≠ 0 := by
    simpa [Mz] using
      complexResolvent_det_ne_zero_of_not_eigen (Node := Node) A0 z hz
  have hdetw : Matrix.det Mw ≠ 0 := by
    simpa [Mw] using
      complexResolvent_det_ne_zero_of_not_eigen (Node := Node) A0 w hw
  have hMzUnit : IsUnit Mz :=
    (Matrix.isUnit_iff_isUnit_det Mz).2 (isUnit_iff_ne_zero.mpr hdetz)
  have hMwUnit : IsUnit Mw :=
    (Matrix.isUnit_iff_isUnit_det Mw).2 (isUnit_iff_ne_zero.mpr hdetw)
  have hunits : IsUnit Mz ↔ IsUnit Mw := ⟨fun _ => hMwUnit, fun _ => hMzUnit⟩
  have hdiff_inv :
      Mz⁻¹ - Mw⁻¹ = Mz⁻¹ * (Mw - Mz) * Mw⁻¹ :=
    Matrix.inv_sub_inv (A := Mz) (B := Mw) hunits
  have hdiff_matrix :
      Mw - Mz = (w - z) • (1 : ComplexNodeMatrix Node) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Mz, Mw, complexResolventMatrix, complexMatrixSub,
        complexIdentityMatrix, complexOfRealMatrix]
    · simp [Mz, Mw, complexResolventMatrix, complexMatrixSub,
        complexIdentityMatrix, complexOfRealMatrix, hij]
  have hscalar :
      Mz⁻¹ * ((w - z) • (1 : ComplexNodeMatrix Node)) * Mw⁻¹ =
        (w - z) • (Mz⁻¹ * Mw⁻¹) := by
    ext i j
    simp [Matrix.mul_apply, Finset.mul_sum]
    ring
  calc
    (complexResolventMatrix (Node := Node) A0 z)⁻¹ -
        (complexResolventMatrix (Node := Node) A0 w)⁻¹ =
        Mz⁻¹ - Mw⁻¹ := rfl
    _ = Mz⁻¹ * (Mw - Mz) * Mw⁻¹ := hdiff_inv
    _ = Mz⁻¹ * ((w - z) • (1 : ComplexNodeMatrix Node)) * Mw⁻¹ := by
          rw [hdiff_matrix]
    _ = (w - z) • (Mz⁻¹ * Mw⁻¹) := hscalar
    _ = (w - z) •
        ((complexResolventMatrix (Node := Node) A0 z)⁻¹ *
          (complexResolventMatrix (Node := Node) A0 w)⁻¹) := rfl

theorem complex_resolvent_inverse_product_entry_eq_div_difference
    [DecidableEq Node]
    (A0 : NodeMatrix Node) (z w : ℂ)
    (hz : ¬ IsComplexRightEigenvalue (Node := Node) A0 z)
    (hw : ¬ IsComplexRightEigenvalue (Node := Node) A0 w)
    (hwz : w ≠ z) (i j : Node) :
    (∑ k : Node,
        ((complexResolventMatrix (Node := Node) A0 z)⁻¹) i k *
          ((complexResolventMatrix (Node := Node) A0 w)⁻¹) k j) =
      (w - z)⁻¹ *
        (((complexResolventMatrix (Node := Node) A0 z)⁻¹) i j -
          ((complexResolventMatrix (Node := Node) A0 w)⁻¹) i j) := by
  classical
  let Rz : ComplexNodeMatrix Node :=
    (complexResolventMatrix (Node := Node) A0 z)⁻¹
  let Rw : ComplexNodeMatrix Node :=
    (complexResolventMatrix (Node := Node) A0 w)⁻¹
  have hidentity :
      Rz - Rw = (w - z) • (Rz * Rw) := by
    simpa [Rz, Rw] using
      complex_resolvent_inverse_identity_two_points (Node := Node)
        A0 z w hz hw
  have hentry :
      Rz i j - Rw i j =
        (w - z) *
          (∑ k : Node, Rz i k * Rw k j) := by
    have h := congrArg (fun M : ComplexNodeMatrix Node => M i j) hidentity
    simpa [Matrix.sub_apply, Matrix.mul_apply, Pi.smul_apply, smul_eq_mul]
      using h
  have hsub_ne : w - z ≠ 0 := sub_ne_zero.mpr hwz
  calc
    (∑ k : Node, Rz i k * Rw k j) =
        (w - z)⁻¹ * ((w - z) *
          (∑ k : Node, Rz i k * Rw k j)) := by
          field_simp [hsub_ne]
    _ = (w - z)⁻¹ * (Rz i j - Rw i j) := by
          rw [← hentry]
    _ =
      (w - z)⁻¹ *
        (((complexResolventMatrix (Node := Node) A0 z)⁻¹) i j -
          ((complexResolventMatrix (Node := Node) A0 w)⁻¹) i j) := by
          simp [Rz, Rw]

def complexConjMatrix (M : ComplexNodeMatrix Node) :
    ComplexNodeMatrix Node :=
  fun i j => conj (M i j)

theorem complexConjMatrix_one [DecidableEq Node] :
    complexConjMatrix (Node := Node) (1 : ComplexNodeMatrix Node) = 1 := by
  classical
  funext i j
  by_cases hij : i = j
  · subst j
    simp [complexConjMatrix]
  · simp [complexConjMatrix, Matrix.one_apply, hij]

theorem complexConjMatrix_mul [DecidableEq Node]
    (M N : ComplexNodeMatrix Node) :
    complexConjMatrix (Node := Node) (M * N) =
      complexConjMatrix (Node := Node) M *
        complexConjMatrix (Node := Node) N := by
  classical
  funext i j
  calc
    complexConjMatrix (Node := Node) (M * N) i j =
        conj (∑ k : Node, M i k * N k j) := by
          simp [complexConjMatrix, Matrix.mul_apply]
    _ = ∑ k : Node, conj (M i k * N k j) := by
          simpa using
            (map_sum Complex.conjAe (fun k : Node => M i k * N k j)
              Finset.univ)
    _ = (complexConjMatrix (Node := Node) M *
          complexConjMatrix (Node := Node) N) i j := by
          simp [complexConjMatrix, Matrix.mul_apply]

theorem complexConjMatrix_resolvent
    (A0 : NodeMatrix Node) (z : ℂ) :
    complexConjMatrix (Node := Node)
        (complexResolventMatrix (Node := Node) A0 z) =
      complexResolventMatrix (Node := Node) A0 (conj z) := by
  classical
  funext i j
  by_cases hij : i = j
  · subst j
    simp [complexConjMatrix, complexResolventMatrix, complexMatrixSub,
      complexIdentityMatrix, complexOfRealMatrix]
  · simp [complexConjMatrix, complexResolventMatrix, complexMatrixSub,
      complexIdentityMatrix, complexOfRealMatrix, hij]

theorem fixed_unit_circle_conj_boundary
    (baseRadius : ℝ) {z : ℂ}
    (hz : ‖z - (1 : ℂ)‖ = baseRadius) :
    ‖conj z - (1 : ℂ)‖ = baseRadius := by
  calc
    ‖conj z - (1 : ℂ)‖ = ‖conj (z - (1 : ℂ))‖ := by
      rw [map_sub]
      simp
    _ = ‖z - (1 : ℂ)‖ := Complex.norm_conj _
    _ = baseRadius := hz

theorem fixed_circleMap_boundary_norm
    (baseRadius : ℝ) (hbaseRadius_pos : 0 < baseRadius) (theta : ℝ) :
    ‖circleMap (1 : ℂ) baseRadius theta - (1 : ℂ)‖ = baseRadius := by
  have hmem :
      circleMap (1 : ℂ) baseRadius theta ∈
        Metric.sphere (1 : ℂ) baseRadius :=
    circleMap_mem_sphere (1 : ℂ) (le_of_lt hbaseRadius_pos) theta
  simpa [Metric.mem_sphere, dist_eq_norm] using hmem

theorem fixed_circleMap_outer_not_mem_closedBall_inner
    {innerRadius outerRadius : ℝ}
    (hinner_pos : 0 < innerRadius) (hradii : innerRadius < outerRadius)
    (theta : ℝ) :
    circleMap (1 : ℂ) outerRadius theta ∉
      Metric.closedBall (1 : ℂ) innerRadius := by
  intro hmem
  have houter_pos : 0 < outerRadius := lt_trans hinner_pos hradii
  have hdist_outer :
      dist (circleMap (1 : ℂ) outerRadius theta) (1 : ℂ) =
        outerRadius := by
    simpa [dist_eq_norm] using
      fixed_circleMap_boundary_norm outerRadius houter_pos theta
  have hdist_le :
      dist (circleMap (1 : ℂ) outerRadius theta) (1 : ℂ) ≤
        innerRadius :=
    Metric.mem_closedBall.mp hmem
  linarith

theorem fixed_circleMap_inner_mem_ball_outer
    {innerRadius outerRadius : ℝ}
    (hinner_nonneg : 0 ≤ innerRadius) (hradii : innerRadius < outerRadius)
    (phi : ℝ) :
    circleMap (1 : ℂ) innerRadius phi ∈
      Metric.ball (1 : ℂ) outerRadius := by
  have hdist_inner :
      dist (circleMap (1 : ℂ) innerRadius phi) (1 : ℂ) =
        innerRadius := by
    by_cases hinner_pos : 0 < innerRadius
    · simpa [dist_eq_norm] using
        fixed_circleMap_boundary_norm innerRadius hinner_pos phi
    · have hinner_zero : innerRadius = 0 := by linarith
      simp [hinner_zero, circleMap, dist_self]
  exact Metric.mem_ball.mpr (by linarith)

theorem fixed_circleIntegral_inner_sub_outer_point_mul_const_eq_zero
    {innerRadius outerRadius : ℝ}
    (hinner_pos : 0 < innerRadius) (hradii : innerRadius < outerRadius)
    (theta : ℝ) (c : ℂ) :
    (∮ w in C((1 : ℂ), innerRadius),
        (w - circleMap (1 : ℂ) outerRadius theta)⁻¹ * c) = 0 := by
  exact circleIntegral_sub_inv_mul_const_eq_zero_of_not_mem_closedBall
    (center := (1 : ℂ)) (pole := circleMap (1 : ℂ) outerRadius theta)
    (radius := innerRadius) (le_of_lt hinner_pos)
    (fixed_circleMap_outer_not_mem_closedBall_inner hinner_pos hradii theta) c

theorem fixed_circleIntegral_outer_inner_point_sub_mul_const_eq_neg
    {innerRadius outerRadius : ℝ}
    (hinner_nonneg : 0 ≤ innerRadius) (hradii : innerRadius < outerRadius)
    (phi : ℝ) (c : ℂ) :
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ z in C((1 : ℂ), outerRadius),
          (circleMap (1 : ℂ) innerRadius phi - z)⁻¹ * c) = -c := by
  exact circleIntegral_w_sub_inv_mul_const_eq_neg_of_mem_ball
    (center := (1 : ℂ)) (pole := circleMap (1 : ℂ) innerRadius phi)
    (radius := outerRadius)
    (fixed_circleMap_inner_mem_ball_outer hinner_nonneg hradii phi) c

theorem fixed_circleParameter_inner_sub_outer_point_mul_const_eq_zero
    {innerRadius outerRadius : ℝ}
    (hinner_pos : 0 < innerRadius) (hradii : innerRadius < outerRadius)
    (theta : ℝ) (c : ℂ) :
    (∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
        deriv (circleMap (1 : ℂ) innerRadius) phi *
          ((circleMap (1 : ℂ) innerRadius phi -
              circleMap (1 : ℂ) outerRadius theta)⁻¹ * c)) = 0 := by
  have hcircle :=
    fixed_circleIntegral_inner_sub_outer_point_mul_const_eq_zero
      (innerRadius := innerRadius) (outerRadius := outerRadius)
      hinner_pos hradii theta c
  rw [circleIntegral_eq_Icc_integral_deriv_mul] at hcircle
  simpa [mul_assoc] using hcircle

theorem fixed_circleParameter_outer_inner_point_sub_mul_const_eq_neg
    {innerRadius outerRadius : ℝ}
    (hinner_nonneg : 0 ≤ innerRadius) (hradii : innerRadius < outerRadius)
    (phi : ℝ) (c : ℂ) :
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
      (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
        deriv (circleMap (1 : ℂ) outerRadius) theta *
          ((circleMap (1 : ℂ) innerRadius phi -
              circleMap (1 : ℂ) outerRadius theta)⁻¹ * c)) = -c := by
  have hcircle :=
    fixed_circleIntegral_outer_inner_point_sub_mul_const_eq_neg
      (innerRadius := innerRadius) (outerRadius := outerRadius)
      hinner_nonneg hradii phi c
  rw [circleIntegral_eq_Icc_integral_deriv_mul] at hcircle
  simpa [mul_assoc] using hcircle

theorem fixed_zero_circleMap_conj
    (baseRadius theta : ℝ) :
    conj (circleMap (0 : ℂ) baseRadius theta) =
      circleMap (0 : ℂ) baseRadius (-theta) := by
  rw [circleMap, circleMap]
  simp only [zero_add, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 1
  apply congrArg Complex.exp
  simp

theorem fixed_circleMap_conj
    (baseRadius theta : ℝ) :
    conj (circleMap (1 : ℂ) baseRadius theta) =
      circleMap (1 : ℂ) baseRadius (-theta) := by
  rw [circleMap, circleMap]
  simp only [map_add, map_one, map_mul, Complex.conj_ofReal,
    ← Complex.exp_conj]
  congr 2
  apply congrArg Complex.exp
  simp

theorem fixed_circleMap_deriv_conj
    (baseRadius theta : ℝ) :
    conj (deriv (circleMap (1 : ℂ) baseRadius) theta) =
      -deriv (circleMap (1 : ℂ) baseRadius) (-theta) := by
  calc
    conj (deriv (circleMap (1 : ℂ) baseRadius) theta) =
        conj (circleMap (0 : ℂ) baseRadius theta * Complex.I) := by
          exact congrArg conj (deriv_circleMap (1 : ℂ) baseRadius theta)
    _ =
        conj (circleMap (0 : ℂ) baseRadius theta) * conj Complex.I := by
          rw [map_mul]
    _ = circleMap (0 : ℂ) baseRadius (-theta) * (-Complex.I) := by
          rw [fixed_zero_circleMap_conj]
          simp
    _ = -(circleMap (0 : ℂ) baseRadius (-theta) * Complex.I) := by
          ring
    _ = -deriv (circleMap (1 : ℂ) baseRadius) (-theta) := by
          exact congrArg (fun z : ℂ => -z)
            (deriv_circleMap (1 : ℂ) baseRadius (-theta)).symm

theorem complex_Icc_integral_conj
    (l u : ℝ) (f : ℝ → ℂ) :
    conj (∫ theta in Set.Icc l u, f theta) =
      ∫ theta in Set.Icc l u, conj (f theta) := by
  simpa using
    (integral_conj
      (μ := volume.restrict (Set.Icc l u)) (f := f)).symm

theorem complex_setIntegral_Icc_eq_intervalIntegral
    (l u : ℝ) (f : ℝ → ℂ) (hlu : l ≤ u) :
    (∫ theta in Set.Icc l u, f theta) =
      ∫ theta in l..u, f theta := by
  rw [intervalIntegral.integral_of_le hlu,
    MeasureTheory.integral_Icc_eq_integral_Ioc]

theorem complex_setIntegral_Icc_Icc_swap_of_continuousOn
    (a b c d : ℝ) (F : ℝ → ℝ → ℂ)
    (hF :
      ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
        (Set.Icc a b ×ˢ Set.Icc c d)) :
    (∫ x in Set.Icc a b, ∫ y in Set.Icc c d, F x y) =
      ∫ y in Set.Icc c d, ∫ x in Set.Icc a b, F x y := by
  classical
  let s : Set ℝ := Set.Icc a b
  let t : Set ℝ := Set.Icc c d
  let G : ℝ × ℝ → ℂ := fun p => F p.1 p.2
  have hcompact : IsCompact (s ×ˢ t) := by
    simpa [s, t] using (isCompact_Icc.prod isCompact_Icc)
  have hmeas : MeasurableSet (s ×ˢ t) := hcompact.measurableSet
  have hfinite : volume (s ×ˢ t) < ⊤ := hcompact.measure_lt_top
  have hGintOn : IntegrableOn G (s ×ˢ t) volume :=
    hF.integrableOn_of_subset_isCompact
      (μ := volume) (K := s ×ˢ t) hcompact hmeas
      (fun p hp => hp) (ne_of_lt hfinite)
  have hGint :
      Integrable (fun p : ℝ × ℝ => G p)
        ((volume.restrict s).prod (volume.restrict t)) := by
    rw [Measure.prod_restrict]
    simpa [IntegrableOn, G] using hGintOn
  calc
    (∫ x in Set.Icc a b, ∫ y in Set.Icc c d, F x y) =
        ∫ x, ∫ y, G (x, y) ∂(volume.restrict t) ∂(volume.restrict s) := by
          simp [s, t, G]
    _ =
        ∫ y, ∫ x, G (x, y) ∂(volume.restrict s) ∂(volume.restrict t) := by
          simpa [G] using
            (MeasureTheory.integral_integral_swap
              (μ := volume.restrict s) (ν := volume.restrict t)
              (f := fun x y => G (x, y)) hGint)
    _ = ∫ y in Set.Icc c d, ∫ x in Set.Icc a b, F x y := by
          simp [s, t, G]

theorem complex_circleParameter_Icc_integral_swap_of_continuousOn
    (center : ℂ) (outerRadius innerRadius : ℝ) (F : ℂ → ℂ → ℂ)
    (hF :
      ContinuousOn
        (fun p : ℝ × ℝ =>
          deriv (circleMap center outerRadius) p.1 *
            (deriv (circleMap center innerRadius) p.2 *
              F (circleMap center outerRadius p.1)
                (circleMap center innerRadius p.2)))
        (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
          Set.Icc (0 : ℝ) (2 * Real.pi))) :
    (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
        deriv (circleMap center outerRadius) theta *
          (∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
            deriv (circleMap center innerRadius) phi *
              F (circleMap center outerRadius theta)
                (circleMap center innerRadius phi))) =
      ∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
        deriv (circleMap center innerRadius) phi *
          (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
            deriv (circleMap center outerRadius) theta *
              F (circleMap center outerRadius theta)
                (circleMap center innerRadius phi)) := by
  classical
  let H : ℝ → ℝ → ℂ := fun theta phi =>
    deriv (circleMap center outerRadius) theta *
      (deriv (circleMap center innerRadius) phi *
        F (circleMap center outerRadius theta)
          (circleMap center innerRadius phi))
  have hswap :
      (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
          ∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi), H theta phi) =
        ∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
          ∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi), H theta phi :=
    complex_setIntegral_Icc_Icc_swap_of_continuousOn
      (0 : ℝ) (2 * Real.pi) (0 : ℝ) (2 * Real.pi) H (by
        simpa [H] using hF)
  calc
    (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
        deriv (circleMap center outerRadius) theta *
          (∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
            deriv (circleMap center innerRadius) phi *
              F (circleMap center outerRadius theta)
                (circleMap center innerRadius phi))) =
        ∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
          ∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi), H theta phi := by
          refine MeasureTheory.setIntegral_congr_fun isCompact_Icc.measurableSet ?_
          intro theta _htheta
          dsimp only
          simpa [H] using
            (MeasureTheory.integral_const_mul
              (μ := volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi)))
              (deriv (circleMap center outerRadius) theta)
              (fun phi : ℝ =>
                deriv (circleMap center innerRadius) phi *
                  F (circleMap center outerRadius theta)
                    (circleMap center innerRadius phi))).symm
    _ = ∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
          ∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi), H theta phi := hswap
    _ =
      ∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
        deriv (circleMap center innerRadius) phi *
          (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
            deriv (circleMap center outerRadius) theta *
              F (circleMap center outerRadius theta)
                (circleMap center innerRadius phi)) := by
          refine MeasureTheory.setIntegral_congr_fun isCompact_Icc.measurableSet ?_
          intro phi _hphi
          dsimp only
          rw [show
              (fun theta : ℝ => H theta phi) =
                fun theta : ℝ =>
                  deriv (circleMap center innerRadius) phi *
                    (deriv (circleMap center outerRadius) theta *
                      F (circleMap center outerRadius theta)
                        (circleMap center innerRadius phi)) by
            funext theta
            simp [H]
            ring]
          simpa using
            (MeasureTheory.integral_const_mul
              (μ := volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi)))
              (deriv (circleMap center innerRadius) phi)
              (fun theta : ℝ =>
                deriv (circleMap center outerRadius) theta *
                  F (circleMap center outerRadius theta)
                    (circleMap center innerRadius phi)))

theorem separated_resolvent_product_circleParameter_continuousOn
    [DecidableEq Node]
    (Aalpha : NodeMatrix Node) {innerRadius outerRadius : ℝ}
    (hinner_pos : 0 < innerRadius) (hradii : innerRadius ≤ outerRadius)
    (hnoAnnulus :
      ∀ z : ℂ, innerRadius ≤ ‖z - (1 : ℂ)‖ →
        ‖z - (1 : ℂ)‖ ≤ outerRadius →
          ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z)
    (i j : Node) :
    ContinuousOn
      (fun p : ℝ × ℝ =>
        deriv (circleMap (1 : ℂ) outerRadius) p.1 *
          (deriv (circleMap (1 : ℂ) innerRadius) p.2 *
            (∑ k : Node,
              ((complexResolventMatrix (Node := Node) Aalpha
                  (circleMap (1 : ℂ) outerRadius p.1))⁻¹) i k *
                ((complexResolventMatrix (Node := Node) Aalpha
                  (circleMap (1 : ℂ) innerRadius p.2))⁻¹) k j)))
      (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
        Set.Icc (0 : ℝ) (2 * Real.pi)) := by
  classical
  let rect : Set (ℝ × ℝ) :=
    Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
      Set.Icc (0 : ℝ) (2 * Real.pi)
  have houter_pos : 0 < outerRadius := lt_of_lt_of_le hinner_pos hradii
  have houter_entry :
      ∀ k : Node,
        ContinuousOn
          (fun p : ℝ × ℝ =>
            ((complexResolventMatrix (Node := Node) Aalpha
                (circleMap (1 : ℂ) outerRadius p.1))⁻¹) i k)
          rect := by
    intro k p hp
    have hz_norm :
        ‖circleMap (1 : ℂ) outerRadius p.1 - (1 : ℂ)‖ =
          outerRadius :=
      fixed_circleMap_boundary_norm outerRadius houter_pos p.1
    have hdet :
        Matrix.det
          (complexResolventMatrix (Node := Node) Aalpha
            (circleMap (1 : ℂ) outerRadius p.1)) ≠ 0 := by
      exact complexResolvent_det_ne_zero_of_not_eigen (Node := Node)
        Aalpha (circleMap (1 : ℂ) outerRadius p.1)
        (hnoAnnulus (circleMap (1 : ℂ) outerRadius p.1)
          (by
            rw [hz_norm]
            exact hradii)
          (by
            rw [hz_norm]))
    have hentry_cont :
        ContinuousAt
          (fun z : ℂ =>
            ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i k)
          (circleMap (1 : ℂ) outerRadius p.1) :=
      (complex_resolvent_inv_entry_differentiableAt_z_of_det_ne_zero
        (Node := Node) Aalpha hdet i k).continuousAt
    have hcircle_cont :
        ContinuousWithinAt
          (fun q : ℝ × ℝ => circleMap (1 : ℂ) outerRadius q.1)
          rect p := by
      exact (continuous_circleMap (1 : ℂ) outerRadius).continuousAt
        |>.comp_continuousWithinAt continuousWithinAt_fst
    exact ContinuousAt.comp_continuousWithinAt
      (f := fun q : ℝ × ℝ => circleMap (1 : ℂ) outerRadius q.1)
      hentry_cont hcircle_cont
  have hinner_entry :
      ∀ k : Node,
        ContinuousOn
          (fun p : ℝ × ℝ =>
            ((complexResolventMatrix (Node := Node) Aalpha
                (circleMap (1 : ℂ) innerRadius p.2))⁻¹) k j)
          rect := by
    intro k p hp
    have hz_norm :
        ‖circleMap (1 : ℂ) innerRadius p.2 - (1 : ℂ)‖ =
          innerRadius :=
      fixed_circleMap_boundary_norm innerRadius hinner_pos p.2
    have hdet :
        Matrix.det
          (complexResolventMatrix (Node := Node) Aalpha
            (circleMap (1 : ℂ) innerRadius p.2)) ≠ 0 := by
      exact complexResolvent_det_ne_zero_of_not_eigen (Node := Node)
        Aalpha (circleMap (1 : ℂ) innerRadius p.2)
        (hnoAnnulus (circleMap (1 : ℂ) innerRadius p.2)
          (by
            rw [hz_norm])
          (by
            rw [hz_norm]
            exact hradii))
    have hentry_cont :
        ContinuousAt
          (fun z : ℂ =>
            ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) k j)
          (circleMap (1 : ℂ) innerRadius p.2) :=
      (complex_resolvent_inv_entry_differentiableAt_z_of_det_ne_zero
        (Node := Node) Aalpha hdet k j).continuousAt
    have hcircle_cont :
        ContinuousWithinAt
          (fun q : ℝ × ℝ => circleMap (1 : ℂ) innerRadius q.2)
          rect p := by
      exact (continuous_circleMap (1 : ℂ) innerRadius).continuousAt
        |>.comp_continuousWithinAt continuousWithinAt_snd
    exact ContinuousAt.comp_continuousWithinAt
      (f := fun q : ℝ × ℝ => circleMap (1 : ℂ) innerRadius q.2)
      hentry_cont hcircle_cont
  have hsum :
      ContinuousOn
        (fun p : ℝ × ℝ =>
          ∑ k : Node,
            ((complexResolventMatrix (Node := Node) Aalpha
                (circleMap (1 : ℂ) outerRadius p.1))⁻¹) i k *
              ((complexResolventMatrix (Node := Node) Aalpha
                (circleMap (1 : ℂ) innerRadius p.2))⁻¹) k j)
        rect := by
    refine continuousOn_finset_sum Finset.univ ?_
    intro k _hk
    exact (houter_entry k).mul (hinner_entry k)
  have hderivOuter :
      ContinuousOn
        (fun p : ℝ × ℝ => deriv (circleMap (1 : ℂ) outerRadius) p.1)
        rect := by
    have hderivTheta :
        Continuous
          (fun theta : ℝ => deriv (circleMap (1 : ℂ) outerRadius) theta) := by
      exact circleMap_deriv_continuous (1 : ℂ) outerRadius
    simpa using (hderivTheta.comp continuous_fst).continuousOn
  have hderivInner :
      ContinuousOn
        (fun p : ℝ × ℝ => deriv (circleMap (1 : ℂ) innerRadius) p.2)
        rect := by
    have hderivTheta :
        Continuous
          (fun theta : ℝ => deriv (circleMap (1 : ℂ) innerRadius) theta) := by
      exact circleMap_deriv_continuous (1 : ℂ) innerRadius
    simpa using (hderivTheta.comp continuous_snd).continuousOn
  simpa [rect] using hderivOuter.mul (hderivInner.mul hsum)

theorem separated_resolvent_product_circleParameter_eq_div_difference
    [DecidableEq Node]
    (Aalpha : NodeMatrix Node) {innerRadius outerRadius : ℝ}
    (hinner_pos : 0 < innerRadius) (hradii : innerRadius < outerRadius)
    (hnoAnnulus :
      ∀ z : ℂ, innerRadius ≤ ‖z - (1 : ℂ)‖ →
        ‖z - (1 : ℂ)‖ ≤ outerRadius →
          ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z)
    (theta phi : ℝ) (i j : Node) :
    (∑ k : Node,
        ((complexResolventMatrix (Node := Node) Aalpha
            (circleMap (1 : ℂ) outerRadius theta))⁻¹) i k *
          ((complexResolventMatrix (Node := Node) Aalpha
            (circleMap (1 : ℂ) innerRadius phi))⁻¹) k j) =
      (circleMap (1 : ℂ) innerRadius phi -
          circleMap (1 : ℂ) outerRadius theta)⁻¹ *
        (((complexResolventMatrix (Node := Node) Aalpha
            (circleMap (1 : ℂ) outerRadius theta))⁻¹) i j -
          ((complexResolventMatrix (Node := Node) Aalpha
            (circleMap (1 : ℂ) innerRadius phi))⁻¹) i j) := by
  classical
  have houter_pos : 0 < outerRadius := lt_trans hinner_pos hradii
  have houter_norm :
      ‖circleMap (1 : ℂ) outerRadius theta - (1 : ℂ)‖ =
        outerRadius :=
    fixed_circleMap_boundary_norm outerRadius houter_pos theta
  have hinner_norm :
      ‖circleMap (1 : ℂ) innerRadius phi - (1 : ℂ)‖ =
        innerRadius :=
    fixed_circleMap_boundary_norm innerRadius hinner_pos phi
  have houter_not :
      ¬ IsComplexRightEigenvalue (Node := Node) Aalpha
        (circleMap (1 : ℂ) outerRadius theta) := by
    exact hnoAnnulus (circleMap (1 : ℂ) outerRadius theta)
      (by
        rw [houter_norm]
        exact le_of_lt hradii)
      (by rw [houter_norm])
  have hinner_not :
      ¬ IsComplexRightEigenvalue (Node := Node) Aalpha
        (circleMap (1 : ℂ) innerRadius phi) := by
    exact hnoAnnulus (circleMap (1 : ℂ) innerRadius phi)
      (by rw [hinner_norm])
      (by
        rw [hinner_norm]
        exact le_of_lt hradii)
  have hneq :
      circleMap (1 : ℂ) innerRadius phi ≠
        circleMap (1 : ℂ) outerRadius theta := by
    intro hsame
    have hnorm_eq : innerRadius = outerRadius := by
      rw [← hinner_norm, hsame, houter_norm]
    exact (ne_of_lt hradii) hnorm_eq
  exact
    complex_resolvent_inverse_product_entry_eq_div_difference
      (Node := Node) Aalpha
      (circleMap (1 : ℂ) outerRadius theta)
      (circleMap (1 : ℂ) innerRadius phi)
      houter_not hinner_not hneq i j

theorem separated_inner_resolvent_cauchy_circleParameter_continuousOn
    [DecidableEq Node]
    (Aalpha : NodeMatrix Node) {innerRadius outerRadius : ℝ}
    (hinner_pos : 0 < innerRadius) (hradii : innerRadius < outerRadius)
    (hnoAnnulus :
      ∀ z : ℂ, innerRadius ≤ ‖z - (1 : ℂ)‖ →
        ‖z - (1 : ℂ)‖ ≤ outerRadius →
          ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z)
    (i j : Node) :
    ContinuousOn
      (fun p : ℝ × ℝ =>
        deriv (circleMap (1 : ℂ) outerRadius) p.1 *
          (deriv (circleMap (1 : ℂ) innerRadius) p.2 *
            ((circleMap (1 : ℂ) innerRadius p.2 -
                circleMap (1 : ℂ) outerRadius p.1)⁻¹ *
              ((complexResolventMatrix (Node := Node) Aalpha
                (circleMap (1 : ℂ) innerRadius p.2))⁻¹) i j)))
      (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
        Set.Icc (0 : ℝ) (2 * Real.pi)) := by
  classical
  let rect : Set (ℝ × ℝ) :=
    Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
      Set.Icc (0 : ℝ) (2 * Real.pi)
  have houter_pos : 0 < outerRadius := lt_trans hinner_pos hradii
  have hden_ne :
      ∀ p : ℝ × ℝ, p ∈ rect →
        circleMap (1 : ℂ) innerRadius p.2 -
            circleMap (1 : ℂ) outerRadius p.1 ≠ 0 := by
    intro p _hp hzero
    have hsame :
        circleMap (1 : ℂ) innerRadius p.2 =
          circleMap (1 : ℂ) outerRadius p.1 := sub_eq_zero.mp hzero
    have hinner_norm :
        ‖circleMap (1 : ℂ) innerRadius p.2 - (1 : ℂ)‖ =
          innerRadius :=
      fixed_circleMap_boundary_norm innerRadius hinner_pos p.2
    have houter_norm :
        ‖circleMap (1 : ℂ) outerRadius p.1 - (1 : ℂ)‖ =
          outerRadius :=
      fixed_circleMap_boundary_norm outerRadius houter_pos p.1
    have hnorm_eq : innerRadius = outerRadius := by
      rw [← hinner_norm, hsame, houter_norm]
    exact (ne_of_lt hradii) hnorm_eq
  have hsub :
      ContinuousOn
        (fun p : ℝ × ℝ =>
          circleMap (1 : ℂ) innerRadius p.2 -
            circleMap (1 : ℂ) outerRadius p.1)
        rect := by
    fun_prop
  have hinv :
      ContinuousOn
        (fun p : ℝ × ℝ =>
          (circleMap (1 : ℂ) innerRadius p.2 -
            circleMap (1 : ℂ) outerRadius p.1)⁻¹)
        rect := by
    intro p hp
    exact ContinuousAt.comp_continuousWithinAt
      (f := fun q : ℝ × ℝ =>
        circleMap (1 : ℂ) innerRadius q.2 -
          circleMap (1 : ℂ) outerRadius q.1)
      (continuousAt_inv₀ (hden_ne p hp)) (hsub p hp)
  have hinner_entry :
      ContinuousOn
        (fun p : ℝ × ℝ =>
          ((complexResolventMatrix (Node := Node) Aalpha
            (circleMap (1 : ℂ) innerRadius p.2))⁻¹) i j)
        rect := by
    intro p hp
    have hz_norm :
        ‖circleMap (1 : ℂ) innerRadius p.2 - (1 : ℂ)‖ =
          innerRadius :=
      fixed_circleMap_boundary_norm innerRadius hinner_pos p.2
    have hdet :
        Matrix.det
          (complexResolventMatrix (Node := Node) Aalpha
            (circleMap (1 : ℂ) innerRadius p.2)) ≠ 0 := by
      exact complexResolvent_det_ne_zero_of_not_eigen (Node := Node)
        Aalpha (circleMap (1 : ℂ) innerRadius p.2)
        (hnoAnnulus (circleMap (1 : ℂ) innerRadius p.2)
          (by rw [hz_norm])
          (by
            rw [hz_norm]
            exact le_of_lt hradii))
    have hentry_cont :
        ContinuousAt
          (fun z : ℂ =>
            ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i j)
          (circleMap (1 : ℂ) innerRadius p.2) :=
      (complex_resolvent_inv_entry_differentiableAt_z_of_det_ne_zero
        (Node := Node) Aalpha hdet i j).continuousAt
    have hcircle_cont :
        ContinuousWithinAt
          (fun q : ℝ × ℝ => circleMap (1 : ℂ) innerRadius q.2)
          rect p := by
      exact (continuous_circleMap (1 : ℂ) innerRadius).continuousAt
        |>.comp_continuousWithinAt continuousWithinAt_snd
    exact ContinuousAt.comp_continuousWithinAt
      (f := fun q : ℝ × ℝ => circleMap (1 : ℂ) innerRadius q.2)
      hentry_cont hcircle_cont
  have hderivOuter :
      ContinuousOn
        (fun p : ℝ × ℝ => deriv (circleMap (1 : ℂ) outerRadius) p.1)
        rect := by
    have hderivTheta :
        Continuous
          (fun theta : ℝ => deriv (circleMap (1 : ℂ) outerRadius) theta) := by
      exact circleMap_deriv_continuous (1 : ℂ) outerRadius
    simpa using (hderivTheta.comp continuous_fst).continuousOn
  have hderivInner :
      ContinuousOn
        (fun p : ℝ × ℝ => deriv (circleMap (1 : ℂ) innerRadius) p.2)
        rect := by
    have hderivTheta :
        Continuous
          (fun theta : ℝ => deriv (circleMap (1 : ℂ) innerRadius) theta) := by
      exact circleMap_deriv_continuous (1 : ℂ) innerRadius
    simpa using (hderivTheta.comp continuous_snd).continuousOn
  have hkernel :
      ContinuousOn
        (fun p : ℝ × ℝ =>
          (circleMap (1 : ℂ) innerRadius p.2 -
              circleMap (1 : ℂ) outerRadius p.1)⁻¹ *
            ((complexResolventMatrix (Node := Node) Aalpha
              (circleMap (1 : ℂ) innerRadius p.2))⁻¹) i j)
        rect :=
    hinv.mul hinner_entry
  simpa [rect] using hderivOuter.mul (hderivInner.mul hkernel)

theorem separated_inner_resolvent_cauchy_outer_residue_integral_eq_neg
    [DecidableEq Node]
    (Aalpha : NodeMatrix Node) {innerRadius outerRadius : ℝ}
    (hinner_pos : 0 < innerRadius) (hradii : innerRadius < outerRadius)
    (i j : Node) :
    (∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
        deriv (circleMap (1 : ℂ) innerRadius) phi *
          ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
            (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
              deriv (circleMap (1 : ℂ) outerRadius) theta *
                ((circleMap (1 : ℂ) innerRadius phi -
                    circleMap (1 : ℂ) outerRadius theta)⁻¹ *
                  ((complexResolventMatrix (Node := Node) Aalpha
                    (circleMap (1 : ℂ) innerRadius phi))⁻¹) i j)))) =
      -∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
        deriv (circleMap (1 : ℂ) innerRadius) phi *
          ((complexResolventMatrix (Node := Node) Aalpha
            (circleMap (1 : ℂ) innerRadius phi))⁻¹) i j := by
  classical
  let c : ℂ := (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹)
  let Rinner : ℝ → ℂ := fun phi =>
    ((complexResolventMatrix (Node := Node) Aalpha
      (circleMap (1 : ℂ) innerRadius phi))⁻¹) i j
  have hpoint :
      ∀ phi : ℝ,
        c *
            (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
              deriv (circleMap (1 : ℂ) outerRadius) theta *
                ((circleMap (1 : ℂ) innerRadius phi -
                    circleMap (1 : ℂ) outerRadius theta)⁻¹ *
                  Rinner phi)) =
          -Rinner phi := by
    intro phi
    simpa [c, Rinner] using
      fixed_circleParameter_outer_inner_point_sub_mul_const_eq_neg
        (innerRadius := innerRadius) (outerRadius := outerRadius)
        (le_of_lt hinner_pos) hradii phi (Rinner phi)
  calc
    (∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
        deriv (circleMap (1 : ℂ) innerRadius) phi *
          ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
            (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
              deriv (circleMap (1 : ℂ) outerRadius) theta *
                ((circleMap (1 : ℂ) innerRadius phi -
                    circleMap (1 : ℂ) outerRadius theta)⁻¹ *
                  ((complexResolventMatrix (Node := Node) Aalpha
                    (circleMap (1 : ℂ) innerRadius phi))⁻¹) i j)))) =
        ∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
          deriv (circleMap (1 : ℂ) innerRadius) phi * (-Rinner phi) := by
          refine MeasureTheory.setIntegral_congr_fun isCompact_Icc.measurableSet ?_
          intro phi _hphi
          simpa [c, Rinner] using
            congrArg
              (fun x : ℂ =>
                deriv (circleMap (1 : ℂ) innerRadius) phi * x)
              (hpoint phi)
    _ =
        ∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
          -(deriv (circleMap (1 : ℂ) innerRadius) phi * Rinner phi) := by
          refine MeasureTheory.setIntegral_congr_fun isCompact_Icc.measurableSet ?_
          intro phi _hphi
          ring
    _ =
      -∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
        deriv (circleMap (1 : ℂ) innerRadius) phi *
          ((complexResolventMatrix (Node := Node) Aalpha
            (circleMap (1 : ℂ) innerRadius phi))⁻¹) i j := by
          rw [MeasureTheory.integral_neg]

theorem separated_outer_inner_resolvent_product_integral_eq_inner
    [DecidableEq Node]
    (Aalpha : NodeMatrix Node) {innerRadius outerRadius : ℝ}
    (hinner_pos : 0 < innerRadius) (hradii : innerRadius < outerRadius)
    (hnoAnnulus :
      ∀ z : ℂ, innerRadius ≤ ‖z - (1 : ℂ)‖ →
        ‖z - (1 : ℂ)‖ ≤ outerRadius →
          ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z)
    (i j : Node) :
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
          deriv (circleMap (1 : ℂ) outerRadius) theta *
            ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
              (∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
                deriv (circleMap (1 : ℂ) innerRadius) phi *
                  (∑ k : Node,
                    ((complexResolventMatrix (Node := Node) Aalpha
                      (circleMap (1 : ℂ) outerRadius theta))⁻¹) i k *
                    ((complexResolventMatrix (Node := Node) Aalpha
                      (circleMap (1 : ℂ) innerRadius phi))⁻¹) k j)))) =
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
          deriv (circleMap (1 : ℂ) innerRadius) phi *
            ((complexResolventMatrix (Node := Node) Aalpha
              (circleMap (1 : ℂ) innerRadius phi))⁻¹) i j) := by
  classical
  let c : ℂ := (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹)
  let I : Set ℝ := Set.Icc (0 : ℝ) (2 * Real.pi)
  have hI_compact : IsCompact I := by
    simpa [I] using isCompact_Icc
  have hI_meas : MeasurableSet I := hI_compact.measurableSet
  let Ro : ℝ → ℂ := fun theta =>
    ((complexResolventMatrix (Node := Node) Aalpha
      (circleMap (1 : ℂ) outerRadius theta))⁻¹) i j
  let Ri : ℝ → ℂ := fun phi =>
    ((complexResolventMatrix (Node := Node) Aalpha
      (circleMap (1 : ℂ) innerRadius phi))⁻¹) i j
  let K : ℝ → ℝ → ℂ := fun theta phi =>
    (circleMap (1 : ℂ) innerRadius phi -
      circleMap (1 : ℂ) outerRadius theta)⁻¹
  have houter_pos : 0 < outerRadius := lt_trans hinner_pos hradii
  have hden_ne :
      ∀ theta phi : ℝ,
        circleMap (1 : ℂ) innerRadius phi -
            circleMap (1 : ℂ) outerRadius theta ≠ 0 := by
    intro theta phi hzero
    have hsame :
        circleMap (1 : ℂ) innerRadius phi =
          circleMap (1 : ℂ) outerRadius theta := sub_eq_zero.mp hzero
    have hinner_norm :
        ‖circleMap (1 : ℂ) innerRadius phi - (1 : ℂ)‖ =
          innerRadius :=
      fixed_circleMap_boundary_norm innerRadius hinner_pos phi
    have houter_norm :
        ‖circleMap (1 : ℂ) outerRadius theta - (1 : ℂ)‖ =
          outerRadius :=
      fixed_circleMap_boundary_norm outerRadius houter_pos theta
    have hnorm_eq : innerRadius = outerRadius := by
      rw [← hinner_norm, hsame, houter_norm]
    exact (ne_of_lt hradii) hnorm_eq
  have hderivInner_cont :
      ContinuousOn
        (fun phi : ℝ => deriv (circleMap (1 : ℂ) innerRadius) phi) I := by
    have hderivTheta :
        Continuous
          (fun phi : ℝ => deriv (circleMap (1 : ℂ) innerRadius) phi) := by
      exact circleMap_deriv_continuous (1 : ℂ) innerRadius
    exact hderivTheta.continuousOn
  have hRi_cont : ContinuousOn Ri I := by
    intro phi _hphi
    have hz_norm :
        ‖circleMap (1 : ℂ) innerRadius phi - (1 : ℂ)‖ =
          innerRadius :=
      fixed_circleMap_boundary_norm innerRadius hinner_pos phi
    have hdet :
        Matrix.det
          (complexResolventMatrix (Node := Node) Aalpha
            (circleMap (1 : ℂ) innerRadius phi)) ≠ 0 := by
      exact complexResolvent_det_ne_zero_of_not_eigen (Node := Node)
        Aalpha (circleMap (1 : ℂ) innerRadius phi)
        (hnoAnnulus (circleMap (1 : ℂ) innerRadius phi)
          (by rw [hz_norm])
          (by
            rw [hz_norm]
            exact le_of_lt hradii))
    have hentry_cont :
        ContinuousAt
          (fun z : ℂ =>
            ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i j)
          (circleMap (1 : ℂ) innerRadius phi) :=
      (complex_resolvent_inv_entry_differentiableAt_z_of_det_ne_zero
        (Node := Node) Aalpha hdet i j).continuousAt
    exact hentry_cont.comp_continuousWithinAt
      (continuous_circleMap (1 : ℂ) innerRadius).continuousAt.continuousWithinAt
  have hK_cont :
      ∀ theta : ℝ, ContinuousOn (fun phi : ℝ => K theta phi) I := by
    intro theta phi _hphi
    have hsub_cont :
        ContinuousWithinAt
          (fun x : ℝ =>
            circleMap (1 : ℂ) innerRadius x -
              circleMap (1 : ℂ) outerRadius theta) I phi :=
      ((continuous_circleMap (1 : ℂ) innerRadius).continuousAt.sub
        continuousAt_const).continuousWithinAt
    exact ContinuousAt.comp_continuousWithinAt
      (f := fun x : ℝ =>
        circleMap (1 : ℂ) innerRadius x -
          circleMap (1 : ℂ) outerRadius theta)
      (continuousAt_inv₀ (hden_ne theta phi)) hsub_cont
  have hphi_integrable :
      ∀ theta : ℝ,
        Integrable
            (fun phi : ℝ =>
              deriv (circleMap (1 : ℂ) innerRadius) phi *
                (K theta phi * Ro theta)) (volume.restrict I) ∧
          Integrable
            (fun phi : ℝ =>
              deriv (circleMap (1 : ℂ) innerRadius) phi *
                (K theta phi * Ri phi)) (volume.restrict I) := by
    intro theta
    have hcompact : IsCompact I := by
      simpa [I] using isCompact_Icc
    have hmeas : MeasurableSet I := hcompact.measurableSet
    have hfinite : volume I < ⊤ := hcompact.measure_lt_top
    have hcont_left :
        ContinuousOn
          (fun phi : ℝ =>
            deriv (circleMap (1 : ℂ) innerRadius) phi *
              (K theta phi * Ro theta)) I :=
      hderivInner_cont.mul ((hK_cont theta).mul continuousOn_const)
    have hcont_right :
        ContinuousOn
          (fun phi : ℝ =>
            deriv (circleMap (1 : ℂ) innerRadius) phi *
              (K theta phi * Ri phi)) I :=
      hderivInner_cont.mul ((hK_cont theta).mul hRi_cont)
    constructor
    · simpa [IntegrableOn] using
        hcont_left.integrableOn_of_subset_isCompact
          (μ := volume) (K := I) hcompact hmeas (fun x hx => hx)
          (ne_of_lt hfinite)
    · simpa [IntegrableOn] using
        hcont_right.integrableOn_of_subset_isCompact
          (μ := volume) (K := I) hcompact hmeas (fun x hx => hx)
          (ne_of_lt hfinite)
  have hprod :
      ∀ theta phi : ℝ,
        (∑ k : Node,
          ((complexResolventMatrix (Node := Node) Aalpha
            (circleMap (1 : ℂ) outerRadius theta))⁻¹) i k *
          ((complexResolventMatrix (Node := Node) Aalpha
            (circleMap (1 : ℂ) innerRadius phi))⁻¹) k j) =
            K theta phi * (Ro theta - Ri phi) := by
    intro theta phi
    simpa [K, Ro, Ri] using
      separated_resolvent_product_circleParameter_eq_div_difference
        (Node := Node) Aalpha hinner_pos hradii hnoAnnulus theta phi i j
  have hsplit :
      ∀ theta : ℝ,
        c *
            (∫ phi in I,
              deriv (circleMap (1 : ℂ) innerRadius) phi *
                (∑ k : Node,
                  ((complexResolventMatrix (Node := Node) Aalpha
                    (circleMap (1 : ℂ) outerRadius theta))⁻¹) i k *
                  ((complexResolventMatrix (Node := Node) Aalpha
                    (circleMap (1 : ℂ) innerRadius phi))⁻¹) k j)) =
          -(c *
            (∫ phi in I,
              deriv (circleMap (1 : ℂ) innerRadius) phi *
                (K theta phi * Ri phi))) := by
    intro theta
    have hzero :
        (∫ phi in I,
          deriv (circleMap (1 : ℂ) innerRadius) phi *
            (K theta phi * Ro theta)) = 0 := by
      simpa [I, K, Ro] using
        fixed_circleParameter_inner_sub_outer_point_mul_const_eq_zero
          (innerRadius := innerRadius) (outerRadius := outerRadius)
          hinner_pos hradii theta (Ro theta)
    calc
      c *
          (∫ phi in I,
            deriv (circleMap (1 : ℂ) innerRadius) phi *
              (∑ k : Node,
                ((complexResolventMatrix (Node := Node) Aalpha
                  (circleMap (1 : ℂ) outerRadius theta))⁻¹) i k *
                ((complexResolventMatrix (Node := Node) Aalpha
                  (circleMap (1 : ℂ) innerRadius phi))⁻¹) k j)) =
          c *
            (∫ phi in I,
              deriv (circleMap (1 : ℂ) innerRadius) phi *
                (K theta phi * (Ro theta - Ri phi))) := by
            congr 1
            refine MeasureTheory.setIntegral_congr_fun isCompact_Icc.measurableSet ?_
            intro phi _hphi
            exact congrArg
              (fun x : ℂ =>
                deriv (circleMap (1 : ℂ) innerRadius) phi * x)
              (hprod theta phi)
      _ =
          c *
            (∫ phi in I,
              deriv (circleMap (1 : ℂ) innerRadius) phi *
                (K theta phi * Ro theta) -
              deriv (circleMap (1 : ℂ) innerRadius) phi *
                (K theta phi * Ri phi)) := by
            congr 1
            refine MeasureTheory.setIntegral_congr_fun isCompact_Icc.measurableSet ?_
            intro phi _hphi
            ring
      _ =
          c *
            ((∫ phi in I,
              deriv (circleMap (1 : ℂ) innerRadius) phi *
                (K theta phi * Ro theta)) -
             (∫ phi in I,
              deriv (circleMap (1 : ℂ) innerRadius) phi *
                (K theta phi * Ri phi))) := by
            rw [MeasureTheory.integral_sub]
            · exact (hphi_integrable theta).1
            · exact (hphi_integrable theta).2
      _ =
          -(c *
            (∫ phi in I,
              deriv (circleMap (1 : ℂ) innerRadius) phi *
                (K theta phi * Ri phi))) := by
            rw [hzero]
            ring
  have hswap :
      (∫ theta in I,
        deriv (circleMap (1 : ℂ) outerRadius) theta *
          (∫ phi in I,
            deriv (circleMap (1 : ℂ) innerRadius) phi *
              (K theta phi * Ri phi))) =
        ∫ phi in I,
          deriv (circleMap (1 : ℂ) innerRadius) phi *
            (∫ theta in I,
              deriv (circleMap (1 : ℂ) outerRadius) theta *
                (K theta phi * Ri phi)) := by
    simpa [I, K, Ri] using
      complex_circleParameter_Icc_integral_swap_of_continuousOn
        (center := (1 : ℂ)) (outerRadius := outerRadius)
        (innerRadius := innerRadius)
        (F := fun z w : ℂ =>
          (w - z)⁻¹ *
            ((complexResolventMatrix (Node := Node) Aalpha w)⁻¹) i j)
        (separated_inner_resolvent_cauchy_circleParameter_continuousOn
          (Node := Node) Aalpha hinner_pos hradii hnoAnnulus i j)
  have hresidue :
      (∫ phi in I,
          deriv (circleMap (1 : ℂ) innerRadius) phi *
            (c *
              (∫ theta in I,
                deriv (circleMap (1 : ℂ) outerRadius) theta *
                  (K theta phi * Ri phi)))) =
        -∫ phi in I,
          deriv (circleMap (1 : ℂ) innerRadius) phi * Ri phi := by
    simpa [I, c, K, Ri] using
      separated_inner_resolvent_cauchy_outer_residue_integral_eq_neg
        (Node := Node) Aalpha hinner_pos hradii i j
  calc
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
          deriv (circleMap (1 : ℂ) outerRadius) theta *
            ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
              (∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
                deriv (circleMap (1 : ℂ) innerRadius) phi *
                  (∑ k : Node,
                    ((complexResolventMatrix (Node := Node) Aalpha
                      (circleMap (1 : ℂ) outerRadius theta))⁻¹) i k *
                    ((complexResolventMatrix (Node := Node) Aalpha
                      (circleMap (1 : ℂ) innerRadius phi))⁻¹) k j)))) =
        c *
          (∫ theta in I,
            deriv (circleMap (1 : ℂ) outerRadius) theta *
              (-(c *
                (∫ phi in I,
                  deriv (circleMap (1 : ℂ) innerRadius) phi *
                    (K theta phi * Ri phi))))) := by
          refine congrArg (fun x : ℂ => c * x) ?_
          refine MeasureTheory.setIntegral_congr_fun isCompact_Icc.measurableSet ?_
          intro theta _htheta
          simpa [c, I] using
            congrArg
              (fun x : ℂ =>
                deriv (circleMap (1 : ℂ) outerRadius) theta * x)
              (hsplit theta)
    _ =
        -c *
          (∫ theta in I,
                    deriv (circleMap (1 : ℂ) outerRadius) theta *
                      (c *
                      (∫ phi in I,
                        deriv (circleMap (1 : ℂ) innerRadius) phi *
                          (K theta phi * Ri phi)))) := by
          have hneg :
              (∫ theta in I,
                deriv (circleMap (1 : ℂ) outerRadius) theta *
                  (-(c *
                    (∫ phi in I,
                      deriv (circleMap (1 : ℂ) innerRadius) phi *
                        (K theta phi * Ri phi))))) =
                -(∫ theta in I,
                  deriv (circleMap (1 : ℂ) outerRadius) theta *
                    (c *
                        (∫ phi in I,
                          deriv (circleMap (1 : ℂ) innerRadius) phi *
                            (K theta phi * Ri phi)))) := by
            calc
              (∫ theta in I,
                deriv (circleMap (1 : ℂ) outerRadius) theta *
                  (-(c *
                    (∫ phi in I,
                      deriv (circleMap (1 : ℂ) innerRadius) phi *
                        (K theta phi * Ri phi))))) =
                  ∫ theta in I,
                    -(deriv (circleMap (1 : ℂ) outerRadius) theta *
                      (c *
                        (∫ phi in I,
                          deriv (circleMap (1 : ℂ) innerRadius) phi *
                            (K theta phi * Ri phi)))) := by
                    refine MeasureTheory.setIntegral_congr_fun hI_meas ?_
                    intro theta _htheta
                    ring
              _ =
                  -(∫ theta in I,
                    deriv (circleMap (1 : ℂ) outerRadius) theta *
                      (c *
                        (∫ phi in I,
                          deriv (circleMap (1 : ℂ) innerRadius) phi *
                            (K theta phi * Ri phi)))) := by
                    rw [MeasureTheory.integral_neg]
          rw [hneg]
          ring
    _ =
        -c *
          (c *
            (∫ theta in I,
              deriv (circleMap (1 : ℂ) outerRadius) theta *
                (∫ phi in I,
                  deriv (circleMap (1 : ℂ) innerRadius) phi *
                    (K theta phi * Ri phi)))) := by
          have hconst :
              (∫ theta in I,
                deriv (circleMap (1 : ℂ) outerRadius) theta *
                  (c *
                    (∫ phi in I,
                      deriv (circleMap (1 : ℂ) innerRadius) phi *
                        (K theta phi * Ri phi)))) =
                c *
                  (∫ theta in I,
                    deriv (circleMap (1 : ℂ) outerRadius) theta *
                      (∫ phi in I,
                        deriv (circleMap (1 : ℂ) innerRadius) phi *
                          (K theta phi * Ri phi))) := by
            calc
              (∫ theta in I,
                deriv (circleMap (1 : ℂ) outerRadius) theta *
                  (c *
                    (∫ phi in I,
                      deriv (circleMap (1 : ℂ) innerRadius) phi *
                        (K theta phi * Ri phi)))) =
                  ∫ theta in I,
                    c *
                      (deriv (circleMap (1 : ℂ) outerRadius) theta *
                        (∫ phi in I,
                          deriv (circleMap (1 : ℂ) innerRadius) phi *
                            (K theta phi * Ri phi))) := by
                    refine MeasureTheory.setIntegral_congr_fun
                      isCompact_Icc.measurableSet ?_
                    intro theta _htheta
                    ring
              _ =
                  c *
                    (∫ theta in I,
                      deriv (circleMap (1 : ℂ) outerRadius) theta *
                        (∫ phi in I,
                          deriv (circleMap (1 : ℂ) innerRadius) phi *
                            (K theta phi * Ri phi))) := by
                    simpa using
                      (MeasureTheory.integral_const_mul
                        (μ := volume.restrict I) c
                        (fun theta : ℝ =>
                          deriv (circleMap (1 : ℂ) outerRadius) theta *
                            (∫ phi in I,
                              deriv (circleMap (1 : ℂ) innerRadius) phi *
                                (K theta phi * Ri phi))))
          rw [hconst]
    _ =
        -c *
          (c *
            (∫ phi in I,
              deriv (circleMap (1 : ℂ) innerRadius) phi *
                (∫ theta in I,
                  deriv (circleMap (1 : ℂ) outerRadius) theta *
                    (K theta phi * Ri phi)))) := by
          rw [hswap]
    _ =
        -c *
          (∫ phi in I,
            deriv (circleMap (1 : ℂ) innerRadius) phi *
              (c *
                (∫ theta in I,
                  deriv (circleMap (1 : ℂ) outerRadius) theta *
                    (K theta phi * Ri phi)))) := by
          have hconst :
              c *
                (∫ phi in I,
                  deriv (circleMap (1 : ℂ) innerRadius) phi *
                    (∫ theta in I,
                      deriv (circleMap (1 : ℂ) outerRadius) theta *
                        (K theta phi * Ri phi))) =
                ∫ phi in I,
                  deriv (circleMap (1 : ℂ) innerRadius) phi *
                    (c *
                      (∫ theta in I,
                        deriv (circleMap (1 : ℂ) outerRadius) theta *
                          (K theta phi * Ri phi))) := by
            calc
              c *
                (∫ phi in I,
                  deriv (circleMap (1 : ℂ) innerRadius) phi *
                    (∫ theta in I,
                      deriv (circleMap (1 : ℂ) outerRadius) theta *
                        (K theta phi * Ri phi))) =
                  ∫ phi in I,
                    c *
                      (deriv (circleMap (1 : ℂ) innerRadius) phi *
                        (∫ theta in I,
                          deriv (circleMap (1 : ℂ) outerRadius) theta *
                            (K theta phi * Ri phi))) := by
                    exact
                      (MeasureTheory.integral_const_mul
                        (μ := volume.restrict I) c
                        (fun phi : ℝ =>
                          deriv (circleMap (1 : ℂ) innerRadius) phi *
                            (∫ theta in I,
                              deriv (circleMap (1 : ℂ) outerRadius) theta *
                                (K theta phi * Ri phi)))).symm
              _ =
                  ∫ phi in I,
                    deriv (circleMap (1 : ℂ) innerRadius) phi *
                      (c *
                        (∫ theta in I,
                          deriv (circleMap (1 : ℂ) outerRadius) theta *
                            (K theta phi * Ri phi))) := by
                    refine MeasureTheory.setIntegral_congr_fun hI_meas ?_
                    intro phi _hphi
                    ring
          rw [hconst]
    _ =
        -c *
          (-(∫ phi in I,
            deriv (circleMap (1 : ℂ) innerRadius) phi * Ri phi)) := by
          rw [hresidue]
    _ =
      (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
          deriv (circleMap (1 : ℂ) innerRadius) phi *
            ((complexResolventMatrix (Node := Node) Aalpha
              (circleMap (1 : ℂ) innerRadius phi))⁻¹) i j) := by
          simp [c, I, Ri]

theorem complex_Icc_integral_neg_eq_of_periodic
    (T : ℝ) (hT_pos : 0 < T) (f : ℝ → ℂ)
    (hf : Function.Periodic f T) :
    (∫ theta in Set.Icc (0 : ℝ) T, f (-theta)) =
      ∫ theta in Set.Icc (0 : ℝ) T, f theta := by
  calc
    (∫ theta in Set.Icc (0 : ℝ) T, f (-theta)) =
        ∫ theta in (0 : ℝ)..T, f (-theta) := by
          exact complex_setIntegral_Icc_eq_intervalIntegral
            (0 : ℝ) T (fun theta => f (-theta)) (le_of_lt hT_pos)
    _ = ∫ theta in -T..-(0 : ℝ), f theta := by
          exact intervalIntegral.integral_comp_neg
            (f := f) (a := (0 : ℝ)) (b := T)
    _ = ∫ theta in (0 : ℝ)..T, f theta := by
          simpa using (hf.intervalIntegral_add_eq (-T) (0 : ℝ))
    _ = ∫ theta in Set.Icc (0 : ℝ) T, f theta := by
          exact (complex_setIntegral_Icc_eq_intervalIntegral
            (0 : ℝ) T f (le_of_lt hT_pos)).symm

theorem fixed_circle_scaled_resolvent_integrand_periodic
    [DecidableEq Node]
    (Aalpha : NodeMatrix Node) (baseRadius : ℝ) (i j : Node) :
    Function.Periodic
      (fun theta : ℝ =>
        deriv (circleMap (1 : ℂ) baseRadius) theta *
          ((complexResolventMatrix (Node := Node) Aalpha
            (circleMap (1 : ℂ) baseRadius theta))⁻¹) i j)
      (2 * Real.pi) := by
  intro theta
  have hcircle :
      circleMap (1 : ℂ) baseRadius (theta + 2 * Real.pi) =
        circleMap (1 : ℂ) baseRadius theta := by
    simpa using
      (periodic_circleMap (1 : ℂ) baseRadius theta)
  have hderiv :
      deriv (circleMap (1 : ℂ) baseRadius) (theta + 2 * Real.pi) =
        deriv (circleMap (1 : ℂ) baseRadius) theta := by
    calc
      deriv (circleMap (1 : ℂ) baseRadius) (theta + 2 * Real.pi) =
          circleMap (0 : ℂ) baseRadius (theta + 2 * Real.pi) * Complex.I :=
        deriv_circleMap (1 : ℂ) baseRadius (theta + 2 * Real.pi)
      _ = circleMap (0 : ℂ) baseRadius theta * Complex.I := by
        rw [show circleMap (0 : ℂ) baseRadius (theta + 2 * Real.pi) =
            circleMap (0 : ℂ) baseRadius theta by
              simpa using (periodic_circleMap (0 : ℂ) baseRadius theta)]
      _ = deriv (circleMap (1 : ℂ) baseRadius) theta :=
        (deriv_circleMap (1 : ℂ) baseRadius theta).symm
  dsimp
  rw [hcircle, hderiv]

theorem fixed_circle_scaled_resolvent_neg_Icc_integral_eq_self
    [DecidableEq Node]
    (Aalpha : NodeMatrix Node) (baseRadius : ℝ) (i j : Node) :
    (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
        deriv (circleMap (1 : ℂ) baseRadius) (-theta) *
          ((complexResolventMatrix (Node := Node) Aalpha
            (circleMap (1 : ℂ) baseRadius (-theta)))⁻¹) i j) =
      ∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
        deriv (circleMap (1 : ℂ) baseRadius) theta *
          ((complexResolventMatrix (Node := Node) Aalpha
            (circleMap (1 : ℂ) baseRadius theta))⁻¹) i j := by
  let f : ℝ → ℂ := fun theta =>
    deriv (circleMap (1 : ℂ) baseRadius) theta *
      ((complexResolventMatrix (Node := Node) Aalpha
        (circleMap (1 : ℂ) baseRadius theta))⁻¹) i j
  have hf : Function.Periodic f (2 * Real.pi) := by
    simpa [f] using
      fixed_circle_scaled_resolvent_integrand_periodic
        (Node := Node) Aalpha baseRadius i j
  simpa [f] using
    complex_Icc_integral_neg_eq_of_periodic
      (2 * Real.pi) Real.two_pi_pos f hf

theorem complexRieszProjectionOnCircle_entry_im_zero_of_scaled_conj_and_neg_integral
    (Aalpha : NodeMatrix Node) (baseRadius : ℝ) (i j : Node)
    (hscaled :
      letI : DecidableEq Node := Classical.decEq Node
      ∀ theta : ℝ,
        conj
            (deriv (circleMap (1 : ℂ) baseRadius) theta *
              ((complexResolventMatrix (Node := Node) Aalpha
                (circleMap (1 : ℂ) baseRadius theta))⁻¹) i j) =
          -deriv (circleMap (1 : ℂ) baseRadius) (-theta) *
              ((complexResolventMatrix (Node := Node) Aalpha
                (circleMap (1 : ℂ) baseRadius (-theta)))⁻¹) i j)
    (hnegIntegral :
      letI : DecidableEq Node := Classical.decEq Node
      (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
        deriv (circleMap (1 : ℂ) baseRadius) (-theta) *
          ((complexResolventMatrix (Node := Node) Aalpha
            (circleMap (1 : ℂ) baseRadius (-theta)))⁻¹) i j) =
      ∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
        deriv (circleMap (1 : ℂ) baseRadius) theta *
          ((complexResolventMatrix (Node := Node) Aalpha
            (circleMap (1 : ℂ) baseRadius theta))⁻¹) i j) :
    ((complexRieszProjectionOnCircle (Node := Node)
      Aalpha (1 : ℂ) baseRadius i j).im = 0) := by
  classical
  letI : DecidableEq Node := Classical.decEq Node
  let c : ℂ := (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹)
  let f : ℝ → ℂ := fun theta =>
    deriv (circleMap (1 : ℂ) baseRadius) theta *
      ((complexResolventMatrix (Node := Node) Aalpha
        (circleMap (1 : ℂ) baseRadius theta))⁻¹) i j
  let fneg : ℝ → ℂ := fun theta =>
    deriv (circleMap (1 : ℂ) baseRadius) (-theta) *
      ((complexResolventMatrix (Node := Node) Aalpha
        (circleMap (1 : ℂ) baseRadius (-theta)))⁻¹) i j
  have hentry :
      complexRieszProjectionOnCircle (Node := Node)
          Aalpha (1 : ℂ) baseRadius i j =
        c * ∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi), f theta := by
    simpa only [c, f, smul_eq_mul] using
      (complexRieszProjectionOnCircle_entry_eq_Icc_integral
        (Node := Node) Aalpha (1 : ℂ) baseRadius i j)
  have hconj_c : conj c = -c := by
    have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
      apply Complex.ext <;> norm_num
    have hpi : conj (Real.pi : ℂ) = (Real.pi : ℂ) := by simp
    calc
      conj c =
          (conj ((2 : ℂ) * (Real.pi : ℂ) * Complex.I))⁻¹ := by
            simp [c]
      _ = (-((2 : ℂ) * (Real.pi : ℂ) * Complex.I))⁻¹ := by
            congr 1
            rw [map_mul, map_mul, htwo, hpi]
            simp
      _ = -c := by
            simp [c]
  have hconj_integral :
      conj (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi), f theta) =
        -∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi), fneg theta := by
    calc
      conj (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi), f theta) =
          ∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi), conj (f theta) := by
            exact complex_Icc_integral_conj (0 : ℝ) (2 * Real.pi) f
      _ = ∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi), -fneg theta := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with theta
            simpa [f, fneg] using hscaled theta
      _ = -∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi), fneg theta := by
            rw [MeasureTheory.integral_neg]
  have hconj_entry :
      conj (complexRieszProjectionOnCircle (Node := Node)
          Aalpha (1 : ℂ) baseRadius i j) =
        complexRieszProjectionOnCircle (Node := Node)
          Aalpha (1 : ℂ) baseRadius i j := by
    calc
      conj (complexRieszProjectionOnCircle (Node := Node)
          Aalpha (1 : ℂ) baseRadius i j) =
          conj (c * ∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi), f theta) := by
            rw [hentry]
      _ =
          conj c *
            conj (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi), f theta) := by
            rw [map_mul]
      _ =
          (-c) *
            (-(∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi), fneg theta)) := by
            rw [hconj_c, hconj_integral]
      _ =
          c * ∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi), fneg theta := by
            ring
      _ =
          c * ∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi), f theta := by
            rw [hnegIntegral]
      _ =
          complexRieszProjectionOnCircle (Node := Node)
            Aalpha (1 : ℂ) baseRadius i j := hentry.symm
  exact Complex.conj_eq_iff_im.mp hconj_entry

theorem fixed_circle_resolvent_inv_entry_circleIntegrable_of_no_boundary
    [DecidableEq Node]
    (Aalpha : NodeMatrix Node) (baseRadius : ℝ)
    (hbaseRadius_pos : 0 < baseRadius)
    (hnoBoundary :
      ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
        ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z)
    (i j : Node) :
    CircleIntegrable
      (fun z : ℂ =>
        ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i j)
      (1 : ℂ) baseRadius := by
  classical
  have hcont_sphere :
      ContinuousOn
        (fun z : ℂ =>
          ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i j)
        (Metric.sphere (1 : ℂ) baseRadius) := by
    intro z hz
    have hz_norm : ‖z - (1 : ℂ)‖ = baseRadius := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hdet_z :
        Matrix.det (complexResolventMatrix (Node := Node) Aalpha z) ≠ 0 :=
      complexResolvent_det_ne_zero_of_not_eigen (Node := Node) Aalpha z
        (hnoBoundary z hz_norm)
    exact
      (complex_resolvent_inv_entry_differentiableAt_z_of_det_ne_zero
        (Node := Node) Aalpha hdet_z i j).continuousAt.continuousWithinAt
  exact hcont_sphere.circleIntegrable (le_of_lt hbaseRadius_pos)

theorem complexRieszProjectionOnCircle_mul_self_entry_eq_single_contour_right
    (Aalpha : NodeMatrix Node) (baseRadius : ℝ)
    (hresolvent_entry_circleIntegrable :
      letI : DecidableEq Node := Classical.decEq Node;
      ∀ i j : Node,
        CircleIntegrable
          (fun z : ℂ =>
            ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i j)
          (1 : ℂ) baseRadius)
    (i j : Node) :
    complexMatrixMul (Node := Node)
        (complexRieszProjectionOnCircle (Node := Node)
          Aalpha (1 : ℂ) baseRadius)
        (complexRieszProjectionOnCircle (Node := Node)
          Aalpha (1 : ℂ) baseRadius) i j =
      (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ z in C((1 : ℂ), baseRadius),
          (letI : DecidableEq Node := Classical.decEq Node;
            (((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) *
              complexRieszProjectionOnCircle (Node := Node)
                Aalpha (1 : ℂ) baseRadius) i j)) := by
  classical
  letI : DecidableEq Node := Classical.decEq Node
  let c : ℂ := (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹)
  let P : ComplexNodeMatrix Node :=
    complexRieszProjectionOnCircle (Node := Node)
      Aalpha (1 : ℂ) baseRadius
  let R : ℂ → ComplexNodeMatrix Node :=
    fun z : ℂ => (complexResolventMatrix (Node := Node) Aalpha z)⁻¹
  have hterm_integrable :
      ∀ k ∈ (Finset.univ : Finset Node),
        CircleIntegrable (fun z : ℂ => R z i k * P k j)
          (1 : ℂ) baseRadius := by
    intro k _hk
    have hk :
        CircleIntegrable (fun z : ℂ => P k j * R z i k)
          (1 : ℂ) baseRadius := by
      simpa [R, Pi.smul_apply, smul_eq_mul] using
        (hresolvent_entry_circleIntegrable i k).const_smul (a := P k j)
    simpa [mul_comm] using hk
  calc
    complexMatrixMul (Node := Node) P P i j =
        ∑ k : Node, P i k * P k j := by
          simp [complexMatrixMul, Matrix.mul_apply, P]
    _ = ∑ k : Node, (c *
          (∮ z in C((1 : ℂ), baseRadius), R z i k)) * P k j := by
          apply Finset.sum_congr rfl
          intro k _hk
          have hPik :
              P i k =
                c * (∮ z in C((1 : ℂ), baseRadius), R z i k) := by
            dsimp [P, c, R]
            rw [complexRieszProjectionOnCircle]
          rw [hPik]
    _ = c *
        ∑ k : Node,
          (∮ z in C((1 : ℂ), baseRadius), R z i k) * P k j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _hk
          ring
    _ = c *
        ∑ k : Node,
          (∮ z in C((1 : ℂ), baseRadius), R z i k * P k j) := by
          congr 1
          apply Finset.sum_congr rfl
          intro k _hk
          simpa [smul_eq_mul] using
            (circleIntegral.integral_smul_const
              (fun z : ℂ => R z i k) (P k j) (1 : ℂ) baseRadius).symm
    _ = c *
        (∮ z in C((1 : ℂ), baseRadius),
          ∑ k : Node, R z i k * P k j) := by
          rw [circleIntegral.integral_fun_sum hterm_integrable]
    _ = c *
        (∮ z in C((1 : ℂ), baseRadius), (R z * P) i j) := by
          simp [Matrix.mul_apply]
    _ =
      (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ z in C((1 : ℂ), baseRadius),
          (((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) *
            complexRieszProjectionOnCircle (Node := Node)
              Aalpha (1 : ℂ) baseRadius) i j) := by
          simp [c, P, R]

theorem complexResolvent_inv_mul_complexRieszProjectionOnCircle_entry_eq_inner_contour
    (Aalpha : NodeMatrix Node) (baseRadius : ℝ)
    (hresolvent_entry_circleIntegrable :
      letI : DecidableEq Node := Classical.decEq Node;
      ∀ i j : Node,
        CircleIntegrable
          (fun z : ℂ =>
            ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i j)
          (1 : ℂ) baseRadius)
    (z : ℂ) (i j : Node) :
    (letI : DecidableEq Node := Classical.decEq Node;
      (((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) *
        complexRieszProjectionOnCircle (Node := Node)
          Aalpha (1 : ℂ) baseRadius) i j) =
      (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ w in C((1 : ℂ), baseRadius),
          (letI : DecidableEq Node := Classical.decEq Node;
            ∑ k : Node,
              ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i k *
                ((complexResolventMatrix (Node := Node) Aalpha w)⁻¹) k j)) := by
  classical
  letI : DecidableEq Node := Classical.decEq Node
  let c : ℂ := (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹)
  let P : ComplexNodeMatrix Node :=
    complexRieszProjectionOnCircle (Node := Node)
      Aalpha (1 : ℂ) baseRadius
  let R : ℂ → ComplexNodeMatrix Node :=
    fun z : ℂ => (complexResolventMatrix (Node := Node) Aalpha z)⁻¹
  have hterm_integrable :
      ∀ k ∈ (Finset.univ : Finset Node),
        CircleIntegrable (fun w : ℂ => R z i k * R w k j)
          (1 : ℂ) baseRadius := by
    intro k _hk
    simpa [R, Pi.smul_apply, smul_eq_mul] using
      (hresolvent_entry_circleIntegrable k j).const_smul
        (a := R z i k)
  calc
    (R z * P) i j =
        ∑ k : Node, R z i k * P k j := by
          simp [Matrix.mul_apply]
    _ = ∑ k : Node,
          R z i k *
            (c * (∮ w in C((1 : ℂ), baseRadius), R w k j)) := by
          apply Finset.sum_congr rfl
          intro k _hk
          have hPkj :
              P k j =
                c * (∮ w in C((1 : ℂ), baseRadius), R w k j) := by
            dsimp [P, c, R]
            rw [complexRieszProjectionOnCircle]
          rw [hPkj]
    _ = c *
        ∑ k : Node,
          R z i k * (∮ w in C((1 : ℂ), baseRadius), R w k j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _hk
          ring
    _ = c *
        ∑ k : Node,
          (∮ w in C((1 : ℂ), baseRadius), R z i k * R w k j) := by
          congr 1
          apply Finset.sum_congr rfl
          intro k _hk
          rw [circleIntegral.integral_const_mul]
    _ = c *
        (∮ w in C((1 : ℂ), baseRadius),
          ∑ k : Node, R z i k * R w k j) := by
          rw [circleIntegral.integral_fun_sum hterm_integrable]
    _ =
      (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ w in C((1 : ℂ), baseRadius),
          ∑ k : Node,
            ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i k *
              ((complexResolventMatrix (Node := Node) Aalpha w)⁻¹) k j) := by
          simp [c, R]

theorem complexResolvent_inv_mul_fixed_matrix_entry_circleIntegral_eq_of_no_eigen_annulus
    [DecidableEq Node]
    (Aalpha : NodeMatrix Node) (P : ComplexNodeMatrix Node)
    {innerRadius outerRadius : ℝ}
    (hinner_pos : 0 < innerRadius) (hradii : innerRadius ≤ outerRadius)
    (hnoAnnulus :
      ∀ z : ℂ, innerRadius ≤ ‖z - (1 : ℂ)‖ →
        ‖z - (1 : ℂ)‖ ≤ outerRadius →
          ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z)
    (i j : Node) :
    (∮ z in C((1 : ℂ), outerRadius),
        (((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) * P) i j) =
      ∮ z in C((1 : ℂ), innerRadius),
        (((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) * P) i j := by
  classical
  have houter_pos : 0 < outerRadius := lt_of_lt_of_le hinner_pos hradii
  have houter_boundary :
      ∀ z : ℂ, ‖z - (1 : ℂ)‖ = outerRadius →
        ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z := by
    intro z hz
    exact hnoAnnulus z (by rw [hz]; exact hradii) (by rw [hz])
  have hinner_boundary :
      ∀ z : ℂ, ‖z - (1 : ℂ)‖ = innerRadius →
        ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z := by
    intro z hz
    exact hnoAnnulus z (by rw [hz]) (by rw [hz]; exact hradii)
  have houter_term :
      ∀ k ∈ (Finset.univ : Finset Node),
        CircleIntegrable
          (fun z : ℂ =>
            ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i k *
              P k j)
          (1 : ℂ) outerRadius := by
    intro k _hk
    have hk :
        CircleIntegrable
          (fun z : ℂ =>
            P k j *
              ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i k)
          (1 : ℂ) outerRadius := by
      simpa [Pi.smul_apply, smul_eq_mul] using
        (fixed_circle_resolvent_inv_entry_circleIntegrable_of_no_boundary
          (Node := Node) Aalpha outerRadius houter_pos houter_boundary i k).const_smul
          (a := P k j)
    simpa [mul_comm] using hk
  have hinner_term :
      ∀ k ∈ (Finset.univ : Finset Node),
        CircleIntegrable
          (fun z : ℂ =>
            ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i k *
              P k j)
          (1 : ℂ) innerRadius := by
    intro k _hk
    have hk :
        CircleIntegrable
          (fun z : ℂ =>
            P k j *
              ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i k)
          (1 : ℂ) innerRadius := by
      simpa [Pi.smul_apply, smul_eq_mul] using
        (fixed_circle_resolvent_inv_entry_circleIntegrable_of_no_boundary
          (Node := Node) Aalpha innerRadius hinner_pos hinner_boundary i k).const_smul
          (a := P k j)
    simpa [mul_comm] using hk
  calc
    (∮ z in C((1 : ℂ), outerRadius),
        (((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) * P) i j) =
        ∮ z in C((1 : ℂ), outerRadius),
          ∑ k : Node,
            ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i k *
              P k j := by
          refine circleIntegral.integral_congr (le_of_lt houter_pos) ?_
          intro z _hz
          simp [Matrix.mul_apply]
    _ =
        ∑ k : Node,
          ∮ z in C((1 : ℂ), outerRadius),
            ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i k *
              P k j := by
          rw [circleIntegral.integral_fun_sum houter_term]
    _ =
        ∑ k : Node,
          (∮ z in C((1 : ℂ), outerRadius),
            ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i k) *
              P k j := by
          apply Finset.sum_congr rfl
          intro k _hk
          simpa [smul_eq_mul] using
            (circleIntegral.integral_smul_const
              (fun z : ℂ =>
                ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i k)
              (P k j) (1 : ℂ) outerRadius)
    _ =
        ∑ k : Node,
          (∮ z in C((1 : ℂ), innerRadius),
            ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i k) *
              P k j := by
          apply Finset.sum_congr rfl
          intro k _hk
          rw [complex_resolvent_inv_entry_circleIntegral_eq_of_no_eigen_annulus
            (Node := Node) Aalpha hinner_pos hradii hnoAnnulus i k]
    _ =
        ∑ k : Node,
          ∮ z in C((1 : ℂ), innerRadius),
            ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i k *
              P k j := by
          apply Finset.sum_congr rfl
          intro k _hk
          simpa [smul_eq_mul] using
            (circleIntegral.integral_smul_const
              (fun z : ℂ =>
                ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i k)
              (P k j) (1 : ℂ) innerRadius).symm
    _ =
        ∮ z in C((1 : ℂ), innerRadius),
          ∑ k : Node,
            ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i k *
              P k j := by
          rw [circleIntegral.integral_fun_sum hinner_term]
    _ =
      ∮ z in C((1 : ℂ), innerRadius),
        (((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) * P) i j := by
          refine circleIntegral.integral_congr (le_of_lt hinner_pos) ?_
          intro z _hz
          simp [Matrix.mul_apply]

set_option maxHeartbeats 800000 in
theorem complexRieszProjectionOnCircle_resolvent_action_eq_self_of_no_boundary
    (Aalpha : NodeMatrix Node) (baseRadius : ℝ)
    (hbaseRadius_pos : 0 < baseRadius)
    (hnoBoundary :
      ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
        ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z)
    (i j : Node) :
    letI : DecidableEq Node := Classical.decEq Node
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ z in C((1 : ℂ), baseRadius),
          (((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) *
            complexRieszProjectionOnCircle (Node := Node)
              Aalpha (1 : ℂ) baseRadius) i j) =
      (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ z in C((1 : ℂ), baseRadius),
          ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i j) := by
  classical
  letI : DecidableEq Node := Classical.decEq Node
  let c : ℂ := (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹)
  let Pbase : ComplexNodeMatrix Node :=
    complexRieszProjectionOnCircle (Node := Node)
      Aalpha (1 : ℂ) baseRadius
  let R : ℂ → ComplexNodeMatrix Node :=
    fun z : ℂ => (complexResolventMatrix (Node := Node) Aalpha z)⁻¹
  rcases exists_no_eigen_annulus_around_fixed_circle
      (Node := Node) Aalpha baseRadius hbaseRadius_pos hnoBoundary with
    ⟨innerRadius, outerRadius, hinner_pos, hinner_lt_base,
      hbase_lt_outer, hnoAnnulus⟩
  let Pinner : ComplexNodeMatrix Node :=
    complexRieszProjectionOnCircle (Node := Node)
      Aalpha (1 : ℂ) innerRadius
  have hinner_lt_outer : innerRadius < outerRadius :=
    lt_trans hinner_lt_base hbase_lt_outer
  have houter_pos : 0 < outerRadius :=
    lt_trans hbaseRadius_pos hbase_lt_outer
  have hnoInnerBase :
      ∀ z : ℂ, innerRadius ≤ ‖z - (1 : ℂ)‖ →
        ‖z - (1 : ℂ)‖ ≤ baseRadius →
          ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z := by
    intro z hl hu
    exact hnoAnnulus z hl (le_trans hu (le_of_lt hbase_lt_outer))
  have hnoBaseOuter :
      ∀ z : ℂ, baseRadius ≤ ‖z - (1 : ℂ)‖ →
        ‖z - (1 : ℂ)‖ ≤ outerRadius →
          ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z := by
    intro z hl hu
    exact hnoAnnulus z (le_trans (le_of_lt hinner_lt_base) hl) hu
  have hinner_boundary :
      ∀ z : ℂ, ‖z - (1 : ℂ)‖ = innerRadius →
        ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z := by
    intro z hz
    exact hnoAnnulus z (by rw [hz]) (by
      rw [hz]
      exact le_of_lt hinner_lt_outer)
  have hPbase_inner : Pbase = Pinner := by
    dsimp [Pbase, Pinner]
    exact
      complexRieszProjectionOnCircle_eq_of_no_eigen_annulus
        (Node := Node) Aalpha hinner_pos (le_of_lt hinner_lt_base)
        hnoInnerBase
  have haction_outer_base :
      (∮ z in C((1 : ℂ), outerRadius), (R z * Pbase) i j) =
        ∮ z in C((1 : ℂ), baseRadius), (R z * Pbase) i j := by
    simpa [R, Pbase] using
      complexResolvent_inv_mul_fixed_matrix_entry_circleIntegral_eq_of_no_eigen_annulus
        (Node := Node) Aalpha Pbase hbaseRadius_pos
        (le_of_lt hbase_lt_outer) hnoBaseOuter i j
  have hresolvent_inner_circleIntegrable :
      ∀ a b : Node,
        CircleIntegrable
          (fun z : ℂ =>
            ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) a b)
          (1 : ℂ) innerRadius := by
    intro a b
    exact fixed_circle_resolvent_inv_entry_circleIntegrable_of_no_boundary
      (Node := Node) Aalpha innerRadius hinner_pos hinner_boundary a b
  have hinner_expand :
      ∀ z : ℂ,
        (R z * Pinner) i j =
          c *
            (∮ w in C((1 : ℂ), innerRadius),
              ∑ k : Node, R z i k * R w k j) := by
    intro z
    simpa [c, R, Pinner] using
      complexResolvent_inv_mul_complexRieszProjectionOnCircle_entry_eq_inner_contour
        (Node := Node) Aalpha innerRadius hresolvent_inner_circleIntegrable
        z i j
  have houter_expand :
      (∮ z in C((1 : ℂ), outerRadius), (R z * Pinner) i j) =
        ∮ z in C((1 : ℂ), outerRadius),
          c *
            (∮ w in C((1 : ℂ), innerRadius),
              ∑ k : Node, R z i k * R w k j) := by
    refine circleIntegral.integral_congr (le_of_lt houter_pos) ?_
    intro z _hz
    exact hinner_expand z
  have hseparated_circle :
      c *
          (∮ z in C((1 : ℂ), outerRadius),
            c *
              (∮ w in C((1 : ℂ), innerRadius),
                ∑ k : Node, R z i k * R w k j)) =
        c *
          (∮ w in C((1 : ℂ), innerRadius), R w i j) := by
    have hinner_parameterized (theta : ℝ) :
        (∮ w in C((1 : ℂ), innerRadius),
            ∑ k : Node,
              R (circleMap (1 : ℂ) outerRadius theta) i k * R w k j) =
          ∫ phi in Set.Icc (0 : ℝ) (2 * Real.pi),
            deriv (circleMap (1 : ℂ) innerRadius) phi *
              (∑ k : Node,
                R (circleMap (1 : ℂ) outerRadius theta) i k *
                  R (circleMap (1 : ℂ) innerRadius phi) k j) := by
      exact circleIntegral_eq_Icc_integral_deriv_mul
        (fun w : ℂ =>
          ∑ k : Node,
            R (circleMap (1 : ℂ) outerRadius theta) i k * R w k j)
        (1 : ℂ) innerRadius
    rw [circleIntegral_eq_Icc_integral_deriv_mul,
      circleIntegral_eq_Icc_integral_deriv_mul]
    simp_rw [hinner_parameterized]
    simpa only [c, R] using
      separated_outer_inner_resolvent_product_integral_eq_inner
        (Node := Node) Aalpha hinner_pos hinner_lt_outer hnoAnnulus i j
  have hresolvent_base_inner :
      (∮ z in C((1 : ℂ), baseRadius), R z i j) =
        ∮ z in C((1 : ℂ), innerRadius), R z i j := by
    simpa [R] using
      complex_resolvent_inv_entry_circleIntegral_eq_of_no_eigen_annulus
        (Node := Node) Aalpha hinner_pos (le_of_lt hinner_lt_base)
        hnoInnerBase i j
  calc
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ z in C((1 : ℂ), baseRadius),
          (((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) *
            complexRieszProjectionOnCircle (Node := Node)
              Aalpha (1 : ℂ) baseRadius) i j) =
        c * (∮ z in C((1 : ℂ), baseRadius), (R z * Pbase) i j) := by
          simp [c, R, Pbase]
    _ = c * (∮ z in C((1 : ℂ), outerRadius), (R z * Pbase) i j) := by
          rw [← haction_outer_base]
    _ = c * (∮ z in C((1 : ℂ), outerRadius), (R z * Pinner) i j) := by
          rw [hPbase_inner]
    _ =
        c *
          (∮ z in C((1 : ℂ), outerRadius),
            c *
              (∮ w in C((1 : ℂ), innerRadius),
                ∑ k : Node, R z i k * R w k j)) := by
          rw [houter_expand]
    _ = c * (∮ w in C((1 : ℂ), innerRadius), R w i j) :=
          hseparated_circle
    _ = c * (∮ z in C((1 : ℂ), baseRadius), R z i j) := by
          rw [hresolvent_base_inner]
    _ =
      (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ z in C((1 : ℂ), baseRadius),
          ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i j) := by
          simp [c, R]

theorem complexConjMatrix_inv_of_det_ne_zero [DecidableEq Node]
    (M : ComplexNodeMatrix Node) (hdet : Matrix.det M ≠ 0) :
    complexConjMatrix (Node := Node) M⁻¹ =
      (complexConjMatrix (Node := Node) M)⁻¹ := by
  classical
  symm
  refine Matrix.inv_eq_right_inv ?_
  calc
    complexConjMatrix (Node := Node) M *
        complexConjMatrix (Node := Node) M⁻¹ =
        complexConjMatrix (Node := Node) (M * M⁻¹) := by
          rw [complexConjMatrix_mul]
    _ = complexConjMatrix (Node := Node) (1 : ComplexNodeMatrix Node) := by
          rw [Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hdet)]
    _ = 1 := complexConjMatrix_one (Node := Node)

theorem complexResolvent_inv_conj_entry_of_not_eigen
    [DecidableEq Node]
    (A0 : NodeMatrix Node) (z : ℂ)
    (hnot : ¬ IsComplexRightEigenvalue (Node := Node) A0 z) (i j : Node) :
    conj
        (((complexResolventMatrix (Node := Node) A0 z)⁻¹) i j) =
      ((complexResolventMatrix (Node := Node) A0 (conj z))⁻¹) i j := by
  classical
  have hdet : Matrix.det (complexResolventMatrix (Node := Node) A0 z) ≠ 0 :=
    complexResolvent_det_ne_zero_of_not_eigen (Node := Node) A0 z hnot
  have hmatrix :=
    complexConjMatrix_inv_of_det_ne_zero (Node := Node)
      (complexResolventMatrix (Node := Node) A0 z) hdet
  have hentry := congrArg (fun M : ComplexNodeMatrix Node => M i j) hmatrix
  simpa [complexConjMatrix, complexConjMatrix_resolvent] using hentry

theorem complex_resolvent_inv_mul_projection_pole
    [DecidableEq Node]
    (A0 P0 : NodeMatrix Node) (z : ℂ)
    (hdet : Matrix.det (complexResolventMatrix (Node := Node) A0 z) ≠ 0)
    (hAcPc :
      complexOfRealMatrix (Node := Node) A0 *
          complexOfRealMatrix (Node := Node) P0 =
        complexOfRealMatrix (Node := Node) P0) :
    (z - (1 : ℂ)) •
        ((complexResolventMatrix (Node := Node) A0 z)⁻¹ *
          complexOfRealMatrix (Node := Node) P0) =
      complexOfRealMatrix (Node := Node) P0 := by
  classical
  let M : ComplexNodeMatrix Node := complexResolventMatrix (Node := Node) A0 z
  let Pc : ComplexNodeMatrix Node := complexOfRealMatrix (Node := Node) P0
  have hunit : IsUnit (Matrix.det M) := by
    exact isUnit_iff_ne_zero.mpr (by simpa [M] using hdet)
  have hMPc : M * Pc = (z - (1 : ℂ)) • Pc := by
    calc
      M * Pc =
          (algebraMap ℂ (ComplexNodeMatrix Node) z -
              complexOfRealMatrix (Node := Node) A0) *
            complexOfRealMatrix (Node := Node) P0 := by
            simp [M, Pc, complexResolventMatrix_eq_algebraMap_sub]
      _ = algebraMap ℂ (ComplexNodeMatrix Node) z *
              complexOfRealMatrix (Node := Node) P0 -
            complexOfRealMatrix (Node := Node) A0 *
              complexOfRealMatrix (Node := Node) P0 := by
            rw [sub_mul]
      _ = algebraMap ℂ (ComplexNodeMatrix Node) z *
              complexOfRealMatrix (Node := Node) P0 -
            complexOfRealMatrix (Node := Node) P0 := by
            rw [hAcPc]
      _ = (z - (1 : ℂ)) • Pc := by
            ext i j
            simp [Pc, complexOfRealMatrix, Matrix.algebraMap_eq_diagonal,
              Matrix.diagonal_mul]
            ring
  have hsmul_pull :
      (z - (1 : ℂ)) • (M⁻¹ * Pc) = M⁻¹ * ((z - (1 : ℂ)) • Pc) := by
    ext i j
    simp [Matrix.mul_apply, Finset.mul_sum]
    ring
  change (z - (1 : ℂ)) • (M⁻¹ * Pc) = Pc
  calc
    (z - (1 : ℂ)) • (M⁻¹ * Pc) =
        M⁻¹ * ((z - (1 : ℂ)) • Pc) := hsmul_pull
    _ = M⁻¹ * (M * Pc) := by rw [← hMPc]
    _ = (M⁻¹ * M) * Pc := by rw [Matrix.mul_assoc]
    _ = Pc := by
      rw [Matrix.nonsing_inv_mul M hunit]
      simp

theorem complex_projection_mul_resolvent_inv_pole
    [DecidableEq Node]
    (A0 P0 : NodeMatrix Node) (z : ℂ)
    (hdet : Matrix.det (complexResolventMatrix (Node := Node) A0 z) ≠ 0)
    (hPcAc :
      complexOfRealMatrix (Node := Node) P0 *
          complexOfRealMatrix (Node := Node) A0 =
        complexOfRealMatrix (Node := Node) P0) :
    (z - (1 : ℂ)) •
        (complexOfRealMatrix (Node := Node) P0 *
          (complexResolventMatrix (Node := Node) A0 z)⁻¹) =
      complexOfRealMatrix (Node := Node) P0 := by
  classical
  let M : ComplexNodeMatrix Node := complexResolventMatrix (Node := Node) A0 z
  let Pc : ComplexNodeMatrix Node := complexOfRealMatrix (Node := Node) P0
  have hunit : IsUnit (Matrix.det M) := by
    exact isUnit_iff_ne_zero.mpr (by simpa [M] using hdet)
  have hPcM : Pc * M = (z - (1 : ℂ)) • Pc := by
    calc
      Pc * M =
          complexOfRealMatrix (Node := Node) P0 *
            (algebraMap ℂ (ComplexNodeMatrix Node) z -
              complexOfRealMatrix (Node := Node) A0) := by
            simp [M, Pc, complexResolventMatrix_eq_algebraMap_sub]
      _ = complexOfRealMatrix (Node := Node) P0 *
              algebraMap ℂ (ComplexNodeMatrix Node) z -
            complexOfRealMatrix (Node := Node) P0 *
              complexOfRealMatrix (Node := Node) A0 := by
            rw [mul_sub]
      _ = complexOfRealMatrix (Node := Node) P0 *
              algebraMap ℂ (ComplexNodeMatrix Node) z -
            complexOfRealMatrix (Node := Node) P0 := by
            rw [hPcAc]
      _ = (z - (1 : ℂ)) • Pc := by
            ext i j
            simp [Pc, complexOfRealMatrix, Matrix.algebraMap_eq_diagonal,
              Matrix.mul_diagonal]
            ring
  have hsmul_pull :
      (z - (1 : ℂ)) • (Pc * M⁻¹) = ((z - (1 : ℂ)) • Pc) * M⁻¹ := by
    ext i j
    simp [Matrix.mul_apply, Finset.mul_sum]
    ring
  change (z - (1 : ℂ)) • (Pc * M⁻¹) = Pc
  calc
    (z - (1 : ℂ)) • (Pc * M⁻¹) =
        ((z - (1 : ℂ)) • Pc) * M⁻¹ := hsmul_pull
    _ = (Pc * M) * M⁻¹ := by rw [← hPcM]
    _ = Pc * (M * M⁻¹) := by rw [Matrix.mul_assoc]
    _ = Pc := by
      rw [Matrix.mul_nonsing_inv M hunit]
      simp

theorem complexified_riesz_projection_fixed_iff
    (A0 P0 : NodeMatrix Node)
    (hfixed :
      ∀ x : RowVector Node,
        matrixMulVector (Node := Node) P0 x = x ↔
          matrixMulVector (Node := Node) A0 x = (1 : ℝ) • x) :
    ∀ v : ComplexRowVector Node,
      complexNodeMatrixMulVector (Node := Node)
          (complexOfRealMatrix (Node := Node) P0) v = v ↔
        complexNodeMatrixMulVector (Node := Node)
          (complexOfRealMatrix (Node := Node) A0) v = v := by
  classical
  intro v
  constructor
  · intro hPv
    have hPv_re :
        matrixMulVector (Node := Node) P0 (fun i : Node => (v i).re) =
          fun i : Node => (v i).re := by
      funext i
      have hi := congrFun hPv i
      have hire := congrArg Complex.re hi
      simpa [complexNodeMatrixMulVector, Matrix.mulVec, matrixMulVector,
        complexOfRealMatrix, dotProduct] using hire
    have hPv_im :
        matrixMulVector (Node := Node) P0 (fun i : Node => (v i).im) =
          fun i : Node => (v i).im := by
      funext i
      have hi := congrFun hPv i
      have hiim := congrArg Complex.im hi
      simpa [complexNodeMatrixMulVector, Matrix.mulVec, matrixMulVector,
        complexOfRealMatrix, dotProduct] using hiim
    have hAv_re :
        matrixMulVector (Node := Node) A0 (fun i : Node => (v i).re) =
          (1 : ℝ) • (fun i : Node => (v i).re) :=
      (hfixed (fun i : Node => (v i).re)).1 hPv_re
    have hAv_im :
        matrixMulVector (Node := Node) A0 (fun i : Node => (v i).im) =
          (1 : ℝ) • (fun i : Node => (v i).im) :=
      (hfixed (fun i : Node => (v i).im)).1 hPv_im
    funext i
    apply Complex.ext
    · have hi := congrFun hAv_re i
      simpa [complexNodeMatrixMulVector, Matrix.mulVec, matrixMulVector,
        complexOfRealMatrix, dotProduct] using hi
    · have hi := congrFun hAv_im i
      simpa [complexNodeMatrixMulVector, Matrix.mulVec, matrixMulVector,
        complexOfRealMatrix, dotProduct] using hi
  · intro hAv
    have hAv_re :
        matrixMulVector (Node := Node) A0 (fun i : Node => (v i).re) =
          (1 : ℝ) • (fun i : Node => (v i).re) := by
      funext i
      have hi := congrFun hAv i
      have hire := congrArg Complex.re hi
      simpa [complexNodeMatrixMulVector, Matrix.mulVec, matrixMulVector,
        complexOfRealMatrix, dotProduct] using hire
    have hAv_im :
        matrixMulVector (Node := Node) A0 (fun i : Node => (v i).im) =
          (1 : ℝ) • (fun i : Node => (v i).im) := by
      funext i
      have hi := congrFun hAv i
      have hiim := congrArg Complex.im hi
      simpa [complexNodeMatrixMulVector, Matrix.mulVec, matrixMulVector,
        complexOfRealMatrix, dotProduct] using hiim
    have hPv_re :
        matrixMulVector (Node := Node) P0 (fun i : Node => (v i).re) =
          fun i : Node => (v i).re :=
      (hfixed (fun i : Node => (v i).re)).2 hAv_re
    have hPv_im :
        matrixMulVector (Node := Node) P0 (fun i : Node => (v i).im) =
          fun i : Node => (v i).im :=
      (hfixed (fun i : Node => (v i).im)).2 hAv_im
    funext i
    apply Complex.ext
    · have hi := congrFun hPv_re i
      simpa [complexNodeMatrixMulVector, Matrix.mulVec, matrixMulVector,
        complexOfRealMatrix, dotProduct] using hi
    · have hi := congrFun hPv_im i
      simpa [complexNodeMatrixMulVector, Matrix.mulVec, matrixMulVector,
        complexOfRealMatrix, dotProduct] using hi

theorem complex_resolvent_shifted_projection_invertible_at_unit
    [DecidableEq Node]
    (A0 P0 : NodeMatrix Node)
    (hfixed :
      ∀ x : RowVector Node,
        matrixMulVector (Node := Node) P0 x = x ↔
          matrixMulVector (Node := Node) A0 x = (1 : ℝ) • x)
    (hPc_idem :
      complexOfRealMatrix (Node := Node) P0 *
          complexOfRealMatrix (Node := Node) P0 =
        complexOfRealMatrix (Node := Node) P0)
    (hAcPc :
      complexOfRealMatrix (Node := Node) A0 *
          complexOfRealMatrix (Node := Node) P0 =
        complexOfRealMatrix (Node := Node) P0)
    (hPcAc :
      complexOfRealMatrix (Node := Node) P0 *
          complexOfRealMatrix (Node := Node) A0 =
        complexOfRealMatrix (Node := Node) P0) :
    Matrix.det
        (complexResolventMatrix (Node := Node) A0 (1 : ℂ) +
          complexOfRealMatrix (Node := Node) P0) ≠ 0 := by
  classical
  let Ac : ComplexNodeMatrix Node := complexOfRealMatrix (Node := Node) A0
  let Pc : ComplexNodeMatrix Node := complexOfRealMatrix (Node := Node) P0
  let M : ComplexNodeMatrix Node :=
    complexResolventMatrix (Node := Node) A0 (1 : ℂ) + Pc
  have hPcM : Pc * M = Pc := by
    calc
      Pc * M =
          Pc * (complexResolventMatrix (Node := Node) A0 (1 : ℂ) + Pc) := rfl
      _ = Pc * complexResolventMatrix (Node := Node) A0 (1 : ℂ) + Pc * Pc := by
          rw [mul_add]
      _ = Pc *
            (algebraMap ℂ (ComplexNodeMatrix Node) (1 : ℂ) - Ac) + Pc := by
          rw [hPc_idem]
          rw [complexResolventMatrix_eq_algebraMap_sub]
      _ = (Pc * algebraMap ℂ (ComplexNodeMatrix Node) (1 : ℂ) -
            Pc * Ac) + Pc := by
          rw [mul_sub]
      _ = Pc := by
          simp [Pc, Ac, hPcAc]
  have _hMPc : M * Pc = Pc := by
    calc
      M * Pc =
          (complexResolventMatrix (Node := Node) A0 (1 : ℂ) + Pc) * Pc := rfl
      _ = complexResolventMatrix (Node := Node) A0 (1 : ℂ) * Pc + Pc * Pc := by
          rw [add_mul]
      _ = (algebraMap ℂ (ComplexNodeMatrix Node) (1 : ℂ) - Ac) *
            Pc + Pc := by
          rw [hPc_idem]
          rw [complexResolventMatrix_eq_algebraMap_sub]
      _ = (algebraMap ℂ (ComplexNodeMatrix Node) (1 : ℂ) * Pc -
            Ac * Pc) + Pc := by
          rw [sub_mul]
      _ = Pc := by
          simp [Pc, Ac, hAcPc]
  change Matrix.det M ≠ 0
  intro hdet
  obtain ⟨v, hvne, hvker⟩ :=
    (Matrix.exists_mulVec_eq_zero_iff (M := M)).2 hdet
  have hPc_kernel : Matrix.mulVec Pc v = 0 := by
    have hleft : Matrix.mulVec (Pc * M) v = 0 := by
      rw [← Matrix.mulVec_mulVec, hvker]
      simp
    simpa [hPcM] using hleft
  have hker_sum :
      Matrix.mulVec (complexResolventMatrix (Node := Node) A0 (1 : ℂ)) v +
          Matrix.mulVec Pc v = 0 := by
    simpa [M, Matrix.add_mulVec] using hvker
  have hres_kernel :
      Matrix.mulVec (complexResolventMatrix (Node := Node) A0 (1 : ℂ)) v =
        0 := by
    simpa [hPc_kernel] using hker_sum
  have hAv_complex :
      complexMatrixMulVector (Node := Node) A0 v = (1 : ℂ) • v :=
    (complexResolventMatrix_mulVec_eq_zero_iff_eigen
      (Node := Node) A0 (1 : ℂ) v).1 (by
        simpa [complexNodeMatrixMulVector] using hres_kernel)
  have hAv_node :
      complexNodeMatrixMulVector (Node := Node) Ac v = v := by
    dsimp [Ac]
    rw [complexNodeMatrixMulVector_complexOfRealMatrix]
    simpa using hAv_complex
  have hPv_eq_v :
      complexNodeMatrixMulVector (Node := Node) Pc v = v := by
    dsimp [Pc]
    exact (complexified_riesz_projection_fixed_iff
      (Node := Node) A0 P0 hfixed v).2 hAv_node
  have hvzero : v = 0 := by
    have hPv_zero :
        complexNodeMatrixMulVector (Node := Node) Pc v = 0 := by
      simpa [complexNodeMatrixMulVector] using hPc_kernel
    rw [← hPv_eq_v]
    exact hPv_zero
  exact hvne hvzero

theorem complex_resolvent_pole_subtracted_eq_shifted_complement
    [DecidableEq Node]
    (A0 P0 : NodeMatrix Node) (z : ℂ)
    (hdet :
      Matrix.det (complexResolventMatrix (Node := Node) A0 z) ≠ 0)
    (hshift_det :
      Matrix.det
        (complexResolventMatrix (Node := Node) A0 z +
          complexOfRealMatrix (Node := Node) P0) ≠ 0)
    (hz_ne_one : z ≠ (1 : ℂ))
    (hPc_idem :
      complexOfRealMatrix (Node := Node) P0 *
          complexOfRealMatrix (Node := Node) P0 =
        complexOfRealMatrix (Node := Node) P0)
    (hAcPc :
      complexOfRealMatrix (Node := Node) A0 *
          complexOfRealMatrix (Node := Node) P0 =
        complexOfRealMatrix (Node := Node) P0)
    (hPcAc :
      complexOfRealMatrix (Node := Node) P0 *
          complexOfRealMatrix (Node := Node) A0 =
        complexOfRealMatrix (Node := Node) P0) :
    (complexResolventMatrix (Node := Node) A0 z)⁻¹ -
        (z - (1 : ℂ))⁻¹ • complexOfRealMatrix (Node := Node) P0 =
      (complexResolventMatrix (Node := Node) A0 z +
          complexOfRealMatrix (Node := Node) P0)⁻¹ *
        (1 - complexOfRealMatrix (Node := Node) P0) := by
  classical
  let M : ComplexNodeMatrix Node := complexResolventMatrix (Node := Node) A0 z
  let Pc : ComplexNodeMatrix Node := complexOfRealMatrix (Node := Node) P0
  let Q : ComplexNodeMatrix Node := 1 - Pc
  have hs_ne : z - (1 : ℂ) ≠ 0 := sub_ne_zero.mpr hz_ne_one
  have hMunit : IsUnit (Matrix.det M) := by
    exact isUnit_iff_ne_zero.mpr (by simpa [M] using hdet)
  have hSunit : IsUnit (Matrix.det (M + Pc)) := by
    exact isUnit_iff_ne_zero.mpr (by simpa [M, Pc] using hshift_det)
  have hleft_smul :
      (z - (1 : ℂ)) • (M⁻¹ * Pc) = Pc := by
    simpa [M, Pc] using
      complex_resolvent_inv_mul_projection_pole (Node := Node)
        A0 P0 z hdet hAcPc
  have hright_smul :
      (z - (1 : ℂ)) • (Pc * M⁻¹) = Pc := by
    simpa [M, Pc] using
      complex_projection_mul_resolvent_inv_pole (Node := Node)
        A0 P0 z hdet hPcAc
  have hleft_pole :
      M⁻¹ * Pc = (z - (1 : ℂ))⁻¹ • Pc := by
    ext i j
    have hentry := congrArg (fun N : ComplexNodeMatrix Node => N i j) hleft_smul
    have hentry' :
        (z - (1 : ℂ)) * (M⁻¹ * Pc) i j = Pc i j := by
      simpa only [Pi.smul_apply, smul_eq_mul] using hentry
    change (M⁻¹ * Pc) i j = (z - (1 : ℂ))⁻¹ * Pc i j
    calc
      (M⁻¹ * Pc) i j =
          (z - (1 : ℂ))⁻¹ * ((z - (1 : ℂ)) * (M⁻¹ * Pc) i j) := by
            field_simp [hs_ne]
      _ = (z - (1 : ℂ))⁻¹ * Pc i j := by rw [hentry']
  have hright_pole :
      Pc * M⁻¹ = (z - (1 : ℂ))⁻¹ • Pc := by
    ext i j
    have hentry := congrArg (fun N : ComplexNodeMatrix Node => N i j) hright_smul
    have hentry' :
        (z - (1 : ℂ)) * (Pc * M⁻¹) i j = Pc i j := by
      simpa only [Pi.smul_apply, smul_eq_mul] using hentry
    change (Pc * M⁻¹) i j = (z - (1 : ℂ))⁻¹ * Pc i j
    calc
      (Pc * M⁻¹) i j =
          (z - (1 : ℂ))⁻¹ * ((z - (1 : ℂ)) * (Pc * M⁻¹) i j) := by
            field_simp [hs_ne]
      _ = (z - (1 : ℂ))⁻¹ * Pc i j := by rw [hentry']
  have hPcQ : Pc * Q = 0 := by
    calc
      Pc * Q = Pc * (1 - Pc) := rfl
      _ = Pc * 1 - Pc * Pc := by rw [mul_sub]
      _ = Pc - Pc := by rw [Matrix.mul_one, hPc_idem]
      _ = 0 := sub_self Pc
  have hscaled_PcQ : ((z - (1 : ℂ))⁻¹ • Pc) * Q = 0 := by
    calc
      ((z - (1 : ℂ))⁻¹ • Pc) * Q =
          (z - (1 : ℂ))⁻¹ • (Pc * Q) := by
            ext i j
            simp [Matrix.mul_apply, Finset.mul_sum]
            ring
      _ = 0 := by rw [hPcQ]; simp
  have hSMQ : (M + Pc) * (M⁻¹ * Q) = Q := by
    calc
      (M + Pc) * (M⁻¹ * Q) =
          (M * M⁻¹) * Q + (Pc * M⁻¹) * Q := by
            rw [add_mul, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = (1 : ComplexNodeMatrix Node) * Q + (Pc * M⁻¹) * Q := by
            rw [Matrix.mul_nonsing_inv M hMunit]
      _ = Q + (Pc * M⁻¹) * Q := by simp
      _ = Q + (((z - (1 : ℂ))⁻¹ • Pc) * Q) := by rw [hright_pole]
      _ = Q := by rw [hscaled_PcQ]; simp
  have hshift :
      M⁻¹ * Q = (M + Pc)⁻¹ * Q := by
    calc
      M⁻¹ * Q = ((M + Pc)⁻¹ * (M + Pc)) * (M⁻¹ * Q) := by
            rw [Matrix.nonsing_inv_mul (M + Pc) hSunit]
            simp
      _ = (M + Pc)⁻¹ * ((M + Pc) * (M⁻¹ * Q)) := by
            rw [Matrix.mul_assoc]
      _ = (M + Pc)⁻¹ * Q := by rw [hSMQ]
  have hdecomp :
      M⁻¹ - (z - (1 : ℂ))⁻¹ • Pc = M⁻¹ * Q := by
    calc
      M⁻¹ - (z - (1 : ℂ))⁻¹ • Pc = M⁻¹ - M⁻¹ * Pc := by
            rw [hleft_pole]
      _ = M⁻¹ * (1 - Pc) := by
            rw [mul_sub, Matrix.mul_one]
      _ = M⁻¹ * Q := rfl
  simpa [M, Pc, Q] using hdecomp.trans hshift

/-- Entrywise base-point residue identity for the fixed Riesz contour.

This is the scalar finite-dimensional contour-calculus leaf beneath Lemma A.1:
on the base separating circle, the integral of the concrete inverse resolvent
has residue exactly the algebraic Riesz projection entry. -/
theorem fixed_circle_base_resolvent_entry_integral_eq_riesz_entry
    (A0 : NodeMatrix Node) (baseRadius : ℝ) (P0 : NodeMatrix Node)
    (hbaseRadius_pos : 0 < baseRadius)
    (hbaseNoBoundary :
      ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
        ¬ IsComplexRightEigenvalue (Node := Node) A0 z)
    (hbaseRiesz :
      IsRieszProjectionAtEigenvalue (Node := Node) A0 1 P0)
    (hbaseEnclosedSpectrum :
      IsComplexRightEigenvalue (Node := Node) A0 (1 : ℂ) ∧
        ∀ z : ℂ, IsComplexRightEigenvalue (Node := Node) A0 z →
          (‖z - (1 : ℂ)‖ < baseRadius ↔ z = (1 : ℂ)) ∧
            (‖z - (1 : ℂ)‖ ≤ baseRadius ↔ z = (1 : ℂ)))
    (i j : Node) :
    (letI : DecidableEq Node := Classical.decEq Node;
      (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ z in C((1 : ℂ), baseRadius),
          ((complexResolventMatrix (Node := Node) A0 z)⁻¹) i j)) =
        (P0 i j : ℂ) := by
  classical
  have hrank :
      RankOneProjection (Node := Node) P0 :=
    IsRieszProjectionAtEigenvalue.rankOne (Node := Node) hbaseRiesz
  have hAP :
      matrixMul (Node := Node) A0 P0 = (1 : ℝ) • P0 :=
    IsRieszProjectionAtEigenvalue.matrix_mul_left (Node := Node) hbaseRiesz
  have hPA :
      matrixMul (Node := Node) P0 A0 = (1 : ℝ) • P0 :=
    IsRieszProjectionAtEigenvalue.matrix_mul_right (Node := Node) hbaseRiesz
  have hfixed :
      ∀ x : RowVector Node,
        matrixMulVector (Node := Node) P0 x = x ↔
          matrixMulVector (Node := Node) A0 x = (1 : ℝ) • x :=
    IsRieszProjectionAtEigenvalue.fixed_iff (Node := Node) hbaseRiesz
  have hsep :
      ∃ radius : ℝ, 0 < radius ∧
        ∀ z : ℂ, ‖z - (1 : ℂ)‖ = radius →
          ¬ IsComplexRightEigenvalue (Node := Node) A0 z :=
    IsRieszProjectionAtEigenvalue.exists_separating_circle (Node := Node)
      hbaseRiesz
  have hsingleton := hbaseEnclosedSpectrum.2
  have hpole :
      (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ z in C((1 : ℂ), baseRadius),
            (z - (1 : ℂ))⁻¹ * (P0 i j : ℂ)) =
        (P0 i j : ℂ) :=
    fixed_circle_simple_pole_entry_integral_eq
      baseRadius hbaseRadius_pos (P0 i j : ℂ)
  have hresolvent_entry_integral_eq_pole :
      (∮ z in C((1 : ℂ), baseRadius),
          ((complexResolventMatrix (Node := Node) A0 z)⁻¹) i j) =
        ∮ z in C((1 : ℂ), baseRadius),
          (z - (1 : ℂ))⁻¹ * (P0 i j : ℂ) := by
    have hcomplexAlgebra :=
      complexified_base_riesz_projection_algebra (Node := Node)
        A0 P0 hrank hAP hPA
    dsimp at hcomplexAlgebra
    rcases hcomplexAlgebra with ⟨hPc_idem, hAcPc, hPcAc⟩
    have hdet_closed_punctured :
        ∀ z : ℂ, ‖z - (1 : ℂ)‖ ≤ baseRadius → z ≠ (1 : ℂ) →
          Matrix.det (complexResolventMatrix (Node := Node) A0 z) ≠ 0 := by
      intro z hzclosed hz_ne_one
      exact fixed_circle_base_resolvent_det_ne_zero_of_ne_unit
        (Node := Node) A0 baseRadius hbaseEnclosedSpectrum z hzclosed
        hz_ne_one
    have hdet_boundary :
        ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
          Matrix.det (complexResolventMatrix (Node := Node) A0 z) ≠ 0 := by
      intro z hzboundary
      exact fixed_circle_base_resolvent_det_ne_zero_on_boundary
        (Node := Node) A0 baseRadius hbaseNoBoundary z hzboundary
    have hleft_pole_on_boundary :
        ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
          (z - (1 : ℂ)) •
              ((complexResolventMatrix (Node := Node) A0 z)⁻¹ *
                complexOfRealMatrix (Node := Node) P0) =
            complexOfRealMatrix (Node := Node) P0 := by
      intro z hzboundary
      exact complex_resolvent_inv_mul_projection_pole (Node := Node)
        A0 P0 z (hdet_boundary z hzboundary) hAcPc
    have hright_pole_on_boundary :
        ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
          (z - (1 : ℂ)) •
              (complexOfRealMatrix (Node := Node) P0 *
                (complexResolventMatrix (Node := Node) A0 z)⁻¹) =
            complexOfRealMatrix (Node := Node) P0 := by
      intro z hzboundary
      exact complex_projection_mul_resolvent_inv_pole (Node := Node)
        A0 P0 z (hdet_boundary z hzboundary) hPcAc
    have hshift_det :
        Matrix.det
            (complexResolventMatrix (Node := Node) A0 (1 : ℂ) +
              complexOfRealMatrix (Node := Node) P0) ≠ 0 :=
      complex_resolvent_shifted_projection_invertible_at_unit
        (Node := Node) A0 P0 hfixed hPc_idem hAcPc hPcAc
    have hshift_det_unit :
        IsUnit
          (Matrix.det
            (complexResolventMatrix (Node := Node) A0 (1 : ℂ) +
              complexOfRealMatrix (Node := Node) P0)) :=
      isUnit_iff_ne_zero.mpr hshift_det
    have hraw_remainder_differentiable_punctured :
        ∀ z ∈ Metric.ball (1 : ℂ) baseRadius \ ({1} : Set ℂ),
          DifferentiableAt ℂ
            (fun w : ℂ =>
              ((complexResolventMatrix (Node := Node) A0 w)⁻¹) i j -
                (w - (1 : ℂ))⁻¹ * (P0 i j : ℂ)) z := by
      intro z hz
      have hz_lt : ‖z - (1 : ℂ)‖ < baseRadius := by
        simpa [Metric.mem_ball, dist_eq_norm] using hz.1
      have hz_ne_one : z ≠ (1 : ℂ) := by
        intro hz1
        exact hz.2 (by simp [hz1])
      have hdet_z :
          Matrix.det (complexResolventMatrix (Node := Node) A0 z) ≠ 0 :=
        hdet_closed_punctured z (le_of_lt hz_lt) hz_ne_one
      have hinv_entry :
          DifferentiableAt ℂ
            (fun w : ℂ =>
              ((complexResolventMatrix (Node := Node) A0 w)⁻¹) i j) z :=
        complex_resolvent_inv_entry_differentiableAt_z_of_det_ne_zero
          (Node := Node) A0 hdet_z i j
      have hpole :
          DifferentiableAt ℂ
            (fun w : ℂ => (w - (1 : ℂ))⁻¹ * (P0 i j : ℂ)) z := by
        have hsub_ne : z - (1 : ℂ) ≠ 0 := sub_ne_zero.mpr hz_ne_one
        have hsub_diff :
            DifferentiableAt ℂ (fun w : ℂ => w - (1 : ℂ)) z :=
          differentiableAt_id.sub
            (differentiableAt_const (𝕜 := ℂ) (c := (1 : ℂ)) (x := z))
        exact ((differentiableAt_inv hsub_ne).comp z hsub_diff).mul
          (differentiableAt_const (𝕜 := ℂ) (c := (P0 i j : ℂ)) (x := z))
      exact hinv_entry.sub hpole
    have hreduced_resolvent_identity :
        ∀ z : ℂ, ‖z - (1 : ℂ)‖ ≤ baseRadius → z ≠ (1 : ℂ) →
          Matrix.det
              (complexResolventMatrix (Node := Node) A0 z +
                complexOfRealMatrix (Node := Node) P0) ≠ 0 →
            (complexResolventMatrix (Node := Node) A0 z)⁻¹ -
                (z - (1 : ℂ))⁻¹ • complexOfRealMatrix (Node := Node) P0 =
              (complexResolventMatrix (Node := Node) A0 z +
                  complexOfRealMatrix (Node := Node) P0)⁻¹ *
                (1 - complexOfRealMatrix (Node := Node) P0) := by
      intro z hzclosed hz_ne_one hshift_det_z
      exact complex_resolvent_pole_subtracted_eq_shifted_complement
        (Node := Node) A0 P0 z
        (hdet_closed_punctured z hzclosed hz_ne_one) hshift_det_z
        hz_ne_one hPc_idem hAcPc hPcAc
    have hshift_det_eventually :
        ∀ᶠ z in 𝓝 (1 : ℂ),
          Matrix.det
            (complexResolventMatrix (Node := Node) A0 z +
              complexOfRealMatrix (Node := Node) P0) ≠ 0 := by
      have hshift_det_analytic :
          AnalyticAt ℂ
            (fun z : ℂ =>
              Matrix.det
                (complexResolventMatrix (Node := Node) A0 z +
                  complexOfRealMatrix (Node := Node) P0))
            (1 : ℂ) := by
        exact complexMatrix_det_analyticAt_z (Node := Node)
          (fun z : ℂ =>
            complexResolventMatrix (Node := Node) A0 z +
              complexOfRealMatrix (Node := Node) P0)
          (z0 := (1 : ℂ)) (by
            intro r c
            simpa using
              (complexResolventMatrix_entry_analyticAt_z
                (Node := Node) A0 (z0 := (1 : ℂ)) r c).add
                (analyticAt_const (𝕜 := ℂ) (E := ℂ) (F := ℂ)
                  (v := complexOfRealMatrix (Node := Node) P0 r c)
                  (x := (1 : ℂ))))
      exact hshift_det_analytic.continuousAt.eventually_ne hshift_det
    let Pc : ComplexNodeMatrix Node := complexOfRealMatrix (Node := Node) P0
    let correctedRemainder : ℂ → ℂ := fun w : ℂ =>
      if w = (1 : ℂ) then
        (((complexResolventMatrix (Node := Node) A0 (1 : ℂ) + Pc)⁻¹ *
          (1 - Pc)) i j)
      else
        ((complexResolventMatrix (Node := Node) A0 w)⁻¹) i j -
          (w - (1 : ℂ))⁻¹ * (P0 i j : ℂ)
    let rawRemainder : ℂ → ℂ := fun w : ℂ =>
      ((complexResolventMatrix (Node := Node) A0 w)⁻¹) i j -
        (w - (1 : ℂ))⁻¹ * (P0 i j : ℂ)
    have hcorrected_eventually_shifted :
        ∀ᶠ w in 𝓝 (1 : ℂ),
          correctedRemainder w =
            (((complexResolventMatrix (Node := Node) A0 w + Pc)⁻¹ *
              (1 - Pc)) i j) := by
      filter_upwards
        [hshift_det_eventually,
          Metric.closedBall_mem_nhds (1 : ℂ) hbaseRadius_pos]
        with w hshift_w hwclosed
      by_cases hw : w = (1 : ℂ)
      · simp [correctedRemainder, Pc, hw]
      · have hwclosed_norm : ‖w - (1 : ℂ)‖ ≤ baseRadius := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hwclosed
        have hid := hreduced_resolvent_identity w hwclosed_norm hw hshift_w
        have hentry := congrArg (fun N : ComplexNodeMatrix Node => N i j) hid
        simpa [correctedRemainder, Pc, hw, Matrix.sub_apply, Pi.smul_apply,
          smul_eq_mul, complexOfRealMatrix] using hentry
    have hshifted_entry_continuousAt :
        ContinuousAt
          (fun w : ℂ =>
            (((complexResolventMatrix (Node := Node) A0 w + Pc)⁻¹ *
              (1 - Pc)) i j))
          (1 : ℂ) := by
      have hmatrix_cont :
          ContinuousAt
            (fun w : ℂ =>
              complexResolventMatrix (Node := Node) A0 w + Pc)
            (1 : ℂ) :=
        ((complexResolventMatrix_continuous_z (Node := Node) A0).add
          continuous_const).continuousAt
      have hdetInverse :
          ContinuousAt Ring.inverse
            (Matrix.det
              (complexResolventMatrix (Node := Node) A0 (1 : ℂ) + Pc)) := by
        simpa only [Ring.inverse_eq_inv'] using
          continuousAt_inv₀ (by simpa [Pc] using hshift_det)
      have hinvAt :
          ContinuousAt (fun M : ComplexNodeMatrix Node => M⁻¹)
            (complexResolventMatrix (Node := Node) A0 (1 : ℂ) + Pc) :=
        continuousAt_matrix_inv
          (complexResolventMatrix (Node := Node) A0 (1 : ℂ) + Pc)
          hdetInverse
      have hinv_comp :
          ContinuousAt
            (fun w : ℂ =>
              (complexResolventMatrix (Node := Node) A0 w + Pc)⁻¹)
            (1 : ℂ) :=
        by
          simpa only [Function.comp_apply] using
            (ContinuousAt.comp
              (f := fun w : ℂ =>
                complexResolventMatrix (Node := Node) A0 w + Pc)
              (g := fun M : ComplexNodeMatrix Node => M⁻¹)
              hinvAt hmatrix_cont)
      have hmul_cont :
          ContinuousAt
            (fun w : ℂ =>
              (complexResolventMatrix (Node := Node) A0 w + Pc)⁻¹ *
                (1 - Pc))
            (1 : ℂ) :=
        hinv_comp.mul continuousAt_const
      exact (continuous_apply j).continuousAt.comp'
        ((continuous_apply i).continuousAt.comp' hmul_cont)
    have hcorrected_continuousAt_unit :
        ContinuousAt correctedRemainder (1 : ℂ) :=
      hshifted_entry_continuousAt.congr_of_eventuallyEq
        hcorrected_eventually_shifted
    have hcorrected_continuousOn_closedBall :
        ContinuousOn correctedRemainder
          (Metric.closedBall (1 : ℂ) baseRadius) := by
      intro z hzclosedBall
      by_cases hz_one : z = (1 : ℂ)
      · subst z
        exact hcorrected_continuousAt_unit.continuousWithinAt
      · have hzclosed_norm : ‖z - (1 : ℂ)‖ ≤ baseRadius := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hzclosedBall
        have hdet_z :
            Matrix.det
              (complexResolventMatrix (Node := Node) A0 z) ≠ 0 :=
          hdet_closed_punctured z hzclosed_norm hz_one
        have hinv_entry :
            DifferentiableAt ℂ
              (fun w : ℂ =>
                ((complexResolventMatrix (Node := Node) A0 w)⁻¹) i j) z :=
          complex_resolvent_inv_entry_differentiableAt_z_of_det_ne_zero
            (Node := Node) A0 hdet_z i j
        have hpole_diff :
            DifferentiableAt ℂ
              (fun w : ℂ => (w - (1 : ℂ))⁻¹ * (P0 i j : ℂ)) z := by
          have hsub_ne : z - (1 : ℂ) ≠ 0 := sub_ne_zero.mpr hz_one
          have hsub_diff :
              DifferentiableAt ℂ (fun w : ℂ => w - (1 : ℂ)) z :=
            differentiableAt_id.sub
              (differentiableAt_const (𝕜 := ℂ) (c := (1 : ℂ)) (x := z))
          exact ((differentiableAt_inv hsub_ne).comp z hsub_diff).mul
            (differentiableAt_const (𝕜 := ℂ)
              (c := (P0 i j : ℂ)) (x := z))
        have hraw_cont : ContinuousAt rawRemainder z := by
          simpa [rawRemainder] using (hinv_entry.sub hpole_diff).continuousAt
        have hcorrected_eventually_raw :
            correctedRemainder =ᶠ[𝓝 z] rawRemainder := by
          filter_upwards [isOpen_ne.eventually_mem hz_one] with w hw
          simp [correctedRemainder, rawRemainder, hw]
        exact
          (hraw_cont.congr_of_eventuallyEq
            hcorrected_eventually_raw).continuousWithinAt
    have hcorrected_differentiableOn_punctured :
        DifferentiableOn ℂ correctedRemainder
          (Metric.ball (1 : ℂ) baseRadius \ ({1} : Set ℂ)) := by
      intro z hz
      have hz_ne_one : z ≠ (1 : ℂ) := by
        intro hz1
        exact hz.2 (by simp [hz1])
      have hraw_diff : DifferentiableAt ℂ rawRemainder z := by
        simpa [rawRemainder] using
          hraw_remainder_differentiable_punctured z hz
      have hcorrected_eventually_raw :
          correctedRemainder =ᶠ[𝓝 z] rawRemainder := by
        filter_upwards [isOpen_ne.eventually_mem hz_ne_one] with w hw
        simp [correctedRemainder, rawRemainder, hw]
      exact
        (hraw_diff.congr_of_eventuallyEq
          hcorrected_eventually_raw).differentiableWithinAt
    have hcorrected_differentiableAt_punctured :
        ∀ z ∈ Metric.ball (1 : ℂ) baseRadius \ ({1} : Set ℂ),
          DifferentiableAt ℂ correctedRemainder z := by
      intro z hz
      have hz_ne_one : z ≠ (1 : ℂ) := by
        intro hz1
        exact hz.2 (by simp [hz1])
      have hraw_diff : DifferentiableAt ℂ rawRemainder z := by
        simpa [rawRemainder] using
          hraw_remainder_differentiable_punctured z hz
      have hcorrected_eventually_raw :
          correctedRemainder =ᶠ[𝓝 z] rawRemainder := by
        filter_upwards [isOpen_ne.eventually_mem hz_ne_one] with w hw
        simp [correctedRemainder, rawRemainder, hw]
      exact hraw_diff.congr_of_eventuallyEq hcorrected_eventually_raw
    have hcorrected_integral_zero :
        (∮ z in C((1 : ℂ), baseRadius), correctedRemainder z) = 0 :=
      Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
        (le_of_lt hbaseRadius_pos) (Set.countable_singleton (1 : ℂ))
        hcorrected_continuousOn_closedBall
        hcorrected_differentiableAt_punctured
    have hraw_integral_zero :
        (∮ z in C((1 : ℂ), baseRadius), rawRemainder z) = 0 := by
      rw [← hcorrected_integral_zero]
      refine circleIntegral.integral_congr (le_of_lt hbaseRadius_pos) ?_
      intro z hz
      have hz_norm : ‖z - (1 : ℂ)‖ = baseRadius := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hz
      have hz_ne_one : z ≠ (1 : ℂ) := by
        intro hz1
        have hzero : (0 : ℝ) = baseRadius := by
          simpa [hz1] using hz_norm
        nlinarith
      simp [correctedRemainder, rawRemainder, hz_ne_one]
    have hresolvent_circleIntegrable :
        CircleIntegrable
          (fun z : ℂ =>
            ((complexResolventMatrix (Node := Node) A0 z)⁻¹) i j)
          (1 : ℂ) baseRadius := by
      have hcont_sphere :
          ContinuousOn
            (fun z : ℂ =>
              ((complexResolventMatrix (Node := Node) A0 z)⁻¹) i j)
            (Metric.sphere (1 : ℂ) baseRadius) := by
        intro z hz
        have hz_norm : ‖z - (1 : ℂ)‖ = baseRadius := by
          simpa [Metric.mem_sphere, dist_eq_norm] using hz
        have hdet_z :
            Matrix.det
              (complexResolventMatrix (Node := Node) A0 z) ≠ 0 :=
          hdet_boundary z hz_norm
        exact
          (complex_resolvent_inv_entry_differentiableAt_z_of_det_ne_zero
            (Node := Node) A0 hdet_z i j).continuousAt.continuousWithinAt
      exact hcont_sphere.circleIntegrable (le_of_lt hbaseRadius_pos)
    have hpole_circleIntegrable :
        CircleIntegrable
          (fun z : ℂ => (z - (1 : ℂ))⁻¹ * (P0 i j : ℂ))
          (1 : ℂ) baseRadius := by
      have hcont_sphere :
          ContinuousOn
            (fun z : ℂ => (z - (1 : ℂ))⁻¹ * (P0 i j : ℂ))
            (Metric.sphere (1 : ℂ) baseRadius) := by
        intro z hz
        have hz_norm : ‖z - (1 : ℂ)‖ = baseRadius := by
          simpa [Metric.mem_sphere, dist_eq_norm] using hz
        have hz_ne_one : z ≠ (1 : ℂ) := by
          intro hz1
          have hzero : (0 : ℝ) = baseRadius := by
            simpa [hz1] using hz_norm
          nlinarith
        have hsub_ne : z - (1 : ℂ) ≠ 0 := sub_ne_zero.mpr hz_ne_one
        have hsub_diff :
            DifferentiableAt ℂ (fun w : ℂ => w - (1 : ℂ)) z :=
          differentiableAt_id.sub
            (differentiableAt_const (𝕜 := ℂ) (c := (1 : ℂ)) (x := z))
        exact
          (((differentiableAt_inv hsub_ne).comp z hsub_diff).mul
            (differentiableAt_const (𝕜 := ℂ)
              (c := (P0 i j : ℂ)) (x := z))).continuousAt.continuousWithinAt
      exact hcont_sphere.circleIntegrable (le_of_lt hbaseRadius_pos)
    have hraw_integral_sub :
        (∮ z in C((1 : ℂ), baseRadius), rawRemainder z) =
          (∮ z in C((1 : ℂ), baseRadius),
              ((complexResolventMatrix (Node := Node) A0 z)⁻¹) i j) -
            ∮ z in C((1 : ℂ), baseRadius),
              (z - (1 : ℂ))⁻¹ * (P0 i j : ℂ) := by
      simpa [rawRemainder] using
        circleIntegral.integral_sub hresolvent_circleIntegrable
          hpole_circleIntegrable
    have hsub_zero :
        (∮ z in C((1 : ℂ), baseRadius),
            ((complexResolventMatrix (Node := Node) A0 z)⁻¹) i j) -
          ∮ z in C((1 : ℂ), baseRadius),
            (z - (1 : ℂ))⁻¹ * (P0 i j : ℂ) = 0 := by
      simpa [hraw_integral_sub] using hraw_integral_zero
    exact sub_eq_zero.mp hsub_zero
  /-
  The simple-pole integral is now discharged above; the only remaining source
  contour theorem is the holomorphic stable-remainder identity
  `hresolvent_entry_integral_eq_pole`.
  -/
  rw [hresolvent_entry_integral_eq_pole]
  exact hpole

/-- Complex base fixed-contour projection equals the algebraic Riesz projection.

This packages the entrywise residue identity into the matrix-level complex
projection equality needed before descending to real entries. -/
theorem complex_fixed_circle_riesz_projection_eq_complexified_riesz_of_base_singleton
    (A0 : NodeMatrix Node) (baseRadius : ℝ) (P0 : NodeMatrix Node)
    (hbaseRadius_pos : 0 < baseRadius)
    (hbaseNoBoundary :
      ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
        ¬ IsComplexRightEigenvalue (Node := Node) A0 z)
    (hbaseRiesz :
      IsRieszProjectionAtEigenvalue (Node := Node) A0 1 P0)
    (hbaseEnclosedSpectrum :
      IsComplexRightEigenvalue (Node := Node) A0 (1 : ℂ) ∧
        ∀ z : ℂ, IsComplexRightEigenvalue (Node := Node) A0 z →
          (‖z - (1 : ℂ)‖ < baseRadius ↔ z = (1 : ℂ)) ∧
            (‖z - (1 : ℂ)‖ ≤ baseRadius ↔ z = (1 : ℂ))) :
    complexRieszProjectionOnCircle (Node := Node) A0 (1 : ℂ) baseRadius =
      complexOfRealMatrix (Node := Node) P0 := by
  classical
  ext i j
  simpa [complexRieszProjectionOnCircle, complexOfRealMatrix] using
    fixed_circle_base_resolvent_entry_integral_eq_riesz_entry (Node := Node)
      A0 baseRadius P0 hbaseRadius_pos hbaseNoBoundary hbaseRiesz
      hbaseEnclosedSpectrum i j

/-- Real descent from the complex base-contour equality. -/
theorem fixed_circle_real_part_eq_of_complexified_riesz
    (A0 : NodeMatrix Node) (baseRadius : ℝ) (P0 : NodeMatrix Node)
    (hcomplex :
      complexRieszProjectionOnCircle (Node := Node) A0 (1 : ℂ) baseRadius =
        complexOfRealMatrix (Node := Node) P0) :
    fixedCircleRieszProjection (Node := Node) A0 (1 : ℂ) baseRadius = P0 := by
  classical
  ext i j
  change
    (complexRieszProjectionOnCircle (Node := Node) A0 (1 : ℂ) baseRadius i j).re =
      P0 i j
  rw [hcomplex]
  simp [complexOfRealMatrix]

/-- Endpoint-local analyticity of the canonical fixed-circle projection.

The source contour argument uses a larger analytic/no-boundary margin than the
closed parameter interval on which the final Riesz branch is stated.  At an
endpoint `|alpha| = rho`, the open-interval hypothesis `hP_analytic` is not
available; instead, shift `alpha` to the origin and use the remaining margin
`rhoAnalytic - |alpha|` to reapply the fixed-contour analytic integral
infrastructure locally. -/
theorem fixed_circle_projection_endpoint_local_analyticity
    [DecidableEq Node]
    (A : ℝ → NodeMatrix Node) (rho rhoAnalytic baseRadius : ℝ)
    (hrho_lt_analytic : rho < rhoAnalytic)
    (hbaseRadius_pos : 0 < baseRadius)
    (hA_analytic :
      ∀ alpha : ℝ, |alpha| < rhoAnalytic → AnalyticAt ℝ A alpha)
    (hnoBoundary :
      ∀ alpha : ℝ, |alpha| ≤ rhoAnalytic →
        ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
          ¬ IsComplexRightEigenvalue (Node := Node) (A alpha) z) :
    ∀ alpha : ℝ, |alpha| ≤ rho →
      AnalyticAt ℝ
        (fun a : ℝ =>
          fixedCircleRieszProjection (Node := Node)
            (A a) (1 : ℂ) baseRadius)
        alpha := by
  classical
  intro alpha halpha
  let eps : ℝ := rhoAnalytic - |alpha|
  have heps_pos : 0 < eps := by
    dsimp [eps]
    exact sub_pos.mpr (lt_of_le_of_lt halpha hrho_lt_analytic)
  let Ashift : ℝ → NodeMatrix Node := fun beta => A (alpha + beta)
  have hAshift :
      ∀ beta : ℝ, |beta| < eps → AnalyticAt ℝ Ashift beta := by
    intro beta hbeta
    have habs_lt : |alpha + beta| < rhoAnalytic := by
      have hsum : |alpha + beta| ≤ |alpha| + |beta| := abs_add_le alpha beta
      have hlt : |alpha| + |beta| < rhoAnalytic := by
        dsimp [eps] at hbeta
        linarith
      exact lt_of_le_of_lt hsum hlt
    have hAat : AnalyticAt ℝ A (alpha + beta) :=
      hA_analytic (alpha + beta) habs_lt
    have haff : AnalyticAt ℝ (fun t : ℝ => alpha + t) beta :=
      analyticAt_const.add analyticAt_id
    simpa [Ashift, Function.comp_def] using hAat.comp haff
  have hnoBoundaryShift :
      ∀ beta : ℝ, |beta| ≤ eps / 2 →
        ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
          ¬ IsComplexRightEigenvalue (Node := Node) (Ashift beta) z := by
    intro beta hbeta z hz
    have habs_le : |alpha + beta| ≤ rhoAnalytic := by
      have hsum : |alpha + beta| ≤ |alpha| + |beta| := abs_add_le alpha beta
      have hbeta_le_eps : |beta| ≤ eps := by
        nlinarith [hbeta, heps_pos]
      have hlt : |alpha| + |beta| ≤ rhoAnalytic := by
        dsimp [eps] at hbeta_le_eps
        linarith
      exact le_trans hsum hlt
    simpa [Ashift] using hnoBoundary (alpha + beta) habs_le z hz
  have hcomplexShift :
      ∀ beta : ℝ, |beta| < eps / 2 →
        ∀ i j : Node,
          AnalyticAt ℝ
            (fun b : ℝ =>
              complexRieszProjectionOnCircle (Node := Node)
                (Ashift b) (1 : ℂ) baseRadius i j)
            beta :=
    complexRieszProjectionOnCircle_entries_analyticAt_of_fixed_interval_integrand
      (Node := Node) Ashift eps (1 : ℂ) baseRadius heps_pos
      (le_of_lt hbaseRadius_pos) hAshift hnoBoundaryShift
      (by
        intro beta i j
        exact complexRieszProjectionOnCircle_entry_eq_Icc_integral
          (Node := Node) (Ashift beta) (1 : ℂ) baseRadius i j)
  have hfixedShift :
      AnalyticAt ℝ
        (fun beta : ℝ =>
          fixedCircleRieszProjection (Node := Node)
            (Ashift beta) (1 : ℂ) baseRadius)
        0 := by
    have hzero : |(0 : ℝ)| < eps / 2 := by
      simpa using half_pos heps_pos
    exact fixedCircleRieszProjection_analyticAt_of_complex_entries
      (Node := Node) Ashift (1 : ℂ) baseRadius
      (alpha := 0) (hcomplexShift 0 hzero)
  have hshiftedAtAlpha :
      AnalyticAt ℝ
        (fun a : ℝ =>
          fixedCircleRieszProjection (Node := Node)
            (Ashift (a - alpha)) (1 : ℂ) baseRadius)
        alpha := by
    simpa using hfixedShift.comp_sub alpha
  simpa [Ashift] using hshiftedAtAlpha

/-- Base rank-one property transported to the canonical fixed contour object.

This is the first input to the source rank-constancy sentence: after the base
contour integral has been identified with the algebraic Riesz projection, the
actual contour projection has rank one at `alpha = 0`. -/
theorem fixed_circle_projection_base_rankOne_of_base_eq
    (A0 : NodeMatrix Node) (baseRadius : ℝ) (P0 : NodeMatrix Node)
    (hbaseContourEq :
      fixedCircleRieszProjection (Node := Node) A0 (1 : ℂ) baseRadius = P0)
    (hbaseRiesz :
      IsRieszProjectionAtEigenvalue (Node := Node) A0 1 P0) :
    RankOneProjection (Node := Node)
      (fixedCircleRieszProjection (Node := Node) A0 (1 : ℂ) baseRadius) := by
  rw [hbaseContourEq]
  exact IsRieszProjectionAtEigenvalue.rankOne (Node := Node) hbaseRiesz

theorem complexRieszProjectionOnCircle_idempotent_and_real_entries_of_no_boundary
    [DecidableEq Node]
    (Aalpha : NodeMatrix Node) (baseRadius : ℝ)
    (hbaseRadius_pos : 0 < baseRadius)
    (hnoBoundary :
      ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
        ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z) :
    complexMatrixMul (Node := Node)
        (complexRieszProjectionOnCircle (Node := Node)
          Aalpha (1 : ℂ) baseRadius)
        (complexRieszProjectionOnCircle (Node := Node)
          Aalpha (1 : ℂ) baseRadius) =
      complexRieszProjectionOnCircle (Node := Node)
        Aalpha (1 : ℂ) baseRadius ∧
      ∀ i j : Node,
        ((complexRieszProjectionOnCircle (Node := Node)
        Aalpha (1 : ℂ) baseRadius i j).im = 0) := by
  classical
  letI : DecidableEq Node := Classical.decEq Node
  have hboundary_det :
      ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
        Matrix.det (complexResolventMatrix (Node := Node) Aalpha z) ≠ 0 := by
    intro z hz
    exact complexResolvent_det_ne_zero_of_not_eigen (Node := Node) Aalpha z
      (hnoBoundary z hz)
  have hresolvent_identity :
      ∀ z w : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
        ‖w - (1 : ℂ)‖ = baseRadius →
          (complexResolventMatrix (Node := Node) Aalpha z)⁻¹ -
              (complexResolventMatrix (Node := Node) Aalpha w)⁻¹ =
            (w - z) •
              ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹ *
                (complexResolventMatrix (Node := Node) Aalpha w)⁻¹) := by
    intro z w hz hw
    exact complex_resolvent_inverse_identity_two_points (Node := Node)
      Aalpha z w (hnoBoundary z hz) (hnoBoundary w hw)
  have hsimple_pole :
      ∀ c : ℂ,
        (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
            (∮ z in C((1 : ℂ), baseRadius), (z - (1 : ℂ))⁻¹ * c) = c := by
    intro c
    exact fixed_circle_simple_pole_entry_integral_eq baseRadius
      hbaseRadius_pos c
  have hboundary_conj :
      ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
        ‖conj z - (1 : ℂ)‖ = baseRadius := by
    intro z hz
    exact fixed_unit_circle_conj_boundary baseRadius hz
  have hresolvent_conj_entry :
      ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
        ∀ i j : Node,
          conj
              (((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i j) =
            ((complexResolventMatrix (Node := Node) Aalpha (conj z))⁻¹) i j := by
    intro z hz i j
    exact complexResolvent_inv_conj_entry_of_not_eigen (Node := Node)
      Aalpha z (hnoBoundary z hz) i j
  have hcircleMap_boundary :
      ∀ theta : ℝ,
        ‖circleMap (1 : ℂ) baseRadius theta - (1 : ℂ)‖ =
          baseRadius := by
    intro theta
    exact fixed_circleMap_boundary_norm baseRadius hbaseRadius_pos theta
  have hcircleMap_conj :
      ∀ theta : ℝ,
        conj (circleMap (1 : ℂ) baseRadius theta) =
          circleMap (1 : ℂ) baseRadius (-theta) := by
    intro theta
    exact fixed_circleMap_conj baseRadius theta
  have hcircleMap_deriv_conj :
      ∀ theta : ℝ,
        conj (deriv (circleMap (1 : ℂ) baseRadius) theta) =
          -deriv (circleMap (1 : ℂ) baseRadius) (-theta) := by
    intro theta
    exact fixed_circleMap_deriv_conj baseRadius theta
  have hscaled_resolvent_conj_entry :
      ∀ theta : ℝ, ∀ i j : Node,
        conj
            (deriv (circleMap (1 : ℂ) baseRadius) theta *
              ((complexResolventMatrix (Node := Node) Aalpha
                (circleMap (1 : ℂ) baseRadius theta))⁻¹) i j) =
          -deriv (circleMap (1 : ℂ) baseRadius) (-theta) *
              ((complexResolventMatrix (Node := Node) Aalpha
                (circleMap (1 : ℂ) baseRadius (-theta)))⁻¹) i j := by
    intro theta i j
    have hres :=
      hresolvent_conj_entry (circleMap (1 : ℂ) baseRadius theta)
        (hcircleMap_boundary theta) i j
    rw [hcircleMap_conj theta] at hres
    calc
      conj
          (deriv (circleMap (1 : ℂ) baseRadius) theta *
            ((complexResolventMatrix (Node := Node) Aalpha
              (circleMap (1 : ℂ) baseRadius theta))⁻¹) i j) =
          conj (deriv (circleMap (1 : ℂ) baseRadius) theta) *
            conj
              (((complexResolventMatrix (Node := Node) Aalpha
                (circleMap (1 : ℂ) baseRadius theta))⁻¹) i j) := by
            rw [map_mul]
      _ =
          -deriv (circleMap (1 : ℂ) baseRadius) (-theta) *
              ((complexResolventMatrix (Node := Node) Aalpha
                (circleMap (1 : ℂ) baseRadius (-theta)))⁻¹) i j := by
            rw [hcircleMap_deriv_conj theta, hres]
  /-
  Remaining complex contour primitive.  The first projection component is the
  standard double-contour calculation: expand the matrix product of the two
  circle integrals, use `hresolvent_identity` entrywise, and reduce the two
  resulting simple-pole circle integrals with `hsimple_pole` to the original
  contour integral.
  The second component is the conjugation-symmetry descent for a real matrix
  on the real-centered circle; the algebraic inverse-resolvent conjugation and
  boundary invariance have now been sharpened to the parameter-level scaled
  integrand identity `hscaled_resolvent_conj_entry`.  Both are strictly below the real
  `fixedCircleRieszProjection` statement and are the contour/Riesz calculus
  still missing from local Mathlib/SOptLib infrastructure.
  -/
  refine ⟨?_, ?_⟩
  · /-
    Exact remaining complex contour primitive: expand the matrix product of
    the two contour integrals, exchange the finite node sum with the two
    circle integrals, apply `hresolvent_identity` entrywise, and reduce the
    two simple-pole terms with `hsimple_pole`.
    -/
    have hresolvent_entry_circleIntegrable :
        ∀ i j : Node,
          CircleIntegrable
            (fun z : ℂ =>
              ((complexResolventMatrix (Node := Node) Aalpha z)⁻¹) i j)
            (1 : ℂ) baseRadius := by
      intro i j
      exact fixed_circle_resolvent_inv_entry_circleIntegrable_of_no_boundary
        (Node := Node) Aalpha baseRadius hbaseRadius_pos hnoBoundary i j
    ext i j
    rw [complexRieszProjectionOnCircle_mul_self_entry_eq_single_contour_right
      (Node := Node) Aalpha baseRadius hresolvent_entry_circleIntegrable i j]
    exact
      complexRieszProjectionOnCircle_resolvent_action_eq_self_of_no_boundary
        (Node := Node) Aalpha baseRadius hbaseRadius_pos hnoBoundary i j
  · intro i j
    exact
      complexRieszProjectionOnCircle_entry_im_zero_of_scaled_conj_and_neg_integral
        (Node := Node) Aalpha baseRadius i j
        (by
          intro theta
          exact hscaled_resolvent_conj_entry theta i j)
        (fixed_circle_scaled_resolvent_neg_Icc_integral_eq_self
          (Node := Node) Aalpha baseRadius i j)

/-- Real fixed-contour idempotence from the complex contour projection.

This is the algebraic descent layer below Lemma A.1: once the complex contour
integral is known to be idempotent and to have real entries, the real-part
projection `fixedCircleRieszProjection` is idempotent in the file's real matrix
algebra. -/
theorem fixed_circle_contour_projection_idempotent_of_complex_idempotent_and_real_entries
    (Aalpha : NodeMatrix Node) (baseRadius : ℝ)
    (hcomplexIdem :
      complexMatrixMul (Node := Node)
          (complexRieszProjectionOnCircle (Node := Node)
            Aalpha (1 : ℂ) baseRadius)
          (complexRieszProjectionOnCircle (Node := Node)
            Aalpha (1 : ℂ) baseRadius) =
        complexRieszProjectionOnCircle (Node := Node)
          Aalpha (1 : ℂ) baseRadius)
    (hreal_entries :
      ∀ i j : Node,
        ((complexRieszProjectionOnCircle (Node := Node)
          Aalpha (1 : ℂ) baseRadius i j).im = 0)) :
    matrixMul (Node := Node)
        (fixedCircleRieszProjection (Node := Node) Aalpha (1 : ℂ) baseRadius)
        (fixedCircleRieszProjection (Node := Node) Aalpha (1 : ℂ) baseRadius) =
      fixedCircleRieszProjection (Node := Node) Aalpha (1 : ℂ) baseRadius := by
  classical
  let Pℝ : NodeMatrix Node :=
    fixedCircleRieszProjection (Node := Node) Aalpha (1 : ℂ) baseRadius
  let Pℂ : ComplexNodeMatrix Node :=
    complexRieszProjectionOnCircle (Node := Node) Aalpha (1 : ℂ) baseRadius
  have hcomplexOfReal :
      complexOfRealMatrix (Node := Node) Pℝ = Pℂ := by
    ext i j
    apply Complex.ext
    · simp [Pℝ, Pℂ, fixedCircleRieszProjection, realPartComplexNodeMatrix,
        complexOfRealMatrix]
    · simp [Pℝ, Pℂ, fixedCircleRieszProjection, realPartComplexNodeMatrix,
        complexOfRealMatrix, hreal_entries i j]
  have hcomplex_real_idem :
      complexOfRealMatrix (Node := Node)
          (matrixMul (Node := Node) Pℝ Pℝ) =
        complexOfRealMatrix (Node := Node) Pℝ := by
    rw [complexOfRealMatrix_matrixMul, hcomplexOfReal]
    exact hcomplexIdem
  change matrixMul (Node := Node) Pℝ Pℝ = Pℝ
  ext i j
  have hentry :=
    congrArg (fun M : ComplexNodeMatrix Node => M i j) hcomplex_real_idem
  exact Complex.ofReal_injective (by
    simpa [complexOfRealMatrix] using hentry)

/-- Pointwise idempotence of the fixed-circle contour projection.

This is the algebraic half of the finite-dimensional contour theorem used in
Lemma A.1: if the fixed circle is contained in the resolvent set, the contour
integral `(2πi)⁻¹ ∮ (zI-A)⁻¹ dz` is a projection.  The remaining proof is the
standard resolvent-identity double-contour calculation, specialized to the
file's concrete `fixedCircleRieszProjection` object. -/
theorem fixed_circle_contour_projection_idempotent_of_no_boundary
    (Aalpha : NodeMatrix Node) (baseRadius : ℝ)
    (hbaseRadius_pos : 0 < baseRadius)
    (hnoBoundary :
      ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
        ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z) :
    matrixMul (Node := Node)
        (fixedCircleRieszProjection (Node := Node) Aalpha (1 : ℂ) baseRadius)
        (fixedCircleRieszProjection (Node := Node) Aalpha (1 : ℂ) baseRadius) =
      fixedCircleRieszProjection (Node := Node) Aalpha (1 : ℂ) baseRadius := by
  classical
  obtain ⟨hcomplexIdem, hreal_entries⟩ :=
    complexRieszProjectionOnCircle_idempotent_and_real_entries_of_no_boundary
      (Node := Node) Aalpha baseRadius hbaseRadius_pos hnoBoundary
  exact
    fixed_circle_contour_projection_idempotent_of_complex_idempotent_and_real_entries
      (Node := Node) Aalpha baseRadius hcomplexIdem hreal_entries

end Setup
end Algorithms.Unverified.TimeVaryingPushPull
