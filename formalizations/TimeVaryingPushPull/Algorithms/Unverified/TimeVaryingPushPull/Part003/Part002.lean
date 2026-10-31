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
import SOptLib.Glue.Martingale
import SOptLib.Layer0.Objective
import SOptLib.Layer1.Telescope
import Algorithms.Unverified.TimeVaryingPushPull.Part002
import Algorithms.Unverified.TimeVaryingPushPull.Part003.Part001

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

/-- Complex fixed-contour commutation with the underlying real matrix.

This is the pointwise resolvent commutation identity integrated around the
canonical fixed circle.  It is a strict contour-calculus primitive below the
Riesz specification: it keeps the concrete `complexRieszProjectionOnCircle`
object and only uses the same no-boundary resolvent hypothesis. -/
theorem complexRieszProjectionOnCircle_commutes_complexOfRealMatrix_of_no_boundary
    [DecidableEq Node]
    (Aalpha : NodeMatrix Node) (baseRadius : ℝ)
    (hbaseRadius_pos : 0 < baseRadius)
    (hnoBoundary :
      ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
        ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z) :
    complexOfRealMatrix (Node := Node) Aalpha *
        complexRieszProjectionOnCircle (Node := Node)
          Aalpha (1 : ℂ) baseRadius =
      complexRieszProjectionOnCircle (Node := Node)
          Aalpha (1 : ℂ) baseRadius *
        complexOfRealMatrix (Node := Node) Aalpha := by
  classical
  simpa [Matrix.rieszProjectionOnCircle, complexRieszProjectionOnCircle,
    complexResolventMatrix, complexMatrixSub, complexIdentityMatrix,
    complexOfRealMatrix] using
      (Matrix.mul_rieszProjectionOnCircle_eq_rieszProjectionOnCircle_mul_of_spectrum_disjoint
        (A := complexOfRealMatrix (Node := Node) Aalpha)
        (center := (1 : ℂ)) (radius := baseRadius) hbaseRadius_pos.le
        (fun z hz => by
          rw [show (fun i j : Node =>
              z * (1 : Matrix Node Node ℂ) i j -
                complexOfRealMatrix (Node := Node) Aalpha i j) =
              complexResolventMatrix (Node := Node) Aalpha z by
            ext i j
            simp only [complexResolventMatrix, complexMatrixSub,
              complexOfRealMatrix]
            rw [complexIdentityMatrix_eq_one (Node := Node)]]
          exact complexResolvent_det_ne_zero_of_not_eigen
            (Node := Node) Aalpha z (hnoBoundary z hz)))

/-- Real fixed-contour commutation with the underlying matrix.

This descends the complex contour commutation through the already-proved real
entry property of the fixed-circle projection. -/
theorem fixedCircleRieszProjection_commutes_of_no_boundary
    (Aalpha : NodeMatrix Node) (baseRadius : ℝ)
    (hbaseRadius_pos : 0 < baseRadius)
    (hnoBoundary :
      ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
        ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z) :
    matrixMul (Node := Node) Aalpha
        (fixedCircleRieszProjection (Node := Node)
          Aalpha (1 : ℂ) baseRadius) =
      matrixMul (Node := Node)
        (fixedCircleRieszProjection (Node := Node)
          Aalpha (1 : ℂ) baseRadius) Aalpha := by
  classical
  letI : DecidableEq Node := Classical.decEq Node
  obtain ⟨_hcomplexIdem, hreal_entries⟩ :=
    complexRieszProjectionOnCircle_idempotent_and_real_entries_of_no_boundary
      (Node := Node) Aalpha baseRadius hbaseRadius_pos hnoBoundary
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
  have hcomplexComm :
      complexOfRealMatrix (Node := Node) Aalpha * Pℂ =
        Pℂ * complexOfRealMatrix (Node := Node) Aalpha := by
    simpa [Pℂ] using
      complexRieszProjectionOnCircle_commutes_complexOfRealMatrix_of_no_boundary
        (Node := Node) Aalpha baseRadius hbaseRadius_pos hnoBoundary
  have hcomplex_real_comm :
      complexOfRealMatrix (Node := Node)
          (matrixMul (Node := Node) Aalpha Pℝ) =
        complexOfRealMatrix (Node := Node)
          (matrixMul (Node := Node) Pℝ Aalpha) := by
    rw [complexOfRealMatrix_matrixMul, complexOfRealMatrix_matrixMul,
      hcomplexOfReal]
    simpa [complexMatrixMul] using hcomplexComm
  change matrixMul (Node := Node) Aalpha Pℝ =
    matrixMul (Node := Node) Pℝ Aalpha
  ext i j
  have hentry :=
    congrArg (fun M : ComplexNodeMatrix Node => M i j) hcomplex_real_comm
  exact Complex.ofReal_injective (by
    simpa [complexOfRealMatrix] using hentry)

/-- The witness-form `RankOneProjection` has one-dimensional matrix-action
range.

This is the converse algebraic bridge to
`rankOneProjection_of_idempotent_finrank_range_eq_one`: the explicit
right/left witness in `RankOneProjection` identifies every point in the range
with a scalar multiple of the nonzero right vector. -/
theorem finrank_range_mulVecLin_eq_one_of_rankOneProjection
    (P : NodeMatrix Node)
    (hrank : RankOneProjection (Node := Node) P) :
    Module.finrank ℝ
        (LinearMap.range
          (Matrix.mulVecLin P :
            RowVector Node →ₗ[ℝ] RowVector Node)) = 1 := by
  exact
    Matrix.IsNormalizedRankOneProjection.finrank_range_mulVecLin_eq_one
      (P := P) hrank

/-- Nearby idempotent finite-dimensional operators have the same range
dimension when each difference is strictly contractive on nonzero vectors.

This is the algebraic core of the standard local rank-constancy argument for a
continuous path of projections: the second projection maps the first range
injectively into its own range, and conversely. -/
theorem finrank_range_eq_of_idempotent_contracting_difference
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (p q : V →ₗ[ℝ] V)
    (hp : p.comp p = p) (hq : q.comp q = q)
    (hpq : ∀ x : V, x ≠ 0 → ‖(p - q) x‖ < ‖x‖)
    (hqp : ∀ x : V, x ≠ 0 → ‖(q - p) x‖ < ‖x‖) :
    Module.finrank ℝ (LinearMap.range p) =
      Module.finrank ℝ (LinearMap.range q) := by
  exact LinearMap.finrank_range_eq_of_idempotent_contracting_sub p q hp hq hpq

/-- Operator-norm form of the local rank-preservation lemma for idempotent
finite-dimensional operators. -/
theorem finrank_range_eq_of_idempotent_opNorm_lt_one
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (p q : V →L[ℝ] V)
    (hp : p.comp p = p) (hq : q.comp q = q)
    (hclose : ‖p - q‖ < 1) :
    Module.finrank ℝ (LinearMap.range (p : V →ₗ[ℝ] V)) =
      Module.finrank ℝ (LinearMap.range (q : V →ₗ[ℝ] V)) := by
  exact ContinuousLinearMap.finrank_range_eq_of_idempotent_norm_sub_lt_one
    p q hp hq hclose

/-- Real matrix action as a continuous linear map on the finite node-vector
space. -/
noncomputable def realMatrixContinuousLinearMap
    (A : NodeMatrix Node) :
    RowVector Node →L[ℝ] RowVector Node :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)

/-- The map sending a real node matrix to its induced continuous linear
operator is continuous. -/
theorem realMatrixContinuousLinearMap_continuous :
    Continuous
      (fun A : NodeMatrix Node =>
        realMatrixContinuousLinearMap (Node := Node) A) := by
  simpa only [realMatrixContinuousLinearMap] using
    (Matrix.continuous_toContinuousLinearMap_mulVecLin
      (𝕜 := ℝ) (m := Node) (n := Node))

/-- Matrix-form local rank preservation for nearby idempotent node matrices. -/
theorem finrank_range_mulVecLin_eq_of_idempotent_operator_close
    (P Q : NodeMatrix Node)
    (hP : matrixMul (Node := Node) P P = P)
    (hQ : matrixMul (Node := Node) Q Q = Q)
    (hclose :
      ‖realMatrixContinuousLinearMap (Node := Node) P -
          realMatrixContinuousLinearMap (Node := Node) Q‖ < 1) :
    Module.finrank ℝ
        (LinearMap.range
          (Matrix.mulVecLin P :
            RowVector Node →ₗ[ℝ] RowVector Node)) =
      Module.finrank ℝ
        (LinearMap.range
          (Matrix.mulVecLin Q :
            RowVector Node →ₗ[ℝ] RowVector Node)) := by
  exact Matrix.finrank_range_mulVecLin_eq_of_idempotent_opNorm_sub_lt_one
    P Q hP hQ hclose

/-- The range dimension of a continuous idempotent node-matrix path is constant
on a connected closed interval. -/
theorem finrank_range_mulVecLin_eq_on_Icc_of_continuous_idempotent
    (P : ℝ → NodeMatrix Node) (rho alpha beta : ℝ)
    (hP_cont : ContinuousOn P (Set.Icc (-rho) rho))
    (hidempotent :
      ∀ t : ℝ, t ∈ Set.Icc (-rho) rho →
        matrixMul (Node := Node) (P t) (P t) = P t)
    (halpha : alpha ∈ Set.Icc (-rho) rho)
    (hbeta : beta ∈ Set.Icc (-rho) rho) :
    Module.finrank ℝ
        (LinearMap.range
          (Matrix.mulVecLin (P alpha) :
            RowVector Node →ₗ[ℝ] RowVector Node)) =
      Module.finrank ℝ
        (LinearMap.range
          (Matrix.mulVecLin (P beta) :
            RowVector Node →ₗ[ℝ] RowVector Node)) := by
  classical
  let s : Set ℝ := Set.Icc (-rho) rho
  haveI : PreconnectedSpace s := Subtype.preconnectedSpace isPreconnected_Icc
  let Q : s → RowVector Node →L[ℝ] RowVector Node := fun t =>
    realMatrixContinuousLinearMap (Node := Node) (P (t : ℝ))
  simpa [Q, realMatrixContinuousLinearMap] using
    ContinuousLinearMap.finrank_range_eq_of_continuous_idempotent_on_preconnected
      Q
      ((realMatrixContinuousLinearMap_continuous (Node := Node)).comp
        hP_cont.restrict)
      (fun t => by
        ext x i
        change matrixMulVector (Node := Node) (P (t : ℝ))
            (matrixMulVector (Node := Node) (P (t : ℝ)) x) i =
          matrixMulVector (Node := Node) (P (t : ℝ)) x i
        rw [← matrixMulVector_matrixMul,
          hidempotent (t : ℝ) t.property])
      ⟨alpha, halpha⟩ ⟨beta, hbeta⟩

/-- Build the file's witness-form rank-one projection from a one-dimensional
range idempotent.

This is the purely algebraic half of the rank-constancy sentence in Appendix
A.  Once the analytic argument supplies that the range of the idempotent
contour projection still has finrank one, this lemma constructs the normalized
right/left vectors required by `RankOneProjection`. -/
theorem rankOneProjection_of_idempotent_finrank_range_eq_one
    (P : NodeMatrix Node)
    (hidempotent : matrixMul (Node := Node) P P = P)
    (hrange_dim :
      Module.finrank ℝ
          (LinearMap.range
            (Matrix.mulVecLin P :
              RowVector Node →ₗ[ℝ] RowVector Node)) = 1) :
    RankOneProjection (Node := Node) P := by
  classical
  simpa [RankOneProjection, matrixMul, matrixMulVector, rowDot,
    Matrix.mul_apply, Matrix.mulVec, dotProduct] using
    (Matrix.isNormalizedRankOneProjection_of_mul_self_eq_and_finrank_range_eq_one
      (𝕜 := ℝ) (ι := Node) P (by simpa [matrixMul, Matrix.mul_apply] using hidempotent)
      hrange_dim)

/-- Rank constancy for an analytic path of fixed-contour projections.

This isolates Lemma A.1's sentence that the rank of `P(alpha)` is constant on
the connected parameter interval.  The intended proof is the standard
finite-dimensional argument: analytic implies continuous, nearby idempotents
with `‖P-Q‖ < 1` have isomorphic ranges, and the integer-valued rank is locally
constant; connectedness of `[-rho, rho]` then propagates the base rank one. -/
theorem analytic_idempotent_fixed_circle_projection_rank_one_on_Icc
    (A : ℝ → NodeMatrix Node) (rho baseRadius : ℝ) (P0 : NodeMatrix Node)
    (hrho_pos : 0 < rho)
    (hP_analytic_closed :
      ∀ alpha : ℝ, |alpha| ≤ rho →
        AnalyticAt ℝ
          (fun a : ℝ =>
            fixedCircleRieszProjection (Node := Node)
              (A a) (1 : ℂ) baseRadius)
          alpha)
    (hbaseContourEq :
      fixedCircleRieszProjection (Node := Node) (A 0) (1 : ℂ) baseRadius = P0)
    (hbaseRankOne : RankOneProjection (Node := Node) P0)
    (hidempotent :
      ∀ alpha : ℝ, |alpha| ≤ rho →
        matrixMul (Node := Node)
            (fixedCircleRieszProjection (Node := Node)
              (A alpha) (1 : ℂ) baseRadius)
            (fixedCircleRieszProjection (Node := Node)
              (A alpha) (1 : ℂ) baseRadius) =
          fixedCircleRieszProjection (Node := Node)
            (A alpha) (1 : ℂ) baseRadius) :
    ∀ alpha : ℝ, |alpha| ≤ rho →
      RankOneProjection (Node := Node)
        (fixedCircleRieszProjection (Node := Node)
          (A alpha) (1 : ℂ) baseRadius) := by
  classical
  let Ppath : ℝ → Matrix Node Node ℝ := fun a =>
    fixedCircleRieszProjection (Node := Node) (A a) (1 : ℂ) baseRadius
  have hP_cont : ContinuousOn Ppath (Set.Icc (-rho) rho) := by
    intro a ha
    exact
      (hP_analytic_closed a (abs_le.mpr ha)).continuousAt.continuousWithinAt
  have hP0 : Matrix.IsNormalizedRankOneProjection (Ppath 0) := by
    simpa [Ppath, RankOneProjection, hbaseContourEq] using hbaseRankOne
  have hP_idem :
      ∀ a : ℝ, |a| ≤ rho → Ppath a * Ppath a = Ppath a := by
    intro a ha
    simpa [Ppath, matrixMul, Matrix.mul_apply] using hidempotent a ha
  have hrank :=
    Matrix.isNormalizedRankOneProjection_on_Icc_of_continuous_idempotent
      Ppath rho hrho_pos hP_cont hP0 hP_idem
  intro alpha halpha
  simpa [Ppath, RankOneProjection] using hrank alpha halpha

/-- Every point has a small spectral separating circle for a finite node matrix.

This closes the finite-dimensional isolation field in
`RieszProjectionAtEigenvalueSpec`.  The hard contour work in the Riesz-spec
bridge is the spectral action of the canonical fixed-circle integral; local
existence of some boundary-free circle around the selected eigenvalue follows
only from finiteness of the matrix spectrum. -/
theorem exists_local_separating_circle_around_complex_eigenvalue
    [DecidableEq Node]
    (Aalpha : NodeMatrix Node) (lambda : ℝ) :
    ∃ radius : ℝ, 0 < radius ∧
      ∀ z : ℂ, ‖z - (lambda : ℂ)‖ = radius →
        ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z := by
  classical
  simpa only [Matrix.spectrum_toLin',
    ← isComplexRightEigenvalue_iff_mem_spectrum_complexOfRealMatrix] using
    (Module.End.exists_sphere_disjoint_spectrum
      ((complexOfRealMatrix (Node := Node) Aalpha).toLin') (lambda : ℂ))

/-- Algebraic forward half of the Riesz fixed-vector specification.

After the contour calculation supplies `A * P = lambda • P`, every vector
fixed by `P` is automatically a `lambda`-eigenvector for `A`.  The reverse
inclusion is the genuine contour/range identification left to the spectral
action primitive. -/
theorem eigenvector_of_fixed_vector_of_matrix_mul_projection_eq
    (Aalpha P : NodeMatrix Node) (lambda : ℝ)
    (hAP : matrixMul (Node := Node) Aalpha P = lambda • P) :
    ∀ x : RowVector Node,
      matrixMulVector (Node := Node) P x = x →
        matrixMulVector (Node := Node) Aalpha x = lambda • x := by
  classical
  intro x hx
  exact Module.End.apply_eq_smul_of_comp_eq_smul_and_fixed
    (Matrix.mulVecLin Aalpha) (Matrix.mulVecLin P) lambda x
    (by
      rw [← Matrix.mulVecLin_mul,
        ← (Matrix.mulVecBilin ℝ ℝ).map_smul]
      apply congrArg Matrix.mulVecLin
      simpa [matrixMul, Matrix.mul_apply] using hAP)
    hx

/-- Package the fixed-vector equivalence from the spectral-action identity and
the remaining range-identification direction.

This keeps the unresolved contour burden at its sharp shape: prove
`A * P = lambda • P` and prove that every `lambda`-eigenvector lies in the
range fixed by the canonical contour projection. -/
theorem fixed_vector_iff_of_matrix_mul_projection_eq_and_eigen_fixed
    (Aalpha P : NodeMatrix Node) (lambda : ℝ)
    (hAP : matrixMul (Node := Node) Aalpha P = lambda • P)
    (heigen_fixed :
      ∀ x : RowVector Node,
        matrixMulVector (Node := Node) Aalpha x = lambda • x →
          matrixMulVector (Node := Node) P x = x) :
    ∀ x : RowVector Node,
      matrixMulVector (Node := Node) P x = x ↔
        matrixMulVector (Node := Node) Aalpha x = lambda • x := by
  intro x
  constructor
  · exact eigenvector_of_fixed_vector_of_matrix_mul_projection_eq
      (Node := Node) Aalpha P lambda hAP x
  · exact heigen_fixed x

theorem complexResolvent_inv_mulVec_eq_inv_smul_of_eigen
    [DecidableEq Node]
    (Aalpha : NodeMatrix Node) (lambda z : ℂ) (v : ComplexRowVector Node)
    (hnot : ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z)
    (hz_ne : z ≠ lambda)
    (hAv :
      complexMatrixMulVector (Node := Node) Aalpha v = lambda • v) :
    Matrix.mulVec
        (complexResolventMatrix (Node := Node) Aalpha z)⁻¹ v =
      (z - lambda)⁻¹ • v := by
  classical
  have hresolvent :
      complexResolventMatrix (Node := Node) Aalpha z =
        z • (1 : Matrix Node Node ℂ) -
          complexOfRealMatrix (Node := Node) Aalpha := by
    ext i j
    simp [complexResolventMatrix, complexMatrixSub, complexIdentityMatrix,
      complexOfRealMatrix, Matrix.one_apply]
  simpa [← hresolvent, complexMatrixMulVector, complexOfRealMatrix] using
      (Matrix.nonsing_inv_mulVec_eq_inv_smul_of_mulVec_eq_smul
        (A := complexOfRealMatrix (Node := Node) Aalpha)
        (lambda := lambda) (z := z) (v := v)
        (by
          rw [← hresolvent]
          exact isUnit_iff_ne_zero.mpr
            (complexResolvent_det_ne_zero_of_not_eigen
              (Node := Node) Aalpha z hnot))
        (by simpa [complexMatrixMulVector, complexOfRealMatrix] using hAv))

theorem complexRieszProjectionOnCircle_mulVec_eq_self_of_eigen_inside
    [DecidableEq Node]
    (Aalpha : NodeMatrix Node) (lambda : ℝ) (baseRadius : ℝ)
    (hbaseRadius_pos : 0 < baseRadius)
    (hnoBoundary :
      ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
        ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z)
    (hlambdaInside :
      ‖(lambda : ℂ) - (1 : ℂ)‖ < baseRadius)
    (v : ComplexRowVector Node)
    (hAv :
      complexMatrixMulVector (Node := Node) Aalpha v =
        (lambda : ℂ) • v) :
    complexNodeMatrixMulVector (Node := Node)
        (complexRieszProjectionOnCircle (Node := Node)
          Aalpha (1 : ℂ) baseRadius) v = v := by
  classical
  simpa [Matrix.rieszProjectionOnCircle, complexRieszProjectionOnCircle,
    complexNodeMatrixMulVector, complexMatrixMulVector, complexOfRealMatrix] using
      (Matrix.rieszProjectionOnCircle_mulVec_eq_self_of_eigenvalue_mem_ball
        (A := complexOfRealMatrix (Node := Node) Aalpha)
        (center := (1 : ℂ)) (lambda := (lambda : ℂ))
        (radius := baseRadius) (v := v)
        (fun z hz => by
          have hresolvent :
              z • (@Matrix.diagonal Node ℂ (Classical.decEq Node) _ (fun _ => 1)) -
                  complexOfRealMatrix (Node := Node) Aalpha =
                complexResolventMatrix (Node := Node) Aalpha z := by
            ext i j
            simp [complexResolventMatrix, complexMatrixSub,
              complexIdentityMatrix, complexOfRealMatrix, Matrix.one_apply]
          rw [hresolvent]
          exact @complexResolvent_det_ne_zero_of_not_eigen Node _ _
            (Classical.decEq Node) Aalpha z (hnoBoundary z hz))
        (by simpa [Metric.mem_ball, dist_eq_norm] using hlambdaInside)
        (by simpa [complexMatrixMulVector, complexOfRealMatrix] using hAv))

theorem complex_fixedCircleRieszProjection_eq_complex_projection
    [DecidableEq Node]
    (Aalpha : NodeMatrix Node) (baseRadius : ℝ)
    (hbaseRadius_pos : 0 < baseRadius)
    (hnoBoundary :
      ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
        ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z) :
    complexOfRealMatrix (Node := Node)
        (fixedCircleRieszProjection (Node := Node)
          Aalpha (1 : ℂ) baseRadius) =
      complexRieszProjectionOnCircle (Node := Node)
        Aalpha (1 : ℂ) baseRadius := by
  classical
  obtain ⟨_hcomplexIdem, hreal_entries⟩ :=
    complexRieszProjectionOnCircle_idempotent_and_real_entries_of_no_boundary
      (Node := Node) Aalpha baseRadius hbaseRadius_pos hnoBoundary
  ext i j
  apply Complex.ext
  · simp [fixedCircleRieszProjection, realPartComplexNodeMatrix,
      complexOfRealMatrix]
  · simp [fixedCircleRieszProjection, realPartComplexNodeMatrix,
      complexOfRealMatrix, hreal_entries i j]

theorem fixedCircleRieszProjection_complexMulVector_eq_self_of_eigen_inside
    [DecidableEq Node]
    (Aalpha : NodeMatrix Node) (lambda : ℝ) (baseRadius : ℝ)
    (hbaseRadius_pos : 0 < baseRadius)
    (hnoBoundary :
      ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
        ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z)
    (hlambdaInside :
      ‖(lambda : ℂ) - (1 : ℂ)‖ < baseRadius)
    (v : ComplexRowVector Node)
    (hAv :
      complexMatrixMulVector (Node := Node) Aalpha v =
        (lambda : ℂ) • v) :
    complexMatrixMulVector (Node := Node)
        (fixedCircleRieszProjection (Node := Node)
          Aalpha (1 : ℂ) baseRadius) v = v := by
  classical
  have hcomplex_fixed :=
    complexRieszProjectionOnCircle_mulVec_eq_self_of_eigen_inside
      (Node := Node) Aalpha lambda baseRadius hbaseRadius_pos hnoBoundary
      hlambdaInside v hAv
  have hcomplexOfReal :
      complexOfRealMatrix (Node := Node)
          (fixedCircleRieszProjection (Node := Node)
            Aalpha (1 : ℂ) baseRadius) =
        complexRieszProjectionOnCircle (Node := Node)
          Aalpha (1 : ℂ) baseRadius :=
    complex_fixedCircleRieszProjection_eq_complex_projection
      (Node := Node) Aalpha baseRadius hbaseRadius_pos hnoBoundary
  rw [← complexNodeMatrixMulVector_complexOfRealMatrix]
  rw [hcomplexOfReal]
  exact hcomplex_fixed

theorem fixedCircleRieszProjection_fixes_real_eigenvector_of_inside
    [DecidableEq Node]
    (Aalpha : NodeMatrix Node) (lambda : ℝ) (baseRadius : ℝ)
    (hbaseRadius_pos : 0 < baseRadius)
    (hnoBoundary :
      ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
        ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z)
    (hlambdaInside :
      ‖(lambda : ℂ) - (1 : ℂ)‖ < baseRadius) :
    ∀ x : RowVector Node,
      matrixMulVector (Node := Node) Aalpha x = lambda • x →
        matrixMulVector (Node := Node)
          (fixedCircleRieszProjection (Node := Node)
            Aalpha (1 : ℂ) baseRadius) x = x := by
  classical
  intro x hx
  have hAv_complex :
      complexMatrixMulVector (Node := Node) Aalpha
          (complexOfRealRow (Node := Node) x) =
        (lambda : ℂ) • complexOfRealRow (Node := Node) x := by
    funext i
    have hi := congrFun hx i
    simpa [complexMatrixMulVector, complexOfRealRow, matrixMulVector,
      dotProduct, Pi.smul_apply] using congrArg (fun t : ℝ => (t : ℂ)) hi
  have hPv_complex :=
    fixedCircleRieszProjection_complexMulVector_eq_self_of_eigen_inside
      (Node := Node) Aalpha lambda baseRadius hbaseRadius_pos hnoBoundary
      hlambdaInside (complexOfRealRow (Node := Node) x) hAv_complex
  funext i
  have hi := congrFun hPv_complex i
  exact Complex.ofReal_injective (by
    simpa [complexMatrixMulVector, complexOfRealRow, matrixMulVector,
      dotProduct] using hi)

theorem matrix_mul_projection_eq_smul_of_rankOneProjection_and_complex_eigen_fixed
    (Aalpha P : NodeMatrix Node) (lambda : ℝ)
    (hrank : RankOneProjection (Node := Node) P)
    (hlambdaEigen :
      IsComplexRightEigenvalue (Node := Node) Aalpha (lambda : ℂ))
    (hcomplex_fixed :
      ∀ v : ComplexRowVector Node,
        complexMatrixMulVector (Node := Node) Aalpha v =
          (lambda : ℂ) • v →
        complexMatrixMulVector (Node := Node) P v = v) :
    matrixMul (Node := Node) Aalpha P = lambda • P := by
  classical
  simpa [RankOneProjection, IsComplexRightEigenvalue, matrixMul,
    complexMatrixMulVector, Matrix.map_apply] using
    (Matrix.IsNormalizedRankOneProjection.mul_left_eq_smul_of_eigenspace_le_fixed_space
      (A := Aalpha) (P := P) (lambda := lambda) hrank hlambdaEigen hcomplex_fixed)

/-- Pointwise spectral-action bridge for a rank-one fixed-contour projection.

Once rank constancy has shown the fixed contour projection is rank one, the
remaining contour calculus identifies it with the Riesz projection for the
unique enclosed eigenvalue branch.  This helper deliberately keeps the
`fixedCircleRieszProjection` object in the conclusion, so it cannot be
satisfied by an arbitrary rank-one projection with a separating circle. -/
theorem fixed_circle_rank_one_contour_projection_is_riesz_at_inside_eigenvalue
    (Aalpha : NodeMatrix Node) (lambda baseRadius : ℝ)
    (hbaseRadius_pos : 0 < baseRadius)
    (hrank :
      RankOneProjection (Node := Node)
        (fixedCircleRieszProjection (Node := Node)
          Aalpha (1 : ℂ) baseRadius))
    (hnoBoundary :
      ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
        ¬ IsComplexRightEigenvalue (Node := Node) Aalpha z)
    (hlambdaEigen :
      IsComplexRightEigenvalue (Node := Node) Aalpha (lambda : ℂ))
    (hlambdaInside :
      ‖(lambda : ℂ) - (1 : ℂ)‖ < baseRadius) :
    IsRieszProjectionAtEigenvalue (Node := Node) Aalpha lambda
      (fixedCircleRieszProjection (Node := Node)
        Aalpha (1 : ℂ) baseRadius) := by
  classical
  let Aℂ : Matrix Node Node ℂ := fun i j => (Aalpha i j : ℂ)
  have hresolvent (z : ℂ) :
      complexResolventMatrix (Node := Node) Aalpha z =
        fun i j : Node =>
          z * (1 : Matrix Node Node ℂ) i j - (Aalpha i j : ℂ) := by
    ext i j
    simp only [complexResolventMatrix, complexMatrixSub, complexOfRealMatrix]
    rw [complexIdentityMatrix_eq_one (Node := Node)]
  have hQ :
      complexRieszProjectionOnCircle (Node := Node) Aalpha
          ((1 : ℝ) : ℂ) baseRadius =
        Matrix.rieszProjectionOnCircle
          (fun i j : Node => (Aalpha i j : ℂ)) ((1 : ℝ) : ℂ) baseRadius := by
    ext i j
    simp only [complexRieszProjectionOnCircle, Matrix.rieszProjectionOnCircle]
    simp_rw [hresolvent]
    simp only [Matrix.one_apply, Matrix.diagonal_apply]
  have hrank' :
      Matrix.IsNormalizedRankOneProjection
        (fun i j =>
          (Matrix.rieszProjectionOnCircle Aℂ (1 : ℂ) baseRadius i j).re) := by
    change Matrix.IsNormalizedRankOneProjection
      (fun i j =>
        (Matrix.rieszProjectionOnCircle
          (fun k l : Node => (Aalpha k l : ℂ))
          ((1 : ℝ) : ℂ) baseRadius i j).re)
    rw [← hQ]
    simpa [RankOneProjection, fixedCircleRieszProjection,
      realPartComplexNodeMatrix] using hrank
  have hspectrum :
      ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
        Matrix.det (fun i j : Node =>
          z * (1 : Matrix Node Node ℂ) i j - (Aalpha i j : ℂ)) ≠ 0 := by
    intro z hz
    have hdet := complexResolvent_det_ne_zero_of_not_eigen
      (Node := Node) Aalpha z (hnoBoundary z hz)
    simpa [complexResolventMatrix, complexMatrixSub, complexIdentityMatrix,
      complexOfRealMatrix] using hdet
  have hlambdaEigen' :
      ∃ v : Node → ℂ, v ≠ 0 ∧
        Matrix.mulVec Aℂ v = (lambda : ℂ) • v := by
    simpa [IsComplexRightEigenvalue, complexMatrixMulVector, Aℂ,
      Matrix.mulVec, dotProduct] using hlambdaEigen
  have h :=
    Matrix.rieszProjectionOnCircle_isRankOneRieszProjectionAt_of_rankOne_and_mem_ball
      (A := Aalpha) (center := 1) (lambda := lambda) (radius := baseRadius)
      hbaseRadius_pos hrank' hspectrum hlambdaEigen' hlambdaInside
  dsimp only at h
  rw [← hQ] at h
  simpa [IsRieszProjectionAtEigenvalue, RieszProjectionAtEigenvalueSpec,
    RankOneProjection, fixedCircleRieszProjection, realPartComplexNodeMatrix,
    matrixMul, matrixMulVector, IsComplexRightEigenvalue,
    complexMatrixMulVector, Matrix.mulVec, dotProduct, Aℂ] using h

/-- Source-faithful fixed-contour branch primitive for Lemma A.1.

The moving Riesz branch is not a consequence of pointwise no-boundary
avoidance alone.  The source proof also uses an analytic matrix family on a
larger open interval and rank constancy of the fixed contour projection on the
connected parameter interval.  This strengthened internal primitive exposes
those source-derived premises explicitly for the canonical
`fixedCircleRieszProjection` object. -/
theorem fixedContour_projection_rankConstancy_branch_spec
    (A : ℝ → NodeMatrix Node) (gamma : ℝ → ℝ)
    (rho rhoAnalytic baseRadius : ℝ) (P0 : NodeMatrix Node)
    (hrho_pos : 0 < rho) (hrho_lt_analytic : rho < rhoAnalytic)
    (hbaseRadius_pos : 0 < baseRadius)
    (hA_analytic :
      ∀ alpha : ℝ, |alpha| < rhoAnalytic → AnalyticAt ℝ A alpha)
    (hP_analytic :
      ∀ alpha : ℝ, |alpha| < rho →
        AnalyticAt ℝ
          (fun a : ℝ =>
            fixedCircleRieszProjection (Node := Node)
              (A a) (1 : ℂ) baseRadius)
          alpha)
    (hnoBoundary :
      ∀ alpha : ℝ, |alpha| ≤ rhoAnalytic →
        ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
          ¬ IsComplexRightEigenvalue (Node := Node) (A alpha) z)
    (hbaseRiesz :
      IsRieszProjectionAtEigenvalue (Node := Node) (A 0) 1 P0)
    (hbaseInteriorSeparates :
      ∀ z : ℂ, IsComplexRightEigenvalue (Node := Node) (A 0) z →
        z ≠ (1 : ℂ) → baseRadius < ‖z - (1 : ℂ)‖)
    (hgamma0 : gamma 0 = 1)
    (hgamma_analytic :
      ∀ alpha : ℝ, |alpha| < rhoAnalytic → AnalyticAt ℝ gamma alpha)
    (hgammaEigen :
      ∀ alpha : ℝ, |alpha| < rhoAnalytic →
        IsComplexRightEigenvalue (Node := Node) (A alpha) (gamma alpha : ℂ))
    (hgammaInside :
      ∀ alpha : ℝ, |alpha| ≤ rho →
        ‖(gamma alpha : ℂ) - (1 : ℂ)‖ < baseRadius) :
    fixedCircleRieszProjection (Node := Node) (A 0) (1 : ℂ) baseRadius = P0 ∧
      ∀ alpha : ℝ, |alpha| ≤ rho →
        IsRieszProjectionAtEigenvalue (Node := Node)
          (A alpha) (gamma alpha)
          (fixedCircleRieszProjection (Node := Node)
            (A alpha) (1 : ℂ) baseRadius) := by
  classical
  have hrhoAnalytic_pos : 0 < rhoAnalytic := lt_trans hrho_pos hrho_lt_analytic
  have hzero_le : |(0 : ℝ)| ≤ rhoAnalytic := by
    simpa using le_of_lt hrhoAnalytic_pos
  have hzero_lt : |(0 : ℝ)| < rhoAnalytic := by
    simpa using hrhoAnalytic_pos
  have hbaseNoBoundary :
      ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
        ¬ IsComplexRightEigenvalue (Node := Node) (A 0) z :=
    hnoBoundary 0 hzero_le
  have hbaseGammaEigen :
      IsComplexRightEigenvalue (Node := Node) (A 0) (1 : ℂ) := by
    simpa [hgamma0] using hgammaEigen 0 hzero_lt
  have hbaseGammaInside :
      ‖(1 : ℂ) - (1 : ℂ)‖ < baseRadius := by
    have hzero_le_rho : |(0 : ℝ)| ≤ rho := by
      simpa using le_of_lt hrho_pos
    simpa [hgamma0] using hgammaInside 0 hzero_le_rho
  have hbaseContourEq :
      fixedCircleRieszProjection (Node := Node) (A 0) (1 : ℂ) baseRadius = P0 := by
    have hbaseEnclosedSpectrum :
        IsComplexRightEigenvalue (Node := Node) (A 0) (1 : ℂ) ∧
          ∀ z : ℂ, IsComplexRightEigenvalue (Node := Node) (A 0) z →
            (‖z - (1 : ℂ)‖ < baseRadius ↔ z = (1 : ℂ)) ∧
              (‖z - (1 : ℂ)‖ ≤ baseRadius ↔ z = (1 : ℂ)) :=
      fixed_circle_base_enclosed_spectrum_singleton (Node := Node)
        (A 0) baseRadius hbaseRadius_pos hbaseGammaEigen
        hbaseInteriorSeparates
    /-
    Concrete remaining base-contour identity: prove that
    `(2πi)⁻¹ ∮ (zI-A(0))⁻¹ dz` over the fixed separating circle is the
    already-identified rank-one unit Riesz projection `P0`.
    The available facts are exactly the base algebraic Riesz spec
    `hbaseRiesz`, no boundary spectrum on the contour, and
    `hbaseEnclosedSpectrum`, which identifies the enclosed base spectrum with
    the singleton `{1}`.
    -/
    have hcomplex :
        complexRieszProjectionOnCircle (Node := Node) (A 0) (1 : ℂ) baseRadius =
          complexOfRealMatrix (Node := Node) P0 :=
      complex_fixed_circle_riesz_projection_eq_complexified_riesz_of_base_singleton
        (Node := Node) (A 0) baseRadius P0 hbaseRadius_pos
        hbaseNoBoundary hbaseRiesz hbaseEnclosedSpectrum
    exact fixed_circle_real_part_eq_of_complexified_riesz (Node := Node)
      (A 0) baseRadius P0 hcomplex
  have hP_analytic_closed :
      ∀ alpha : ℝ, |alpha| ≤ rho →
        AnalyticAt ℝ
          (fun a : ℝ =>
            fixedCircleRieszProjection (Node := Node)
              (A a) (1 : ℂ) baseRadius)
          alpha :=
    fixed_circle_projection_endpoint_local_analyticity (Node := Node)
      A rho rhoAnalytic baseRadius hrho_lt_analytic hbaseRadius_pos
      hA_analytic hnoBoundary
  refine ⟨hbaseContourEq, ?_⟩
  /-
  Exact remaining source primitive: from `hA_analytic`, `hP_analytic`,
  the endpoint-safe strengthening `hP_analytic_closed`, `hnoBoundary`,
  `hgamma_analytic`, `hgammaEigen`, `hgammaInside`, and the base projection
  equality, prove rank constancy of the canonical fixed
  contour projection on the connected interval and identify it with the
  moving one-dimensional eigenspace of `gamma alpha`.
  -/
  have hbaseRankOne :
      RankOneProjection (Node := Node)
        (fixedCircleRieszProjection (Node := Node)
          (A 0) (1 : ℂ) baseRadius) :=
    fixed_circle_projection_base_rankOne_of_base_eq (Node := Node)
      (A 0) baseRadius P0 hbaseContourEq hbaseRiesz
  have hcontour_idempotent :
      ∀ alpha : ℝ, |alpha| ≤ rho →
        matrixMul (Node := Node)
            (fixedCircleRieszProjection (Node := Node)
              (A alpha) (1 : ℂ) baseRadius)
            (fixedCircleRieszProjection (Node := Node)
              (A alpha) (1 : ℂ) baseRadius) =
          fixedCircleRieszProjection (Node := Node)
            (A alpha) (1 : ℂ) baseRadius := by
    intro alpha halpha
    have halpha_analytic : |alpha| ≤ rhoAnalytic :=
      le_trans halpha (le_of_lt hrho_lt_analytic)
    exact fixed_circle_contour_projection_idempotent_of_no_boundary
      (Node := Node) (A alpha) baseRadius hbaseRadius_pos
      (hnoBoundary alpha halpha_analytic)
  have hrankAll :
      ∀ alpha : ℝ, |alpha| ≤ rho →
        RankOneProjection (Node := Node)
          (fixedCircleRieszProjection (Node := Node)
            (A alpha) (1 : ℂ) baseRadius) :=
    analytic_idempotent_fixed_circle_projection_rank_one_on_Icc
      (Node := Node) A rho baseRadius P0 hrho_pos hP_analytic_closed
      hbaseContourEq
      (by
        simpa [hbaseContourEq] using hbaseRankOne)
      hcontour_idempotent
  intro alpha halpha
  have halpha_lt_analytic : |alpha| < rhoAnalytic :=
    lt_of_le_of_lt halpha hrho_lt_analytic
  have halpha_le_analytic : |alpha| ≤ rhoAnalytic :=
    le_of_lt halpha_lt_analytic
  exact fixed_circle_rank_one_contour_projection_is_riesz_at_inside_eigenvalue
    (Node := Node) (A alpha) (gamma alpha) baseRadius hbaseRadius_pos
    (hrankAll alpha halpha)
    (hnoBoundary alpha halpha_le_analytic)
    (hgammaEigen alpha halpha_lt_analytic)
    (hgammaInside alpha halpha)

/-- Fixed-contour Riesz projection supplier for Appendix A, after the analytic
eigenvalue branch `gamma` has been chosen.

This is the first missing finite-dimensional perturbation primitive: from the
base separating circle and the resolvent identity, shrink the parameter
interval and define the contour projection `P(alpha)`.  The conclusion exposes
exactly the branch data consumed by the later stable-complement algebra. -/
theorem fixedContour_rieszProjection_branch_near_zero
    (A : ℝ → NodeMatrix Node) (alpha1 r0 : ℝ)
    (hanalytic : RealAnalyticMatrixFamilyNear (Node := Node) A alpha1)
    (right left : RowVector Node)
    (hspectrum :
      SimpleIsolatedUnitEigenvalueStableSpectrum (Node := Node) (A 0) r0 right left)
    (gamma : ℝ → ℝ) (r : ℝ → RowVector Node)
    (hgamma0 : gamma 0 = 1) (hr0 : r 0 = right)
    (hbranch : ∀ᶠ alpha : ℝ in 𝓝 0,
      AnalyticAt ℝ gamma alpha ∧ AnalyticAt ℝ r alpha ∧
        matrixMulVector (Node := Node) (A alpha) (r alpha) =
          gamma alpha • r alpha ∧
        rowDot (Node := Node) left (r alpha) = 1)
    (baseRadius : ℝ) (hbaseRadius_pos : 0 < baseRadius)
    (hbaseRadius_lt_gap : baseRadius < 1 - r0)
    (hbaseCircle : ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
      ¬ IsComplexRightEigenvalue (Node := Node) (A 0) z)
    (hbaseInteriorSeparates :
      ∀ z : ℂ, IsComplexRightEigenvalue (Node := Node) (A 0) z →
        z ≠ (1 : ℂ) → baseRadius < ‖z - (1 : ℂ)‖)
    (hbaseRiesz :
      IsUnitRieszProjection (Node := Node) (fun _ : ℝ => A 0) 0
        (fun i j : Node => right i * left j)) :
    ∃ alphaP : ℝ, ∃ P : ℝ → NodeMatrix Node,
      alphaP ≤ alpha1 ∧ 0 < alphaP ∧
        (∀ alpha : ℝ, |alpha| < alphaP → AnalyticAt ℝ gamma alpha) ∧
          (∀ alpha : ℝ, |alpha| < alphaP → AnalyticAt ℝ P alpha) ∧
            P 0 = (fun i j : Node => right i * left j) ∧
            ∀ alpha : ℝ, |alpha| ≤ alphaP →
              IsRieszProjectionAtEigenvalue (Node := Node)
                (A alpha) (gamma alpha) (P alpha) := by
  classical
  let Pcontour : ℝ → NodeMatrix Node := fun alpha =>
    fixedCircleRieszProjection (Node := Node) (A alpha) (1 : ℂ) baseRadius
  /-
  The branch is the paper's fixed-contour object:
  `fixedCircleRieszProjection (A alpha) 1 baseRadius`, whose body unfolds to
  Mathlib's `circleIntegral` of the complex resolvent inverse.  The proof
  below supplies the local Lemma A.1 contour step: resolvent persistence on the
  fixed circle, analyticity and real descent of the contour integral, and
  identification with the moving one-dimensional eigenspace of `gamma alpha`.
  -/
  rcases eventually_nhds_zero_abs_radius_of_pos
      (p := fun alpha : ℝ =>
        AnalyticAt ℝ gamma alpha ∧ AnalyticAt ℝ r alpha ∧
          matrixMulVector (Node := Node) (A alpha) (r alpha) =
            gamma alpha • r alpha ∧
          rowDot (Node := Node) left (r alpha) = 1)
      hanalytic.1 hbranch with
    ⟨alphaBranch, halphaBranch_le, halphaBranch_pos, hbranchOn⟩
  rcases fixed_circle_resolvent_persistence_near_zero (Node := Node)
      A alpha1 baseRadius hanalytic hbaseRadius_pos hbaseCircle with
    ⟨alphaResolvent, halphaResolvent_le, halphaResolvent_pos,
      hfixedCircleNoEigen⟩
  have hcontourRieszBranch :
      ∃ alphaP : ℝ,
        alphaP ≤ alpha1 ∧ 0 < alphaP ∧
          (∀ alpha : ℝ, |alpha| < alphaP → AnalyticAt ℝ gamma alpha) ∧
            (∀ alpha : ℝ, |alpha| < alphaP →
              AnalyticAt ℝ Pcontour alpha) ∧
              Pcontour 0 = (fun i j : Node => right i * left j) ∧
              ∀ alpha : ℝ, |alpha| ≤ alphaP →
                IsRieszProjectionAtEigenvalue (Node := Node)
                  (A alpha) (gamma alpha) (Pcontour alpha) := by
    have hfixedCircleContourPrimitive :
        ∃ alphaP : ℝ,
          alphaP ≤ min alphaBranch alphaResolvent ∧ 0 < alphaP ∧
            (∀ alpha : ℝ, |alpha| < alphaP →
              AnalyticAt ℝ Pcontour alpha) ∧
              Pcontour 0 = (fun i j : Node => right i * left j) ∧
              ∀ alpha : ℝ, |alpha| ≤ alphaP →
                IsRieszProjectionAtEigenvalue (Node := Node)
                  (A alpha) (gamma alpha) (Pcontour alpha) := by
      /-
      Canonical circle-integral contour/Riesz primitive.  The surrounding
      neighborhood extraction and gamma-branch analyticity are handled above;
      this block proves that the fixed contour integral is analytic, equals the
      base rank-one projection at `0`, and is the Riesz projection for the
      enclosed moving eigenvalue `gamma alpha`.
      -/
      have hprimitiveNoEigen :
          ∀ alpha : ℝ, |alpha| ≤ min alphaBranch alphaResolvent →
            ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
              ¬ IsComplexRightEigenvalue (Node := Node) (A alpha) z := by
        intro alpha halpha z hz
        exact hfixedCircleNoEigen alpha
          (le_trans halpha (min_le_right alphaBranch alphaResolvent)) z hz
      have hresolventInverseEntryAnalytic :
          ∀ alpha : ℝ, |alpha| < min alphaBranch alphaResolvent →
            ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
              ∀ i j : Node,
                AnalyticAt ℝ
                  (fun a : ℝ =>
                    (complexResolventMatrix (Node := Node) (A a) z)⁻¹ i j)
                  alpha := by
        intro alpha halpha z hz i j
        have hAalpha : AnalyticAt ℝ A alpha := by
          exact hanalytic.2 alpha
            (lt_of_lt_of_le halpha
              (le_trans (min_le_left alphaBranch alphaResolvent)
                halphaBranch_le))
        have hnot :
            ¬ IsComplexRightEigenvalue (Node := Node) (A alpha) z :=
          hprimitiveNoEigen alpha (le_of_lt halpha) z hz
        exact complexResolventInverse_entry_analyticAt_alpha_of_not_eigen
          (Node := Node) A z hAalpha hnot i j
      have hprimitiveBaseSeparates :
          ∀ z : ℂ, IsComplexRightEigenvalue (Node := Node) (A 0) z →
            z ≠ (1 : ℂ) → baseRadius < ‖z - (1 : ℂ)‖ :=
        hbaseInteriorSeparates
      have hscaledResolventEntryAnalytic :
          ∀ alpha : ℝ, |alpha| < min alphaBranch alphaResolvent →
            ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
              ∀ i j : Node,
                AnalyticAt ℝ
                  (fun a : ℝ =>
                    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
                      (complexResolventMatrix (Node := Node) (A a) z)⁻¹ i j)
                  alpha := by
        intro alpha halpha z hz i j
        exact analyticAt_const.mul
          (hresolventInverseEntryAnalytic alpha halpha z hz i j)
      have hP_analytic_of_complexContour :
          (∀ alpha : ℝ, |alpha| < min alphaBranch alphaResolvent →
            ∀ i j : Node,
              AnalyticAt ℝ
                (fun a : ℝ =>
                  complexRieszProjectionOnCircle (Node := Node)
                    (A a) (1 : ℂ) baseRadius i j)
                alpha) →
            ∀ alpha : ℝ, |alpha| < min alphaBranch alphaResolvent →
              AnalyticAt ℝ Pcontour alpha := by
        intro hcomplex alpha halpha
        have hfixed :
            AnalyticAt ℝ
              (fun a : ℝ =>
                fixedCircleRieszProjection (Node := Node)
                  (A a) (1 : ℂ) baseRadius)
              alpha :=
          fixedCircleRieszProjection_analyticAt_of_complex_entries
            (Node := Node) A (1 : ℂ) baseRadius (alpha := alpha)
            (hcomplex alpha halpha)
        simpa [Pcontour] using hfixed
      have hcontourEntryIcc :
          ∀ alpha : ℝ, ∀ i j : Node,
            complexRieszProjectionOnCircle (Node := Node)
                (A alpha) (1 : ℂ) baseRadius i j =
              (letI : DecidableEq Node := Classical.decEq Node;
                (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
                  (∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
                    deriv (circleMap (1 : ℂ) baseRadius) theta •
                      ((complexResolventMatrix (Node := Node) (A alpha)
                        (circleMap (1 : ℂ) baseRadius theta))⁻¹) i j)) := by
        intro alpha i j
        exact complexRieszProjectionOnCircle_entry_eq_Icc_integral
          (Node := Node) (A alpha) (1 : ℂ) baseRadius i j
      have hintegrandAnalytic :
          ∀ alpha : ℝ, |alpha| < min alphaBranch alphaResolvent →
            ∀ theta : ℝ, ∀ i j : Node,
              AnalyticAt ℝ
                (fun a : ℝ =>
                  deriv (circleMap (1 : ℂ) baseRadius) theta *
                    ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
                      (complexResolventMatrix (Node := Node) (A a)
                        (circleMap (1 : ℂ) baseRadius theta))⁻¹ i j))
                alpha := by
        intro alpha halpha theta i j
        exact fixedCircle_scaledResolvent_intervalIntegrand_analyticAt
          (Node := Node) A (center := (1 : ℂ)) (radius := baseRadius)
          (alpha := alpha) (le_of_lt hbaseRadius_pos)
          (by
            intro z hz p q
            exact hscaledResolventEntryAnalytic alpha halpha z hz p q)
          theta i j
      have hprimitiveRadius_pos : 0 < min alphaBranch alphaResolvent :=
        lt_min halphaBranch_pos halphaResolvent_pos
      have hhalfPrimitive_lt :
          (min alphaBranch alphaResolvent) / 2 <
            min alphaBranch alphaResolvent := by
        nlinarith
      have hhalfPrimitive_le :
          (min alphaBranch alphaResolvent) / 2 ≤
            min alphaBranch alphaResolvent :=
        le_of_lt hhalfPrimitive_lt
      have hAanalyticOnPrimitive :
          ∀ alpha : ℝ, |alpha| < min alphaBranch alphaResolvent →
            AnalyticAt ℝ A alpha := by
        intro alpha halpha
        exact hanalytic.2 alpha
          (lt_of_lt_of_le halpha
            (le_trans (min_le_left alphaBranch alphaResolvent)
              halphaBranch_le))
      have hintegrandContinuousOn :
          ∀ i j : Node,
            ContinuousOn
              (fun p : ℝ × ℝ =>
                deriv (circleMap (1 : ℂ) baseRadius) p.2 *
                  ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
                    (complexResolventMatrix (Node := Node) (A p.1)
                      (circleMap (1 : ℂ) baseRadius p.2))⁻¹ i j))
              (Set.Icc (-(min alphaBranch alphaResolvent / 2))
                  (min alphaBranch alphaResolvent / 2) ×ˢ
                Set.Icc (0 : ℝ) (2 * Real.pi)) := by
        intro i j
        exact fixedCircle_scaledResolvent_intervalIntegrand_continuousOn
          (Node := Node) A (min alphaBranch alphaResolvent / 2)
          (min alphaBranch alphaResolvent) (1 : ℂ) baseRadius
          (le_of_lt hbaseRadius_pos) hAanalyticOnPrimitive
          hhalfPrimitive_lt
          (by
            intro alpha halpha z hz
            exact hprimitiveNoEigen alpha
              (le_trans halpha hhalfPrimitive_le) z hz)
          i j
      have hcomplexHalf :
          ∀ alpha : ℝ,
            |alpha| < (min alphaBranch alphaResolvent) / 2 →
              ∀ i j : Node,
                AnalyticAt ℝ
                  (fun a : ℝ =>
                    complexRieszProjectionOnCircle (Node := Node)
                      (A a) (1 : ℂ) baseRadius i j)
                  alpha :=
        complexRieszProjectionOnCircle_entries_analyticAt_of_fixed_interval_integrand
          (Node := Node) A (min alphaBranch alphaResolvent) (1 : ℂ)
          baseRadius hprimitiveRadius_pos (le_of_lt hbaseRadius_pos)
          hAanalyticOnPrimitive
          (by
            intro alpha halpha z hz
            exact hprimitiveNoEigen alpha
              (le_trans halpha hhalfPrimitive_le) z hz)
          hcontourEntryIcc
      have hP_analyticHalf :
          ∀ alpha : ℝ,
            |alpha| < (min alphaBranch alphaResolvent) / 2 →
              AnalyticAt ℝ Pcontour alpha := by
        intro alpha halpha
        have hfixed :
            AnalyticAt ℝ
              (fun a : ℝ =>
                fixedCircleRieszProjection (Node := Node)
                  (A a) (1 : ℂ) baseRadius)
              alpha :=
          fixedCircleRieszProjection_analyticAt_of_complex_entries
            (Node := Node) A (1 : ℂ) baseRadius (alpha := alpha)
            (hcomplexHalf alpha halpha)
        simpa [Pcontour] using hfixed
      have hbaseAndRiesz :
          Pcontour 0 = (fun i j : Node => right i * left j) ∧
            ∀ alpha : ℝ,
              |alpha| ≤ (min alphaBranch alphaResolvent) / 2 →
                IsRieszProjectionAtEigenvalue (Node := Node)
                  (A alpha) (gamma alpha) (Pcontour alpha) := by
        have hgammaComplexEigen :
            ∀ alpha : ℝ, |alpha| < alphaBranch →
              IsComplexRightEigenvalue (Node := Node)
                (A alpha) (gamma alpha : ℂ) := by
          intro alpha halpha
          rcases hbranchOn alpha halpha with
            ⟨_hgamma_an, _hr_an, heigen, hnormalized⟩
          exact isComplexRightEigenvalue_of_real_eigenpair_rowDot_one
            (Node := Node) (A alpha) (gamma alpha) (r alpha) left
            heigen hnormalized
        have hhalf_lt_branch :
            (min alphaBranch alphaResolvent) / 2 < alphaBranch :=
          lt_of_lt_of_le hhalfPrimitive_lt
            (min_le_left alphaBranch alphaResolvent)
        have hgammaInside :
            ∀ alpha : ℝ,
              |alpha| ≤ (min alphaBranch alphaResolvent) / 2 →
                ‖(gamma alpha : ℂ) - (1 : ℂ)‖ < baseRadius := by
          exact eigenbranch_stays_inside_fixed_circle_of_no_boundary
            (Node := Node) A gamma
            ((min alphaBranch alphaResolvent) / 2) alphaBranch baseRadius
            hgamma0 hbaseRadius_pos hhalf_lt_branch
            (fun alpha halpha => (hbranchOn alpha halpha).1)
            hgammaComplexEigen
            (by
              intro alpha halpha z hz
              exact hprimitiveNoEigen alpha
                (le_trans halpha hhalfPrimitive_le) z hz)
        let rho := (min alphaBranch alphaResolvent) / 2
        have hrho_pos : 0 < rho := by
          simpa [rho] using half_pos hprimitiveRadius_pos
        have hP_fixed_analytic :
            ∀ alpha : ℝ, |alpha| < rho →
              AnalyticAt ℝ
                (fun a : ℝ =>
                  fixedCircleRieszProjection (Node := Node)
                    (A a) (1 : ℂ) baseRadius)
                alpha := by
          intro alpha halpha
          simpa [Pcontour, rho] using hP_analyticHalf alpha halpha
        have hnoBoundaryClosed :
            ∀ alpha : ℝ, |alpha| ≤ rho →
              ∀ z : ℂ, ‖z - (1 : ℂ)‖ = baseRadius →
                ¬ IsComplexRightEigenvalue (Node := Node) (A alpha) z := by
          intro alpha halpha z hz
          exact hprimitiveNoEigen alpha
            (le_trans halpha (by simpa [rho] using hhalfPrimitive_le)) z hz
        have hgammaEigenClosed :
            ∀ alpha : ℝ, |alpha| ≤ rho →
              IsComplexRightEigenvalue (Node := Node)
                (A alpha) (gamma alpha : ℂ) := by
          intro alpha halpha
          exact hgammaComplexEigen alpha
            (lt_of_le_of_lt halpha (by simpa [rho] using hhalf_lt_branch))
        have hgammaInsideClosed :
            ∀ alpha : ℝ, |alpha| ≤ rho →
              ‖(gamma alpha : ℂ) - (1 : ℂ)‖ < baseRadius := by
          intro alpha halpha
          exact hgammaInside alpha (by simpa [rho] using halpha)
        have hgammaAnalyticPrimitive :
            ∀ alpha : ℝ, |alpha| < min alphaBranch alphaResolvent →
              AnalyticAt ℝ gamma alpha := by
          intro alpha halpha
          exact (hbranchOn alpha
            (lt_of_lt_of_le halpha
              (min_le_left alphaBranch alphaResolvent))).1
        have hgammaEigenPrimitive :
            ∀ alpha : ℝ, |alpha| < min alphaBranch alphaResolvent →
              IsComplexRightEigenvalue (Node := Node)
                (A alpha) (gamma alpha : ℂ) := by
          intro alpha halpha
          exact hgammaComplexEigen alpha
            (lt_of_lt_of_le halpha
              (min_le_left alphaBranch alphaResolvent))
        have hbridge :=
          fixedContour_projection_rankConstancy_branch_spec
            (Node := Node) A gamma rho (min alphaBranch alphaResolvent) baseRadius
            (fun i j : Node => right i * left j)
            hrho_pos (by simpa [rho] using hhalfPrimitive_lt)
            hbaseRadius_pos hAanalyticOnPrimitive hP_fixed_analytic
            hprimitiveNoEigen
            (IsUnitRieszProjection.isRieszProjectionAtEigenvalue_one
              (Node := Node) hbaseRiesz)
            hbaseInteriorSeparates hgamma0 hgammaAnalyticPrimitive
            hgammaEigenPrimitive
            hgammaInsideClosed
        simpa [Pcontour, rho] using hbridge
      refine ⟨(min alphaBranch alphaResolvent) / 2, hhalfPrimitive_le,
        half_pos hprimitiveRadius_pos, hP_analyticHalf, hbaseAndRiesz.1,
        hbaseAndRiesz.2⟩
    rcases hfixedCircleContourPrimitive with
      ⟨alphaP, halphaP_le_branch, halphaP_pos, hP_analytic, hP0, hRiesz⟩
    refine ⟨alphaP,
      le_trans (le_trans halphaP_le_branch
        (min_le_left alphaBranch alphaResolvent)) halphaBranch_le,
      halphaP_pos, ?_, hP_analytic, hP0, hRiesz⟩
    intro alpha halpha
    exact (hbranchOn alpha
      (lt_of_lt_of_le halpha
        (le_trans halphaP_le_branch
          (min_le_left alphaBranch alphaResolvent)))).1
  rcases hcontourRieszBranch with
    ⟨alphaP, halphaP_le, halphaP_pos, hgamma_analytic, hP_analytic,
      hP0, hRiesz⟩
  exact ⟨alphaP, Pcontour, halphaP_le, halphaP_pos, hgamma_analytic,
    hP_analytic, hP0, hRiesz⟩

/-- Finite-dimensional spectral upper-semicontinuity step used in Appendix A.

After the Riesz branch has produced the stable complement `F`, the paper
shrinks the parameter interval so the spectrum of `F alpha` remains in a
strictly larger disk than the base stable spectrum.  This is the Mathlib-style
finite-matrix primitive needed by `stableComplement_resolventDisk_shrink_of_riesz_branch`:
continuity of the matrix entries plus a base spectral gap should give a
uniform open spectral enclosure near `alpha = 0`. -/
theorem finiteNodeMatrix_spectrum_upperSemicontinuity_stableDisk
    (F : ℝ → NodeMatrix Node) (alphaAnalytic r0 theta : ℝ)
    (hFanalytic :
      ∀ alpha : ℝ, |alpha| < alphaAnalytic → AnalyticAt ℝ F alpha)
    (halphaAnalytic_pos : 0 < alphaAnalytic)
    (hr0_theta : r0 < theta) (htheta_lt_one : theta < 1)
    (hbaseSpectrum : ∀ z : ℂ,
      IsComplexRightEigenvalue (Node := Node) (F 0) z → ‖z‖ ≤ r0) :
    ∃ alpha0 : ℝ,
      alpha0 ≤ alphaAnalytic ∧ 0 < alpha0 ∧
        StableRemainderResolventDisk (Node := Node) F alpha0 theta := by
  classical
  /-
  Typed same-interface attempt for the source's spectral upper-semicontinuity
  sentence in Lemma A.1.  The first unavailable primitive is a finite-dimensional
  theorem converting entrywise/analytic continuity of `F` and the strict base
  spectral gap `r0 < theta` into persistence of all complex eigenvalues inside
  `|z| < theta` on a smaller real parameter interval.  A direct Mathlib/SOptLib
  symbol search found no theorem exposing this for `Matrix Node Node ℂ` with the
  local `IsComplexRightEigenvalue` predicate.
  -/
  have hbaseInside := hbaseSpectrum
  have hbaseSpectrum_mathlib : ∀ z : ℂ,
      z ∈ spectrum ℂ (complexOfRealMatrix (Node := Node) (F 0)) →
        ‖z‖ ≤ r0 := by
    intro z hz
    exact hbaseSpectrum z
      ((isComplexRightEigenvalue_iff_mem_spectrum_complexOfRealMatrix
        (Node := Node) (F 0) z).2 hz)
  have hsourceConclusion_mathlib :
      ∀ alpha0' : ℝ,
        StableRemainderResolventDisk (Node := Node) F alpha0' theta ↔
          ∀ alpha : ℝ, |alpha| ≤ alpha0' →
            (∀ z : ℂ,
              z ∈ spectrum ℂ (complexOfRealMatrix (Node := Node) (F alpha)) →
                ‖z‖ < theta) ∧
              ∀ z : ℂ, ‖z‖ = theta →
                z ∉ spectrum ℂ (complexOfRealMatrix (Node := Node) (F alpha)) := by
    intro alpha0'
    exact stableRemainderResolventDisk_iff_mathlib_spectrum (Node := Node)
      F alpha0' theta
  have hgap : 0 < theta - r0 := sub_pos.mpr hr0_theta
  have hcontinuousNearBase := hFanalytic
  have hnonemptyRadius : 0 < min alphaAnalytic ((theta - r0) / 2) := by
    exact lt_min halphaAnalytic_pos (half_pos hgap)
  have hG_continuousAt :
      ContinuousAt
        (fun alpha : ℝ =>
          complexOfRealMatrix (Node := Node) (F alpha)) 0 :=
    complexOfRealMatrix_family_continuousAt_zero_of_analytic
      (Node := Node) F alphaAnalytic hFanalytic halphaAnalytic_pos
  obtain ⟨eps, heps_pos, hspectrumNear⟩ :=
    complexNodeMatrix_spectrum_upperSemicontinuity_norm_lt (Node := Node)
      (fun alpha : ℝ =>
        complexOfRealMatrix (Node := Node) (F alpha))
      r0 theta hG_continuousAt hr0_theta hbaseSpectrum_mathlib
  let alpha0 : ℝ := min (alphaAnalytic / 2) (eps / 2)
  have halpha0_le_alphaAnalytic : alpha0 ≤ alphaAnalytic := by
    have hle_half : alpha0 ≤ alphaAnalytic / 2 := by
      exact min_le_left (alphaAnalytic / 2) (eps / 2)
    linarith
  have halpha0_pos : 0 < alpha0 := by
    exact lt_min (half_pos halphaAnalytic_pos) (half_pos heps_pos)
  refine ⟨alpha0, halpha0_le_alphaAnalytic, halpha0_pos, ?_⟩
  exact (hsourceConclusion_mathlib alpha0).2 (by
    intro alpha halpha
    have halpha_lt_eps : |alpha| < eps := by
      have hle_eps_half : |alpha| ≤ eps / 2 := by
        exact le_trans halpha (by
          have hmin : alpha0 ≤ eps / 2 :=
            min_le_right (alphaAnalytic / 2) (eps / 2)
          simpa [alpha0] using hmin)
      linarith
    constructor
    · intro z hz
      exact hspectrumNear alpha halpha_lt_eps z hz
    · intro z hzNorm hz
      have hlt := hspectrumNear alpha halpha_lt_eps z hz
      rw [hzNorm] at hlt
      exact (lt_irrefl theta hlt))

/-- Stable-complement spectral shrink after the moving Riesz projection branch
has been constructed.

This is the second contour-persistence primitive in Appendix A: after
`P(alpha)` has been identified as the Riesz projection for `gamma(alpha)`,
shrink the interval and choose `r0 < theta < 1` so the spectrum of
`A(alpha)-gamma(alpha)P(alpha)` remains strictly inside `|z| = theta`. -/
theorem stableComplement_resolventDisk_shrink_of_riesz_branch
    (A : ℝ → NodeMatrix Node) (alpha1 r0 : ℝ)
    (hanalytic : RealAnalyticMatrixFamilyNear (Node := Node) A alpha1)
    (right left : RowVector Node)
    (hspectrum :
      SimpleIsolatedUnitEigenvalueStableSpectrum (Node := Node) (A 0) r0 right left)
    (gamma : ℝ → ℝ) (P : ℝ → NodeMatrix Node) (alphaP : ℝ)
    (halphaP_le : alphaP ≤ alpha1) (halphaP_pos : 0 < alphaP)
    (hgamma_analytic :
      ∀ alpha : ℝ, |alpha| < alphaP → AnalyticAt ℝ gamma alpha)
    (hP_analytic :
      ∀ alpha : ℝ, |alpha| < alphaP → AnalyticAt ℝ P alpha)
    (hgamma0 : gamma 0 = 1)
    (hP0 : P 0 = (fun i j : Node => right i * left j))
    (hRiesz : ∀ alpha : ℝ, |alpha| ≤ alphaP →
      IsRieszProjectionAtEigenvalue (Node := Node)
        (A alpha) (gamma alpha) (P alpha)) :
    ∃ alpha0 theta : ℝ,
      alpha0 ≤ alphaP ∧ 0 < alpha0 ∧ r0 < theta ∧ theta < 1 ∧
        StableRemainderResolventDisk (Node := Node)
          (stableComplementFromRiesz (Node := Node) A gamma P) alpha0 theta := by
  classical
  /-
  Typed source-stage attempt.  The remaining missing primitive is spectral
  upper-semicontinuity for the custom finite `NodeMatrix` scalar extension,
  applied to the stable complement produced from the Riesz branch.
  -/
  have hstableAtBase : ∀ z : ℂ,
      IsComplexRightEigenvalue (Node := Node) (A 0) z →
        z ≠ (1 : ℂ) → ‖z‖ ≤ r0 :=
    hspectrum.2.2.2.2.2.2
  have hRieszAtBase :
      IsRieszProjectionAtEigenvalue (Node := Node)
        (A 0) 1 (P 0) := by
    have hzero_le : |(0 : ℝ)| ≤ alphaP := by
      simpa using halphaP_pos.le
    simpa [hgamma0] using hRiesz 0 hzero_le
  have hbaseProjectionIdentified :
      P 0 = (fun i j : Node => right i * left j) := hP0
  have hbaseComplementIdentified :
      stableComplementFromRiesz (Node := Node) A gamma P 0 =
        stableComplementMatrix (Node := Node) (A 0) 1
          (fun i j : Node => right i * left j) := by
    funext i j
    simp [stableComplementFromRiesz, stableComplementMatrix, hgamma0,
      hbaseProjectionIdentified]
  have hbaseComplementAlgebra :
      A 0 =
          matrixAdd (Node := Node) ((1 : ℝ) • P 0)
            (stableComplementMatrix (Node := Node) (A 0) 1 (P 0)) ∧
        matrixMul (Node := Node) (P 0)
            (stableComplementMatrix (Node := Node) (A 0) 1 (P 0)) = 0 ∧
          matrixMul (Node := Node)
            (stableComplementMatrix (Node := Node) (A 0) 1 (P 0)) (P 0) = 0 :=
    rieszProjection_stableComplementMatrix_algebra (Node := Node)
      (A 0) 1 (P 0) hRieszAtBase
  have hprojectionBranch := hRiesz
  have hbaseComplementSpectrum :
      ∀ z : ℂ,
        IsComplexRightEigenvalue (Node := Node)
          (stableComplementFromRiesz (Node := Node) A gamma P 0) z →
          ‖z‖ ≤ r0 := by
    intro z hz
    have hz' :
        IsComplexRightEigenvalue (Node := Node)
          (stableComplementMatrix (Node := Node) (A 0) 1 (P 0)) z := by
      have hz_outer :
          IsComplexRightEigenvalue (Node := Node)
            (stableComplementMatrix (Node := Node) (A 0) 1
              (fun i j : Node => right i * left j)) z := by
        simpa [hbaseComplementIdentified] using hz
      simpa [hP0] using hz_outer
    exact stableComplementMatrix_base_spectrum_le_of_riesz (Node := Node)
      (A 0) r0 right left (P 0) hspectrum hRieszAtBase hP0 z hz'
  let theta : ℝ := (r0 + 1) / 2
  have hr0_theta : r0 < theta := by
    dsimp [theta]
    linarith [hspectrum.2.1]
  have htheta_lt_one : theta < 1 := by
    dsimp [theta]
    linarith [hspectrum.2.1]
  have hF_analytic : ∀ alpha : ℝ, |alpha| < alphaP →
      AnalyticAt ℝ
        (stableComplementFromRiesz (Node := Node) A gamma P) alpha := by
    intro alpha halpha
    exact stableComplementFromRiesz_analyticAt (Node := Node)
      A gamma P alpha
      (hanalytic.2 alpha (lt_of_lt_of_le halpha halphaP_le))
      (hgamma_analytic alpha halpha) (hP_analytic alpha halpha)
  obtain ⟨alpha0, halpha0_le, halpha0_pos, hresolvent⟩ :=
    finiteNodeMatrix_spectrum_upperSemicontinuity_stableDisk (Node := Node)
      (stableComplementFromRiesz (Node := Node) A gamma P)
      alphaP r0 theta hF_analytic halphaP_pos
      hr0_theta htheta_lt_one hbaseComplementSpectrum
  exact ⟨alpha0, theta, halpha0_le, halpha0_pos, hr0_theta,
    htheta_lt_one, hresolvent⟩

/-- Appendix A fixed-contour Riesz projection branch before the stable
complement algebra is folded in.

This core source-stage theorem is the remaining contour/resolvent construction
after the normalized eigenbranch has already supplied the slow multiplier
`gamma`.  It should be proved by choosing the fixed contour around the base
unit eigenvalue, shrinking the parameter interval so the contour remains in the
resolvent set, defining `P(alpha)` by the Riesz integral, and shrinking again so
the stable complement has a uniform resolvent disk. -/
theorem analytic_riesz_projection_branch_core_near_zero
    (A : ℝ → NodeMatrix Node) (alpha1 r0 : ℝ)
    (hanalytic : RealAnalyticMatrixFamilyNear (Node := Node) A alpha1)
    (right left : RowVector Node)
    (hspectrum :
      SimpleIsolatedUnitEigenvalueStableSpectrum (Node := Node) (A 0) r0 right left)
    (gamma : ℝ → ℝ) (r : ℝ → RowVector Node)
    (hgamma0 : gamma 0 = 1) (hr0 : r 0 = right)
    (hbranch : ∀ᶠ alpha : ℝ in 𝓝 0,
      AnalyticAt ℝ gamma alpha ∧ AnalyticAt ℝ r alpha ∧
        matrixMulVector (Node := Node) (A alpha) (r alpha) =
          gamma alpha • r alpha ∧
        rowDot (Node := Node) left (r alpha) = 1) :
    ∃ alpha0 theta : ℝ, ∃ P : ℝ → NodeMatrix Node,
      alpha0 ≤ alpha1 ∧ 0 < alpha0 ∧ r0 < theta ∧ theta < 1 ∧
        (∀ alpha : ℝ, |alpha| < alpha0 → AnalyticAt ℝ gamma alpha) ∧
          (∀ alpha : ℝ, |alpha| < alpha0 → AnalyticAt ℝ P alpha) ∧
            (∀ alpha : ℝ, |alpha| ≤ alpha0 →
              IsRieszProjectionAtEigenvalue (Node := Node)
                (A alpha) (gamma alpha) (P alpha)) ∧
              StableRemainderResolventDisk (Node := Node)
                (stableComplementFromRiesz (Node := Node) A gamma P)
                alpha0 theta := by
  classical
  obtain ⟨baseRadius, hbaseRadius_pos, hbaseRadius_lt_gap,
      hbaseCircle, hbaseInteriorSeparates⟩ :=
    exists_unit_spectral_separating_circle_strong (Node := Node)
      (A 0) r0 right left hspectrum
  have hbaseRiesz :
      IsUnitRieszProjection (Node := Node) (fun _ : ℝ => A 0) 0
        (fun i j : Node => right i * left j) := by
    exact normalized_unit_outer_product_isUnitRieszProjection_at_base
      (Node := Node) (A 0) r0 right left hspectrum
  obtain ⟨alphaP, P, halphaP_le, halphaP_pos, hgamma_analytic,
      hP_analytic, hP0, hRiesz⟩ :=
    fixedContour_rieszProjection_branch_near_zero (Node := Node)
      A alpha1 r0 hanalytic right left hspectrum gamma r hgamma0 hr0
      hbranch baseRadius hbaseRadius_pos hbaseRadius_lt_gap hbaseCircle
      hbaseInteriorSeparates hbaseRiesz
  obtain ⟨alpha0, theta, halpha0_leP, halpha0_pos, hr0_theta,
      htheta_lt_one, hresolvent⟩ :=
    stableComplement_resolventDisk_shrink_of_riesz_branch (Node := Node)
      A alpha1 r0 hanalytic right left hspectrum gamma P alphaP
      halphaP_le halphaP_pos hgamma_analytic hP_analytic hgamma0 hP0 hRiesz
  refine ⟨alpha0, theta, P, le_trans halpha0_leP halphaP_le, halpha0_pos,
    hr0_theta, htheta_lt_one, ?_, ?_, ?_, hresolvent⟩
  · intro alpha halpha
    exact hgamma_analytic alpha (lt_of_lt_of_le halpha halpha0_leP)
  · intro alpha halpha
    exact hP_analytic alpha (lt_of_lt_of_le halpha halpha0_leP)
  · intro alpha halpha
    exact hRiesz alpha (le_trans halpha halpha0_leP)

/-- Appendix A fixed-contour Riesz projection branch before the stable
complement algebra is folded in.

This is the exact source construction from Lemma A.1 proof steps 1--4: choose
a contour around the base unit eigenvalue, persist the resolvent on a smaller
parameter interval, define the real Riesz projection branch `P(α)`, follow the
enclosed multiplier `γ(α)`, and shrink once more so the complement
`A(α)-γ(α)P(α)` has a uniform stable resolvent disk. -/
theorem analytic_riesz_projection_branch_near_zero
    (A : ℝ → NodeMatrix Node) (alpha1 r0 : ℝ)
    (hanalytic : RealAnalyticMatrixFamilyNear (Node := Node) A alpha1)
    (right left : RowVector Node)
    (hspectrum :
      SimpleIsolatedUnitEigenvalueStableSpectrum (Node := Node) (A 0) r0 right left) :
    ∃ alpha0 theta : ℝ, ∃ gamma : ℝ → ℝ,
      ∃ P : ℝ → NodeMatrix Node,
        alpha0 ≤ alpha1 ∧ 0 < alpha0 ∧ r0 < theta ∧ theta < 1 ∧
          gamma 0 = 1 ∧
            (∀ alpha : ℝ, |alpha| < alpha0 → AnalyticAt ℝ gamma alpha) ∧
              (∀ alpha : ℝ, |alpha| < alpha0 → AnalyticAt ℝ P alpha) ∧
                (∀ alpha : ℝ, |alpha| < alpha0 →
                  AnalyticAt ℝ
                    (stableComplementFromRiesz (Node := Node) A gamma P) alpha) ∧
                  (∃ Aderiv : NodeMatrix Node,
                    HasDerivAt A Aderiv 0 ∧
                      HasDerivAt gamma
                        (rowDot (Node := Node) left
                          (matrixMulVector (Node := Node) Aderiv right)) 0) ∧
                    (∀ alpha : ℝ, |alpha| ≤ alpha0 →
                      IsRieszProjectionAtEigenvalue (Node := Node)
                        (A alpha) (gamma alpha) (P alpha)) ∧
                      StableRemainderResolventDisk (Node := Node)
                        (stableComplementFromRiesz (Node := Node) A gamma P)
                        alpha0 theta := by
  classical
  have hsimple :
      UnitEigenvalueAlgebraicallySimple (Node := Node) (A 0) right :=
    hspectrum.unit_algebraicallySimple
  obtain ⟨gamma, r, hgamma0, hr0, hbranch⟩ :=
    analytic_normalized_right_eigenbranch_eventually (Node := Node)
      A alpha1 right left hanalytic hspectrum.2.2.1.2
        hspectrum.2.2.2.1.2 hspectrum.2.2.2.2.1 hsimple
  obtain ⟨alpha0, theta, P, halpha0_le, halpha0_pos, hr0_theta,
      htheta_lt_one, hgamma_analytic, hP_analytic, hRiesz, hresolvent⟩ :=
    analytic_riesz_projection_branch_core_near_zero (Node := Node)
      A alpha1 r0 hanalytic right left hspectrum gamma r hgamma0 hr0 hbranch
  have hF_analytic : ∀ alpha : ℝ, |alpha| < alpha0 →
      AnalyticAt ℝ
        (stableComplementFromRiesz (Node := Node) A gamma P) alpha := by
    intro alpha halpha
    exact stableComplementFromRiesz_analyticAt (Node := Node)
      A gamma P alpha (hanalytic.2 alpha (lt_of_lt_of_le halpha halpha0_le))
      (hgamma_analytic alpha halpha) (hP_analytic alpha halpha)
  have hderiv :
      ∃ Aderiv : NodeMatrix Node,
        HasDerivAt A Aderiv 0 ∧
          HasDerivAt gamma
            (rowDot (Node := Node) left
              (matrixMulVector (Node := Node) Aderiv right)) 0 :=
    normalized_eigenbranch_derivative_pairing_eventual (Node := Node)
      A gamma r alpha1 right left hanalytic hspectrum.2.2.2.1.2
      hr0 hspectrum.2.2.2.2.1 hgamma0 hbranch
  exact ⟨alpha0, theta, gamma, P, halpha0_le, halpha0_pos, hr0_theta,
    htheta_lt_one, hgamma0, hgamma_analytic, hP_analytic, hF_analytic,
    hderiv, hRiesz, hresolvent⟩

/-- Appendix A fixed-contour Riesz projection branch near a simple isolated
unit eigenvalue.

The output is the source-facing object requested by Lemma A.1: `P alpha` is
the unit Riesz projection for `A alpha`, `F alpha = A alpha (I-P alpha)` is the
stable complement, and the complement has a uniform resolvent disk. The proof
is the paper's compact-contour argument: choose a separating circle from
`exists_unit_spectral_separating_circle`, use resolvent persistence to define
the analytic projection, identify the base projection with the normalized outer
product, and shrink the parameter interval until the complementary spectrum
lies inside a fixed `theta < 1`. -/
theorem analytic_unit_riesz_projection_near_zero
    (A : ℝ → NodeMatrix Node) (alpha1 r0 : ℝ)
    (hanalytic : RealAnalyticMatrixFamilyNear (Node := Node) A alpha1)
    (right left : RowVector Node)
    (hspectrum :
      SimpleIsolatedUnitEigenvalueStableSpectrum (Node := Node) (A 0) r0 right left) :
    ∃ alpha0 alphaAnalytic theta : ℝ, ∃ gamma : ℝ → ℝ,
      ∃ P F : ℝ → NodeMatrix Node,
        alpha0 ≤ alphaAnalytic ∧ alphaAnalytic ≤ alpha1 ∧
          0 < alpha0 ∧ alpha0 < alphaAnalytic ∧
          r0 < theta ∧ theta < 1 ∧
          gamma 0 = 1 ∧
            (∀ alpha : ℝ, |alpha| < alphaAnalytic → AnalyticAt ℝ gamma alpha) ∧
              (∀ alpha : ℝ, |alpha| < alphaAnalytic → AnalyticAt ℝ P alpha) ∧
                (∀ alpha : ℝ, |alpha| < alphaAnalytic → AnalyticAt ℝ F alpha) ∧
                  (∃ Aderiv : NodeMatrix Node,
                    HasDerivAt A Aderiv 0 ∧
                      HasDerivAt gamma
                        (rowDot (Node := Node) left
                          (matrixMulVector (Node := Node) Aderiv right)) 0) ∧
                    (∀ alpha : ℝ, |alpha| ≤ alpha0 →
                      IsRieszProjectionAtEigenvalue (Node := Node)
                        (A alpha) (gamma alpha) (P alpha) ∧
                        A alpha = matrixAdd (Node := Node)
                          ((gamma alpha) • P alpha) (F alpha) ∧
                          matrixMul (Node := Node) (P alpha) (F alpha) = 0 ∧
                            matrixMul (Node := Node) (F alpha) (P alpha) = 0) ∧
                      StableRemainderResolventDisk (Node := Node) F alpha0 theta := by
  classical
  obtain ⟨alphaCore, theta, gamma, P, halphaCore_le, halphaCore_pos,
      hr0_theta, htheta_lt_one, hgamma0, hgamma_analytic,
      hP_analytic, hF_analytic, hderiv, hRiesz, hresolvent⟩ :=
    analytic_riesz_projection_branch_near_zero (Node := Node)
      A alpha1 r0 hanalytic right left hspectrum
  let alpha0 : ℝ := alphaCore / 2
  have halpha0_pos : 0 < alpha0 := by
    dsimp [alpha0]
    linarith
  have halpha0_lt_core : alpha0 < alphaCore := by
    dsimp [alpha0]
    linarith
  have halpha0_le_core : alpha0 ≤ alphaCore := le_of_lt halpha0_lt_core
  let F : ℝ → NodeMatrix Node :=
    stableComplementFromRiesz (Node := Node) A gamma P
  refine ⟨alpha0, alphaCore, theta, gamma, P, F, halpha0_le_core, halphaCore_le,
    halpha0_pos, halpha0_lt_core, hr0_theta, htheta_lt_one, hgamma0,
    hgamma_analytic, hP_analytic,
    ?_, hderiv, ?_, ?_⟩
  · simpa [F] using hF_analytic
  · intro alpha halpha
    have halg :=
      rieszProjection_stableComplementMatrix_algebra (Node := Node)
        (A alpha) (gamma alpha) (P alpha)
        (hRiesz alpha (le_trans halpha halpha0_le_core))
    exact ⟨hRiesz alpha (le_trans halpha halpha0_le_core),
      halg.1, halg.2.1, halg.2.2⟩
  · intro alpha halpha
    exact hresolvent alpha (le_trans halpha halpha0_le_core)

/-- Compact-contour resolvent bound used in Appendix A's proof of (A.2).

This helper isolates the finite-dimensional step "the resolvent is continuous
on the compact product `{|alpha| <= alpha0} x {|z| = theta}`, hence uniformly
bounded" for the file's custom `NodeMatrix` model. -/
theorem stableRemainder_resolventNorm_uniform_on_circle
    (F : ℝ → NodeMatrix Node) (alpha0 alphaAnalytic theta : ℝ)
    (hFanalytic :
      ∀ alpha : ℝ, |alpha| < alphaAnalytic → AnalyticAt ℝ F alpha)
    (hmargin : alpha0 < alphaAnalytic)
    (halpha0 : 0 < alpha0) (htheta_pos : 0 < theta) (htheta_lt_one : theta < 1)
    (hresolvent :
      StableRemainderResolventDisk (Node := Node) F alpha0 theta) :
    ∃ M : ℝ, 0 ≤ M ∧
      UniformComplexResolventBoundOnCircle (Node := Node) F alpha0 theta M := by
  classical
  /-
  Typed source-stage attempt.  `hresolvent` supplies absence of point spectrum
  on the circle.  The first missing Mathlib/project bridge is the finite
  custom-matrix equivalence between "not an eigenvalue" and existence of a
  two-sided inverse for `complexResolventMatrix`, followed by continuity of
  that inverse as a function of `(alpha,z)`.
  -/
  have hcircleNoEigen : ∀ alpha : ℝ, |alpha| ≤ alpha0 →
      ∀ z : ℂ, ‖z‖ = theta →
        ¬ IsComplexRightEigenvalue (Node := Node) (F alpha) z := by
    intro alpha halpha z hz
    exact (hresolvent alpha halpha).2 z hz
  have hresolventExists : ∀ alpha : ℝ, |alpha| ≤ alpha0 →
      ∀ z : ℂ, ‖z‖ = theta →
        ∃ R : ComplexNodeMatrix Node,
          HasComplexResolvent (Node := Node) (F alpha) z R := by
    intro alpha halpha z hz
    exact exists_complexResolvent_of_not_eigen (Node := Node)
      (F alpha) z (hcircleNoEigen alpha halpha z hz)
  let contourSet : Set (ℝ × ℂ) :=
    Set.Icc (-alpha0) alpha0 ×ˢ Metric.sphere (0 : ℂ) theta
  let resolventNormOnContour : ℝ × ℂ → ℝ := fun p =>
    complexMatrixOperatorNorm (Node := Node)
      ((complexResolventMatrix (Node := Node) (F p.1) p.2)⁻¹)
  have hcompact : IsCompact contourSet := by
    simpa [contourSet] using
      (isCompact_Icc.prod (isCompact_sphere (0 : ℂ) theta))
  have hFcontinuousOn : ContinuousOn F (Set.Icc (-alpha0) alpha0) :=
    analytic_matrixFamily_continuousOn_Icc_of_lt (Node := Node)
      F alpha0 alphaAnalytic hFanalytic hmargin
  have hcont : ContinuousOn resolventNormOnContour contourSet := by
    simpa [resolventNormOnContour, contourSet] using
      complexResolventOperatorNorm_continuousOn_contour (Node := Node)
        F alpha0 theta hFcontinuousOn hcircleNoEigen
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
      exact (abs_le.mp halpha)
    have hzSphere : z ∈ Metric.sphere (0 : ℂ) theta := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hp : (alpha, z) ∈ contourSet := by
      exact ⟨halphaIcc, hzSphere⟩
    have hbound := hM_bound (alpha, z) hp
    have hnonneg : 0 ≤ complexMatrixOperatorNorm (Node := Node) R :=
      (complexMatrixOperatorNorm_spec (Node := Node) R).1
    have hle_abs :
        complexMatrixOperatorNorm (Node := Node) R ≤
          ‖complexMatrixOperatorNorm (Node := Node) R‖ :=
      le_abs_self _
    exact le_trans hle_abs (by
      simpa [resolventNormOnContour, R] using hbound)

/-- Canonical inverse bridge for the source-circle resolvent bound.

`UniformComplexResolventBoundOnCircle` is intentionally stated with an
existential resolvent inverse, while the contour integrals use Mathlib's
canonical matrix inverse.  This helper identifies those inverses by uniqueness
of a right inverse and transfers the uniform operator-norm bound. -/
theorem complex_resolvent_canonical_inverse_bound_of_uniform_on_circle
    [DecidableEq Node]
    (F : ℝ → NodeMatrix Node) (alpha0 theta M : ℝ)
    (hresolventBound :
      UniformComplexResolventBoundOnCircle (Node := Node) F alpha0 theta M) :
    ∀ alpha : ℝ, |alpha| ≤ alpha0 →
      ∀ z : ℂ, ‖z‖ = theta →
        complexMatrixOperatorNorm (Node := Node)
          ((complexResolventMatrix (Node := Node) (F alpha) z)⁻¹) ≤ M := by
  intro alpha halpha z hz
  rcases hresolventBound alpha halpha z hz with ⟨R, hRspec, hRbound⟩
  have hR_eq :
      (complexResolventMatrix (Node := Node) (F alpha) z)⁻¹ = R := by
    exact Matrix.inv_eq_right_inv (by
      simpa [complexMatrixMul, complexIdentityMatrix_eq_one] using hRspec.1)
  simpa [hR_eq] using hRbound

/-- A concrete finite-dimensional upper bound for the file's scalar matrix
Euclidean operator norm.

This exposes the estimate proved internally in
`matrixEuclideanOperatorNorm_spec`: the operator norm is bounded by the
entrywise `l¹` matrix norm times the square root of the number of nodes. -/
theorem matrixEuclideanOperatorNorm_le_sum_abs_mul_sqrt_card
    (A : NodeMatrix Node) :
    matrixEuclideanOperatorNorm (Node := Node) A ≤
      (∑ i : Node, ∑ j : Node, |A i j|) *
        Real.sqrt (nodeCount (Node := Node) : ℝ) := by
  classical
  simpa [matrixEuclideanOperatorNorm, rowEuclideanNorm, rowNormSq,
    matrixMulVector, nodeCount, Matrix.mulVec, dotProduct, Real.norm_eq_abs,
    sq_abs] using Matrix.euclidean_opNorm_le_sum_norm_mul_sqrt_card
      (m := Node) (n := Node) (𝕜 := ℝ) A

/-- Entrywise absolute-value control implies a concrete real operator-norm
bound for the custom node-matrix norm. -/
theorem matrixEuclideanOperatorNorm_le_of_entrywise_abs_bound
    (A : NodeMatrix Node) (B : ℝ) (hB : 0 ≤ B)
    (hentry : ∀ i j : Node, |A i j| ≤ B) :
    matrixEuclideanOperatorNorm (Node := Node) A ≤
      (((nodeCount (Node := Node) : ℝ) ^ 2) *
          Real.sqrt (nodeCount (Node := Node) : ℝ)) * B := by
  simpa [matrixEuclideanOperatorNorm, rowEuclideanNorm, rowNormSq,
    matrixMulVector, nodeCount, Matrix.mulVec, dotProduct, Real.norm_eq_abs,
    sq_abs, pow_two] using
      Matrix.euclidean_opNorm_le_of_entrywise_norm_le (A := A) (B := B)
        (by simpa [Real.norm_eq_abs] using hentry)

/-- Entrywise bound for the scaled Cauchy integral appearing in the stable
power formula.  The only analytic input is the canonical inverse norm bound on
the contour; the estimate itself is Mathlib's circle-integral length bound. -/
theorem cauchy_scaled_resolvent_entry_integral_bound
    [DecidableEq Node]
    (F : ℝ → NodeMatrix Node) (alpha0 theta M : ℝ)
    (htheta_nonneg : 0 ≤ theta) (hM_nonneg : 0 ≤ M)
    (hcanonicalResolventBound :
      ∀ alpha : ℝ, |alpha| ≤ alpha0 →
        ∀ z : ℂ, ‖z‖ = theta →
          complexMatrixOperatorNorm (Node := Node)
            ((complexResolventMatrix (Node := Node) (F alpha) z)⁻¹) ≤ M)
    (alpha : ℝ) (halpha : |alpha| ≤ alpha0)
    (j : ℕ) (i k : Node) :
    ‖(((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ z in C((0 : ℂ), theta),
          z ^ j *
            ((complexResolventMatrix (Node := Node) (F alpha) z)⁻¹) i k)‖ ≤
      theta * (theta ^ j * M) := by
  classical
  have hC_nonneg : 0 ≤ theta ^ j * M := by
    exact mul_nonneg (pow_nonneg htheta_nonneg j) hM_nonneg
  have hpoint :
      ∀ z ∈ Metric.sphere (0 : ℂ) theta,
        ‖z ^ j *
            ((complexResolventMatrix (Node := Node) (F alpha) z)⁻¹) i k‖ ≤
          theta ^ j * M := by
    intro z hz
    have hz_norm : ‖z‖ = theta := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hentry :
        ‖((complexResolventMatrix (Node := Node) (F alpha) z)⁻¹) i k‖ ≤ M := by
      exact le_trans
        (complexMatrix_entry_norm_le_operatorNorm (Node := Node)
          ((complexResolventMatrix (Node := Node) (F alpha) z)⁻¹) i k)
        (hcanonicalResolventBound alpha halpha z hz_norm)
    calc
      ‖z ^ j *
          ((complexResolventMatrix (Node := Node) (F alpha) z)⁻¹) i k‖ =
          ‖z‖ ^ j *
            ‖((complexResolventMatrix (Node := Node) (F alpha) z)⁻¹) i k‖ := by
            rw [norm_mul, norm_pow]
      _ = theta ^ j *
            ‖((complexResolventMatrix (Node := Node) (F alpha) z)⁻¹) i k‖ := by
            rw [hz_norm]
      _ ≤ theta ^ j * M :=
            mul_le_mul_of_nonneg_left hentry (pow_nonneg htheta_nonneg j)
  have hscaled :=
    circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
      (c := (0 : ℂ)) (R := theta) (C := theta ^ j * M)
      htheta_nonneg hpoint
  simpa [smul_eq_mul] using hscaled

/-- A spectral disk enclosure gives the no-boundary condition on the
zero-centered contour. -/
theorem no_complex_eigen_on_circle_of_spectrum_inside_disk
    (A : NodeMatrix Node) (theta : ℝ) (htheta_pos : 0 < theta)
    (hspectrum_inside :
      ∀ z : ℂ, IsComplexRightEigenvalue (Node := Node) A z → ‖z‖ < theta) :
    ∀ z : ℂ, ‖z‖ = theta →
      ¬ IsComplexRightEigenvalue (Node := Node) A z := by
  intro z hz heig
  have htheta_nonneg : 0 ≤ theta := htheta_pos.le
  have hlt : ‖z‖ < theta := hspectrum_inside z heig
  have hself : theta < theta := by
    simpa [hz] using hlt
  exact (lt_irrefl theta) hself

/-- Complexification commutes with the file's custom right-recursive matrix
power. -/
theorem complexOfRealMatrix_matrixPower
    [DecidableEq Node] (A : NodeMatrix Node) :
    ∀ j : ℕ,
      complexOfRealMatrix (Node := Node) (matrixPower (Node := Node) A j) =
        (complexOfRealMatrix (Node := Node) A) ^ j := by
  intro j
  induction j with
  | zero =>
      ext i k
      by_cases hik : i = k
      · subst k
        simp [matrixPower, identityMatrix, complexOfRealMatrix]
      · simp [matrixPower, identityMatrix, complexOfRealMatrix, hik]
  | succ j ih =>
      rw [matrixPower, complexOfRealMatrix_matrixMul, ih, pow_succ]
      simp [complexMatrixMul]

/-- One-point resolvent algebra for the right-multiplication recurrence:
`(zI - A)^{-1} A = z (zI - A)^{-1} - I`. -/
theorem complexResolvent_inv_mul_complexOfRealMatrix_eq_z_smul_sub_one
    [DecidableEq Node]
    (A : NodeMatrix Node) (z : ℂ)
    (hnot : ¬ IsComplexRightEigenvalue (Node := Node) A z) :
    (complexResolventMatrix (Node := Node) A z)⁻¹ *
        complexOfRealMatrix (Node := Node) A =
      z • (complexResolventMatrix (Node := Node) A z)⁻¹ -
        (1 : ComplexNodeMatrix Node) := by
  simpa only [Algebra.smul_def, mul_one,
    ← complexResolventMatrix_eq_algebraMap_sub] using
    Matrix.nonsing_inv_mul_eq_smul_inv_sub_one_of_scalar_sub
      (complexOfRealMatrix (Node := Node) A) z (by
        apply isUnit_iff_ne_zero.mpr
        simpa only [Algebra.smul_def, mul_one,
          ← complexResolventMatrix_eq_algebraMap_sub] using
          complexResolvent_det_ne_zero_of_not_eigen (Node := Node) A z hnot)

/-- Monomials have zero integral on a zero-centered nonnegative circle.

This is the scalar analytic cancellation used in the Cauchy-power recurrence:
the identity contribution integrates to zero after multiplication by `z ^ m`. -/
theorem zero_center_circleIntegral_zpow_eq_zero
    (theta : ℝ) (htheta_nonneg : 0 ≤ theta) (m : ℕ) :
    (∮ z in C((0 : ℂ), theta), z ^ m) = 0 := by
  classical
  refine
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
      htheta_nonneg (s := (∅ : Set ℂ)) Set.countable_empty ?_ ?_
  · intro z _hz
    exact (continuousAt_pow z m).continuousWithinAt
  · intro z _hz
    exact differentiableAt_pow (𝕜 := ℂ) m

/-- Resolvent entries multiplied by a monomial are circle-integrable on the
zero-centered contour whenever the contour has no spectrum. -/
theorem zero_center_zpow_resolvent_inv_entry_circleIntegrable_of_no_boundary
    [DecidableEq Node]
    (A : NodeMatrix Node) (theta : ℝ) (htheta_pos : 0 < theta)
    (hnoBoundary :
      ∀ z : ℂ, ‖z‖ = theta →
        ¬ IsComplexRightEigenvalue (Node := Node) A z)
    (m : ℕ) (i j : Node) :
    CircleIntegrable
      (fun z : ℂ =>
        z ^ m * ((complexResolventMatrix (Node := Node) A z)⁻¹) i j)
      (0 : ℂ) theta := by
  classical
  have hcont_sphere :
      ContinuousOn
        (fun z : ℂ =>
          z ^ m * ((complexResolventMatrix (Node := Node) A z)⁻¹) i j)
        (Metric.sphere (0 : ℂ) theta) := by
    have hzpow :
        ContinuousOn (fun z : ℂ => z ^ m) (Metric.sphere (0 : ℂ) theta) :=
      continuousOn_pow m
    have hresolvent :
        ContinuousOn
          (fun z : ℂ =>
            ((complexResolventMatrix (Node := Node) A z)⁻¹) i j)
          (Metric.sphere (0 : ℂ) theta) := by
      intro z hz
      have hz_norm : ‖z‖ = theta := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hz
      have hdet_z :
          Matrix.det (complexResolventMatrix (Node := Node) A z) ≠ 0 :=
        complexResolvent_det_ne_zero_of_not_eigen (Node := Node) A z
          (hnoBoundary z hz_norm)
      exact
        (complex_resolvent_inv_entry_differentiableAt_z_of_det_ne_zero
          (Node := Node) A hdet_z i j).continuousAt.continuousWithinAt
    exact hzpow.mul hresolvent
  exact hcont_sphere.circleIntegrable (le_of_lt htheta_pos)

/-- Zero-centered annulus deformation for concrete inverse-resolvent entries.

This is the contour-calculus bridge used to enlarge the stable Cauchy circle
without crossing spectrum. -/
theorem zero_center_resolvent_inv_entry_circleIntegral_eq_of_no_eigen_annulus
    [DecidableEq Node]
    (A : NodeMatrix Node) {innerRadius outerRadius : ℝ}
    (hinner_pos : 0 < innerRadius) (hradii : innerRadius ≤ outerRadius)
    (hnoAnnulus :
      ∀ z : ℂ, innerRadius ≤ ‖z‖ →
        ‖z‖ ≤ outerRadius →
          ¬ IsComplexRightEigenvalue (Node := Node) A z)
    (i j : Node) :
    (∮ z in C((0 : ℂ), outerRadius),
        ((complexResolventMatrix (Node := Node) A z)⁻¹) i j) =
      ∮ z in C((0 : ℂ), innerRadius),
        ((complexResolventMatrix (Node := Node) A z)⁻¹) i j := by
  classical
  refine
    Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
      (c := (0 : ℂ)) hinner_pos hradii (s := (∅ : Set ℂ))
      Set.countable_empty ?_ ?_
  · intro z hz
    rcases hz with ⟨hzclosed, hznotball⟩
    have hlower : innerRadius ≤ ‖z‖ := by
      have hnotlt : ¬ dist z (0 : ℂ) < innerRadius := by
        intro hlt
        exact hznotball (Metric.mem_ball.2 hlt)
      simpa [dist_eq_norm] using le_of_not_gt hnotlt
    have hupper : ‖z‖ ≤ outerRadius := by
      simpa [dist_eq_norm] using (Metric.mem_closedBall.mp hzclosed)
    have hdet :
        Matrix.det (complexResolventMatrix (Node := Node) A z) ≠ 0 :=
      complexResolvent_det_ne_zero_of_not_eigen (Node := Node) A z
        (hnoAnnulus z hlower hupper)
    exact
      (complex_resolvent_inv_entry_differentiableAt_z_of_det_ne_zero
        (Node := Node) A hdet i j).continuousAt.continuousWithinAt
  · intro z hz
    rcases hz with ⟨⟨hzball, hznotclosed⟩, _hznotempty⟩
    have hlower : innerRadius ≤ ‖z‖ := by
      have hnotle : ¬ dist z (0 : ℂ) ≤ innerRadius := by
        intro hle
        exact hznotclosed (Metric.mem_closedBall.2 hle)
      exact le_of_lt (by
        simpa [dist_eq_norm] using lt_of_not_ge hnotle)
    have hupper : ‖z‖ ≤ outerRadius := by
      exact le_of_lt (by
        simpa [dist_eq_norm] using (Metric.mem_ball.mp hzball))
    have hdet :
        Matrix.det (complexResolventMatrix (Node := Node) A z) ≠ 0 :=
      complexResolvent_det_ne_zero_of_not_eigen (Node := Node) A z
        (hnoAnnulus z hlower hupper)
    exact complex_resolvent_inv_entry_differentiableAt_z_of_det_ne_zero
      (Node := Node) A hdet i j

/-- Every complex right eigenvalue is bounded by the concrete complex
operator norm of the complexified matrix. -/
theorem complex_right_eigenvalue_norm_le_operatorNorm
    [DecidableEq Node]
    (A : NodeMatrix Node) {z : ℂ}
    (hz : IsComplexRightEigenvalue (Node := Node) A z) :
    ‖z‖ ≤
      complexMatrixOperatorNorm (Node := Node)
        (complexOfRealMatrix (Node := Node) A) := by
  classical
  rcases hz with ⟨v, hvne, hv⟩
  have hAv :
      complexNodeMatrixMulVector (Node := Node)
          (complexOfRealMatrix (Node := Node) A) v =
        z • v := by
    rw [complexNodeMatrixMulVector_complexOfRealMatrix]
    exact hv
  have hbound :=
    (complexMatrixOperatorNorm_spec (Node := Node)
      (complexOfRealMatrix (Node := Node) A)).2 v
  rw [hAv] at hbound
  have hvnorm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hvne
  have hmul :
      ‖z‖ * ‖v‖ ≤
        complexMatrixOperatorNorm (Node := Node)
            (complexOfRealMatrix (Node := Node) A) * ‖v‖ := by
    simpa [norm_smul] using hbound
  nlinarith [hmul, hvnorm_pos]

/-- A circle whose radius dominates the complex operator norm contains no
complex spectrum on its boundary. -/
theorem no_complex_eigen_on_circle_of_operator_norm_lt_radius
    [DecidableEq Node]
    (A : NodeMatrix Node) {R : ℝ}
    (hR :
      complexMatrixOperatorNorm (Node := Node)
          (complexOfRealMatrix (Node := Node) A) < R) :
    ∀ z : ℂ, ‖z‖ = R →
      ¬ IsComplexRightEigenvalue (Node := Node) A z := by
  intro z hz heig
  have hle :
      ‖z‖ ≤
        complexMatrixOperatorNorm (Node := Node)
          (complexOfRealMatrix (Node := Node) A) :=
    complex_right_eigenvalue_norm_le_operatorNorm (Node := Node) A heig
  have hlt : ‖z‖ < R := lt_of_le_of_lt hle hR
  exact (lt_irrefl R) (by simpa [hz] using hlt)

/-- Compact zero-circle bound for the canonical inverse resolvent.

This is the single-circle specialization of the Appendix A compact-contour
bound: the inverse-resolvent operator norm is continuous on `|z| = R`, hence
bounded there. -/
theorem exists_zero_circle_resolvent_operatorNorm_bound_of_no_boundary
    [DecidableEq Node]
    (A : NodeMatrix Node) {R : ℝ} (_hR_pos : 0 < R)
    (hnoBoundary :
      ∀ z : ℂ, ‖z‖ = R →
        ¬ IsComplexRightEigenvalue (Node := Node) A z) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ z : ℂ, ‖z‖ = R →
        complexMatrixOperatorNorm (Node := Node)
          ((complexResolventMatrix (Node := Node) A z)⁻¹) ≤ M := by
  classical
  let F : ℝ → NodeMatrix Node := fun _ => A
  let contourSet : Set (ℝ × ℂ) :=
    Set.Icc (-(1 : ℝ)) 1 ×ˢ Metric.sphere (0 : ℂ) R
  let resolventNormOnContour : ℝ × ℂ → ℝ := fun p =>
    complexMatrixOperatorNorm (Node := Node)
      ((complexResolventMatrix (Node := Node) (F p.1) p.2)⁻¹)
  have hcompact : IsCompact contourSet := by
    simpa [contourSet] using
      (isCompact_Icc.prod (isCompact_sphere (0 : ℂ) R))
  have hFcontinuousOn : ContinuousOn F (Set.Icc (-(1 : ℝ)) 1) := by
    exact continuousOn_const
  have hcircleNoEigen :
      ∀ alpha : ℝ, |alpha| ≤ 1 →
        ∀ z : ℂ, ‖z‖ = R →
          ¬ IsComplexRightEigenvalue (Node := Node) (F alpha) z := by
    intro _alpha _halpha z hz
    exact hnoBoundary z hz
  have hcont : ContinuousOn resolventNormOnContour contourSet := by
    simpa [resolventNormOnContour, contourSet, F] using
      complexResolventOperatorNorm_continuousOn_contour (Node := Node)
        F 1 R hFcontinuousOn hcircleNoEigen
  obtain ⟨M, hM_nonneg, hM_bound⟩ :=
    exists_nonneg_norm_bound_of_isCompact_of_continuousOn
      resolventNormOnContour hcompact hcont
  refine ⟨M, hM_nonneg, ?_⟩
  intro z hz
  have hp : ((0 : ℝ), z) ∈ contourSet := by
    constructor
    · norm_num
    · simpa [Metric.mem_sphere, dist_eq_norm] using hz
  have hbound := hM_bound ((0 : ℝ), z) hp
  have hle_abs :
      complexMatrixOperatorNorm (Node := Node)
          ((complexResolventMatrix (Node := Node) A z)⁻¹) ≤
        ‖complexMatrixOperatorNorm (Node := Node)
          ((complexResolventMatrix (Node := Node) A z)⁻¹)‖ :=
    le_abs_self _
  exact le_trans hle_abs (by
    simpa [resolventNormOnContour, F] using hbound)

/-- Finite right-Neumann expansion with an explicit remainder.

This is a purely algebraic helper: a one-step recurrence `R = a I + a R B`
iterates into the finite Laurent prefix and the right-multiplication tail. -/
theorem complexMatrix_finite_neumann_remainder_of_right_recurrence
    [DecidableEq Node]
    (R B : ComplexNodeMatrix Node) (a : ℂ)
    (hrec : R = a • (1 : ComplexNodeMatrix Node) + a • (R * B)) :
    ∀ N : ℕ,
      R =
        Finset.sum (Finset.range (N + 1))
          (fun n => a ^ (n + 1) • (B ^ n)) +
          a ^ (N + 1) • (R * B ^ (N + 1)) :=
  eq_sum_smul_pow_add_right_remainder_of_affine_recurrence R B a hrec

/-- Pointwise finite Neumann expansion for the canonical inverse resolvent.

On a spectral-parameter point where `z ≠ 0` and `zI - A` is nonsingular, the
right recurrence `(zI-A)^{-1} A = z (zI-A)^{-1} - I` gives a finite Laurent
prefix plus the right-multiplication remainder. -/
theorem complexResolvent_inverse_finite_neumann_remainder
    [DecidableEq Node]
    (A : NodeMatrix Node) {z : ℂ} (hz_ne : z ≠ 0)
    (hnot : ¬ IsComplexRightEigenvalue (Node := Node) A z) (N : ℕ) :
    (complexResolventMatrix (Node := Node) A z)⁻¹ =
      Finset.sum (Finset.range (N + 1))
        (fun n => (z⁻¹) ^ (n + 1) •
          ((complexOfRealMatrix (Node := Node) A) ^ n)) +
        (z⁻¹) ^ (N + 1) •
          ((complexResolventMatrix (Node := Node) A z)⁻¹ *
            (complexOfRealMatrix (Node := Node) A) ^ (N + 1)) := by
  simpa only [Algebra.smul_def, mul_one,
    ← complexResolventMatrix_eq_algebraMap_sub] using
    Matrix.scalar_sub_inv_eq_finite_neumann_add_remainder
      (complexOfRealMatrix (Node := Node) A) z hz_ne (by
        simpa only [Algebra.smul_def, mul_one,
          ← complexResolventMatrix_eq_algebraMap_sub] using
          complexResolvent_det_ne_zero_of_not_eigen (Node := Node) A z hnot) N

/-- Pointwise entrywise bound for the finite Neumann remainder on `|z| = R`. -/
theorem zero_center_neumann_remainder_entry_norm_bound
    [DecidableEq Node]
    (A : NodeMatrix Node) {R M : ℝ} (hR_pos : 0 < R) (hM_nonneg : 0 ≤ M)
    (hM_bound :
      ∀ z : ℂ, ‖z‖ = R →
        complexMatrixOperatorNorm (Node := Node)
          ((complexResolventMatrix (Node := Node) A z)⁻¹) ≤ M)
    (N : ℕ) (i k : Node) :
    ∀ z ∈ Metric.sphere (0 : ℂ) R,
      ‖(((z⁻¹) ^ (N + 1) •
          (((complexResolventMatrix (Node := Node) A z)⁻¹) *
            (complexOfRealMatrix (Node := Node) A) ^ (N + 1))) i k)‖ ≤
        M *
          (complexMatrixOperatorNorm (Node := Node)
              (complexOfRealMatrix (Node := Node) A) / R) ^ (N + 1) := by
  classical
  let Ac : ComplexNodeMatrix Node := complexOfRealMatrix (Node := Node) A
  have hopNorm (B : ComplexNodeMatrix Node) :
      ‖B‖ = complexMatrixOperatorNorm (Node := Node) B := by
    rw [Matrix.linfty_opNorm_eq_opNorm]
    rfl
  have hresolvent (z : ℂ) :
      z • (1 : ComplexNodeMatrix Node) - Ac =
        complexResolventMatrix (Node := Node) A z := by
    simpa only [Ac, Algebra.smul_def, mul_one] using
      (complexResolventMatrix_eq_algebraMap_sub (Node := Node) A z).symm
  have hM_bound' :
      ∀ z : ℂ, ‖z‖ = R →
        ‖(z • (1 : ComplexNodeMatrix Node) - Ac)⁻¹‖ ≤ M := by
    intro z hz
    rw [hresolvent z, hopNorm]
    exact hM_bound z hz
  intro z hz
  have h := Matrix.neumann_resolvent_remainder_entry_norm_le_on_sphere
    Ac R M hM_bound' N i k z hz
  rw [hresolvent z, hopNorm] at h
  exact h

/-- Normalized circle-integral bound for the finite Neumann remainder. -/
theorem zero_center_neumann_remainder_integral_bound
    [DecidableEq Node]
    (A : NodeMatrix Node) {R M : ℝ} (hR_pos : 0 < R) (hM_nonneg : 0 ≤ M)
    (hM_bound :
      ∀ z : ℂ, ‖z‖ = R →
        complexMatrixOperatorNorm (Node := Node)
          ((complexResolventMatrix (Node := Node) A z)⁻¹) ≤ M)
    (N : ℕ) (i k : Node) :
    ‖(((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ z in C((0 : ℂ), R),
          (((z⁻¹) ^ (N + 1) •
            (((complexResolventMatrix (Node := Node) A z)⁻¹) *
              (complexOfRealMatrix (Node := Node) A) ^ (N + 1))) i k))‖ ≤
      R *
        (M *
          (complexMatrixOperatorNorm (Node := Node)
              (complexOfRealMatrix (Node := Node) A) / R) ^ (N + 1)) := by
  classical
  simpa only [smul_eq_mul, Algebra.smul_def, mul_one,
      ← complexResolventMatrix_eq_algebraMap_sub,
      Matrix.linfty_opNorm_eq_opNorm, complexMatrixOperatorNorm,
      complexMatrixContinuousLinearMap] using
    Matrix.norm_normalized_circleIntegral_neumann_resolvent_remainder_le
      (complexOfRealMatrix (Node := Node) A) R M hR_pos.le (by
        intro z hz
        simpa only [Algebra.smul_def, mul_one,
            ← complexResolventMatrix_eq_algebraMap_sub,
            Matrix.linfty_opNorm_eq_opNorm, complexMatrixOperatorNorm,
            complexMatrixContinuousLinearMap] using
          hM_bound z hz) N i k

/-- Normalized Laurent monomials on a zero-centered circle: only the
`z⁻¹` coefficient contributes. -/
theorem zero_center_normalized_circleIntegral_inv_pow_succ_mul_const
    {R : ℝ} (hR_pos : 0 < R) (n : ℕ) (c : ℂ) :
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ z in C((0 : ℂ), R), (z⁻¹) ^ (n + 1) * c) =
      if n = 0 then c else 0 := by
  exact circleIntegral.normalized_zero_center_inv_pow_succ_mul_const hR_pos.ne' n c

/-- The finite Neumann Laurent prefix integrates to the identity entry on a
zero-centered circle. -/
theorem zero_center_neumann_prefix_integral_eq_one_entry
    [DecidableEq Node]
    (A : NodeMatrix Node) {R : ℝ} (hR_pos : 0 < R)
    (N : ℕ) (i k : Node) :
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ z in C((0 : ℂ), R),
          (Finset.sum (Finset.range (N + 1))
            (fun n => (z⁻¹) ^ (n + 1) •
              ((complexOfRealMatrix (Node := Node) A) ^ n))) i k) =
      (1 : ComplexNodeMatrix Node) i k := by
  classical
  simpa only [Pi.smul_apply, Matrix.sum_apply, smul_eq_mul, pow_zero,
    Matrix.one_apply] using
    (circleIntegral.normalized_sum_inv_pow_succ_smul_eq_zero_coeff
      (coeff := fun n =>
        (((complexOfRealMatrix (Node := Node) A) ^ n) i k))
      R N hR_pos.ne')

/-- The scalar entry of a finite zero-centered Neumann Laurent prefix is
circle-integrable. -/
theorem zero_center_neumann_prefix_entry_circleIntegrable
    [DecidableEq Node]
    (A : NodeMatrix Node) {R : ℝ} (hR_pos : 0 < R)
    (N : ℕ) (i k : Node) :
    CircleIntegrable
      (fun z : ℂ =>
        (Finset.sum (Finset.range (N + 1))
          (fun n => (z⁻¹) ^ (n + 1) •
            ((complexOfRealMatrix (Node := Node) A) ^ n))) i k)
      (0 : ℂ) R := by
  classical
  let Ac : ComplexNodeMatrix Node := complexOfRealMatrix (Node := Node) A
  have hterm_integrable :
      ∀ n ∈ Finset.range (N + 1),
        CircleIntegrable
          (fun z : ℂ => ((z⁻¹) ^ (n + 1) • (Ac ^ n)) i k)
          (0 : ℂ) R := by
    intro n _hn
    have hcont :
        ContinuousOn
          (fun z : ℂ => ((z⁻¹) ^ (n + 1) • (Ac ^ n)) i k)
          (Metric.sphere (0 : ℂ) R) := by
      intro z hz
      have hz_norm : ‖z‖ = R := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hz
      have hz_ne : z ≠ 0 := by
        intro hz0
        have hzero_eq_R : (0 : ℝ) = R := by
          simpa [hz0] using hz_norm
        linarith
      have hpow :
          ContinuousAt (fun z : ℂ => (z⁻¹) ^ (n + 1)) z :=
        (continuousAt_inv₀ hz_ne).pow (n + 1)
      simpa [Pi.smul_apply, smul_eq_mul] using
        (hpow.mul continuousAt_const).continuousWithinAt
    exact hcont.circleIntegrable hR_pos.le
  have hsum_integrable :
      CircleIntegrable
        (fun z : ℂ =>
          ∑ n ∈ Finset.range (N + 1),
            ((z⁻¹) ^ (n + 1) • (Ac ^ n)) i k)
        (0 : ℂ) R :=
    CircleIntegrable.fun_sum (Finset.range (N + 1)) hterm_integrable
  have hfun :
      (fun z : ℂ =>
        (Finset.sum (Finset.range (N + 1))
          (fun n => (z⁻¹) ^ (n + 1) •
            ((complexOfRealMatrix (Node := Node) A) ^ n))) i k) =
      (fun z : ℂ =>
        ∑ n ∈ Finset.range (N + 1),
          ((z⁻¹) ^ (n + 1) • (Ac ^ n)) i k) := by
    funext z
    let M : ℕ → ComplexNodeMatrix Node :=
      fun n => (z⁻¹) ^ (n + 1) • (Ac ^ n)
    have hrow :
        ((∑ n ∈ Finset.range (N + 1), M n) i) =
          ∑ n ∈ Finset.range (N + 1), (M n) i := by
      exact
        (Finset.sum_apply
          (a := i) (s := Finset.range (N + 1)) (g := fun n => M n))
    calc
      (∑ n ∈ Finset.range (N + 1),
          (z⁻¹) ^ (n + 1) •
            ((complexOfRealMatrix (Node := Node) A) ^ n)) i k =
          ((∑ n ∈ Finset.range (N + 1), M n) i) k := by
            rfl
      _ = (∑ n ∈ Finset.range (N + 1), (M n) i) k := by
            rw [hrow]
      _ = ∑ n ∈ Finset.range (N + 1), (M n) i k := by
            exact
              (Finset.sum_apply
                (a := k) (s := Finset.range (N + 1))
                (g := fun n => (M n) i))
      _ = ∑ n ∈ Finset.range (N + 1),
          ((z⁻¹) ^ (n + 1) • (Ac ^ n)) i k := by
            rfl
  rw [hfun]
  simpa [Pi.smul_apply, smul_eq_mul] using hsum_integrable

/-- A fixed complex number bounded by every tail of a decaying geometric
majorant must vanish. -/
theorem zero_center_norm_le_geometric_tail_for_all_N_forces_eq_zero
    {R M q : ℝ} {D : ℂ} (hR_pos : 0 < R) (hM_nonneg : 0 ≤ M)
    (hq_nonneg : 0 ≤ q) (hq_lt_one : q < 1)
    (hbound : ∀ N : ℕ, ‖D‖ ≤ R * (M * q ^ (N + 1))) :
    D = 0 := by
  have hq_norm_lt : ‖q‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hq_nonneg] using hq_lt_one
  exact eq_zero_of_norm_le_of_tendsto_zero atTop D
    (fun N : ℕ => R * (M * q ^ (N + 1)))
    (Filter.Eventually.of_forall hbound) (by
      have hbase := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq_norm_lt
      simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using
        (hbase.const_mul q).const_mul (R * M))

/-- A scalar spectral-radius extraction from uniform geometric domination of
all positive powers. -/
theorem scalar_pow_le_geometric_for_all_forces_base_le
    {a q theta M c : ℝ} (ha_nonneg : 0 ≤ a) (hq_nonneg : 0 ≤ q)
    (hc_pos : 0 < c) (hq_lt_theta : q < theta)
    (hbound : ∀ N : ℕ, a ^ (N + 1) * c ≤ M * q ^ (N + 1) * c) :
    a ≤ theta := by
  exact (le_of_pow_le_const_mul_pow_for_all hq_nonneg fun N =>
    le_of_mul_le_mul_right (hbound N) hc_pos).trans hq_lt_theta.le

/-- Large-radius zero-centered Cauchy primitive for the whole-spectrum
projection.

The norm dominance premise puts the entire spectrum inside the contour.  The
remaining analytic content is the finite-dimensional Neumann/Cauchy evaluation
of the concrete inverse-resolvent integral. -/
theorem zero_center_large_radius_resolvent_projection_eq_one_of_norm_lt_radius
    [DecidableEq Node]
    (A : NodeMatrix Node) {R : ℝ} (hR_pos : 0 < R)
    (hAc_norm_lt :
      complexMatrixOperatorNorm (Node := Node)
          (complexOfRealMatrix (Node := Node) A) < R)
    (i k : Node) :
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ z in C((0 : ℂ), R),
          ((complexResolventMatrix (Node := Node) A z)⁻¹) i k) =
      (1 : ComplexNodeMatrix Node) i k := by
  classical
  have hnoBoundary :
      ∀ z : ℂ, ‖z‖ = R →
        ¬ IsComplexRightEigenvalue (Node := Node) A z :=
    no_complex_eigen_on_circle_of_operator_norm_lt_radius
      (Node := Node) A hAc_norm_lt
  obtain ⟨M, hM_nonneg, hM_bound⟩ :=
    exists_zero_circle_resolvent_operatorNorm_bound_of_no_boundary
      (Node := Node) A hR_pos hnoBoundary
  have hfiniteExpansion :
      ∀ N : ℕ, ∀ z : ℂ, ‖z‖ = R →
        (complexResolventMatrix (Node := Node) A z)⁻¹ =
          Finset.sum (Finset.range (N + 1))
            (fun n => (z⁻¹) ^ (n + 1) •
              ((complexOfRealMatrix (Node := Node) A) ^ n)) +
            (z⁻¹) ^ (N + 1) •
              ((complexResolventMatrix (Node := Node) A z)⁻¹ *
                (complexOfRealMatrix (Node := Node) A) ^ (N + 1)) := by
    intro N z hz
    have hz_ne : z ≠ 0 := by
      intro hz0
      have hzero_eq_R : (0 : ℝ) = R := by
        simpa [hz0] using hz
      linarith
    exact
      complexResolvent_inverse_finite_neumann_remainder
        (Node := Node) A hz_ne (hnoBoundary z hz) N
  let q : ℝ :=
    complexMatrixOperatorNorm (Node := Node)
      (complexOfRealMatrix (Node := Node) A) / R
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg
      (complexMatrixOperatorNorm_spec (Node := Node)
        (complexOfRealMatrix (Node := Node) A)).1 hR_pos.le
  have hq_lt_one : q < 1 := by
    dsimp [q]
    rw [div_lt_one hR_pos]
    exact hAc_norm_lt
  have hremainderIntegralBound :
      ∀ N : ℕ,
        ‖(((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
            (∮ z in C((0 : ℂ), R),
              (((z⁻¹) ^ (N + 1) •
                (((complexResolventMatrix (Node := Node) A z)⁻¹) *
                  (complexOfRealMatrix (Node := Node) A) ^ (N + 1))) i k))‖ ≤
          R * (M * q ^ (N + 1)) := by
    intro N
    simpa [q] using
      zero_center_neumann_remainder_integral_bound
        (Node := Node) A hR_pos hM_nonneg hM_bound N i k
  let c : ℂ := ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹
  let lhs : ℂ :=
    c *
      (∮ z in C((0 : ℂ), R),
        ((complexResolventMatrix (Node := Node) A z)⁻¹) i k)
  let oneEntry : ℂ := (1 : ComplexNodeMatrix Node) i k
  have hdiffBound :
      ∀ N : ℕ, ‖lhs - oneEntry‖ ≤ R * (M * q ^ (N + 1)) := by
    intro N
    let Ac : ComplexNodeMatrix Node := complexOfRealMatrix (Node := Node) A
    let res : ℂ → ℂ := fun z : ℂ =>
      ((complexResolventMatrix (Node := Node) A z)⁻¹) i k
    let pref : ℂ → ℂ := fun z : ℂ =>
      (Finset.sum (Finset.range (N + 1))
        (fun n => (z⁻¹) ^ (n + 1) • (Ac ^ n))) i k
    let rem : ℂ → ℂ := fun z : ℂ =>
      (((z⁻¹) ^ (N + 1) •
        (((complexResolventMatrix (Node := Node) A z)⁻¹) *
          Ac ^ (N + 1))) i k)
    have hres_integrable :
        CircleIntegrable res (0 : ℂ) R := by
      have hcont : ContinuousOn res (Metric.sphere (0 : ℂ) R) := by
        intro z hz
        have hz_norm : ‖z‖ = R := by
          simpa [Metric.mem_sphere, dist_eq_norm] using hz
        have hdet_z :
            Matrix.det (complexResolventMatrix (Node := Node) A z) ≠ 0 :=
          complexResolvent_det_ne_zero_of_not_eigen (Node := Node) A z
            (hnoBoundary z hz_norm)
        exact
          (complex_resolvent_inv_entry_differentiableAt_z_of_det_ne_zero
            (Node := Node) A hdet_z i k).continuousAt.continuousWithinAt
      exact hcont.circleIntegrable hR_pos.le
    have hpref_integrable :
        CircleIntegrable pref (0 : ℂ) R := by
      simpa [pref, Ac] using
        zero_center_neumann_prefix_entry_circleIntegrable
          (Node := Node) A (R := R) hR_pos N i k
    have hrem_eq_sub :
        (∮ z in C((0 : ℂ), R), rem z) =
          ∮ z in C((0 : ℂ), R), res z - pref z := by
      refine circleIntegral.integral_congr hR_pos.le ?_
      intro z hzSphere
      have hz_norm : ‖z‖ = R := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hzSphere
      have hentry :=
        congrArg (fun B : ComplexNodeMatrix Node => B i k)
          (hfiniteExpansion N z hz_norm)
      have hentry' : res z = pref z + rem z := by
        simpa [res, pref, rem, Ac, Matrix.add_apply] using hentry
      change rem z = res z - pref z
      rw [hentry']
      ring
    have hsub_split :
        (∮ z in C((0 : ℂ), R), res z - pref z) =
          (∮ z in C((0 : ℂ), R), res z) -
            ∮ z in C((0 : ℂ), R), pref z :=
      circleIntegral.integral_sub hres_integrable hpref_integrable
    have hrem_sub :
        (∮ z in C((0 : ℂ), R), rem z) =
          (∮ z in C((0 : ℂ), R), res z) -
            ∮ z in C((0 : ℂ), R), pref z := by
      rw [hrem_eq_sub, hsub_split]
    have hpref_eval :
        c * (∮ z in C((0 : ℂ), R), pref z) = oneEntry := by
      simpa [c, pref, Ac, oneEntry] using
        zero_center_neumann_prefix_integral_eq_one_entry
          (Node := Node) A (R := R) hR_pos N i k
    have hdiff_eq :
        lhs - oneEntry = c * (∮ z in C((0 : ℂ), R), rem z) := by
      dsimp [lhs, c]
      rw [← hpref_eval, hrem_sub]
      ring
    calc
      ‖lhs - oneEntry‖ = ‖c * (∮ z in C((0 : ℂ), R), rem z)‖ := by
          rw [hdiff_eq]
      _ ≤ R * (M * q ^ (N + 1)) := by
          simpa [c, rem, Ac] using hremainderIntegralBound N
  have hdiff_zero :
      lhs - oneEntry = 0 :=
    zero_center_norm_le_geometric_tail_for_all_N_forces_eq_zero
      (R := R) (M := M) (q := q) (D := lhs - oneEntry)
      hR_pos hM_nonneg hq_nonneg hq_lt_one hdiffBound
  have hlhs_eq : lhs = oneEntry := sub_eq_zero.mp hdiff_zero
  simpa [lhs, oneEntry, c] using hlhs_eq

/-- Base case for the zero-centered Cauchy resolvent power formula: if the
entire complex spectrum lies inside `|z| < theta`, then the Riesz projection
on the contour `C(0, theta)` is the identity.

This is the `j = 0` whole-spectrum projection identity in the source proof of
Lemma A.1.  It is intentionally stated for the canonical concrete resolvent
integral, not for an arbitrary projection witness. -/
theorem zero_center_resolvent_projection_eq_one_of_spectrum_inside_disk
    [DecidableEq Node]
    (A : NodeMatrix Node) (theta : ℝ) (htheta_pos : 0 < theta)
    (hspectrum_inside :
      ∀ z : ℂ, IsComplexRightEigenvalue (Node := Node) A z → ‖z‖ < theta)
    (hnoBoundary :
      ∀ z : ℂ, ‖z‖ = theta →
        ¬ IsComplexRightEigenvalue (Node := Node) A z)
    (i k : Node) :
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ z in C((0 : ℂ), theta),
          ((complexResolventMatrix (Node := Node) A z)⁻¹) i k) =
      (1 : ComplexNodeMatrix Node) i k := by
  classical
  simpa only [Algebra.smul_def, mul_one,
      ← complexResolventMatrix_eq_algebraMap_sub] using
    (Matrix.normalized_circleIntegral_resolvent_apply_eq_one_of_spectrum_inside_disk
      (complexOfRealMatrix (Node := Node) A) theta htheta_pos
      (fun z hz => hspectrum_inside z
        ((isComplexRightEigenvalue_iff_mem_spectrum_complexOfRealMatrix
          (Node := Node) A z).2 hz)) i k)

/-- Successor step for the zero-centered Cauchy resolvent power integral.

The pointwise recurrence `(zI-A)⁻¹ A = z(zI-A)⁻¹ - I` turns the
`m+1` contour integral into the right multiplication of the `m` integral by
`A`; the scalar identity term vanishes by the monomial circle-integral
cancellation. -/
theorem zero_center_cauchy_resolvent_power_integral_succ
    [DecidableEq Node]
    (A : NodeMatrix Node) (theta : ℝ) (htheta_pos : 0 < theta)
    (hnoBoundary :
      ∀ z : ℂ, ‖z‖ = theta →
        ¬ IsComplexRightEigenvalue (Node := Node) A z)
    (hresolventRightMul :
      ∀ z : ℂ, ‖z‖ = theta →
        (complexResolventMatrix (Node := Node) A z)⁻¹ *
            complexOfRealMatrix (Node := Node) A =
          z • (complexResolventMatrix (Node := Node) A z)⁻¹ -
            (1 : ComplexNodeMatrix Node))
    (m : ℕ) (i k : Node) :
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ z in C((0 : ℂ), theta),
          z ^ (m + 1) *
            ((complexResolventMatrix (Node := Node) A z)⁻¹) i k) =
      ∑ l : Node,
        ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
          (∮ z in C((0 : ℂ), theta),
            z ^ m *
              ((complexResolventMatrix (Node := Node) A z)⁻¹) i l)) *
          complexOfRealMatrix (Node := Node) A l k := by
  apply Matrix.normalized_circleIntegral_pow_resolvent_succ_apply
    (A := complexOfRealMatrix (Node := Node) A)
    (R := fun z : ℂ => (complexResolventMatrix (Node := Node) A z)⁻¹)
    theta htheta_pos.le m i k
  · intro l
    exact zero_center_zpow_resolvent_inv_entry_circleIntegrable_of_no_boundary
      (Node := Node) A theta htheta_pos hnoBoundary m i l
  · exact hresolventRightMul

/-- Zero-centered Cauchy matrix-power formula for the stable complement.

This is the source-level analytic primitive from Lemma A.1, step 4:
when every complex eigenvalue of the finite real matrix lies strictly inside
`|z| < theta`, Cauchy's matrix functional calculus identifies the `j`th power
with the contour integral of `z^j (zI-A)^{-1}` on `|z| = theta`.

The surrounding proof has already discharged the contour no-spectrum and
norm-estimate parts; the remaining obligation is this finite-dimensional
custom-`matrixPower` Cauchy formula. -/
theorem complex_matrix_power_cauchy_entry_formula_of_spectrum_inside_disk
    [DecidableEq Node]
    (A : NodeMatrix Node) (theta : ℝ) (htheta_pos : 0 < theta)
    (hspectrum_inside :
      ∀ z : ℂ, IsComplexRightEigenvalue (Node := Node) A z → ‖z‖ < theta)
    (j : ℕ) (i k : Node) :
    ((matrixPower (Node := Node) A j i k : ℂ)) =
      (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ z in C((0 : ℂ), theta),
          z ^ j *
            ((complexResolventMatrix (Node := Node) A z)⁻¹) i k) := by
  classical
  simpa only [← complexOfRealMatrix_matrixPower (Node := Node) A j,
      complexOfRealMatrix, Algebra.smul_def, mul_one,
      ← complexResolventMatrix_eq_algebraMap_sub] using
    (Matrix.pow_apply_eq_normalized_circleIntegral_pow_resolvent
      (complexOfRealMatrix (Node := Node) A) theta htheta_pos
      (fun z hz => hspectrum_inside z
        ((isComplexRightEigenvalue_iff_mem_spectrum_complexOfRealMatrix
          (Node := Node) A z).2 hz)) j i k)

/-- Cauchy matrix-function power estimate from a uniform contour-resolvent
bound.

This is the final finite-dimensional analytic step in Appendix A: integrate
`z^j (zI-F(alpha))^{-1}` on `|z| = theta` and enlarge the constant to include
`j = 0`. -/
theorem stableRemainder_cauchy_power_bound_from_resolvent
    (F : ℝ → NodeMatrix Node) (alpha0 theta M : ℝ)
    (halpha0 : 0 < alpha0) (htheta_pos : 0 < theta) (htheta_lt_one : theta < 1)
    (hM_nonneg : 0 ≤ M)
    (hstableSpectrum :
      ∀ alpha : ℝ, |alpha| ≤ alpha0 →
        ∀ z : ℂ, IsComplexRightEigenvalue (Node := Node) (F alpha) z →
          ‖z‖ < theta)
    (hresolventBound :
      UniformComplexResolventBoundOnCircle (Node := Node) F alpha0 theta M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ alpha : ℝ, |alpha| ≤ alpha0 →
        ∀ j : ℕ,
          matrixEuclideanOperatorNorm (Node := Node)
              (matrixPower (Node := Node) (F alpha) j) ≤
            K * theta ^ j := by
  classical
  have hcanonicalResolventBound :
      ∀ alpha : ℝ, |alpha| ≤ alpha0 →
        ∀ z : ℂ, ‖z‖ = theta →
          complexMatrixOperatorNorm (Node := Node)
            ((complexResolventMatrix (Node := Node) (F alpha) z)⁻¹) ≤ M :=
    complex_resolvent_canonical_inverse_bound_of_uniform_on_circle (Node := Node)
      F alpha0 theta M hresolventBound
  let n : ℝ := nodeCount (Node := Node)
  let Fc : {alpha : ℝ // |alpha| ≤ alpha0} →
      Module.End ℂ (Node → ℂ) := fun alpha =>
    Matrix.toLinAlgEquiv' (complexOfRealMatrix (Node := Node) (F alpha))
  obtain ⟨Kc, hKc_nonneg, hKc⟩ :=
    Module.End.uniform_pow_norm_le_of_spectrum_inside_circle_of_resolvent_bound
      Fc theta M htheta_pos (by
        intro alpha z hz
        let A : Matrix Node Node ℂ :=
          complexOfRealMatrix (Node := Node) (F alpha)
        let e := Matrix.toContinuousLinearMapAlgEquiv (K := ℂ) (ι := Node)
        let Aop : Module.End ℂ (Node → ℂ) := Matrix.toLinAlgEquiv' A
        let Op : (Node → ℂ) →L[ℂ] (Node → ℂ) :=
          Module.End.toContinuousLinearMap (Node → ℂ) Aop
        have hz' : z ∈ spectrum ℂ A := by
          have : z ∈ spectrum ℂ Op := by simpa [Op, Aop, A, Fc] using hz
          simpa [Op, Aop, e, Matrix.toContinuousLinearMapAlgEquiv] using this
        exact hstableSpectrum alpha alpha.property z
          ((isComplexRightEigenvalue_iff_mem_spectrum_complexOfRealMatrix
            (Node := Node) (F alpha) z).2 (by simpa [A] using hz'))) (by
        intro alpha z hz
        let A : Matrix Node Node ℂ :=
          complexOfRealMatrix (Node := Node) (F alpha)
        let e := Matrix.toContinuousLinearMapAlgEquiv (K := ℂ) (ι := Node)
        let Aop : Module.End ℂ (Node → ℂ) := Matrix.toLinAlgEquiv' A
        let Op : (Node → ℂ) →L[ℂ] (Node → ℂ) :=
          Module.End.toContinuousLinearMap (Node → ℂ) Aop
        have hop_sub :
            algebraMap ℂ ((Node → ℂ) →L[ℂ] (Node → ℂ)) z - Op =
              e (algebraMap ℂ (Matrix Node Node ℂ) z - A) := by
          change algebraMap ℂ ((Node → ℂ) →L[ℂ] (Node → ℂ)) z - e A =
            e (algebraMap ℂ (Matrix Node Node ℂ) z - A)
          rw [← e.commutes z]
          exact (map_sub e (algebraMap ℂ (Matrix Node Node ℂ) z) A).symm
        have hres_eq :
            resolvent Op z = e ((algebraMap ℂ (Matrix Node Node ℂ) z - A)⁻¹) := by
          rw [resolvent, hop_sub]
          simpa [Matrix.nonsing_inv_eq_ringInverse] using
            (RingEquiv.map_ringInverse e.toRingEquiv
              (algebraMap ℂ (Matrix Node Node ℂ) z - A)).symm
        have hbound := hcanonicalResolventBound alpha alpha.property z hz
        change ‖resolvent Op z‖ ≤ M
        rw [hres_eq]
        simpa [A, e, Matrix.toContinuousLinearMapAlgEquiv,
          complexMatrixOperatorNorm, complexMatrixContinuousLinearMap,
          Algebra.algebraMap_eq_smul_one,
          complexResolventMatrix_eq_algebraMap_sub] using hbound)
  let K : ℝ := (n ^ 2 * Real.sqrt n) * Kc
  refine ⟨K, ?_, ?_⟩
  · dsimp [K, n]
    positivity
  · intro alpha halpha j
    let B : ℝ := Kc * theta ^ j
    have hB_nonneg : 0 ≤ B := by
      dsimp [B]
      positivity
    have hentry :
        ∀ i k : Node,
          |matrixPower (Node := Node) (F alpha) j i k| ≤ B := by
      intro i k
      have hcomplex :
          ‖((matrixPower (Node := Node) (F alpha) j i k : ℂ))‖ ≤ B := by
        calc
          ‖((matrixPower (Node := Node) (F alpha) j i k : ℂ))‖ ≤
              complexMatrixOperatorNorm (Node := Node)
                (complexOfRealMatrix (Node := Node)
                  (matrixPower (Node := Node) (F alpha) j)) := by
            simpa only [complexOfRealMatrix] using
              complexMatrix_entry_norm_le_operatorNorm (Node := Node)
                (complexOfRealMatrix (Node := Node)
                  (matrixPower (Node := Node) (F alpha) j)) i k
          _ ≤ B := by
            let A : Matrix Node Node ℂ :=
              complexOfRealMatrix (Node := Node) (F alpha)
            let e := Matrix.toContinuousLinearMapAlgEquiv (K := ℂ) (ι := Node)
            have hpow := hKc ⟨alpha, halpha⟩ j
            have hpow_map :
                (Module.End.toContinuousLinearMap (Node → ℂ)
                  (Fc ⟨alpha, halpha⟩)) ^ j = e (A ^ j) := by
              change (e A) ^ j = e (A ^ j)
              exact (map_pow e A j).symm
            have hpow' : ‖e (A ^ j)‖ ≤ Kc * theta ^ j := by
              rw [← hpow_map]
              exact hpow
            simpa only [B, A, e, Matrix.toContinuousLinearMapAlgEquiv,
              complexMatrixOperatorNorm, complexMatrixContinuousLinearMap,
              complexOfRealMatrix_matrixPower] using hpow'
      simpa [Complex.normSq, Real.norm_eq_abs] using hcomplex
    have hop :=
      matrixEuclideanOperatorNorm_le_of_entrywise_abs_bound (Node := Node)
        (matrixPower (Node := Node) (F alpha) j) B hB_nonneg hentry
    calc
      matrixEuclideanOperatorNorm (Node := Node)
          (matrixPower (Node := Node) (F alpha) j) ≤
          ((n ^ 2 * Real.sqrt n) * B) := by
            simpa [n] using hop
      _ = K * theta ^ j := by
            dsimp [K, B, n]
            ring

/-- Uniform Cauchy/resolvent power bound for the stable complement in
Appendix A.

From a compact parameter interval and a fixed resolvent circle containing the
stable spectrum, the matrix resolvent is uniformly bounded on the
parameter-contour product. Cauchy's matrix-function formula then gives a single
constant `K` controlling every power `j`, including `j = 0`. -/
theorem uniform_stable_remainder_power_bound
    (F : ℝ → NodeMatrix Node) (alpha0 alphaAnalytic theta : ℝ)
    (hFanalytic :
      ∀ alpha : ℝ, |alpha| < alphaAnalytic → AnalyticAt ℝ F alpha)
    (hmargin : alpha0 < alphaAnalytic)
    (halpha0 : 0 < alpha0) (htheta_pos : 0 < theta) (htheta_lt_one : theta < 1)
    (hresolvent :
      StableRemainderResolventDisk (Node := Node) F alpha0 theta) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ alpha : ℝ, |alpha| ≤ alpha0 →
        ∀ j : ℕ,
          matrixEuclideanOperatorNorm (Node := Node)
              (matrixPower (Node := Node) (F alpha) j) ≤
            K * theta ^ j := by
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
  let Fc : ℝ → (ComplexRowVector Node →L[ℂ] ComplexRowVector Node) :=
    fun alpha => complexMatrixContinuousLinearMap (Node := Node)
      (complexOfRealMatrix (Node := Node) (F alpha))
  have hFc_analytic : ∀ alpha : ℝ, |alpha| ≤ alpha0 →
      AnalyticAt ℝ Fc alpha := by
    intro alpha halpha
    letI : NormedSpace ℝ (ComplexNodeMatrix Node) :=
      NormedSpace.restrictScalars ℝ ℂ _
    letI : IsBoundedSMul ℝ (ComplexNodeMatrix Node) :=
      IsBoundedSMul.of_norm_smul_le NormedSpace.norm_smul_le
    letI : ContinuousSMul ℝ (ComplexNodeMatrix Node) :=
      IsBoundedSMul.continuousSMul
    have hdelta := fixed_contour_matrix_delta_analyticAt (Node := Node)
      F alpha (hFanalytic alpha (lt_of_le_of_lt halpha hmargin))
    have hcomplex : AnalyticAt ℝ
        (fun a => complexOfRealMatrix (Node := Node) (F a)) alpha := by
      have hadd := hdelta.add
        (analyticAt_const : AnalyticAt ℝ
          (fun _ : ℝ => complexOfRealMatrix (Node := Node) (F alpha)) alpha)
      have heq :
          (fun a => complexOfRealMatrix (Node := Node) (F a)) =
            (fun a => complexOfRealMatrix (Node := Node)
              (matrixSub (Node := Node) (F a) (F alpha))) +
              fun _ => complexOfRealMatrix (Node := Node) (F alpha) := by
        funext a
        ext i j
        simp [matrixSub, complexOfRealMatrix]
      rw [heq]
      exact hadd
    let op : ComplexNodeMatrix Node →L[ℝ]
        (ComplexRowVector Node →L[ℂ] ComplexRowVector Node) :=
      (complexMatrixOperatorAlgHom (Node := Node)).toContinuousLinearMap.restrictScalars ℝ
    have hmapped : AnalyticAt ℝ
        (op ∘ fun a => complexOfRealMatrix (Node := Node) (F a)) alpha :=
      (op.analyticAt
        (complexOfRealMatrix (Node := Node) (F alpha))).comp
          (f := fun a : ℝ => complexOfRealMatrix (Node := Node) (F a)) hcomplex
    simpa [Fc, op, complexMatrixOperatorAlgHom_apply,
      Function.comp_apply] using hmapped
  have hFc_continuousOn : ContinuousOn Fc (Set.Icc (-alpha0) alpha0) := by
    intro alpha halpha
    exact (hFc_analytic alpha (abs_le.mpr halpha)).continuousAt.continuousWithinAt
  obtain ⟨Kc, hKc_nonneg, hKc⟩ :=
    Module.End.exists_uniform_geometric_power_bound_of_continuousOn_of_spectrum_inside_disk
      Fc alpha0 theta hFc_continuousOn htheta_pos (by
        intro alpha halpha z hz
        let A : Matrix Node Node ℂ :=
          complexOfRealMatrix (Node := Node) (F alpha)
        let e := complexMatrixOperatorAlgEquiv (Node := Node)
        have hz' : z ∈ spectrum ℂ A := by
          rw [← AlgEquiv.spectrum_eq e A]
          simpa [e, A, Fc] using hz
        exact (hresolvent alpha halpha).1 z
          ((isComplexRightEigenvalue_iff_mem_spectrum_complexOfRealMatrix
            (Node := Node) (F alpha) z).2 (by simpa [A] using hz')))
  let n : ℝ := nodeCount (Node := Node)
  let K : ℝ := (n ^ 2 * Real.sqrt n) * Kc
  refine ⟨K, ?_, ?_⟩
  · dsimp [K, n]
    positivity
  · intro alpha halpha j
    let B : ℝ := Kc * theta ^ j
    have hB_nonneg : 0 ≤ B := by
      dsimp [B]
      positivity
    have hentry : ∀ i k : Node,
        |matrixPower (Node := Node) (F alpha) j i k| ≤ B := by
      intro i k
      have hcomplex :
          ‖((matrixPower (Node := Node) (F alpha) j i k : ℂ))‖ ≤ B := by
        calc
          ‖((matrixPower (Node := Node) (F alpha) j i k : ℂ))‖ ≤
              complexMatrixOperatorNorm (Node := Node)
                (complexOfRealMatrix (Node := Node)
                  (matrixPower (Node := Node) (F alpha) j)) := by
            simpa only [complexOfRealMatrix] using
              complexMatrix_entry_norm_le_operatorNorm (Node := Node)
                (complexOfRealMatrix (Node := Node)
                  (matrixPower (Node := Node) (F alpha) j)) i k
          _ ≤ B := by
            have hpow := hKc alpha halpha j
            have hpow_map :
                (Fc alpha) ^ j =
                  complexMatrixContinuousLinearMap (Node := Node)
                    ((complexOfRealMatrix (Node := Node) (F alpha)) ^ j) := by
              change
                (complexMatrixContinuousLinearMap (Node := Node)
                  (complexOfRealMatrix (Node := Node) (F alpha))) ^ j =
                complexMatrixContinuousLinearMap (Node := Node)
                  ((complexOfRealMatrix (Node := Node) (F alpha)) ^ j)
              exact (map_pow
                (complexMatrixOperatorAlgHom (Node := Node))
                (complexOfRealMatrix (Node := Node) (F alpha)) j).symm
            rw [hpow_map] at hpow
            simpa only [B, complexMatrixOperatorNorm,
              complexOfRealMatrix_matrixPower] using hpow
      simpa [Complex.normSq, Real.norm_eq_abs] using hcomplex
    have hop :=
      matrixEuclideanOperatorNorm_le_of_entrywise_abs_bound (Node := Node)
        (matrixPower (Node := Node) (F alpha) j) B hB_nonneg hentry
    calc
      matrixEuclideanOperatorNorm (Node := Node)
          (matrixPower (Node := Node) (F alpha) j) ≤
          ((n ^ 2 * Real.sqrt n) * B) := by
            simpa [n] using hop
      _ = K * theta ^ j := by
            dsimp [K, B, n]
            ring

theorem PeriodicSpectralDecomposition
    (A : ℝ → NodeMatrix Node) (alpha1 r0 : ℝ)
    (_hanalytic : RealAnalyticMatrixFamilyNear (Node := Node) A alpha1)
    (right left : RowVector Node)
    (_hspectrum :
      SimpleIsolatedUnitEigenvalueStableSpectrum (Node := Node) (A 0) r0 right left) :
    ∃ alpha0 theta K : ℝ, ∃ gamma : ℝ → ℝ,
      ∃ P F : ℝ → NodeMatrix Node,
        alpha0 ≤ alpha1 ∧
          PeriodicSpectralSplitting (Node := Node) A r0 alpha0 theta K
            right left gamma P F := by
  classical
  obtain ⟨alpha0, alphaAnalytic, theta, gamma, P, F, halpha0_le_analytic,
      halphaAnalytic_le, halpha0_pos, halpha0_lt_analytic,
      hr0_theta, htheta_lt_one, hgamma0, hgamma_analytic,
      hP_analytic, hF_analytic, hderiv, hlocal, hresolvent⟩ :=
    analytic_unit_riesz_projection_near_zero (Node := Node)
      A alpha1 r0 _hanalytic right left _hspectrum
  have htheta_pos : 0 < theta := lt_of_le_of_lt _hspectrum.1 hr0_theta
  obtain ⟨K, hK_nonneg, hpower⟩ :=
    uniform_stable_remainder_power_bound (Node := Node)
      F alpha0 alphaAnalytic theta hF_analytic halpha0_lt_analytic
      halpha0_pos htheta_pos htheta_lt_one hresolvent
  refine ⟨alpha0, theta, K, gamma, P, F,
    le_trans halpha0_le_analytic halphaAnalytic_le, ?_⟩
  unfold PeriodicSpectralSplitting
  refine ⟨halpha0_pos, hr0_theta, htheta_lt_one, hK_nonneg, hgamma0,
    ?_, ?_, hderiv, ?_⟩
  · intro alpha halpha
    exact hgamma_analytic alpha (lt_trans halpha halpha0_lt_analytic)
  · intro alpha halpha
    exact hP_analytic alpha (lt_trans halpha halpha0_lt_analytic)
  intro alpha halpha
  obtain ⟨hRiesz, hsplit, hPF, hFP⟩ := hlocal alpha halpha
  exact ⟨hRiesz, hsplit, hPF, hFP, hpower alpha halpha⟩

/-- Lemma A.1 with the base Riesz projection kept in the interface.

`PeriodicSpectralSplitting` deliberately records only the fields used by the
generic spectral-power API.  Appendix C.1 also needs the source-normalized base
projection `P(0)=right*left` in order to prove the alpha-zero stable-output
cancellation.  This is the same construction as `PeriodicSpectralDecomposition`,
but it preserves the base-projection identity produced by the fixed-contour
Riesz branch. -/
theorem PeriodicSpectralDecomposition_with_base_projection
    (A : ℝ → NodeMatrix Node) (alpha1 r0 : ℝ)
    (hanalytic : RealAnalyticMatrixFamilyNear (Node := Node) A alpha1)
    (right left : RowVector Node)
    (hspectrum :
      SimpleIsolatedUnitEigenvalueStableSpectrum (Node := Node) (A 0) r0 right left) :
    ∃ alpha0 theta K : ℝ, ∃ gamma : ℝ → ℝ,
      ∃ P F : ℝ → NodeMatrix Node,
        alpha0 ≤ alpha1 ∧
          P 0 = (fun i j : Node => right i * left j) ∧
          PeriodicSpectralSplitting (Node := Node) A r0 alpha0 theta K
            right left gamma P F := by
  have hresidual (x : RowVector Node) :
      ∃ z : RowVector Node,
        matrixMulVector (Node := Node) (A 0) z - z =
          x - rowDot (Node := Node) left x • right := by
    obtain ⟨bordered, hbordered⟩ :=
      bordered_unit_eigenpair_jacobian_equiv (Node := Node)
        (A 0) right left hspectrum.2.2.2.1.2 hspectrum.2.2.2.2.1
        hspectrum.unit_algebraicallySimple
    let y : RowVector Node :=
      x - rowDot (Node := Node) left x • right
    obtain ⟨w, hw⟩ := bordered.surjective ((0 : ℝ), y)
    have hw' :
        (rowDot (Node := Node) left w.2,
          matrixMulVector (Node := Node) (A 0) w.2 - w.2 - w.1 • right) =
            ((0 : ℝ), y) := by
      simpa [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using
        (Eq.trans (hbordered w).symm hw)
    have hw_left : rowDot (Node := Node) left w.2 = 0 :=
      congrArg Prod.fst hw'
    have hw_residual :
        matrixMulVector (Node := Node) (A 0) w.2 - w.2 - w.1 • right = y :=
      congrArg Prod.snd hw'
    have hleft_action (z : RowVector Node) :
        rowDot (Node := Node) left
            (matrixMulVector (Node := Node) (A 0) z) =
          rowDot (Node := Node) left z := by
      rw [rowDot_matrixMulVector_eq_rowMulMatrix_rowDot,
        hspectrum.2.2.2.1.2]
    have hnormalization : ∑ i : Node, left i * right i = 1 := by
      simpa [rowDot] using hspectrum.2.2.2.2.1
    have hrowDot_sub (u v : RowVector Node) :
        rowDot (Node := Node) left (u - v) =
          rowDot (Node := Node) left u - rowDot (Node := Node) left v := by
      unfold rowDot
      simp_rw [Pi.sub_apply, mul_sub]
      rw [Finset.sum_sub_distrib]
    have hrowDot_smul (c : ℝ) :
        rowDot (Node := Node) left (c • right) = c := by
      unfold rowDot
      simp only [Pi.smul_apply, smul_eq_mul]
      calc
        ∑ i : Node, left i * (c * right i) =
            c * ∑ i : Node, left i * right i := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = c := by rw [hnormalization]; ring
    have hy_left : rowDot (Node := Node) left y = 0 := by
      dsimp only [y]
      rw [hrowDot_sub, hrowDot_smul]
      ring
    have hw_one : w.1 = 0 := by
      have hp :
          rowDot (Node := Node) left
              (matrixMulVector (Node := Node) (A 0) w.2 - w.2 - w.1 • right) =
            -w.1 := by
        rw [hrowDot_sub, hrowDot_sub, hrowDot_smul, hleft_action, hw_left]
        ring
      have hp0 : -w.1 = 0 := by
        calc
          -w.1 = rowDot (Node := Node) left
              (matrixMulVector (Node := Node) (A 0) w.2 - w.2 -
                w.1 • right) := hp.symm
          _ = rowDot (Node := Node) left y := by rw [hw_residual]
          _ = 0 := hy_left
      linarith
    refine ⟨w.2, ?_⟩
    simpa [y, hw_one] using hw_residual
  simpa only [PeriodicSpectralSplitting] using
    (Module.End.exists_analyticRankOneSpectralSplitting_with_base_projection
      (Node := Node)
      (matrixAdd (Node := Node)) (matrixMul (Node := Node))
      (matrixPower (Node := Node)) (matrixEuclideanOperatorNorm (Node := Node))
      (IsRieszProjectionAtEigenvalue (Node := Node))
      A alpha1 r0 right left hspectrum.2.2.1.2
      (by
        intro M lambda P hP x
        simpa [matrixMulVector, Matrix.mulVec] using hP.fixed_iff x)
      (by
        intro M lambda P hP
        simpa [matrixMul, Matrix.mul_apply] using hP.matrix_mul_right)
      hresidual (by
        simpa only [PeriodicSpectralSplitting] using
          PeriodicSpectralDecomposition (Node := Node)
            A alpha1 r0 hanalytic right left hspectrum))

/-- The Appendix A.1 tracker-tail denominator is positive for the
counterexample range `0 < epsilon < 1`. -/
theorem two_step_counterexample_tail_denominator_pos
    (epsilon : ℝ) (hepsilon_pos : 0 < epsilon) (hepsilon_lt : epsilon < 1) :
    0 < twoStepCounterexampleTailDenominator epsilon := by
  unfold twoStepCounterexampleTailDenominator
  have hepsilon_sq_lt : epsilon ^ 2 < epsilon := by
    calc
      epsilon ^ 2 = epsilon * epsilon := by ring
      _ < epsilon * 1 := mul_lt_mul_of_pos_left hepsilon_lt hepsilon_pos
      _ = epsilon := by ring
  nlinarith

/-- Nonzero form of `two_step_counterexample_tail_denominator_pos`. -/
theorem two_step_counterexample_tail_denominator_ne_zero
    (epsilon : ℝ) (hepsilon_pos : 0 < epsilon) (hepsilon_lt : epsilon < 1) :
    twoStepCounterexampleTailDenominator epsilon ≠ 0 :=
  ne_of_gt
    (two_step_counterexample_tail_denominator_pos
      epsilon hepsilon_pos hepsilon_lt)

/-- Closed form of the Appendix A.1 slow coefficient after substituting the
two phase tail coefficients. -/
theorem two_step_counterexample_spectral_slope_formula
    (epsilon : ℝ) (hD : twoStepCounterexampleTailDenominator epsilon ≠ 0) :
    twoStepCounterexampleSpectralSlope epsilon =
      epsilon * (2 * epsilon - 3) ^ 2 /
        (2 * twoStepCounterexampleTailDenominator epsilon) := by
  set_option maxHeartbeats 200000 in
  unfold twoStepCounterexampleSpectralSlope rowSum
    twoStepCounterexampleNoiseChannelA twoStepCounterexampleNoiseChannelB
    twoStepCounterexampleTailA twoStepCounterexampleTailB
  simp
  field_simp [hD]
  unfold twoStepCounterexampleTailDenominator
  ring

/-- Positivity of the Appendix A.1 slow coefficient `s_epsilon`. -/
theorem two_step_counterexample_spectral_slope_pos
    (epsilon : ℝ) (hepsilon_pos : 0 < epsilon) (hepsilon_lt : epsilon < 1) :
    0 < twoStepCounterexampleSpectralSlope epsilon := by
  have hDpos :=
    two_step_counterexample_tail_denominator_pos
      epsilon hepsilon_pos hepsilon_lt
  have hDne :=
    two_step_counterexample_tail_denominator_ne_zero
      epsilon hepsilon_pos hepsilon_lt
  rw [two_step_counterexample_spectral_slope_formula epsilon hDne]
  have hsquare_pos : 0 < (2 * epsilon - 3) ^ 2 := by
    apply sq_pos_of_ne_zero
    nlinarith
  exact div_pos
    (mul_pos hepsilon_pos hsquare_pos)
    (mul_pos (by norm_num : (0 : ℝ) < 2) hDpos)

/-- A small scalar calculus helper for coordinate polynomial entries. -/
theorem hasDerivAt_quadratic_at_zero (a b c : ℝ) :
    HasDerivAt (fun x : ℝ => a * x ^ 2 + b * x + c) b 0 := by
  have hx : HasDerivAt (fun x : ℝ => x) 1 0 := hasDerivAt_id 0
  have hx2 : HasDerivAt (fun x : ℝ => x ^ 2) 0 0 := by
    simpa [pow_two] using hx.mul hx
  have h :=
    (hx2.const_mul a).add
      ((hx.const_mul b).add (hasDerivAt_const (0 : ℝ) c))
  convert h using 1
  · funext x
    simp
    ring
  · ring

/-- Explicit derivative at zero of the Appendix A.1 two-step propagator in
the reduced `(x_1,x_2,h)` coordinates. -/
theorem two_step_counterexample_propagator_hasDerivAt_zero_explicit
    (epsilon lambda : ℝ) :
    HasDerivAt
      (fun alpha : ℝ => twoStepCounterexamplePropagator epsilon lambda alpha)
      (fun i j : Fin 3 =>
        if i = 0 then
          if j = 0 then lambda * (2 * epsilon - 3) / 2
          else if j = 1 then -2 * lambda * epsilon
          else (4 * epsilon - 3) / 2
        else if i = 1 then
          if j = 0 then lambda * (2 * epsilon - 3) / 2
          else if j = 1 then -lambda
          else 1 / 2
        else
          if j = 0 then lambda ^ 2 / 4
          else if j = 1 then -lambda ^ 2 * epsilon
          else lambda * (4 * epsilon + 1) / 4)
      0 := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  fin_cases i
  · fin_cases j
    · simp [twoStepCounterexamplePropagator,
        twoStepCounterexampleLiftedStep, twoNodeCounterexamplePush,
        twoNodeCounterexamplePullA, twoNodeCounterexamplePullB, matrixMul,
        Fin.sum_univ_succ, Fin.sum_univ_two]
      convert hasDerivAt_quadratic_at_zero
        (lambda ^ 2) (lambda * (2 * epsilon - 3) / 2)
        ((1 - epsilon / 2) * (1 - epsilon / 2) +
          epsilon / 2 * ((1 - epsilon) / 2)) using 1 <;> (try funext x) <;> ring
    · simp [twoStepCounterexamplePropagator,
        twoStepCounterexampleLiftedStep, twoNodeCounterexamplePush,
        twoNodeCounterexamplePullA, twoNodeCounterexamplePullB, matrixMul,
        Fin.sum_univ_succ, Fin.sum_univ_two]
      convert hasDerivAt_quadratic_at_zero
        0 (-2 * lambda * epsilon)
        ((1 - epsilon / 2) * (epsilon / 2) +
          epsilon / 2 * ((1 + epsilon) / 2)) using 1 <;> (try funext x) <;> ring
    · simp [twoStepCounterexamplePropagator,
        twoStepCounterexampleLiftedStep, twoNodeCounterexamplePush,
        twoNodeCounterexamplePullA, twoNodeCounterexamplePullB, matrixMul,
        Fin.sum_univ_succ, Fin.sum_univ_two]
      convert hasDerivAt_quadratic_at_zero
        lambda ((4 * epsilon - 3) / 2) 0 using 1 <;> (try funext x) <;> ring
  · fin_cases j
    · simp [twoStepCounterexamplePropagator,
        twoStepCounterexampleLiftedStep, twoNodeCounterexamplePush,
        twoNodeCounterexamplePullA, twoNodeCounterexamplePullB, matrixMul,
        Fin.sum_univ_succ, Fin.sum_univ_two]
      convert hasDerivAt_quadratic_at_zero
        0 (lambda * (2 * epsilon - 3) / 2)
        (((1 - epsilon) / 2) * (1 - epsilon / 2) +
          ((1 + epsilon) / 2) * ((1 - epsilon) / 2)) using 1 <;> (try funext x) <;> ring
    · simp [twoStepCounterexamplePropagator,
        twoStepCounterexampleLiftedStep, twoNodeCounterexamplePush,
        twoNodeCounterexamplePullA, twoNodeCounterexamplePullB, matrixMul,
        Fin.sum_univ_succ, Fin.sum_univ_two]
      convert hasDerivAt_quadratic_at_zero
        (lambda ^ 2) (-lambda)
        (((1 + epsilon) / 2) * ((1 + epsilon) / 2)) using 1 <;> (try funext x) <;> ring
    · simp [twoStepCounterexamplePropagator,
        twoStepCounterexampleLiftedStep, twoNodeCounterexamplePush,
        twoNodeCounterexamplePullA, twoNodeCounterexamplePullB, matrixMul,
        Fin.sum_univ_succ, Fin.sum_univ_two]
      convert hasDerivAt_quadratic_at_zero (-lambda) (1 / 2) 0 using 1 <;> (try funext x) <;> ring
  · fin_cases j
    · simp [twoStepCounterexamplePropagator,
        twoStepCounterexampleLiftedStep, twoNodeCounterexamplePush,
        twoNodeCounterexamplePullA, twoNodeCounterexamplePullB, matrixMul,
        Fin.sum_univ_succ, Fin.sum_univ_two]
      convert hasDerivAt_quadratic_at_zero
        0 (lambda ^ 2 / 4)
        (lambda * (3 / 4 - 1) * (1 - epsilon / 2)) using 1 <;> (try funext x) <;> ring
    · simp [twoStepCounterexamplePropagator,
        twoStepCounterexampleLiftedStep, twoNodeCounterexamplePush,
        twoNodeCounterexamplePullA, twoNodeCounterexamplePullB, matrixMul,
        Fin.sum_univ_succ, Fin.sum_univ_two]
      convert hasDerivAt_quadratic_at_zero
        0 (-lambda ^ 2 * epsilon)
        (lambda * epsilon * ((1 + epsilon) / 2)) using 1 <;> (try funext x) <;> ring
    · simp [twoStepCounterexamplePropagator,
        twoStepCounterexampleLiftedStep, twoNodeCounterexamplePush,
        twoNodeCounterexamplePullA, twoNodeCounterexamplePullB, matrixMul,
        Fin.sum_univ_succ, Fin.sum_univ_two]
      convert hasDerivAt_quadratic_at_zero
        0 (lambda * (4 * epsilon + 1) / 4)
        ((3 / 4 - epsilon) * (1 / 2 - epsilon)) using 1 <;> (try funext x) <;> ring

/-- Appendix A.1 finite-coordinate calculation:
`left^T A'(0) right = -2 L s_epsilon` for the printed eigenvectors. -/
theorem two_step_counterexample_deriv_pairing
    (epsilon lambda : ℝ) (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt : epsilon < 1) :
    let right0 : RowVector (Fin 3) :=
      fun i =>
        if i = 0 then 1
        else if i = 1 then 1
        else
          lambda * (8 * epsilon ^ 2 - 18 * epsilon + 5) /
            (8 * epsilon ^ 2 - 10 * epsilon - 5)
    let left0 : RowVector (Fin 3) :=
      fun i =>
        if i = 0 then 1 - epsilon
        else if i = 1 then epsilon
        else 0
    ∀ Aderiv : NodeMatrix (Fin 3),
      HasDerivAt
        (fun alpha : ℝ => twoStepCounterexamplePropagator epsilon lambda alpha)
        Aderiv 0 →
      rowDot (Node := Fin 3) left0
        (matrixMulVector (Node := Fin 3) Aderiv right0) =
        -2 * lambda * twoStepCounterexampleSpectralSlope epsilon := by
  classical
  have hDne :
      twoStepCounterexampleTailDenominator epsilon ≠ 0 :=
    two_step_counterexample_tail_denominator_ne_zero
      epsilon hepsilon_pos hepsilon_lt
  have hDform_ne :
      5 / 8 + 5 / 4 * epsilon - epsilon ^ 2 ≠ 0 := by
    simpa [twoStepCounterexampleTailDenominator] using hDne
  have hden_ne :
      8 * epsilon ^ 2 - 10 * epsilon - 5 ≠ 0 := by
    intro hden
    apply hDne
    unfold twoStepCounterexampleTailDenominator
    nlinarith
  have hden_ne' :
      -5 - epsilon * 10 + epsilon ^ 2 * 8 ≠ 0 := by
    intro hden
    apply hden_ne
    nlinarith
  have hden20_ne :
      20 + epsilon * 40 - epsilon ^ 2 * 32 ≠ 0 := by
    intro hden
    apply hDform_ne
    nlinarith
  have hden_alt_ne :
      epsilon * (epsilon * 8 - 10) - 5 ≠ 0 := by
    intro hden
    apply hden_ne
    nlinarith
  have hden20_alt_ne :
      5 * (4 + epsilon * 8) - epsilon ^ 2 * 4 * 8 ≠ 0 := by
    intro hden
    apply hden20_ne
    nlinarith
  let Aexplicit : NodeMatrix (Fin 3) :=
    fun i j =>
      if i = 0 then
        if j = 0 then lambda * (2 * epsilon - 3) / 2
        else if j = 1 then -2 * lambda * epsilon
        else (4 * epsilon - 3) / 2
      else if i = 1 then
        if j = 0 then lambda * (2 * epsilon - 3) / 2
        else if j = 1 then -lambda
        else 1 / 2
      else
        if j = 0 then lambda ^ 2 / 4
        else if j = 1 then -lambda ^ 2 * epsilon
        else lambda * (4 * epsilon + 1) / 4
  have hAexplicit :
      HasDerivAt
        (fun alpha : ℝ => twoStepCounterexamplePropagator epsilon lambda alpha)
        Aexplicit 0 := by
    simpa [Aexplicit] using
      two_step_counterexample_propagator_hasDerivAt_zero_explicit
        epsilon lambda
  dsimp
  intro Aderiv hAderiv
  have hAeq : Aderiv = Aexplicit := hAderiv.unique hAexplicit
  subst Aderiv
  rw [two_step_counterexample_spectral_slope_formula epsilon hDne]
  unfold rowDot matrixMulVector
  simp [Aexplicit, Fin.sum_univ_succ, Fin.sum_univ_two]
  unfold twoStepCounterexampleTailDenominator
  field_simp [hDform_ne, hden_ne, hden_ne']
  field_simp [hden_alt_ne, hden20_alt_ne]
  ring

/-- Squared Euclidean norm of a Bool-indexed row is nonnegative. -/
theorem rowNormSq_bool_nonneg (w : RowVector Bool) :
    0 ≤ rowNormSq (Node := Bool) w := by
  unfold rowNormSq
  simp
  nlinarith [sq_nonneg (w false), sq_nonneg (w true)]

/-- A Bool-indexed row with nonzero sum has positive squared Euclidean norm. -/
theorem rowNormSq_bool_pos_of_rowSum_ne_zero
    (w : RowVector Bool) (hsum : rowSum (Node := Bool) w ≠ 0) :
    0 < rowNormSq (Node := Bool) w := by
  have hnonneg : 0 ≤ rowNormSq (Node := Bool) w :=
    rowNormSq_bool_nonneg w
  have hne : rowNormSq (Node := Bool) w ≠ 0 := by
    intro hzero
    have hsum_zero : rowSum (Node := Bool) w = 0 := by
      unfold rowNormSq at hzero
      unfold rowSum
      simp at hzero ⊢
      have htrue_sq : w true ^ 2 = 0 := by
        nlinarith [sq_nonneg (w false), sq_nonneg (w true)]
      have hfalse_sq : w false ^ 2 = 0 := by
        nlinarith [sq_nonneg (w false), sq_nonneg (w true)]
      have htrue : w true = 0 := sq_eq_zero_iff.mp htrue_sq
      have hfalse : w false = 0 := sq_eq_zero_iff.mp hfalse_sq
      nlinarith
    exact hsum hsum_zero
  exact lt_of_le_of_ne' hnonneg hne

/-- Closed form for the phase-B row sum used to witness nonzero noise energy. -/
theorem two_step_counterexample_noise_channelB_rowSum_formula
    (epsilon : ℝ) (hD : twoStepCounterexampleTailDenominator epsilon ≠ 0) :
    rowSum (Node := Bool) (twoStepCounterexampleNoiseChannelB epsilon) =
      (8 * epsilon ^ 3 - 22 * epsilon ^ 2 + 15 * epsilon + 1) /
        (4 * twoStepCounterexampleTailDenominator epsilon) := by
  set_option maxHeartbeats 200000 in
  unfold rowSum twoStepCounterexampleNoiseChannelB
    twoStepCounterexampleTailB
  simp
  field_simp [hD]
  unfold twoStepCounterexampleTailDenominator
  ring

/-- Positivity of the numerator in the phase-B row-sum formula on
`0 < epsilon < 1`, written in Bernstein form on `[0,1]`. -/
theorem two_step_counterexample_noise_channelB_rowSum_numerator_pos
    (epsilon : ℝ) (hepsilon_pos : 0 < epsilon) (hepsilon_lt : epsilon < 1) :
    0 < 8 * epsilon ^ 3 - 22 * epsilon ^ 2 + 15 * epsilon + 1 := by
  have h0 : 0 ≤ epsilon := le_of_lt hepsilon_pos
  have h1 : 0 ≤ 1 - epsilon := by linarith
  have hbern :
      8 * epsilon ^ 3 - 22 * epsilon ^ 2 + 15 * epsilon + 1 =
        (1 - epsilon) ^ 3 +
          18 * epsilon * (1 - epsilon) ^ 2 +
          11 * epsilon ^ 2 * (1 - epsilon) +
          2 * epsilon ^ 3 := by
    ring
  rw [hbern]
  positivity

/-- Positivity of the Appendix A.1 phase-noise coefficient `q_epsilon`. -/
theorem two_step_counterexample_noise_coefficient_pos
    (epsilon : ℝ) (hepsilon_pos : 0 < epsilon) (hepsilon_lt : epsilon < 1) :
    0 < twoStepCounterexampleNoiseCoefficient epsilon := by
  have hDpos :=
    two_step_counterexample_tail_denominator_pos
      epsilon hepsilon_pos hepsilon_lt
  have hDne :=
    two_step_counterexample_tail_denominator_ne_zero
      epsilon hepsilon_pos hepsilon_lt
  have hnum_pos :=
    two_step_counterexample_noise_channelB_rowSum_numerator_pos
      epsilon hepsilon_pos hepsilon_lt
  have hrow_pos :
      0 < rowSum (Node := Bool) (twoStepCounterexampleNoiseChannelB epsilon) := by
    rw [two_step_counterexample_noise_channelB_rowSum_formula epsilon hDne]
    exact div_pos hnum_pos
      (mul_pos (by norm_num : (0 : ℝ) < 4) hDpos)
  have hBnorm_pos :
      0 < rowNormSq (Node := Bool)
        (twoStepCounterexampleNoiseChannelB epsilon) :=
    rowNormSq_bool_pos_of_rowSum_ne_zero
      (twoStepCounterexampleNoiseChannelB epsilon) (ne_of_gt hrow_pos)
  have hAnorm_nonneg :
      0 ≤ rowNormSq (Node := Bool)
        (twoStepCounterexampleNoiseChannelA epsilon) :=
    rowNormSq_bool_nonneg (twoStepCounterexampleNoiseChannelA epsilon)
  unfold twoStepCounterexampleNoiseCoefficient
  positivity

/-- Enlarge the geometric constants in a periodic spectral splitting.

This is the scalar bookkeeping behind the Appendix A.1 phrase "enlarge
`theta` slightly": the analytic and algebraic splitting data are unchanged,
while the stable power estimate is weakened by monotonicity of nonnegative
powers and by increasing the prefactor. -/
theorem periodicSpectralSplitting_weaken_geometric_constants
    (A : ℝ → NodeMatrix Node) (r0 alpha0 theta K theta' K' : ℝ)
    (right left : RowVector Node)
    (gamma : ℝ → ℝ) (P F : ℝ → NodeMatrix Node)
    (hs :
      PeriodicSpectralSplitting (Node := Node) A r0 alpha0 theta K
        right left gamma P F)
    (htheta_nonneg : 0 ≤ theta)
    (htheta_le : theta ≤ theta')
    (htheta'_lt_one : theta' < 1)
    (hK_le : K ≤ K')
    (hK'_nonneg : 0 ≤ K') :
    PeriodicSpectralSplitting (Node := Node) A r0 alpha0 theta' K'
      right left gamma P F := by
  simpa only [PeriodicSpectralSplitting] using
    (analyticRankOneSpectralSplitting_weaken_geometric_constants
      (matrixAdd (Node := Node)) (matrixMul (Node := Node))
      (matrixPower (Node := Node)) (matrixEuclideanOperatorNorm (Node := Node))
      (matrixMulVector (Node := Node)) (rowDot (Node := Node))
      (IsRieszProjectionAtEigenvalue (Node := Node)) A 1 r0 alpha0 1
      theta K theta' K' right left gamma P F hs htheta_nonneg htheta_le
      htheta'_lt_one hK_le)

/-- At `alpha = 0`, every phase innovation enters only the tracker coordinate
in the reduced two-step coordinates. This is the exact finite-coordinate part
of the Appendix A.1 stable-output cancellation. -/
theorem two_step_counterexample_phase_input_channel_zero_primal
    (epsilon lambda : ℝ) (phase : TwoStepPhase) (node : Bool) :
    twoStepCounterexamplePhaseInputChannel epsilon lambda 0 phase node (0 : Fin 3) = 0 ∧
      twoStepCounterexamplePhaseInputChannel epsilon lambda 0 phase node (1 : Fin 3) = 0 := by
  cases phase <;> cases node <;>
    simp [twoStepCounterexamplePhaseInputChannel,
      twoStepCounterexampleOneStepNoiseInput,
      twoStepCounterexampleLiftedStep, twoNodeCounterexamplePush,
      twoNodeCounterexamplePullA, twoNodeCounterexamplePullB,
      matrixMulVector, Fin.sum_univ_succ, Fin.sum_univ_two]

/-- Zero-lag version of the Appendix A.1 base stable-output cancellation.
At `alpha = 0`, the phase input has no primal coordinates, so the arithmetic
average output is exactly zero before any stable propagation. -/
theorem two_step_counterexample_stable_impulse_zero_alpha_zero_lag
    (F : ℝ → NodeMatrix (Fin 3)) (epsilon lambda : ℝ)
    (phase : TwoStepPhase) :
    twoStepCounterexampleStableImpulseFrom F epsilon lambda 0 phase 0 = 0 := by
  have hvec :
      twoStepCounterexampleStableImpulseVectorFrom F epsilon lambda 0 phase 0 =
        (fun _ : Bool => 0) := by
    funext node
    obtain ⟨h0, h1⟩ :=
      two_step_counterexample_phase_input_channel_zero_primal
        epsilon lambda phase node
    simp [twoStepCounterexampleStableImpulseVectorFrom,
      twoStepCounterexampleStableImpulseFrom,
      twoStepCounterexampleArithmeticAverageOutput, matrixPower,
      identityMatrix, matrixMulVector, h0, h1]
  simp [twoStepCounterexampleStableImpulseFrom, hvec, rowEuclideanNorm,
    rowNormSq]

/-- At the base point, the concrete two-step propagator maps tracker-only
vectors back into the tracker-only subspace. -/
theorem two_step_counterexample_base_tracker_subspace_invariant
    (epsilon lambda : ℝ) (x : RowVector (Fin 3))
    (hx0 : x (0 : Fin 3) = 0) (hx1 : x (1 : Fin 3) = 0) :
    matrixMulVector (Node := Fin 3)
        (twoStepCounterexamplePropagator epsilon lambda 0) x (0 : Fin 3) = 0 ∧
      matrixMulVector (Node := Fin 3)
        (twoStepCounterexamplePropagator epsilon lambda 0) x (1 : Fin 3) = 0 := by
  constructor <;>
    simp [twoStepCounterexamplePropagator, twoStepCounterexampleLiftedStep,
      twoNodeCounterexamplePush, twoNodeCounterexamplePullA,
      twoNodeCounterexamplePullB, matrixMul, matrixMulVector,
      Fin.sum_univ_succ, Fin.sum_univ_two, hx0, hx1]

/-- The base Riesz projection annihilates the tracker-only coordinate.  This is
the finite-coordinate content behind the Appendix A.1 statement that at
`alpha = 0` tracker innovations do not contribute to the arithmetic average. -/
theorem two_step_counterexample_riesz_projection_zero_on_tracker_subspace
    (epsilon lambda : ℝ) (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt : epsilon < 1) (P0 : NodeMatrix (Fin 3))
    (hRiesz :
      IsRieszProjectionAtEigenvalue (Node := Fin 3)
        (twoStepCounterexamplePropagator epsilon lambda 0) 1 P0) :
    ∀ x : RowVector (Fin 3),
      x (0 : Fin 3) = 0 → x (1 : Fin 3) = 0 →
        matrixMulVector (Node := Fin 3) P0 x = 0 := by
  classical
  let d : ℝ := (1 / 2 - epsilon) * (3 / 4 - epsilon)
  have hd_ne_one : d ≠ 1 := by
    have heps_sq_lt : epsilon ^ 2 < epsilon := by
      have hmul := mul_lt_mul_of_pos_left hepsilon_lt hepsilon_pos
      simpa [pow_two] using hmul
    have hd_lt_one : d < 1 := by
      dsimp [d]
      nlinarith
    exact ne_of_lt hd_lt_one
  have hPA :
      matrixMul (Node := Fin 3) P0
          (twoStepCounterexamplePropagator epsilon lambda 0) = P0 := by
    simpa using
      IsRieszProjectionAtEigenvalue.matrix_mul_right (Node := Fin 3) hRiesz
  have hcol2 : ∀ i : Fin 3, P0 i (2 : Fin 3) = 0 := by
    intro i
    let A : Module.End ℝ (Fin 3 → ℝ) :=
      Matrix.toLin' (twoStepCounterexamplePropagator epsilon lambda 0)
    let P : Module.End ℝ (Fin 3 → ℝ) := Matrix.toLin' P0
    let e : Fin 3 → ℝ := fun j => if j = (2 : Fin 3) then 1 else 0
    have hcomp : P.comp A = P := by
      apply LinearMap.ext
      intro x
      funext j
      have hx := congrFun
        (matrixMulVector_matrixMul (Node := Fin 3) P0
          (twoStepCounterexamplePropagator epsilon lambda 0) x) j
      rw [hPA] at hx
      simpa [A, P, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        matrixMulVector] using hx.symm
    have h20 : (2 : Fin 3) ≠ (0 : Fin 3) := by decide
    have h21 : (2 : Fin 3) ≠ (1 : Fin 3) := by decide
    have h02 : (0 : Fin 3) ≠ (2 : Fin 3) := by decide
    have h12 : (1 : Fin 3) ≠ (2 : Fin 3) := by decide
    have h01 : (0 : Fin 3) ≠ (1 : Fin 3) := by decide
    have h10 : (1 : Fin 3) ≠ (0 : Fin 3) := by decide
    have heigen : A e = d • e := by
      funext j
      fin_cases j <;>
        norm_num [A, e, d, Matrix.toLin'_apply,
          twoStepCounterexamplePropagator, twoStepCounterexampleLiftedStep,
          twoNodeCounterexamplePush, twoNodeCounterexamplePullA,
          twoNodeCounterexamplePullB, matrixMul, Matrix.mulVec, dotProduct,
          Fin.sum_univ_succ, Fin.sum_univ_two,
          h20, h21, h02, h12, h01, h10] <;>
        simp <;>
        ring
    have hzero : P e = 0 :=
      Module.End.apply_eq_zero_of_comp_eq_self_of_apply_eq_smul
        A P d e hcomp heigen hd_ne_one
    have hi := congrFun hzero i
    simpa [P, e, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Fin.sum_univ_two,
      h20, h21, h02, h12, h01, h10] using hi
  intro x hx0 hx1
  funext i
  simp [matrixMulVector, Fin.sum_univ_succ, Fin.sum_univ_two,
    hx0, hx1, hcol2 i]

/-- The stable complement at `alpha = 0` preserves tracker-only vectors once
the base Riesz projection has been removed. -/
theorem two_step_counterexample_stable_base_tracker_subspace_invariant
    (epsilon lambda : ℝ) (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt : epsilon < 1) (P0 F0 : NodeMatrix (Fin 3))
    (hRiesz :
      IsRieszProjectionAtEigenvalue (Node := Fin 3)
        (twoStepCounterexamplePropagator epsilon lambda 0) 1 P0)
    (hsplit :
      twoStepCounterexamplePropagator epsilon lambda 0 =
        matrixAdd (Node := Fin 3) P0 F0)
    (x : RowVector (Fin 3))
    (hx0 : x (0 : Fin 3) = 0) (hx1 : x (1 : Fin 3) = 0) :
    matrixMulVector (Node := Fin 3) F0 x (0 : Fin 3) = 0 ∧
      matrixMulVector (Node := Fin 3) F0 x (1 : Fin 3) = 0 := by
  classical
  have hA :=
    two_step_counterexample_base_tracker_subspace_invariant
      epsilon lambda x hx0 hx1
  have hP :=
    two_step_counterexample_riesz_projection_zero_on_tracker_subspace
      epsilon lambda hepsilon_pos hepsilon_lt P0 hRiesz x hx0 hx1
  have hmul_add :
      matrixMulVector (Node := Fin 3)
          (twoStepCounterexamplePropagator epsilon lambda 0) x =
        fun i =>
          matrixMulVector (Node := Fin 3) P0 x i +
            matrixMulVector (Node := Fin 3) F0 x i := by
    funext i
    rw [hsplit]
    simp [matrixMulVector, matrixAdd, Finset.sum_add_distrib, add_mul]
  constructor
  · have hcoord := congrFun hmul_add (0 : Fin 3)
    have hAcoord :
        matrixMulVector (Node := Fin 3)
          (twoStepCounterexamplePropagator epsilon lambda 0) x (0 : Fin 3) = 0 := hA.1
    have hPcoord :
        matrixMulVector (Node := Fin 3) P0 x (0 : Fin 3) = 0 := by
      simpa using congrFun hP (0 : Fin 3)
    nlinarith
  · have hcoord := congrFun hmul_add (1 : Fin 3)
    have hAcoord :
        matrixMulVector (Node := Fin 3)
          (twoStepCounterexamplePropagator epsilon lambda 0) x (1 : Fin 3) = 0 := hA.2
    have hPcoord :
        matrixMulVector (Node := Fin 3) P0 x (1 : Fin 3) = 0 := by
      simpa using congrFun hP (1 : Fin 3)
    nlinarith

/-- Powers of the base stable complement preserve the tracker-only subspace. -/
theorem two_step_counterexample_stable_power_tracker_subspace_invariant
    (epsilon lambda : ℝ) (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt : epsilon < 1) (P0 F0 : NodeMatrix (Fin 3))
    (hRiesz :
      IsRieszProjectionAtEigenvalue (Node := Fin 3)
        (twoStepCounterexamplePropagator epsilon lambda 0) 1 P0)
    (hsplit :
      twoStepCounterexamplePropagator epsilon lambda 0 =
        matrixAdd (Node := Fin 3) P0 F0) :
    ∀ (j : ℕ) (x : RowVector (Fin 3)),
      x (0 : Fin 3) = 0 → x (1 : Fin 3) = 0 →
        matrixMulVector (Node := Fin 3)
            (matrixPower (Node := Fin 3) F0 j) x (0 : Fin 3) = 0 ∧
          matrixMulVector (Node := Fin 3)
            (matrixPower (Node := Fin 3) F0 j) x (1 : Fin 3) = 0 := by
  intro j
  induction j with
  | zero =>
      intro x hx0 hx1
      constructor <;> simp [matrixPower, identityMatrix, matrixMulVector,
        Fin.sum_univ_succ, Fin.sum_univ_two, hx0, hx1]
  | succ j ih =>
      intro x hx0 hx1
      rw [matrixPower, matrixMulVector_matrixMul]
      have hFx :=
        two_step_counterexample_stable_base_tracker_subspace_invariant
          epsilon lambda hepsilon_pos hepsilon_lt P0 F0 hRiesz hsplit x hx0 hx1
      exact ih (matrixMulVector (Node := Fin 3) F0 x) hFx.1 hFx.2

/-- Vector-valued all-lag version of the Appendix A.1 base stable-output
cancellation.  This is the form needed by the Duhamel/telescoping perturbation
estimate: at `alpha = 0`, the stable output row vanishes for every input phase,
node, and lag. -/
theorem two_step_counterexample_stable_impulse_vector_zero_alpha_all_lags
    (epsilon lambda alpha0 theta K : ℝ)
    (right0 left0 : RowVector (Fin 3))
    (gamma : ℝ → ℝ) (P F : ℝ → NodeMatrix (Fin 3))
    (hepsilon_pos : 0 < epsilon) (hepsilon_lt : epsilon < 1)
    (hsplitting :
      PeriodicSpectralSplitting (Node := Fin 3)
        (fun alpha => twoStepCounterexamplePropagator epsilon lambda alpha)
        (1 / 2) alpha0 theta K right0 left0 gamma P F) :
    ∀ phase j,
      twoStepCounterexampleStableImpulseVectorFrom F epsilon lambda 0 phase j =
        (fun _ : Bool => 0) := by
  classical
  rcases hsplitting with
    ⟨halpha0_pos, _hr0_theta, _htheta_lt_one, _hK_nonneg, hgamma0,
      _hgamma_analytic, _hP_analytic, _hderiv, hlocal⟩
  have hbase_local :
      IsRieszProjectionAtEigenvalue (Node := Fin 3)
          (twoStepCounterexamplePropagator epsilon lambda 0) (gamma 0) (P 0) ∧
        twoStepCounterexamplePropagator epsilon lambda 0 =
          matrixAdd (Node := Fin 3) ((gamma 0) • P 0) (F 0) ∧
          matrixMul (Node := Fin 3) (P 0) (F 0) = 0 ∧
            matrixMul (Node := Fin 3) (F 0) (P 0) = 0 ∧
              ∀ j : ℕ,
                matrixEuclideanOperatorNorm (Node := Fin 3)
                    (matrixPower (Node := Fin 3) (F 0) j) ≤
                  K * theta ^ j := by
    simpa using hlocal 0 (by simpa [abs_of_nonneg halpha0_pos.le] using halpha0_pos.le)
  have hRiesz1 :
      IsRieszProjectionAtEigenvalue (Node := Fin 3)
        (twoStepCounterexamplePropagator epsilon lambda 0) 1 (P 0) := by
    simpa [hgamma0] using hbase_local.1
  have hsplit1 :
      twoStepCounterexamplePropagator epsilon lambda 0 =
        matrixAdd (Node := Fin 3) (P 0) (F 0) := by
    simpa [hgamma0] using hbase_local.2.1
  intro phase j
  funext node
  obtain ⟨hinput0, hinput1⟩ :=
    two_step_counterexample_phase_input_channel_zero_primal
      epsilon lambda phase node
  have hpow :=
    two_step_counterexample_stable_power_tracker_subspace_invariant
      epsilon lambda hepsilon_pos hepsilon_lt (P 0) (F 0) hRiesz1 hsplit1
      j (twoStepCounterexamplePhaseInputChannel epsilon lambda 0 phase node)
      hinput0 hinput1
  simp [twoStepCounterexampleStableImpulseVectorFrom,
    twoStepCounterexampleArithmeticAverageOutput, hpow.1, hpow.2]

/-- All-lag version of the Appendix A.1 base stable-output cancellation. -/
theorem two_step_counterexample_stable_impulse_zero_alpha_all_lags
    (epsilon lambda alpha0 theta K : ℝ)
    (right0 left0 : RowVector (Fin 3))
    (gamma : ℝ → ℝ) (P F : ℝ → NodeMatrix (Fin 3))
    (hepsilon_pos : 0 < epsilon) (hepsilon_lt : epsilon < 1)
    (hsplitting :
      PeriodicSpectralSplitting (Node := Fin 3)
        (fun alpha => twoStepCounterexamplePropagator epsilon lambda alpha)
        (1 / 2) alpha0 theta K right0 left0 gamma P F) :
    ∀ phase j,
      twoStepCounterexampleStableImpulseFrom F epsilon lambda 0 phase j = 0 := by
  classical
  intro phase j
  have hvec :=
    two_step_counterexample_stable_impulse_vector_zero_alpha_all_lags
      epsilon lambda alpha0 theta K right0 left0 gamma P F
      hepsilon_pos hepsilon_lt hsplitting phase j
  simp [twoStepCounterexampleStableImpulseFrom, hvec, rowEuclideanNorm,
    rowNormSq]

/-- Scalar absorption for the Appendix A.1 rate enlargement: a linear factor
can be absorbed into any strictly larger geometric rate. -/
theorem one_plus_nat_mul_geometric_absorb
    {theta theta1 : ℝ} (htheta_pos : 0 < theta)
    (htheta_lt_theta1 : theta < theta1) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ j : ℕ, ((j : ℝ) + 1) * theta ^ j ≤ A * theta1 ^ j := by
  exact exists_const_one_add_natCast_mul_pow_le_pow_of_lt htheta_pos.le htheta_lt_theta1

/-- Coordinatewise absolute control for a concrete three-row implies a
Euclidean row-norm bound. -/
theorem rowEuclideanNorm_fin3_le_of_abs_le
    (w : RowVector (Fin 3)) {B : ℝ} (hB : 0 ≤ B)
    (hcoord : ∀ i : Fin 3, |w i| ≤ B) :
    rowEuclideanNorm (Node := Fin 3) w ≤ 3 * B := by
  classical
  calc
    rowEuclideanNorm (Node := Fin 3) w =
        stateFrobeniusNorm (Node := Fin 3) (E := ℝ) w := by
          simp [rowEuclideanNorm, rowNormSq, stateFrobeniusNorm,
            frobeniusNormSq, Real.norm_eq_abs, sq_abs]
    _ ≤ stateL1Norm (Node := Fin 3) (E := ℝ) w :=
        stateFrobeniusNorm_le_stateL1Norm (Node := Fin 3) (E := ℝ) w
    _ = ∑ i : Fin 3, |w i| := by
        simp [stateL1Norm, Real.norm_eq_abs]
    _ ≤ ∑ _i : Fin 3, B := by
        apply Finset.sum_le_sum
        intro i _hi
        exact hcoord i
    _ = 3 * B := by
        simp

/-- Analytic matrix families are locally `O(alpha)` at the base point in the
file's custom Euclidean operator norm. -/
theorem analyticAt_matrix_operator_norm_sub_le_mul_near_zero
    (H : ℝ → NodeMatrix Node) (hH : AnalyticAt ℝ H 0) :
    ∃ δ L : ℝ, 0 < δ ∧ 0 ≤ L ∧
      ∀ alpha : ℝ, 0 ≤ alpha → alpha ≤ δ →
        matrixEuclideanOperatorNorm (Node := Node)
            (matrixSub (Node := Node) (H alpha) (H 0)) ≤
          L * alpha := by
  classical
  obtain ⟨c, hc, hevent⟩ :=
    hH.differentiableAt.exists_norm_sub_le_mul_dist
  rcases Metric.eventually_nhds_iff.mp hevent with ⟨η, hη_pos, hη⟩
  let factor : ℝ :=
    ((nodeCount (Node := Node) : ℝ) ^ 2) *
      Real.sqrt (nodeCount (Node := Node) : ℝ)
  refine ⟨η / 2, factor * c, by positivity, ?_, ?_⟩
  · exact mul_nonneg (by dsimp [factor]; positivity) hc
  · intro alpha halpha_nonneg halpha_le
    have hdist : dist alpha (0 : ℝ) < η := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg halpha_nonneg]
      nlinarith
    have hnorm : ‖H alpha - H 0‖ ≤ c * alpha := by
      have hraw := hη hdist
      simpa [Real.dist_eq, abs_of_nonneg halpha_nonneg] using hraw
    have hB_nonneg : 0 ≤ c * alpha :=
      mul_nonneg hc halpha_nonneg
    have hentry :
        ∀ i j : Node,
          |(matrixSub (Node := Node) (H alpha) (H 0)) i j| ≤
            c * alpha := by
      intro i j
      have hcoord :
          ‖(H alpha - H 0) i j‖ ≤ ‖H alpha - H 0‖ :=
        le_trans (norm_le_pi_norm ((H alpha - H 0) i) j)
          (norm_le_pi_norm (H alpha - H 0) i)
      calc
        |(matrixSub (Node := Node) (H alpha) (H 0)) i j| =
            ‖(H alpha - H 0) i j‖ := by
              simp [matrixSub, Real.norm_eq_abs]
        _ ≤ ‖H alpha - H 0‖ := hcoord
        _ ≤ c * alpha := hnorm
    calc
      matrixEuclideanOperatorNorm (Node := Node)
          (matrixSub (Node := Node) (H alpha) (H 0)) ≤
          factor * (c * alpha) :=
        matrixEuclideanOperatorNorm_le_of_entrywise_abs_bound
          (Node := Node) (matrixSub (Node := Node) (H alpha) (H 0))
          (c * alpha) hB_nonneg hentry
      _ = (factor * c) * alpha := by ring

/-- T1 bridge for Appendix A.1: the stable complement supplied by
`PeriodicSpectralSplitting` is locally `O(alpha)` in operator norm.  The proof
uses the analytic Riesz-splitting data, identifies the local branch with the
canonical `stableComplementFromRiesz`, and transfers the analytic local bound
back to the supplied `F`. -/
theorem spectralSplitting_stableComplement_local_operator_lipschitz_at_zero
    (A : ℝ → NodeMatrix Node) (alphaAnalytic r0 alpha0 theta K : ℝ)
    (right left : RowVector Node)
    (gamma : ℝ → ℝ) (P F : ℝ → NodeMatrix Node)
    (hanalytic : RealAnalyticMatrixFamilyNear (Node := Node) A alphaAnalytic)
    (hsplitting :
      PeriodicSpectralSplitting (Node := Node) A r0 alpha0 theta K
        right left gamma P F) :
    ∃ δ LF : ℝ, 0 < δ ∧ 0 ≤ LF ∧
      ∀ alpha : ℝ, 0 ≤ alpha → alpha ≤ δ →
        matrixEuclideanOperatorNorm (Node := Node)
            (matrixSub (Node := Node) (F alpha) (F 0)) ≤
          LF * alpha := by
  classical
  rcases hsplitting with
    ⟨halpha0_pos, _hr0_theta, _htheta_lt_one, _hK_nonneg, _hgamma0,
      hgamma_analytic, hP_analytic, _hderiv, hlocal⟩
  let H : ℝ → NodeMatrix Node :=
    stableComplementFromRiesz (Node := Node) A gamma P
  have hA0 : AnalyticAt ℝ A 0 :=
    hanalytic.2 0 (by simpa using hanalytic.1)
  have hgamma0_analytic : AnalyticAt ℝ gamma 0 :=
    hgamma_analytic 0 (by simpa [abs_of_nonneg halpha0_pos.le] using halpha0_pos)
  have hP0_analytic : AnalyticAt ℝ P 0 :=
    hP_analytic 0 (by simpa [abs_of_nonneg halpha0_pos.le] using halpha0_pos)
  have hH_analytic : AnalyticAt ℝ H 0 :=
    stableComplementFromRiesz_analyticAt (Node := Node) A gamma P 0
      hA0 hgamma0_analytic hP0_analytic
  obtain ⟨δH, LH, hδH_pos, hLH_nonneg, hH_bound⟩ :=
    analyticAt_matrix_operator_norm_sub_le_mul_near_zero
      (Node := Node) H hH_analytic
  refine ⟨min δH alpha0, LH, lt_min hδH_pos halpha0_pos, hLH_nonneg, ?_⟩
  intro alpha halpha_nonneg halpha_le
  have halpha_le_δH : alpha ≤ δH := le_trans halpha_le (min_le_left _ _)
  have halpha_le_alpha0 : alpha ≤ alpha0 := le_trans halpha_le (min_le_right _ _)
  have hH_alpha_eq : H alpha = F alpha := by
    have hloc := hlocal alpha (by
      rw [abs_of_nonneg halpha_nonneg]
      exact halpha_le_alpha0)
    have hsplit := hloc.2.1
    ext i j
    have hcoord := congrFun (congrFun hsplit i) j
    simp [H, stableComplementFromRiesz, stableComplementMatrix, matrixSub,
      matrixAdd] at hcoord ⊢
    linarith
  have hH_zero_eq : H 0 = F 0 := by
    have hloc := hlocal 0 (by
      simpa [abs_of_nonneg halpha0_pos.le] using halpha0_pos.le)
    have hsplit := hloc.2.1
    ext i j
    have hcoord := congrFun (congrFun hsplit i) j
    simp [H, stableComplementFromRiesz, stableComplementMatrix, matrixSub,
      matrixAdd] at hcoord ⊢
    linarith
  have hbound := hH_bound alpha halpha_nonneg halpha_le_δH
  simpa [hH_alpha_eq, hH_zero_eq] using hbound

/-- Analytic three-coordinate row-vector families are locally `O(alpha)` at
the base point in the file's Euclidean row norm. -/
theorem analyticAt_rowEuclideanNorm_fin3_sub_le_mul_near_zero
    (b : ℝ → RowVector (Fin 3)) (hb : AnalyticAt ℝ b 0) :
    ∃ δ L : ℝ, 0 < δ ∧ 0 ≤ L ∧
      ∀ alpha : ℝ, 0 ≤ alpha → alpha ≤ δ →
        rowEuclideanNorm (Node := Fin 3)
            (fun i => b alpha i - b 0 i) ≤
          L * alpha := by
  classical
  have hbig :
      (fun alpha : ℝ => b alpha - b 0) =O[𝓝 (0 : ℝ)]
        (fun alpha : ℝ => alpha - 0) :=
    hb.differentiableAt.hasDerivAt.isBigO_sub
  obtain ⟨c, hc⟩ := hbig.bound
  have hevent :
      ∀ᶠ alpha : ℝ in 𝓝 (0 : ℝ),
        ‖b alpha - b 0‖ ≤ max c 0 * |alpha| := by
    filter_upwards [hc] with alpha halpha
    have hle_c :
        c * ‖alpha - 0‖ ≤ max c 0 * ‖alpha - 0‖ :=
      mul_le_mul_of_nonneg_right (le_max_left c 0) (norm_nonneg _)
    have habs : ‖alpha - 0‖ = |alpha| := by
      simp [Real.norm_eq_abs]
    exact le_trans halpha (by simpa [habs] using hle_c)
  rcases Metric.eventually_nhds_iff.mp hevent with ⟨η, hη_pos, hη⟩
  refine ⟨η / 2, 3 * max c 0, by positivity,
    mul_nonneg (by norm_num) (le_max_right c 0), ?_⟩
  intro alpha halpha_nonneg halpha_le
  have hdist : dist alpha (0 : ℝ) < η := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg halpha_nonneg]
    nlinarith
  have hnorm : ‖b alpha - b 0‖ ≤ max c 0 * alpha := by
    have hraw := hη hdist
    simpa [abs_of_nonneg halpha_nonneg] using hraw
  have hB_nonneg : 0 ≤ max c 0 * alpha :=
    mul_nonneg (le_max_right c 0) halpha_nonneg
  have hcoord :
      ∀ i : Fin 3, |b alpha i - b 0 i| ≤ max c 0 * alpha := by
    intro i
    have hcoord_norm : ‖(b alpha - b 0) i‖ ≤ ‖b alpha - b 0‖ :=
      norm_le_pi_norm (b alpha - b 0) i
    calc
      |b alpha i - b 0 i| = ‖(b alpha - b 0) i‖ := by
        simp [Pi.sub_apply, Real.norm_eq_abs]
      _ ≤ ‖b alpha - b 0‖ := hcoord_norm
      _ ≤ max c 0 * alpha := hnorm
  calc
    rowEuclideanNorm (Node := Fin 3)
        (fun i => b alpha i - b 0 i) ≤
        3 * (max c 0 * alpha) :=
      rowEuclideanNorm_fin3_le_of_abs_le
        (fun i => b alpha i - b 0 i) hB_nonneg hcoord
    _ = (3 * max c 0) * alpha := by ring

/-- The concrete Appendix A.1 phase-input channel varies locally linearly in
`alpha` around the base point. -/
theorem two_step_counterexample_phase_input_channel_lipschitz_at_zero
    (epsilon lambda : ℝ) (phase : TwoStepPhase) (node : Bool) :
    ∃ δ LB : ℝ, 0 < δ ∧ 0 ≤ LB ∧
      ∀ alpha : ℝ, 0 ≤ alpha → alpha ≤ δ →
        rowEuclideanNorm (Node := Fin 3)
            (fun i =>
              twoStepCounterexamplePhaseInputChannel epsilon lambda alpha phase node i -
                twoStepCounterexamplePhaseInputChannel epsilon lambda 0 phase node i) ≤
          LB * alpha := by
  classical
  have hB_analytic :
      AnalyticAt ℝ
        (fun alpha : ℝ =>
          twoStepCounterexamplePhaseInputChannel epsilon lambda alpha phase node) 0 := by
    cases phase <;>
      apply AnalyticAt.pi <;>
      intro i <;>
      fin_cases i <;>
      cases node <;>
      simp [twoStepCounterexamplePhaseInputChannel,
        twoStepCounterexampleOneStepNoiseInput,
        twoStepCounterexampleLiftedStep, matrixMulVector,
        twoNodeCounterexamplePush, twoNodeCounterexamplePullA,
        twoNodeCounterexamplePullB, Fin.sum_univ_succ, Fin.sum_univ_two] <;>
      fun_prop
  simpa using
    analyticAt_rowEuclideanNorm_fin3_sub_le_mul_near_zero
      (fun alpha : ℝ =>
        twoStepCounterexamplePhaseInputChannel epsilon lambda alpha phase node)
      hB_analytic

/-- Finite phase/node aggregation of the local analytic phase-input control. -/
theorem two_step_counterexample_phase_input_channel_uniform_lipschitz_at_zero
    (epsilon lambda : ℝ)
    (hB_lip :
      ∀ phase node,
        ∃ δB LB : ℝ, 0 < δB ∧ 0 ≤ LB ∧
          ∀ alpha : ℝ, 0 ≤ alpha → alpha ≤ δB →
            rowEuclideanNorm (Node := Fin 3)
                (fun i =>
                  twoStepCounterexamplePhaseInputChannel
                      epsilon lambda alpha phase node i -
                    twoStepCounterexamplePhaseInputChannel
                      epsilon lambda 0 phase node i) ≤
              LB * alpha) :
    ∃ δB LB : ℝ, 0 < δB ∧ 0 ≤ LB ∧
      ∀ phase node alpha, 0 ≤ alpha → alpha ≤ δB →
        rowEuclideanNorm (Node := Fin 3)
            (fun i =>
              twoStepCounterexamplePhaseInputChannel epsilon lambda alpha phase node i -
                twoStepCounterexamplePhaseInputChannel epsilon lambda 0 phase node i) ≤
          LB * alpha := by
  classical
  letI : Fintype TwoStepPhase :=
    { elems := {TwoStepPhase.phaseA, TwoStepPhase.phaseB}
      complete := by intro phase; cases phase <;> simp }
  simpa only [Prod.forall] using
    (Finite.exists_uniform_local_linear_bound
      (phi := fun p : TwoStepPhase × Bool => fun alpha : ℝ =>
        rowEuclideanNorm (Node := Fin 3)
          (fun i =>
            twoStepCounterexamplePhaseInputChannel
                epsilon lambda alpha p.1 p.2 i -
              twoStepCounterexamplePhaseInputChannel
                epsilon lambda 0 p.1 p.2 i))
      (fun p => hB_lip p.1 p.2))

/-- The concrete phase-input channel is uniformly bounded on any source
interval `[0, alpha0]`, after finite aggregation over phases and nodes. -/
theorem two_step_counterexample_phase_input_channel_bound_on_interval
    (epsilon lambda alpha0 : ℝ) (halpha0_pos : 0 < alpha0) :
    ∃ MB : ℝ, 0 ≤ MB ∧
      ∀ alpha phase node, 0 ≤ alpha → alpha ≤ alpha0 →
        rowEuclideanNorm (Node := Fin 3)
            (twoStepCounterexamplePhaseInputChannel epsilon lambda alpha phase node) ≤
          MB := by
  classical
  letI : Fintype TwoStepPhase :=
    { elems := {TwoStepPhase.phaseA, TwoStepPhase.phaseB}
      complete := by intro phase; cases phase <;> simp }
  obtain ⟨MB, hMB_nonneg, hMB⟩ :=
    exists_nonneg_uniform_norm_bound_of_finite_of_isCompact_of_continuousOn
      (s := Set.Icc (0 : ℝ) alpha0)
      (f := fun p : TwoStepPhase × Bool => fun alpha : ℝ =>
        rowEuclideanNorm (Node := Fin 3)
          (twoStepCounterexamplePhaseInputChannel epsilon lambda alpha p.1 p.2))
      isCompact_Icc (by
        rintro ⟨phase, node⟩
        refine Continuous.continuousOn ?_
        cases phase <;> cases node <;>
          simp [rowEuclideanNorm, rowNormSq, twoStepCounterexamplePhaseInputChannel,
            twoStepCounterexampleOneStepNoiseInput,
            twoStepCounterexampleLiftedStep, matrixMulVector,
            twoNodeCounterexamplePush, twoNodeCounterexamplePullA,
            twoNodeCounterexamplePullB, Fin.sum_univ_succ, Fin.sum_univ_two] <;>
          fun_prop)
  refine ⟨MB, hMB_nonneg, ?_⟩
  intro alpha phase node halpha_nonneg halpha_le
  have h := hMB (phase, node) alpha ⟨halpha_nonneg, halpha_le⟩
  simpa only [Real.norm_eq_abs, rowEuclideanNorm,
    abs_of_nonneg (Real.sqrt_nonneg _)] using h

/-- The arithmetic-average output row has operator norm at most one with
respect to the concrete three-coordinate Euclidean row norm. -/
theorem twoStepCounterexampleArithmeticAverageOutput_abs_le_rowEuclideanNorm
    (v : RowVector (Fin 3)) :
    |twoStepCounterexampleArithmeticAverageOutput v| ≤
      rowEuclideanNorm (Node := Fin 3) v := by
  classical
  have hsquare :
      |twoStepCounterexampleArithmeticAverageOutput v| ^ 2 ≤
        rowNormSq (Node := Fin 3) v := by
    simp [twoStepCounterexampleArithmeticAverageOutput, rowNormSq,
      Fin.sum_univ_succ, Fin.sum_univ_two, sq_abs]
    nlinarith [sq_nonneg (v 0 - v 1), sq_nonneg (v 2)]
  calc
    |twoStepCounterexampleArithmeticAverageOutput v| =
        Real.sqrt (|twoStepCounterexampleArithmeticAverageOutput v| ^ 2) := by
          rw [Real.sqrt_sq (abs_nonneg _)]
    _ ≤ Real.sqrt (rowNormSq (Node := Fin 3) v) :=
        Real.sqrt_le_sqrt hsquare
    _ = rowEuclideanNorm (Node := Fin 3) v := rfl

/-- Coordinatewise absolute control for a Bool-row implies a concrete
Euclidean row-norm bound. -/
theorem rowEuclideanNorm_bool_le_of_abs_le
    (w : RowVector Bool) {B : ℝ} (hB : 0 ≤ B)
    (hcoord : ∀ node : Bool, |w node| ≤ B) :
    rowEuclideanNorm (Node := Bool) w ≤ 2 * B := by
  classical
  calc
    rowEuclideanNorm (Node := Bool) w =
        stateFrobeniusNorm (Node := Bool) (E := ℝ) w := by
          simp [rowEuclideanNorm, rowNormSq, stateFrobeniusNorm,
            frobeniusNormSq, Real.norm_eq_abs, sq_abs]
    _ ≤ stateL1Norm (Node := Bool) (E := ℝ) w :=
        stateFrobeniusNorm_le_stateL1Norm (Node := Bool) (E := ℝ) w
    _ = ∑ node : Bool, |w node| := by
        simp [stateL1Norm, Real.norm_eq_abs]
    _ ≤ ∑ _node : Bool, B := by
        apply Finset.sum_le_sum
        intro node _hi
        exact hcoord node
    _ = 2 * B := by
        simp

/-- If every node's propagated three-coordinate action is within `B` of the
base action and the base stable output vanishes, then the Bool-row stable
impulse is bounded by `2 * B`. -/
theorem twoStepCounterexampleStableImpulseFrom_le_of_action_diff_bound
    (F : ℝ → NodeMatrix (Fin 3)) (epsilon lambda alpha : ℝ)
    (phase : TwoStepPhase) (j : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hzero :
      twoStepCounterexampleStableImpulseVectorFrom F epsilon lambda 0 phase j =
        (fun _ : Bool => 0))
    (hcoord :
      ∀ node : Bool,
        rowEuclideanNorm (Node := Fin 3)
            (fun i =>
              matrixMulVector (Node := Fin 3)
                  (matrixPower (Node := Fin 3) (F alpha) j)
                  (twoStepCounterexamplePhaseInputChannel
                    epsilon lambda alpha phase node) i -
                matrixMulVector (Node := Fin 3)
                  (matrixPower (Node := Fin 3) (F 0) j)
                  (twoStepCounterexamplePhaseInputChannel
                    epsilon lambda 0 phase node) i) ≤
          B) :
    twoStepCounterexampleStableImpulseFrom F epsilon lambda alpha phase j ≤
      2 * B := by
  classical
  unfold twoStepCounterexampleStableImpulseFrom
  apply rowEuclideanNorm_bool_le_of_abs_le
  · exact hB
  · intro node
    have hzero_node := congrFun hzero node
    have houtput_diff :
        twoStepCounterexampleArithmeticAverageOutput
            (fun i =>
              matrixMulVector (Node := Fin 3)
                  (matrixPower (Node := Fin 3) (F alpha) j)
                  (twoStepCounterexamplePhaseInputChannel
                    epsilon lambda alpha phase node) i -
                matrixMulVector (Node := Fin 3)
                  (matrixPower (Node := Fin 3) (F 0) j)
                  (twoStepCounterexamplePhaseInputChannel
                    epsilon lambda 0 phase node) i) =
          twoStepCounterexampleStableImpulseVectorFrom F epsilon lambda alpha phase j node -
            twoStepCounterexampleStableImpulseVectorFrom F epsilon lambda 0 phase j node := by
      simp [twoStepCounterexampleStableImpulseVectorFrom,
        twoStepCounterexampleArithmeticAverageOutput]
      ring
    calc
      |twoStepCounterexampleStableImpulseVectorFrom F epsilon lambda alpha phase j node| =
          |twoStepCounterexampleArithmeticAverageOutput
              (fun i =>
                matrixMulVector (Node := Fin 3)
                    (matrixPower (Node := Fin 3) (F alpha) j)
                    (twoStepCounterexamplePhaseInputChannel
                      epsilon lambda alpha phase node) i -
                  matrixMulVector (Node := Fin 3)
                    (matrixPower (Node := Fin 3) (F 0) j)
                    (twoStepCounterexamplePhaseInputChannel
                      epsilon lambda 0 phase node) i)| := by
            rw [houtput_diff, hzero_node, sub_zero]
      _ ≤ rowEuclideanNorm (Node := Fin 3)
              (fun i =>
                matrixMulVector (Node := Fin 3)
                    (matrixPower (Node := Fin 3) (F alpha) j)
                    (twoStepCounterexamplePhaseInputChannel
                      epsilon lambda alpha phase node) i -
                  matrixMulVector (Node := Fin 3)
                    (matrixPower (Node := Fin 3) (F 0) j)
                    (twoStepCounterexamplePhaseInputChannel
                      epsilon lambda 0 phase node) i) :=
            twoStepCounterexampleArithmeticAverageOutput_abs_le_rowEuclideanNorm _
      _ ≤ B := hcoord node

/-- Linearity of the custom matrix-vector action in the vector argument,
packaged in the row-vector subtraction form used by the Duhamel split. -/
theorem matrixMulVector_sub_vector
    (A : NodeMatrix Node) (x y : RowVector Node) :
    matrixMulVector (Node := Node) A (fun i => x i - y i) =
      fun i =>
        matrixMulVector (Node := Node) A x i -
          matrixMulVector (Node := Node) A y i := by
  classical
  funext i
  simp [matrixMulVector, Finset.sum_sub_distrib, mul_sub]

/-- The custom `matrixSub` acts as subtraction after multiplying a vector. -/
theorem matrixMulVector_matrixSub
    (A B : NodeMatrix Node) (x : RowVector Node) :
    matrixMulVector (Node := Node) (matrixSub (Node := Node) A B) x =
      fun i =>
        matrixMulVector (Node := Node) A x i -
          matrixMulVector (Node := Node) B x i := by
  classical
  funext i
  simp [matrixMulVector, matrixSub, Finset.sum_sub_distrib, sub_mul]

/-- Triangle inequality for the file's concrete row Euclidean norm. -/
theorem rowEuclideanNorm_add_le
    (x y : RowVector Node) :
    rowEuclideanNorm (Node := Node) (x + y) ≤
      rowEuclideanNorm (Node := Node) x +
        rowEuclideanNorm (Node := Node) y := by
  classical
  calc
    rowEuclideanNorm (Node := Node) (x + y) =
        stateFrobeniusNorm (Node := Node) (E := ℝ) (x + y) := by
          simp [rowEuclideanNorm, rowNormSq, stateFrobeniusNorm,
            frobeniusNormSq, Real.norm_eq_abs, sq_abs]
    _ ≤ stateFrobeniusNorm (Node := Node) (E := ℝ) x +
          stateFrobeniusNorm (Node := Node) (E := ℝ) y :=
        stateFrobeniusNorm_add_le (Node := Node) (E := ℝ) x y
    _ = rowEuclideanNorm (Node := Node) x +
          rowEuclideanNorm (Node := Node) y := by
        simp [rowEuclideanNorm, rowNormSq, stateFrobeniusNorm,
          frobeniusNormSq, Real.norm_eq_abs, sq_abs]

/-- Finite-sum triangle inequality for the file's concrete row Euclidean
norm.  This is the aggregation form used by Duhamel/telescoping estimates. -/
theorem rowEuclideanNorm_finset_sum_le
    {ι : Type*} (s : Finset ι) (x : ι → RowVector Node) :
    rowEuclideanNorm (Node := Node) (∑ j ∈ s, x j) ≤
      ∑ j ∈ s, rowEuclideanNorm (Node := Node) (x j) := by
  classical
  calc
    rowEuclideanNorm (Node := Node) (∑ j ∈ s, x j) =
        stateFrobeniusNorm (Node := Node) (E := ℝ) (∑ j ∈ s, x j) := by
          simp [rowEuclideanNorm, rowNormSq, stateFrobeniusNorm,
            frobeniusNormSq, Real.norm_eq_abs, sq_abs]
    _ ≤ ∑ j ∈ s,
          stateFrobeniusNorm (Node := Node) (E := ℝ) (x j) :=
        stateFrobeniusNorm_finset_sum_le (Node := Node) (E := ℝ) s x
    _ = ∑ j ∈ s, rowEuclideanNorm (Node := Node) (x j) := by
        simp [rowEuclideanNorm, rowNormSq, stateFrobeniusNorm,
          frobeniusNormSq, Real.norm_eq_abs, sq_abs]

/-- Coordinatewise absolute control implies a Euclidean row-norm bound on any
finite carrier. -/
theorem rowEuclideanNorm_le_card_mul_of_abs_le
    (w : RowVector Node) {B : ℝ} (hB : 0 ≤ B)
    (hcoord : ∀ i : Node, |w i| ≤ B) :
    rowEuclideanNorm (Node := Node) w ≤
      (nodeCount (Node := Node) : ℝ) * B := by
  classical
  calc
    rowEuclideanNorm (Node := Node) w =
        stateFrobeniusNorm (Node := Node) (E := ℝ) w := by
          simp [rowEuclideanNorm, rowNormSq, stateFrobeniusNorm,
            frobeniusNormSq, Real.norm_eq_abs, sq_abs]
    _ ≤ stateL1Norm (Node := Node) (E := ℝ) w :=
        stateFrobeniusNorm_le_stateL1Norm (Node := Node) (E := ℝ) w
    _ = ∑ i : Node, |w i| := by
        simp [stateL1Norm, Real.norm_eq_abs]
    _ ≤ ∑ _i : Node, B := by
        apply Finset.sum_le_sum
        intro i _hi
        exact hcoord i
    _ = (nodeCount (Node := Node) : ℝ) * B := by
        simp [nodeCount]

/-- Direct action form of the custom matrix Euclidean operator norm. -/
theorem rowEuclideanNorm_matrixMulVector_le
    (A : NodeMatrix Node) (x : RowVector Node) :
    rowEuclideanNorm (Node := Node)
        (matrixMulVector (Node := Node) A x) ≤
      matrixEuclideanOperatorNorm (Node := Node) A *
        rowEuclideanNorm (Node := Node) x :=
  (matrixEuclideanOperatorNorm_spec (Node := Node) A).2 x

/-- Submultiplicativity for the file's custom scalar matrix Euclidean
operator norm.  This is the operator-level primitive needed before applying a
Duhamel/telescoping bound to powers of nearby stable complements. -/
theorem matrixEuclideanOperatorNorm_matrixMul_le
    (A B : NodeMatrix Node) :
    matrixEuclideanOperatorNorm (Node := Node)
        (matrixMul (Node := Node) A B) ≤
      matrixEuclideanOperatorNorm (Node := Node) A *
        matrixEuclideanOperatorNorm (Node := Node) B := by
  classical
  let c :=
    matrixEuclideanOperatorNorm (Node := Node) A *
      matrixEuclideanOperatorNorm (Node := Node) B
  have hA_nonneg :
      0 ≤ matrixEuclideanOperatorNorm (Node := Node) A :=
    (matrixEuclideanOperatorNorm_spec (Node := Node) A).1
  have hB_nonneg :
      0 ≤ matrixEuclideanOperatorNorm (Node := Node) B :=
    (matrixEuclideanOperatorNorm_spec (Node := Node) B).1
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg hA_nonneg hB_nonneg
  have hscalar (x : RowVector Node) :
      rowEuclideanNorm (Node := Node)
          (matrixMulVector (Node := Node)
            (matrixMul (Node := Node) A B) x) ≤
        c * rowEuclideanNorm (Node := Node) x := by
    calc
      rowEuclideanNorm (Node := Node)
          (matrixMulVector (Node := Node)
            (matrixMul (Node := Node) A B) x) =
          rowEuclideanNorm (Node := Node)
            (matrixMulVector (Node := Node) A
              (matrixMulVector (Node := Node) B x)) := by
            rw [matrixMulVector_matrixMul]
      _ ≤ matrixEuclideanOperatorNorm (Node := Node) A *
            rowEuclideanNorm (Node := Node)
              (matrixMulVector (Node := Node) B x) :=
          rowEuclideanNorm_matrixMulVector_le (Node := Node) A
            (matrixMulVector (Node := Node) B x)
      _ ≤ matrixEuclideanOperatorNorm (Node := Node) A *
            (matrixEuclideanOperatorNorm (Node := Node) B *
              rowEuclideanNorm (Node := Node) x) :=
          mul_le_mul_of_nonneg_left
            (rowEuclideanNorm_matrixMulVector_le (Node := Node) B x)
            hA_nonneg
      _ = c * rowEuclideanNorm (Node := Node) x := by
          dsimp [c]
          ring
  unfold matrixEuclideanOperatorNorm
  apply csInf_le
  · refine ⟨0, ?_⟩
    intro d hd
    exact hd.1
  · exact ⟨hc_nonneg, hscalar⟩

/-- Applying a stable power to a bounded row vector preserves the geometric
operator bound in action form. -/
theorem matrixPower_action_norm_bound
    (A : NodeMatrix Node) (x : RowVector Node) (j : ℕ)
    {K theta M : ℝ}
    (hpower :
      matrixEuclideanOperatorNorm (Node := Node)
          (matrixPower (Node := Node) A j) ≤
        K * theta ^ j)
    (hx : rowEuclideanNorm (Node := Node) x ≤ M) :
    rowEuclideanNorm (Node := Node)
        (matrixMulVector (Node := Node)
          (matrixPower (Node := Node) A j) x) ≤
      (K * theta ^ j) * M := by
  have hx_nonneg : 0 ≤ rowEuclideanNorm (Node := Node) x := by
    simpa [rowEuclideanNorm] using
      Real.sqrt_nonneg (rowNormSq (Node := Node) x)
  have hpower_rhs_nonneg :
      0 ≤ K * theta ^ j := by
    exact le_trans
      ((matrixEuclideanOperatorNorm_spec (Node := Node)
        (matrixPower (Node := Node) A j)).1) hpower
  calc
    rowEuclideanNorm (Node := Node)
        (matrixMulVector (Node := Node)
          (matrixPower (Node := Node) A j) x) ≤
        matrixEuclideanOperatorNorm (Node := Node)
          (matrixPower (Node := Node) A j) *
          rowEuclideanNorm (Node := Node) x :=
      rowEuclideanNorm_matrixMulVector_le (Node := Node)
        (matrixPower (Node := Node) A j) x
    _ ≤ (K * theta ^ j) * M :=
      mul_le_mul hpower hx hx_nonneg hpower_rhs_nonneg

/-- Stable-power action on a locally small input perturbation.  This is the
first, non-telescoping term in the Appendix A.1 Duhamel split. -/
theorem matrixPower_input_perturbation_bound
    (A : NodeMatrix Node) (x y : RowVector Node)
    (j : ℕ) {K theta L alpha : ℝ}
    (hK : 0 ≤ K) (htheta : 0 ≤ theta) (hL : 0 ≤ L)
    (halpha : 0 ≤ alpha)
    (hpower :
      matrixEuclideanOperatorNorm (Node := Node)
          (matrixPower (Node := Node) A j) ≤
        K * theta ^ j)
    (hinput :
      rowEuclideanNorm (Node := Node) (fun i => x i - y i) ≤
        L * alpha) :
    rowEuclideanNorm (Node := Node)
        (fun i =>
          matrixMulVector (Node := Node)
              (matrixPower (Node := Node) A j) x i -
            matrixMulVector (Node := Node)
              (matrixPower (Node := Node) A j) y i) ≤
      (K * theta ^ j) * (L * alpha) := by
  classical
  let P := matrixPower (Node := Node) A j
  have hP_nonneg :
      0 ≤ matrixEuclideanOperatorNorm (Node := Node) P :=
    (matrixEuclideanOperatorNorm_spec (Node := Node) P).1
  have hpower_rhs_nonneg : 0 ≤ K * theta ^ j :=
    mul_nonneg hK (pow_nonneg htheta j)
  have hinput_nonneg :
      0 ≤ rowEuclideanNorm (Node := Node) (fun i => x i - y i) := by
    simpa [rowEuclideanNorm] using
      Real.sqrt_nonneg (rowNormSq (Node := Node) (fun i => x i - y i))
  calc
    rowEuclideanNorm (Node := Node)
        (fun i =>
          matrixMulVector (Node := Node) P x i -
            matrixMulVector (Node := Node) P y i) =
        rowEuclideanNorm (Node := Node)
          (matrixMulVector (Node := Node) P (fun i => x i - y i)) := by
          rw [matrixMulVector_sub_vector]
    _ ≤ matrixEuclideanOperatorNorm (Node := Node) P *
          rowEuclideanNorm (Node := Node) (fun i => x i - y i) :=
        rowEuclideanNorm_matrixMulVector_le (Node := Node) P (fun i => x i - y i)
    _ ≤ (K * theta ^ j) * (L * alpha) :=
        mul_le_mul hpower hinput hinput_nonneg hpower_rhs_nonneg

/-- Triangle split for the two pieces of the Duhamel action estimate:
input perturbation at fixed `A`, plus power perturbation at fixed base input. -/
theorem matrixPower_action_diff_split_bound
    (A B : NodeMatrix Node) (x y : RowVector Node)
    {Rinput Rpower : ℝ}
    (hinput :
      rowEuclideanNorm (Node := Node)
          (fun i =>
            matrixMulVector (Node := Node) A x i -
              matrixMulVector (Node := Node) A y i) ≤
        Rinput)
    (hpower :
      rowEuclideanNorm (Node := Node)
          (fun i =>
            matrixMulVector (Node := Node) A y i -
              matrixMulVector (Node := Node) B y i) ≤
        Rpower) :
    rowEuclideanNorm (Node := Node)
        (fun i =>
          matrixMulVector (Node := Node) A x i -
            matrixMulVector (Node := Node) B y i) ≤
      Rinput + Rpower := by
  classical
  let u : RowVector Node :=
    fun i =>
      matrixMulVector (Node := Node) A x i -
        matrixMulVector (Node := Node) A y i
  let v : RowVector Node :=
    fun i =>
      matrixMulVector (Node := Node) A y i -
        matrixMulVector (Node := Node) B y i
  have hsum :
      (fun i =>
        matrixMulVector (Node := Node) A x i -
          matrixMulVector (Node := Node) B y i) = u + v := by
    funext i
    dsimp [u, v]
    ring
  calc
    rowEuclideanNorm (Node := Node)
        (fun i =>
          matrixMulVector (Node := Node) A x i -
            matrixMulVector (Node := Node) B y i) =
        rowEuclideanNorm (Node := Node) (u + v) := by rw [hsum]
    _ ≤ rowEuclideanNorm (Node := Node) u +
          rowEuclideanNorm (Node := Node) v :=
        rowEuclideanNorm_add_le (Node := Node) u v
    _ ≤ Rinput + Rpower := add_le_add hinput hpower

/-- Recursive scalar budget for the custom right-recursive Duhamel action
telescope.  The successor step isolates the newest perturbation term and then
propagates the base input through one more `B`. -/
def stablePowerActionTelescopeBudget
    (K theta L alpha M : ℝ) : ℕ → ℝ
  | 0 => 0
  | j + 1 =>
      (K * theta ^ j) * ((L * alpha) * M) +
        stablePowerActionTelescopeBudget K theta L alpha ((K * theta) * M) j

/-- Duhamel/telescope action bound for the file's custom matrix powers.

This compares `A^j y` and `B^j y` using only stable-power estimates for both
families, an operator perturbation bound for `A - B`, and a bound on the base
input. -/
theorem matrixPower_stable_power_action_telescope_bound
    (A B : NodeMatrix Node) :
    ∀ (j : ℕ) (y : RowVector Node) {K theta L alpha M : ℝ},
      0 ≤ K → 0 ≤ theta → 0 ≤ L → 0 ≤ alpha → 0 ≤ M →
      (∀ n : ℕ,
        matrixEuclideanOperatorNorm (Node := Node)
            (matrixPower (Node := Node) A n) ≤
          K * theta ^ n) →
      (∀ n : ℕ,
        matrixEuclideanOperatorNorm (Node := Node)
            (matrixPower (Node := Node) B n) ≤
          K * theta ^ n) →
      matrixEuclideanOperatorNorm (Node := Node)
          (matrixSub (Node := Node) A B) ≤
        L * alpha →
      rowEuclideanNorm (Node := Node) y ≤ M →
      rowEuclideanNorm (Node := Node)
          (fun i =>
            matrixMulVector (Node := Node)
                (matrixPower (Node := Node) A j) y i -
              matrixMulVector (Node := Node)
                (matrixPower (Node := Node) B j) y i) ≤
        stablePowerActionTelescopeBudget K theta L alpha M j := by
  classical
  intro j
  induction j with
  | zero =>
      intro y K theta L alpha M hK htheta hL halpha hM hpowerA hpowerB hdiff hy
      simp [stablePowerActionTelescopeBudget, matrixPower, identityMatrix,
        matrixMulVector, rowEuclideanNorm, rowNormSq]
  | succ j ih =>
      intro y K theta L alpha M hK htheta hL halpha hM hpowerA hpowerB hdiff hy
      let u : RowVector Node :=
        matrixMulVector (Node := Node)
          (matrixPower (Node := Node) A j)
          (matrixMulVector (Node := Node) (matrixSub (Node := Node) A B) y)
      let v : RowVector Node :=
        fun i =>
          matrixMulVector (Node := Node)
              (matrixPower (Node := Node) A j)
              (matrixMulVector (Node := Node) B y) i -
            matrixMulVector (Node := Node)
              (matrixPower (Node := Node) B j)
              (matrixMulVector (Node := Node) B y) i
      have hdecomp :
          (fun i =>
            matrixMulVector (Node := Node)
                (matrixPower (Node := Node) A (j + 1)) y i -
              matrixMulVector (Node := Node)
                (matrixPower (Node := Node) B (j + 1)) y i) =
            u + v := by
        funext i
        have hsub_action :=
          congrFun
            (matrixMulVector_sub_vector (Node := Node)
              (matrixPower (Node := Node) A j)
              (matrixMulVector (Node := Node) A y)
              (matrixMulVector (Node := Node) B y)) i
        have hmatrix_sub :=
          matrixMulVector_matrixSub (Node := Node) A B y
        dsimp [u, v]
        rw [matrixPower, matrixPower, matrixMulVector_matrixMul,
          matrixMulVector_matrixMul]
        calc
          matrixMulVector (Node := Node)
                (matrixPower (Node := Node) A j)
                (matrixMulVector (Node := Node) A y) i -
              matrixMulVector (Node := Node)
                (matrixPower (Node := Node) B j)
                (matrixMulVector (Node := Node) B y) i =
              (matrixMulVector (Node := Node)
                    (matrixPower (Node := Node) A j)
                    (matrixMulVector (Node := Node) A y) i -
                matrixMulVector (Node := Node)
                    (matrixPower (Node := Node) A j)
                    (matrixMulVector (Node := Node) B y) i) +
                (matrixMulVector (Node := Node)
                    (matrixPower (Node := Node) A j)
                    (matrixMulVector (Node := Node) B y) i -
                  matrixMulVector (Node := Node)
                    (matrixPower (Node := Node) B j)
                    (matrixMulVector (Node := Node) B y) i) := by ring
          _ =
              matrixMulVector (Node := Node)
                    (matrixPower (Node := Node) A j)
                    (fun k =>
                      matrixMulVector (Node := Node) A y k -
                        matrixMulVector (Node := Node) B y k) i +
                (matrixMulVector (Node := Node)
                    (matrixPower (Node := Node) A j)
                    (matrixMulVector (Node := Node) B y) i -
                  matrixMulVector (Node := Node)
                    (matrixPower (Node := Node) B j)
                    (matrixMulVector (Node := Node) B y) i) := by
                rw [hsub_action]
          _ =
              matrixMulVector (Node := Node)
                    (matrixPower (Node := Node) A j)
                    (matrixMulVector (Node := Node)
                      (matrixSub (Node := Node) A B) y) i +
                (matrixMulVector (Node := Node)
                    (matrixPower (Node := Node) A j)
                    (matrixMulVector (Node := Node) B y) i -
                  matrixMulVector (Node := Node)
                    (matrixPower (Node := Node) B j)
                    (matrixMulVector (Node := Node) B y) i) := by
                rw [hmatrix_sub]
      have hdiff_rhs_nonneg : 0 ≤ L * alpha :=
        mul_nonneg hL halpha
      have hy_nonneg : 0 ≤ rowEuclideanNorm (Node := Node) y := by
        simpa [rowEuclideanNorm] using
          Real.sqrt_nonneg (rowNormSq (Node := Node) y)
      have hdiff_action :
          rowEuclideanNorm (Node := Node)
              (matrixMulVector (Node := Node)
                (matrixSub (Node := Node) A B) y) ≤
            (L * alpha) * M := by
        calc
          rowEuclideanNorm (Node := Node)
              (matrixMulVector (Node := Node)
                (matrixSub (Node := Node) A B) y) ≤
              matrixEuclideanOperatorNorm (Node := Node)
                (matrixSub (Node := Node) A B) *
                rowEuclideanNorm (Node := Node) y :=
            rowEuclideanNorm_matrixMulVector_le (Node := Node)
              (matrixSub (Node := Node) A B) y
          _ ≤ (L * alpha) * M :=
            mul_le_mul hdiff hy hy_nonneg hdiff_rhs_nonneg
      have hu :
          rowEuclideanNorm (Node := Node) u ≤
            (K * theta ^ j) * ((L * alpha) * M) := by
        dsimp [u]
        exact
          matrixPower_action_norm_bound (Node := Node) A
            (matrixMulVector (Node := Node) (matrixSub (Node := Node) A B) y)
            j (K := K) (theta := theta) (M := (L * alpha) * M)
            (hpowerA j) hdiff_action
      have hM_next : 0 ≤ (K * theta) * M :=
        mul_nonneg (mul_nonneg hK htheta) hM
      have hBy :
          rowEuclideanNorm (Node := Node)
              (matrixMulVector (Node := Node) B y) ≤
            (K * theta) * M := by
        have hraw :=
          matrixPower_action_norm_bound (Node := Node) B y 1
            (K := K) (theta := theta) (M := M)
            (hpowerB 1) hy
        simpa [matrixPower, matrixMul_identity_left, pow_one] using hraw
      have hv :
          rowEuclideanNorm (Node := Node) v ≤
            stablePowerActionTelescopeBudget K theta L alpha ((K * theta) * M) j := by
        dsimp [v]
        exact ih (matrixMulVector (Node := Node) B y)
          hK htheta hL halpha hM_next hpowerA hpowerB hdiff hBy
      calc
        rowEuclideanNorm (Node := Node)
            (fun i =>
              matrixMulVector (Node := Node)
                  (matrixPower (Node := Node) A (j + 1)) y i -
                matrixMulVector (Node := Node)
                  (matrixPower (Node := Node) B (j + 1)) y i) =
            rowEuclideanNorm (Node := Node) (u + v) := by rw [hdecomp]
        _ ≤ rowEuclideanNorm (Node := Node) u +
              rowEuclideanNorm (Node := Node) v :=
            rowEuclideanNorm_add_le (Node := Node) u v
        _ ≤
            (K * theta ^ j) * ((L * alpha) * M) +
              stablePowerActionTelescopeBudget K theta L alpha
                ((K * theta) * M) j :=
            add_le_add hu hv
        _ =
            stablePowerActionTelescopeBudget K theta L alpha M (j + 1) := by
            rfl

/-- Indexed scalar budget for the right-recursive Duhamel action telescope.

The old scalar recursion updated the base input bound by `K * theta` at each
step.  This budget instead records a bound for the entire `B`-orbit of the
initial input, so the induction only shifts the orbit index. -/
def stablePowerActionDuhamelBudget
    (K theta L alpha : ℝ) (N : ℕ → ℝ) : ℕ → ℝ :=
  SOptLib.shifted_orbit_duhamel_majorant K theta L alpha N

/-- Route-fit Duhamel/telescope action bound for the file's custom
right-recursive matrix powers.

The conclusion is intentionally indexed by a caller-supplied bound for
`B^k y`; this avoids strengthening the splitting assumptions with an
unavailable `K * theta < theta1` condition. -/
theorem matrixPower_stable_power_action_duhamel_budget_bound
    (A B : NodeMatrix Node) :
    ∀ (j : ℕ) (y : RowVector Node) {K theta L alpha : ℝ} {N : ℕ → ℝ},
      0 ≤ K → 0 ≤ theta → 0 ≤ L → 0 ≤ alpha →
      (∀ n : ℕ,
        matrixEuclideanOperatorNorm (Node := Node)
            (matrixPower (Node := Node) A n) ≤
          K * theta ^ n) →
      matrixEuclideanOperatorNorm (Node := Node)
          (matrixSub (Node := Node) A B) ≤
        L * alpha →
      (∀ n : ℕ,
        rowEuclideanNorm (Node := Node)
            (matrixMulVector (Node := Node)
              (matrixPower (Node := Node) B n) y) ≤
          N n) →
      rowEuclideanNorm (Node := Node)
          (fun i =>
            matrixMulVector (Node := Node)
                (matrixPower (Node := Node) A j) y i -
              matrixMulVector (Node := Node)
                (matrixPower (Node := Node) B j) y i) ≤
        stablePowerActionDuhamelBudget K theta L alpha N j := by
  classical
  intro j y K theta L alpha N _hK _htheta _hL _halpha
    hpowerA hdiff hB_orbit
  let A' : EuclideanSpace ℝ Node →L[ℝ] EuclideanSpace ℝ Node :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) A
  let B' : EuclideanSpace ℝ Node →L[ℝ] EuclideanSpace ℝ Node :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) B
  have hrow_norm (z : RowVector Node) :
      ‖(WithLp.toLp 2 z : EuclideanSpace ℝ Node)‖ =
        rowEuclideanNorm (Node := Node) z := by
    rw [← stateFrobeniusNorm_eq_piLp_norm (Node := Node) (E := ℝ)]
    simp [rowEuclideanNorm, rowNormSq, stateFrobeniusNorm,
      frobeniusNormSq, Real.norm_eq_abs, sq_abs]
  have hop_le (C : NodeMatrix Node) :
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) C‖ ≤
        matrixEuclideanOperatorNorm (Node := Node) C := by
    apply ContinuousLinearMap.opNorm_le_bound
    · exact (matrixEuclideanOperatorNorm_spec (Node := Node) C).1
    · intro z
      rw [show z = WithLp.toLp 2 (WithLp.ofLp z) by simp,
        Matrix.toEuclideanCLM_toLp, hrow_norm, hrow_norm]
      exact rowEuclideanNorm_matrixMulVector_le
        (Node := Node) C (WithLp.ofLp z)
  have hpow_apply (C : NodeMatrix Node) (n : ℕ) (z : RowVector Node) :
      (Matrix.toEuclideanCLM (𝕜 := ℝ) C ^ n) (WithLp.toLp 2 z) =
        WithLp.toLp 2
          (matrixMulVector (Node := Node)
            (matrixPower (Node := Node) C n) z) := by
    induction n generalizing z with
    | zero =>
        rw [pow_zero, ContinuousLinearMap.one_apply, matrixPower]
        congr 1
        funext i
        simp [matrixMulVector, identityMatrix]
    | succ n ih =>
        rw [pow_succ, ContinuousLinearMap.mul_apply,
          Matrix.toEuclideanCLM_toLp, ih, matrixPower,
          matrixMulVector_matrixMul]
        congr 1
  have hpow_clm (C : NodeMatrix Node) (n : ℕ) :
      Matrix.toEuclideanCLM (𝕜 := ℝ) C ^ n =
        Matrix.toEuclideanCLM (𝕜 := ℝ)
          (matrixPower (Node := Node) C n) := by
    ext z
    rw [show z = WithLp.toLp 2 (WithLp.ofLp z) by simp,
      hpow_apply, Matrix.toEuclideanCLM_toLp]
    congr 1
  have hA_power : ∀ n : ℕ, ‖A' ^ n‖ ≤ K * theta ^ n := by
    intro n
    change ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A ^ n‖ ≤ K * theta ^ n
    calc
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A ^ n‖ =
          ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
            (matrixPower (Node := Node) A n)‖ := by rw [hpow_clm]
      _ ≤ matrixEuclideanOperatorNorm (Node := Node)
            (matrixPower (Node := Node) A n) := hop_le _
      _ ≤ K * theta ^ n := hpowerA n
  have hclm_sub :
      Matrix.toEuclideanCLM (𝕜 := ℝ)
          (matrixSub (Node := Node) A B) = A' - B' := by
    ext z
    rw [show z = WithLp.toLp 2 (WithLp.ofLp z) by simp]
    simp [A', B', matrixSub, Matrix.toEuclideanCLM_toLp, Matrix.mulVec,
      dotProduct, Finset.sum_sub_distrib, sub_mul]
  have hAB_diff : ‖A' - B'‖ ≤ L * alpha := by
    rw [← hclm_sub]
    exact (hop_le _).trans hdiff
  have hB_orbit' :
      ∀ n : ℕ, ‖(B' ^ n) (WithLp.toLp 2 y)‖ ≤ N n := by
    intro n
    change ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) B ^ n)
      (WithLp.toLp 2 y)‖ ≤ N n
    rw [hpow_apply, hrow_norm]
    exact hB_orbit n
  have hbound :=
    ContinuousLinearMap.norm_pow_apply_sub_pow_apply_le_shifted_orbit_duhamel_majorant
      A' B' j (WithLp.toLp 2 y) hA_power hAB_diff hB_orbit'
  dsimp [A', B'] at hbound
  rw [hpow_apply, hpow_apply] at hbound
  simpa [stablePowerActionDuhamelBudget, ← WithLp.toLp_sub, hrow_norm] using hbound

/-- Scalar unfolding of the indexed Duhamel budget on a geometric base orbit.

For the route-local use below the base orbit is bounded by
`N k = (K * theta^k) * M`.  The right-recursive Duhamel budget is therefore
at most linear in the lag, with the missing one power of `theta` paid for by
the positive factor `theta⁻¹`. -/
theorem stablePowerActionDuhamelBudget_geometric_orbit_le
    {K theta L alpha : ℝ}
    (hK : 0 ≤ K) (htheta_pos : 0 < theta) (hL : 0 ≤ L)
    (halpha : 0 ≤ alpha) :
    ∀ (j : ℕ) {M : ℝ}, 0 ≤ M →
      stablePowerActionDuhamelBudget K theta L alpha
          (fun k => (K * theta ^ k) * M) j ≤
        (((j : ℝ) + 1) * ((K * K * L * M) / theta)) *
          alpha * theta ^ j := by
  exact fun j M hM =>
    SOptLib.shifted_orbit_duhamel_majorant_geometric_orbit_le
      j htheta_pos hL halpha hM

/-- Local scalar absorption for the Appendix A.1 stable-impulse Duhamel
budget: the input perturbation and the indexed power perturbation together fit
inside the enlarged geometric rate. -/
theorem stablePowerActionDuhamelBudget_with_input_absorb
    {K theta L LB MB alpha theta1 Ageo : ℝ} (j : ℕ)
    (hK : 0 ≤ K) (htheta_pos : 0 < theta) (hL : 0 ≤ L)
    (hLB : 0 ≤ LB) (hMB : 0 ≤ MB) (halpha : 0 ≤ alpha)
    (hAgeo : 0 ≤ Ageo)
    (hgeom : ∀ j : ℕ, ((j : ℝ) + 1) * theta ^ j ≤ Ageo * theta1 ^ j) :
    (K * theta ^ j) * (LB * alpha) +
        stablePowerActionDuhamelBudget K theta L alpha
          (fun k => (K * theta ^ k) * MB) j ≤
      ((K * LB + (K * K * L * MB) / theta) * Ageo) *
        alpha * theta1 ^ j := by
  exact SOptLib.shifted_orbit_duhamel_majorant_add_input_le_geometric_of_linear_geometric_le
    (K := K) (theta := theta) (L := L) (inputBound := LB) (orbitBound := MB)
    (alpha := alpha) (theta1 := theta1) (geometricConstant := Ageo) j
    hK htheta_pos hL hLB hMB halpha (hgeom j)

/-- Powers of the continuous linear action induced by a node matrix agree with
the paper-local recursive matrix powers. -/
@[simp]
theorem realMatrixContinuousLinearMap_pow_apply
    (F : NodeMatrix Node) (t : ℕ) (z : RowVector Node) :
    (realMatrixContinuousLinearMap (Node := Node) F ^ t) z =
      matrixMulVector (Node := Node) (matrixPower (Node := Node) F t) z := by
  classical
  induction t generalizing z with
  | zero =>
      rw [pow_zero, ContinuousLinearMap.one_apply, matrixPower]
      funext i
      simp [matrixMulVector, identityMatrix]
  | succ t ih =>
      rw [pow_succ, ContinuousLinearMap.mul_apply, matrixPower,
        matrixMulVector_matrixMul, ih]
      have hF :
          realMatrixContinuousLinearMap (Node := Node) F z =
            matrixMulVector (Node := Node) F z := by
        rfl
      rw [hF]

/-- Closed-form Duhamel response for a stable period map with block inputs.

This is the deterministic pathwise object behind Appendix C.1's stable
component before taking expectations: a homogeneous stable response from the
initial boundary state plus the finite sum of propagated period innovations. -/
noncomputable def stablePowerDuhamelClosedResponse
    (F : NodeMatrix Node) (z0 : RowVector Node)
    (xi : ℕ → RowVector Node) (t : ℕ) : RowVector Node :=
  matrixMulVector (Node := Node) (matrixPower (Node := Node) F t) z0 +
    ∑ j ∈ Finset.range t,
      matrixMulVector (Node := Node)
        (matrixPower (Node := Node) F (t - 1 - j)) (xi j)

/-- Squared form of the concrete row Euclidean norm. -/
theorem rowEuclideanNorm_sq_eq_rowNormSq
    (w : RowVector Node) :
    rowEuclideanNorm (Node := Node) w ^ 2 =
      rowNormSq (Node := Node) w := by
  rw [rowEuclideanNorm, Real.sq_sqrt]
  unfold rowNormSq
  positivity

/-- A finite scalar row vector with coordinatewise `L²` entries has integrable
Euclidean norm square. -/
theorem rowEuclideanNorm_sq_integrable_of_coordinate_memLp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → RowVector Node}
    (hX : ∀ i : Node, MemLp (fun ω => X ω i) 2 μ) :
    Integrable
      (fun ω =>
        rowEuclideanNorm (Node := Node) (X ω) ^ 2) μ := by
  classical
  have hrow :
      Integrable (fun ω => rowNormSq (Node := Node) (X ω)) μ := by
    unfold rowNormSq
    apply integrable_finset_sum Finset.univ
    intro i _hi
    simpa [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm
        (hX i).aestronglyMeasurable).1 (hX i)
  convert hrow using 1
  funext ω
  exact rowEuclideanNorm_sq_eq_rowNormSq (Node := Node) (X ω)

/-- Coordinatewise `L²` closure of the finite Duhamel response. -/
theorem stablePowerDuhamelClosedResponse_coordinate_memLp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (F : NodeMatrix Node)
    (z0 : Ω → RowVector Node) (xi : ℕ → Ω → RowVector Node)
    (hz0 : ∀ i : Node, MemLp (fun ω => z0 ω i) 2 μ)
    (hxi : ∀ k : ℕ, ∀ i : Node, MemLp (fun ω => xi k ω i) 2 μ)
    (t : ℕ) :
    ∀ i : Node,
      MemLp
        (fun ω =>
          stablePowerDuhamelClosedResponse (Node := Node) F (z0 ω)
            (fun k => xi k ω) t i) 2 μ := by
  intro i
  simpa [SOptLib.linearDuhamelResponse, stablePowerDuhamelClosedResponse] using
    (SOptLib.linearDuhamelResponse_memLp
      (realMatrixContinuousLinearMap (Node := Node) F) z0 xi
      (MemLp.of_eval hz0) t (fun k _hk => MemLp.of_eval (hxi k))).eval i

/-- Stable-power control gives the pointwise geometric Duhamel bound for the
closed response. -/
theorem stablePowerDuhamelClosedResponse_norm_bound
    (F : NodeMatrix Node) (z0 : RowVector Node)
    (xi : ℕ → RowVector Node) {K theta : ℝ}
    (hpower :
      ∀ j : ℕ,
        matrixEuclideanOperatorNorm (Node := Node)
            (matrixPower (Node := Node) F j) ≤
          K * theta ^ j)
    (t : ℕ) :
    rowEuclideanNorm (Node := Node)
        (stablePowerDuhamelClosedResponse (Node := Node) F z0 xi t) ≤
      K * theta ^ t * rowEuclideanNorm (Node := Node) z0 +
        Finset.sum (Finset.range t) fun j =>
          K * theta ^ (t - 1 - j) *
            rowEuclideanNorm (Node := Node) (xi j) := by
  classical
  let A : EuclideanSpace ℝ Node →L[ℝ] EuclideanSpace ℝ Node :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) F
  have hrow_norm (z : RowVector Node) :
      ‖(WithLp.toLp 2 z : EuclideanSpace ℝ Node)‖ =
        rowEuclideanNorm (Node := Node) z := by
    rw [← stateFrobeniusNorm_eq_piLp_norm (Node := Node) (E := ℝ)]
    simp [rowEuclideanNorm, rowNormSq, stateFrobeniusNorm,
      frobeniusNormSq, Real.norm_eq_abs, sq_abs]
  have hpow_apply (j : ℕ) (z : RowVector Node) :
      (A ^ j) (WithLp.toLp 2 z) =
        WithLp.toLp 2
          (matrixMulVector (Node := Node)
            (matrixPower (Node := Node) F j) z) := by
    induction j generalizing z with
    | zero =>
        rw [pow_zero, ContinuousLinearMap.one_apply, matrixPower]
        congr 1
        funext i
        simp [matrixMulVector, identityMatrix]
    | succ j ih =>
        rw [pow_succ, ContinuousLinearMap.mul_apply]
        have hAz :
            A (WithLp.toLp 2 z) =
              WithLp.toLp 2 (matrixMulVector (Node := Node) F z) := by
          change Matrix.toEuclideanCLM (𝕜 := ℝ) F (WithLp.toLp 2 z) = _
          rw [Matrix.toEuclideanCLM_toLp]
          congr 1
        rw [hAz, ih, matrixPower, matrixMulVector_matrixMul]
  have hA_power : ∀ j : ℕ, ‖A ^ j‖ ≤ K * theta ^ j := by
    intro j
    apply ContinuousLinearMap.opNorm_le_bound
    · exact le_trans
        ((matrixEuclideanOperatorNorm_spec (Node := Node)
          (matrixPower (Node := Node) F j)).1) (hpower j)
    · intro x
      rw [show x = WithLp.toLp 2 (WithLp.ofLp x) by simp, hpow_apply,
        hrow_norm, hrow_norm]
      exact matrixPower_action_norm_bound (Node := Node) F (WithLp.ofLp x) j
        (K := K) (theta := theta)
        (M := rowEuclideanNorm (Node := Node) (WithLp.ofLp x))
        (hpower j) le_rfl
  simpa [SOptLib.linearDuhamelResponse, stablePowerDuhamelClosedResponse,
    hpow_apply, hrow_norm] using
    (SOptLib.linearDuhamelResponse_norm_le_geometric_convolution
      A (WithLp.toLp 2 z0) (fun j => WithLp.toLp 2 (xi j)) hA_power t)

/-- Deterministic square-sum stable Duhamel estimate obtained by applying
Lemma B.1 to the closed stable response. -/
theorem stablePowerDuhamelClosedResponse_square_sum_le
    (F : NodeMatrix Node) (z0 : RowVector Node)
    (xi : ℕ → RowVector Node) {K theta : ℝ}
    (hK : 0 ≤ K) (htheta_pos : 0 < theta) (htheta_lt_one : theta < 1)
    (hpower :
      ∀ j : ℕ,
        matrixEuclideanOperatorNorm (Node := Node)
            (matrixPower (Node := Node) F j) ≤
          K * theta ^ j)
    (N : ℕ) :
    Finset.sum (Finset.range (N + 1)) (fun t =>
      rowEuclideanNorm (Node := Node)
          (stablePowerDuhamelClosedResponse (Node := Node) F z0 xi t) ^ 2) ≤
      (2 * K ^ 2 / (1 - theta ^ 2)) *
          (rowEuclideanNorm (Node := Node) z0) ^ 2 +
        (2 * K ^ 2 / (1 - theta) ^ 2) *
          Finset.sum (Finset.range N) (fun j =>
            (rowEuclideanNorm (Node := Node) (xi j)) ^ 2) := by
  classical
  let A : EuclideanSpace ℝ Node →L[ℝ] EuclideanSpace ℝ Node :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) F
  have hrow_norm (z : RowVector Node) :
      ‖(WithLp.toLp 2 z : EuclideanSpace ℝ Node)‖ =
        rowEuclideanNorm (Node := Node) z := by
    rw [← stateFrobeniusNorm_eq_piLp_norm (Node := Node) (E := ℝ)]
    simp [rowEuclideanNorm, rowNormSq, stateFrobeniusNorm,
      frobeniusNormSq, Real.norm_eq_abs, sq_abs]
  have hpow_apply (j : ℕ) (z : RowVector Node) :
      (A ^ j) (WithLp.toLp 2 z) =
        WithLp.toLp 2
          (matrixMulVector (Node := Node)
            (matrixPower (Node := Node) F j) z) := by
    induction j generalizing z with
    | zero =>
        rw [pow_zero, ContinuousLinearMap.one_apply, matrixPower]
        congr 1
        funext i
        simp [matrixMulVector, identityMatrix]
    | succ j ih =>
        rw [pow_succ, ContinuousLinearMap.mul_apply]
        have hAz :
            A (WithLp.toLp 2 z) =
              WithLp.toLp 2 (matrixMulVector (Node := Node) F z) := by
          change Matrix.toEuclideanCLM (𝕜 := ℝ) F (WithLp.toLp 2 z) = _
          rw [Matrix.toEuclideanCLM_toLp]
          congr 1
        rw [hAz, ih, matrixPower, matrixMulVector_matrixMul]
  have hA_power : ∀ j ≤ N, ‖A ^ j‖ ≤ K * theta ^ j := by
    intro j _
    apply ContinuousLinearMap.opNorm_le_bound
    · exact le_trans
        ((matrixEuclideanOperatorNorm_spec (Node := Node)
          (matrixPower (Node := Node) F j)).1) (hpower j)
    · intro x
      rw [show x = WithLp.toLp 2 (WithLp.ofLp x) by simp, hpow_apply,
        hrow_norm, hrow_norm]
      exact matrixPower_action_norm_bound (Node := Node) F (WithLp.ofLp x) j
        (K := K) (theta := theta)
        (M := rowEuclideanNorm (Node := Node) (WithLp.ofLp x))
        (hpower j) le_rfl
  have hresponse (t : ℕ) :
      SOptLib.linearDuhamelResponse A (WithLp.toLp 2 z0)
          (fun j => WithLp.toLp 2 (xi j)) t =
        WithLp.toLp 2
          (stablePowerDuhamelClosedResponse (Node := Node) F z0 xi t) := by
    simp_rw [SOptLib.linearDuhamelResponse,
      stablePowerDuhamelClosedResponse, hpow_apply]
    simp
  simpa only [hresponse, hrow_norm] using
    (SOptLib.linearDuhamelResponse_sum_norm_sq_le
      A (WithLp.toLp 2 z0) (fun j => WithLp.toLp 2 (xi j))
      htheta_pos.le htheta_lt_one N hA_power)

/-- Direct stable-impulse bound from a stable power estimate and a uniform
bound on the concrete phase-input channels. -/
theorem twoStepCounterexampleStableImpulseFrom_le_power_input_bound
    (F : ℝ → NodeMatrix (Fin 3)) (epsilon lambda alpha : ℝ)
    (phase : TwoStepPhase) (j : ℕ) {K theta MB : ℝ}
    (hK : 0 ≤ K) (htheta : 0 ≤ theta) (hMB : 0 ≤ MB)
    (hpower :
      matrixEuclideanOperatorNorm (Node := Fin 3)
          (matrixPower (Node := Fin 3) (F alpha) j) ≤
        K * theta ^ j)
    (hinput :
      ∀ node : Bool,
        rowEuclideanNorm (Node := Fin 3)
            (twoStepCounterexamplePhaseInputChannel
              epsilon lambda alpha phase node) ≤
          MB) :
    twoStepCounterexampleStableImpulseFrom F epsilon lambda alpha phase j ≤
      2 * ((K * theta ^ j) * MB) := by
  classical
  unfold twoStepCounterexampleStableImpulseFrom
  apply rowEuclideanNorm_bool_le_of_abs_le
  · exact mul_nonneg (mul_nonneg hK (pow_nonneg htheta j)) hMB
  · intro node
    calc
      |twoStepCounterexampleStableImpulseVectorFrom F epsilon lambda alpha phase j node| =
          |twoStepCounterexampleArithmeticAverageOutput
            (matrixMulVector (Node := Fin 3)
              (matrixPower (Node := Fin 3) (F alpha) j)
              (twoStepCounterexamplePhaseInputChannel
                epsilon lambda alpha phase node))| := by
            rfl
      _ ≤ rowEuclideanNorm (Node := Fin 3)
            (matrixMulVector (Node := Fin 3)
              (matrixPower (Node := Fin 3) (F alpha) j)
              (twoStepCounterexamplePhaseInputChannel
                epsilon lambda alpha phase node)) :=
            twoStepCounterexampleArithmeticAverageOutput_abs_le_rowEuclideanNorm _
      _ ≤ (K * theta ^ j) * MB :=
            matrixPower_action_norm_bound (Node := Fin 3) (F alpha)
              (twoStepCounterexamplePhaseInputChannel
                epsilon lambda alpha phase node)
              j (K := K) (theta := theta) (M := MB)
              hpower (hinput node)

/-- Appendix A.1 source bridge for the stable impulse response after enlarging
the geometric rate.

The finite-coordinate base cancellation is proved above. The remaining
source-level content is the analytic perturbation/telescoping argument that
lifts the exact `alpha = 0` cancellation to a uniform `O(alpha * theta1^j)`
bound, using the stable-power field from `PeriodicSpectralSplitting`. -/
theorem two_step_counterexample_stable_impulse_alpha_geometric_bound
    (epsilon lambda alpha0 theta K theta1 : ℝ)
    (right0 left0 : RowVector (Fin 3))
    (gamma : ℝ → ℝ) (P F : ℝ → NodeMatrix (Fin 3))
    (hepsilon_pos : 0 < epsilon) (hepsilon_lt : epsilon < 1)
    (hbaseEigen :
      IsRightUnitEigenvector (Node := Fin 3)
        (twoStepCounterexamplePropagator epsilon lambda 0) right0 ∧
        IsLeftUnitEigenvector (Node := Fin 3)
          (twoStepCounterexamplePropagator epsilon lambda 0) left0 ∧
          rowDot (Node := Fin 3) left0 right0 = 1)
    (hspectrum :
      SimpleIsolatedUnitEigenvalueStableSpectrum (Node := Fin 3)
        (twoStepCounterexamplePropagator epsilon lambda 0) (1 / 2)
        right0 left0)
    (hanalytic :
      RealAnalyticMatrixFamilyNear (Node := Fin 3)
        (fun alpha => twoStepCounterexamplePropagator epsilon lambda alpha) 1)
    (hsplitting :
      PeriodicSpectralSplitting (Node := Fin 3)
        (fun alpha => twoStepCounterexamplePropagator epsilon lambda alpha)
        (1 / 2) alpha0 theta K right0 left0 gamma P F)
    (htheta_lt_theta1 : theta < theta1)
    (htheta1_lt_one : theta1 < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ alpha phase j, 0 ≤ alpha → alpha ≤ alpha0 →
        twoStepCounterexampleStableImpulseFrom F epsilon lambda alpha phase j ≤
          C * alpha * theta1 ^ j := by
  classical
  have hzero_vec :
      ∀ phase j,
        twoStepCounterexampleStableImpulseVectorFrom F epsilon lambda 0 phase j =
          (fun _ : Bool => 0) :=
    two_step_counterexample_stable_impulse_vector_zero_alpha_all_lags
      epsilon lambda alpha0 theta K right0 left0 gamma P F
      hepsilon_pos hepsilon_lt hsplitting
  have hzero_all :
      ∀ phase j,
        twoStepCounterexampleStableImpulseFrom F epsilon lambda 0 phase j = 0 :=
    two_step_counterexample_stable_impulse_zero_alpha_all_lags
      epsilon lambda alpha0 theta K right0 left0 gamma P F
      hepsilon_pos hepsilon_lt hsplitting
  obtain ⟨δF, LF, hδF_pos, hLF_nonneg, hF_lip⟩ :
      ∃ δ LF : ℝ, 0 < δ ∧ 0 ≤ LF ∧
        ∀ alpha : ℝ, 0 ≤ alpha → alpha ≤ δ →
          matrixEuclideanOperatorNorm (Node := Fin 3)
              (matrixSub (Node := Fin 3) (F alpha) (F 0)) ≤
            LF * alpha :=
    spectralSplitting_stableComplement_local_operator_lipschitz_at_zero
      (Node := Fin 3)
      (fun alpha => twoStepCounterexamplePropagator epsilon lambda alpha)
      1 (1 / 2) alpha0 theta K right0 left0 gamma P F
      hanalytic hsplitting
  have hB_lip :
      ∀ phase node,
        ∃ δB LB : ℝ, 0 < δB ∧ 0 ≤ LB ∧
          ∀ alpha : ℝ, 0 ≤ alpha → alpha ≤ δB →
            rowEuclideanNorm (Node := Fin 3)
                (fun i =>
                  twoStepCounterexamplePhaseInputChannel
                      epsilon lambda alpha phase node i -
                    twoStepCounterexamplePhaseInputChannel
                      epsilon lambda 0 phase node i) ≤
              LB * alpha := by
    intro phase node
    exact two_step_counterexample_phase_input_channel_lipschitz_at_zero
      epsilon lambda phase node
  rcases hsplitting with
    ⟨halpha0_pos, _hr0_theta, _htheta_lt_one, _hK_nonneg, _hgamma0,
      _hgamma_analytic, _hP_analytic, _hderiv, hlocal⟩
  obtain ⟨δB, LB, hδB_pos, hLB_nonneg, hB_uniform_lip⟩ :=
    two_step_counterexample_phase_input_channel_uniform_lipschitz_at_zero
      epsilon lambda hB_lip
  obtain ⟨MB, hMB_nonneg, hB_bound⟩ :=
    two_step_counterexample_phase_input_channel_bound_on_interval
      epsilon lambda alpha0 halpha0_pos
  have htheta_pos : 0 < theta := by
    linarith [_hr0_theta]
  obtain ⟨Ageo, hAgeo_nonneg, hgeom_absorb⟩ :=
    one_plus_nat_mul_geometric_absorb
      (theta := theta) (theta1 := theta1) htheta_pos htheta_lt_theta1
  have hzero_lag :
      ∀ phase : TwoStepPhase,
        twoStepCounterexampleStableImpulseFrom F epsilon lambda 0 phase 0 = 0 := by
    intro phase
    exact hzero_all phase 0
  have hbase_local :
      IsRieszProjectionAtEigenvalue (Node := Fin 3)
          (twoStepCounterexamplePropagator epsilon lambda 0) (gamma 0) (P 0) ∧
        twoStepCounterexamplePropagator epsilon lambda 0 =
          matrixAdd (Node := Fin 3) ((gamma 0) • P 0) (F 0) ∧
          matrixMul (Node := Fin 3) (P 0) (F 0) = 0 ∧
            matrixMul (Node := Fin 3) (F 0) (P 0) = 0 ∧
              ∀ j : ℕ,
                matrixEuclideanOperatorNorm (Node := Fin 3)
                    (matrixPower (Node := Fin 3) (F 0) j) ≤
                  K * theta ^ j := by
    simpa using hlocal 0 (by simpa [abs_of_nonneg halpha0_pos.le] using halpha0_pos.le)
  have hpower0 := hbase_local.2.2.2.2
  have hinput_perturbation_term :
      ∀ alpha phase node j, 0 ≤ alpha → alpha ≤ alpha0 → alpha ≤ δB →
        rowEuclideanNorm (Node := Fin 3)
            (fun i =>
              matrixMulVector (Node := Fin 3)
                  (matrixPower (Node := Fin 3) (F alpha) j)
                  (twoStepCounterexamplePhaseInputChannel
                    epsilon lambda alpha phase node) i -
                matrixMulVector (Node := Fin 3)
                  (matrixPower (Node := Fin 3) (F alpha) j)
                  (twoStepCounterexamplePhaseInputChannel
                    epsilon lambda 0 phase node) i) ≤
          (K * theta ^ j) * (LB * alpha) := by
    intro alpha phase node j halpha_nonneg halpha_le_alpha0 halpha_le_δB
    have hloc := hlocal alpha (by
      rw [abs_of_nonneg halpha_nonneg]
      exact halpha_le_alpha0)
    exact
      matrixPower_input_perturbation_bound
        (Node := Fin 3) (A := F alpha)
        (x := twoStepCounterexamplePhaseInputChannel
          epsilon lambda alpha phase node)
        (y := twoStepCounterexamplePhaseInputChannel
          epsilon lambda 0 phase node)
        (j := j) (K := K) (theta := theta) (L := LB) (alpha := alpha)
        _hK_nonneg htheta_pos.le hLB_nonneg halpha_nonneg
        (hloc.2.2.2.2 j)
        (hB_uniform_lip phase node alpha halpha_nonneg halpha_le_δB)
  have hpower_perturbation_term :
      ∀ alpha phase node j, 0 ≤ alpha → alpha ≤ alpha0 → alpha ≤ δF →
        rowEuclideanNorm (Node := Fin 3)
            (fun i =>
              matrixMulVector (Node := Fin 3)
                  (matrixPower (Node := Fin 3) (F alpha) j)
                  (twoStepCounterexamplePhaseInputChannel
                    epsilon lambda 0 phase node) i -
                matrixMulVector (Node := Fin 3)
                  (matrixPower (Node := Fin 3) (F 0) j)
                  (twoStepCounterexamplePhaseInputChannel
                    epsilon lambda 0 phase node) i) ≤
          stablePowerActionDuhamelBudget K theta LF alpha
            (fun k => (K * theta ^ k) * MB) j := by
    intro alpha phase node j halpha_nonneg halpha_le_alpha0 halpha_le_δF
    have hloc := hlocal alpha (by
      rw [abs_of_nonneg halpha_nonneg]
      exact halpha_le_alpha0)
    have hbase_input :
        rowEuclideanNorm (Node := Fin 3)
            (twoStepCounterexamplePhaseInputChannel
              epsilon lambda 0 phase node) ≤
          MB := by
      exact hB_bound 0 phase node le_rfl halpha0_pos.le
    have hbase_orbit :
        ∀ n : ℕ,
          rowEuclideanNorm (Node := Fin 3)
              (matrixMulVector (Node := Fin 3)
                (matrixPower (Node := Fin 3) (F 0) n)
                (twoStepCounterexamplePhaseInputChannel
                  epsilon lambda 0 phase node)) ≤
            (K * theta ^ n) * MB := by
      intro n
      exact
        matrixPower_action_norm_bound (Node := Fin 3) (F 0)
          (twoStepCounterexamplePhaseInputChannel
            epsilon lambda 0 phase node)
          n (K := K) (theta := theta) (M := MB)
          (hpower0 n) hbase_input
    exact
      matrixPower_stable_power_action_duhamel_budget_bound
        (Node := Fin 3) (F alpha) (F 0) j
        (twoStepCounterexamplePhaseInputChannel
          epsilon lambda 0 phase node)
        _hK_nonneg htheta_pos.le hLF_nonneg halpha_nonneg
        (hloc.2.2.2.2)
        (hF_lip alpha halpha_nonneg halpha_le_δF)
        hbase_orbit
  have haction_diff_term :
      ∀ alpha phase node j,
        0 ≤ alpha → alpha ≤ alpha0 → alpha ≤ δB → alpha ≤ δF →
        rowEuclideanNorm (Node := Fin 3)
            (fun i =>
              matrixMulVector (Node := Fin 3)
                  (matrixPower (Node := Fin 3) (F alpha) j)
                  (twoStepCounterexamplePhaseInputChannel
                    epsilon lambda alpha phase node) i -
                matrixMulVector (Node := Fin 3)
                  (matrixPower (Node := Fin 3) (F 0) j)
                  (twoStepCounterexamplePhaseInputChannel
                    epsilon lambda 0 phase node) i) ≤
          (K * theta ^ j) * (LB * alpha) +
            stablePowerActionDuhamelBudget K theta LF alpha
              (fun k => (K * theta ^ k) * MB) j := by
    intro alpha phase node j halpha_nonneg halpha_le_alpha0 halpha_le_δB
      halpha_le_δF
    exact
      matrixPower_action_diff_split_bound
        (Node := Fin 3)
        (A := matrixPower (Node := Fin 3) (F alpha) j)
        (B := matrixPower (Node := Fin 3) (F 0) j)
        (x := twoStepCounterexamplePhaseInputChannel
          epsilon lambda alpha phase node)
        (y := twoStepCounterexamplePhaseInputChannel
          epsilon lambda 0 phase node)
        (Rinput := (K * theta ^ j) * (LB * alpha))
        (Rpower := stablePowerActionDuhamelBudget K theta LF alpha
          (fun k => (K * theta ^ k) * MB) j)
        (hinput_perturbation_term alpha phase node j
          halpha_nonneg halpha_le_alpha0 halpha_le_δB)
        (hpower_perturbation_term alpha phase node j
          halpha_nonneg halpha_le_alpha0 halpha_le_δF)
  let δlocal : ℝ := min δB δF
  have hδlocal_pos : 0 < δlocal := lt_min hδB_pos hδF_pos
  have htheta1_pos : 0 < theta1 := lt_trans htheta_pos htheta_lt_theta1
  let Clocal : ℝ := (K * LB + (K * K * LF * MB) / theta) * Ageo
  have hClocal_nonneg : 0 ≤ Clocal := by
    have hdiv_nonneg : 0 ≤ (K * K * LF * MB) / theta := by
      exact div_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg _hK_nonneg _hK_nonneg)
          hLF_nonneg) hMB_nonneg) htheta_pos.le
    dsimp [Clocal]
    exact mul_nonneg (add_nonneg (mul_nonneg _hK_nonneg hLB_nonneg) hdiv_nonneg)
      hAgeo_nonneg
  have hlocal_linear :
      ∀ alpha (p : TwoStepPhase × ℕ),
        0 ≤ alpha → alpha ≤ alpha0 → alpha ≤ δlocal →
          twoStepCounterexampleStableImpulseFrom
              F epsilon lambda alpha p.1 p.2 ≤
            (2 * Clocal) * alpha * theta1 ^ p.2 := by
    intro alpha p halpha_nonneg halpha_le_alpha0 hlocal_alpha
    rcases p with ⟨phase, j⟩
    have htheta1_pow_nonneg : 0 ≤ theta1 ^ j :=
      pow_nonneg htheta1_pos.le j
    have halpha_le_δB : alpha ≤ δB :=
      le_trans hlocal_alpha (min_le_left δB δF)
    have halpha_le_δF : alpha ≤ δF :=
      le_trans hlocal_alpha (min_le_right δB δF)
    have hlocal_scalar :
        (K * theta ^ j) * (LB * alpha) +
            stablePowerActionDuhamelBudget K theta LF alpha
              (fun k => (K * theta ^ k) * MB) j ≤
          Clocal * alpha * theta1 ^ j := by
      dsimp [Clocal]
      exact
        stablePowerActionDuhamelBudget_with_input_absorb
          (K := K) (theta := theta) (L := LF) (LB := LB)
          (MB := MB) (alpha := alpha) (theta1 := theta1)
          (Ageo := Ageo) j _hK_nonneg htheta_pos hLF_nonneg
          hLB_nonneg hMB_nonneg halpha_nonneg hAgeo_nonneg hgeom_absorb
    have hB_nonneg : 0 ≤ Clocal * alpha * theta1 ^ j :=
      mul_nonneg (mul_nonneg hClocal_nonneg halpha_nonneg) htheta1_pow_nonneg
    have hcoord :
        ∀ node : Bool,
          rowEuclideanNorm (Node := Fin 3)
              (fun i =>
                matrixMulVector (Node := Fin 3)
                    (matrixPower (Node := Fin 3) (F alpha) j)
                    (twoStepCounterexamplePhaseInputChannel
                      epsilon lambda alpha phase node) i -
                  matrixMulVector (Node := Fin 3)
                    (matrixPower (Node := Fin 3) (F 0) j)
                    (twoStepCounterexamplePhaseInputChannel
                      epsilon lambda 0 phase node) i) ≤
            Clocal * alpha * theta1 ^ j := by
      intro node
      exact le_trans
        (haction_diff_term alpha phase node j halpha_nonneg
          halpha_le_alpha0 halpha_le_δB halpha_le_δF)
        hlocal_scalar
    have himpulse :=
      twoStepCounterexampleStableImpulseFrom_le_of_action_diff_bound
        F epsilon lambda alpha phase j (B := Clocal * alpha * theta1 ^ j)
        hB_nonneg (hzero_vec phase j) hcoord
    calc
      twoStepCounterexampleStableImpulseFrom F epsilon lambda alpha phase j ≤
          2 * (Clocal * alpha * theta1 ^ j) := himpulse
      _ = (2 * Clocal) * alpha * theta1 ^ j := by ring
  have huniform_geometric :
      ∀ alpha (p : TwoStepPhase × ℕ),
        0 ≤ alpha → alpha ≤ alpha0 →
          twoStepCounterexampleStableImpulseFrom
              F epsilon lambda alpha p.1 p.2 ≤
            (2 * K * MB * Ageo) * theta1 ^ p.2 := by
    intro alpha p halpha_nonneg halpha_le_alpha0
    rcases p with ⟨phase, j⟩
    have hloc := hlocal alpha (by
      rw [abs_of_nonneg halpha_nonneg]
      exact halpha_le_alpha0)
    have hinput_bound :
        ∀ node : Bool,
          rowEuclideanNorm (Node := Fin 3)
              (twoStepCounterexamplePhaseInputChannel
                epsilon lambda alpha phase node) ≤
            MB := by
      intro node
      exact hB_bound alpha phase node halpha_nonneg halpha_le_alpha0
    have himpulse_raw :=
      twoStepCounterexampleStableImpulseFrom_le_power_input_bound
        F epsilon lambda alpha phase j _hK_nonneg htheta_pos.le hMB_nonneg
        (hloc.2.2.2.2 j) hinput_bound
    have hpow_nonneg : 0 ≤ theta ^ j := pow_nonneg htheta_pos.le j
    have hj_factor : theta ^ j ≤ ((j : ℝ) + 1) * theta ^ j := by
      have hj_one : 1 ≤ (j : ℝ) + 1 := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
      calc
        theta ^ j = 1 * theta ^ j := by ring
        _ ≤ ((j : ℝ) + 1) * theta ^ j :=
          mul_le_mul_of_nonneg_right hj_one hpow_nonneg
    have htheta_to_theta1 : theta ^ j ≤ Ageo * theta1 ^ j :=
      le_trans hj_factor (hgeom_absorb j)
    have hcoef_nonneg : 0 ≤ 2 * K * MB := by
      exact mul_nonneg (mul_nonneg (by norm_num) _hK_nonneg) hMB_nonneg
    calc
      twoStepCounterexampleStableImpulseFrom F epsilon lambda alpha phase j ≤
          2 * ((K * theta ^ j) * MB) := himpulse_raw
      _ = (2 * K * MB) * theta ^ j := by ring
      _ ≤ (2 * K * MB) * (Ageo * theta1 ^ j) :=
        mul_le_mul_of_nonneg_left htheta_to_theta1 hcoef_nonneg
      _ = (2 * K * MB * Ageo) * theta1 ^ j := by ring
  obtain ⟨C, hC_nonneg, hglobal⟩ :=
    exists_global_linear_bound_of_local_linear_and_uniform_bound
      (response := fun alpha (p : TwoStepPhase × ℕ) =>
        twoStepCounterexampleStableImpulseFrom
          F epsilon lambda alpha p.1 p.2)
      (weight := fun p : TwoStepPhase × ℕ => theta1 ^ p.2)
      (alphaMax := alpha0) (delta := δlocal)
      (Clocal := 2 * Clocal) (Cuniform := 2 * K * MB * Ageo)
      hδlocal_pos (fun p => pow_nonneg htheta1_pos.le p.2)
      hlocal_linear huniform_geometric
  refine ⟨C, hC_nonneg, ?_⟩
  intro alpha phase j halpha_nonneg halpha_le_alpha0
  exact hglobal alpha (phase, j) halpha_nonneg halpha_le_alpha0

/-- The concrete two-step counterexample propagator is a real-analytic
finite-entry matrix family near the base point. -/
theorem two_step_counterexample_propagator_analytic_near_zero
    (epsilon lambda : ℝ) :
    RealAnalyticMatrixFamilyNear (Node := Fin 3)
      (fun alpha => twoStepCounterexamplePropagator epsilon lambda alpha) 1 := by
  classical
  refine ⟨by norm_num, ?_⟩
  intro alpha _halpha
  apply AnalyticAt.pi
  intro i
  apply AnalyticAt.pi
  intro j
  fin_cases i <;> fin_cases j <;>
    simp [twoStepCounterexamplePropagator, twoStepCounterexampleLiftedStep,
      twoNodeCounterexamplePush, twoNodeCounterexamplePullA,
      twoNodeCounterexamplePullB, matrixMul, Fin.sum_univ_succ,
      Fin.sum_univ_two] <;>
    fun_prop

/-- One-dimensional analytic Taylor remainder at first order, in the
`O(alpha^2)` form used by the Appendix A.1 slow multiplier expansion. -/
theorem analyticAt_scalar_first_order_remainder_isBigO_sq
    {f : ℝ → ℝ} {c d : ℝ}
    (hf : AnalyticAt ℝ f 0) (hf0 : f 0 = c)
    (hderiv : HasDerivAt f d 0) :
    Asymptotics.IsBigO (nhds 0)
      (fun alpha => f alpha - (c + alpha * d))
      (fun alpha => alpha ^ 2) := by
  simpa using analyticAt_sub_linearization_isBigO_sq (x₀ := 0) hf hf0 hderiv

/-- T1 bridge for Appendix A.1: the slow multiplier quadratic remainder
follows from Lemma A.1's spectral splitting once the concrete derivative
pairing for the selected left/right eigenvectors has been identified. -/
theorem two_step_counterexample_slow_multiplier_bigO_of_deriv_pairing
    (epsilon lambda alpha0 theta K : ℝ)
    (right left : RowVector (Fin 3))
    (gamma : ℝ → ℝ) (P F : ℝ → NodeMatrix (Fin 3))
    (hsplitting :
      PeriodicSpectralSplitting (Node := Fin 3)
        (fun alpha => twoStepCounterexamplePropagator epsilon lambda alpha)
        (1 / 2) alpha0 theta K right left gamma P F)
    (hpair :
      ∀ Aderiv : NodeMatrix (Fin 3),
        HasDerivAt
          (fun alpha => twoStepCounterexamplePropagator epsilon lambda alpha)
          Aderiv 0 →
        rowDot (Node := Fin 3) left
          (matrixMulVector (Node := Fin 3) Aderiv right) =
          -2 * lambda * twoStepCounterexampleSpectralSlope epsilon) :
    Asymptotics.IsBigO (nhds 0)
      (fun alpha =>
        gamma alpha -
          twoStepSlowMultiplierApprox lambda
            (twoStepCounterexampleSpectralSlope epsilon) alpha)
      (fun alpha => alpha ^ 2) := by
  rcases hsplitting with
    ⟨halpha0_pos, _hr0theta, _htheta_lt_one, _hK_nonneg,
      hgamma0, hgamma_analytic, _hP_analytic, hderiv, _hlocal⟩
  rcases hderiv with ⟨Aderiv, hAderiv, hgamma_deriv⟩
  have hgamma_analytic0 : AnalyticAt ℝ gamma 0 := by
    exact hgamma_analytic 0 (by simpa using halpha0_pos)
  have hgamma_deriv_slow :
      HasDerivAt gamma
        (-2 * lambda * twoStepCounterexampleSpectralSlope epsilon) 0 := by
    simpa [hpair Aderiv hAderiv] using hgamma_deriv
  have hO :=
    analyticAt_scalar_first_order_remainder_isBigO_sq
      hgamma_analytic0 hgamma0 hgamma_deriv_slow
  refine hO.congr ?_ (fun _ => rfl)
  intro alpha
  unfold twoStepSlowMultiplierApprox
  ring

/-- The second stable eigenvalue printed in Appendix A.1 lies in the
`1 / 2` spectral disk throughout the counterexample parameter range. -/
theorem two_step_counterexample_base_product_eigenvalue_abs_le_half
    (epsilon : ℝ) (_hepsilon_pos : 0 < epsilon)
    (hepsilon_lt : epsilon < 1) :
    |(1 / 2 - epsilon) * (3 / 4 - epsilon)| ≤ (1 / 2 : ℝ) := by
  have hepsilon_nonneg : 0 ≤ epsilon := le_of_lt _hepsilon_pos
  have hfirst : |1 / 2 - epsilon| ≤ (1 / 2 : ℝ) := by
    rw [abs_sub_le_iff]
    constructor <;> linarith
  have hsecond : |3 / 4 - epsilon| ≤ (3 / 4 : ℝ) := by
    rw [abs_sub_le_iff]
    constructor <;> linarith
  calc
    |(1 / 2 - epsilon) * (3 / 4 - epsilon)| =
        |1 / 2 - epsilon| * |3 / 4 - epsilon| := by
          rw [abs_mul]
    _ ≤ (1 / 2 : ℝ) * (3 / 4 : ℝ) := by
          exact mul_le_mul hfirst hsecond (abs_nonneg _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) := by norm_num

/-- The concrete phase-noise expression is definitionally equal to the printed
Appendix A.1 approximation, hence has zero cubic remainder. -/
theorem two_step_counterexample_phase_noise_bigO
    (epsilon : ℝ) :
    Asymptotics.IsBigO (nhds 0)
      (fun alpha =>
        twoStepCounterexamplePhaseNoise epsilon alpha -
          twoStepPhaseNoiseApprox
            (twoStepCounterexampleNoiseCoefficient epsilon) alpha)
      (fun alpha => alpha ^ 3) := by
  simpa [twoStepCounterexamplePhaseNoise, twoStepPhaseNoiseApprox] using
    (Asymptotics.isBigO_zero
      (fun alpha : ℝ => alpha ^ 3) (nhds (0 : ℝ)))

/-- Characteristic determinant of the Appendix A.1 base two-step matrix in
the reduced three-dimensional coordinates. -/
theorem two_step_counterexample_base_resolvent_det_formula
    (epsilon lambda : ℝ) (z : ℂ) :
    Matrix.det
        (complexResolventMatrix (Node := Fin 3)
          (twoStepCounterexamplePropagator epsilon lambda 0) z) =
      (z - 1) * (z - ((1 / 4 : ℝ) : ℂ)) *
        (z - (((1 / 2 - epsilon) * (3 / 4 - epsilon) : ℝ) : ℂ)) := by
  classical
  rw [Matrix.det_fin_three]
  simp [complexResolventMatrix, complexMatrixSub, complexIdentityMatrix,
    complexOfRealMatrix, twoStepCounterexamplePropagator,
    twoStepCounterexampleLiftedStep, twoNodeCounterexamplePush,
    twoNodeCounterexamplePullA, twoNodeCounterexamplePullB, matrixMul,
    Fin.sum_univ_succ, Fin.sum_univ_two]
  ring

/-- Appendix A.1 eigenvalue classification for the concrete base matrix:
every complex right eigenvalue is one of the three printed spectral values. -/
theorem two_step_counterexample_base_eigenvalue_classification
    (epsilon lambda : ℝ) {z : ℂ}
    (hz :
      IsComplexRightEigenvalue (Node := Fin 3)
        (twoStepCounterexamplePropagator epsilon lambda 0) z) :
    z = (1 : ℂ) ∨ z = ((1 / 4 : ℝ) : ℂ) ∨
      z = (((1 / 2 - epsilon) * (3 / 4 - epsilon) : ℝ) : ℂ) := by
  classical
  rcases hz with ⟨v, hvne, hv⟩
  have hkernel :
      complexNodeMatrixMulVector (Node := Fin 3)
          (complexResolventMatrix (Node := Fin 3)
            (twoStepCounterexamplePropagator epsilon lambda 0) z) v = 0 := by
    exact
      (complexResolventMatrix_mulVec_eq_zero_iff_eigen
        (Node := Fin 3)
        (twoStepCounterexamplePropagator epsilon lambda 0) z v).2 hv
  have hdet_zero :
      Matrix.det
          (complexResolventMatrix (Node := Fin 3)
            (twoStepCounterexamplePropagator epsilon lambda 0) z) = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff
      (M := complexResolventMatrix (Node := Fin 3)
        (twoStepCounterexamplePropagator epsilon lambda 0) z)]
    exact ⟨v, hvne, by simpa [complexNodeMatrixMulVector] using hkernel⟩
  rw [two_step_counterexample_base_resolvent_det_formula] at hdet_zero
  rcases mul_eq_zero.mp hdet_zero with hleft | hthird
  · rcases mul_eq_zero.mp hleft with hone | hquarter
    · exact Or.inl (sub_eq_zero.mp hone)
    · exact Or.inr (Or.inl (sub_eq_zero.mp hquarter))
  · exact Or.inr (Or.inr (sub_eq_zero.mp hthird))

/-- Stable-spectrum half-disk consequence of the Appendix A.1 eigenvalue
classification for the concrete base matrix. -/
theorem two_step_counterexample_base_stable_spectrum_le_half
    (epsilon lambda : ℝ) (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt : epsilon < 1) :
    ∀ z : ℂ,
      IsComplexRightEigenvalue (Node := Fin 3)
        (twoStepCounterexamplePropagator epsilon lambda 0) z →
        z ≠ (1 : ℂ) → ‖z‖ ≤ (1 / 2 : ℝ) := by
  intro z hz hz_ne_one
  rcases two_step_counterexample_base_eigenvalue_classification
      epsilon lambda hz with hz_one | hz_stable
  · exact False.elim (hz_ne_one hz_one)
  · rcases hz_stable with hz_quarter | hz_product
    · subst z
      norm_num
    · subst z
      have hreal :
          |(1 / 2 - epsilon) * (3 / 4 - epsilon)| ≤ (1 / 2 : ℝ) :=
        two_step_counterexample_base_product_eigenvalue_abs_le_half
          epsilon hepsilon_pos hepsilon_lt
      have hnorm :
          ‖(((1 / 2 - epsilon) * (3 / 4 - epsilon) : ℝ) : ℂ)‖ =
            |(1 / 2 - epsilon) * (3 / 4 - epsilon)| := by
        simpa [Real.norm_eq_abs] using
          (Complex.norm_real
            ((1 / 2 - epsilon) * (3 / 4 - epsilon)))
      rw [hnorm]
      exact hreal

/-- Scalar rational identity for the tracker coordinate of the Appendix A.1
zeroth-order right eigenvector. -/
theorem two_step_counterexample_right_tracker_coordinate_identity
    (epsilon lambda : ℝ)
    (hden : -5 - epsilon * 10 + epsilon ^ 2 * 8 ≠ 0) :
    -(lambda * 5) + lambda * epsilon * 18 -
              lambda * epsilon * (-5 - epsilon * 10 + epsilon ^ 2 * 8)⁻¹ * 104 -
            lambda * epsilon ^ 2 * 8 +
          lambda * epsilon ^ 2 * (-5 - epsilon * 10 + epsilon ^ 2 * 8)⁻¹ * 244 -
        lambda * epsilon ^ 3 * (-5 - epsilon * 10 + epsilon ^ 2 * 8)⁻¹ * 224 +
      lambda * epsilon ^ 4 * (-5 - epsilon * 10 + epsilon ^ 2 * 8)⁻¹ * 64 +
    lambda * (-5 - epsilon * 10 + epsilon ^ 2 * 8)⁻¹ * 15 =
      -(lambda * epsilon * (-5 - epsilon * 10 + epsilon ^ 2 * 8)⁻¹ * 144) +
        lambda * epsilon ^ 2 * (-5 - epsilon * 10 + epsilon ^ 2 * 8)⁻¹ * 64 +
      lambda * (-5 - epsilon * 10 + epsilon ^ 2 * 8)⁻¹ * 40 := by
  field_simp [hden]
  ring

/-- The concrete zeroth-order right/left unit eigenvectors printed in
Appendix A.1, equation (A.4), satisfy the real eigenvector and normalization
clauses for the two-step counterexample base matrix. -/
theorem two_step_counterexample_base_right_left_unit_eigen
    (epsilon lambda : ℝ) (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt : epsilon < 1) :
    let right0 : RowVector (Fin 3) :=
      fun i =>
        if i = 0 then 1
        else if i = 1 then 1
        else
          lambda * (8 * epsilon ^ 2 - 18 * epsilon + 5) /
            (8 * epsilon ^ 2 - 10 * epsilon - 5)
    let left0 : RowVector (Fin 3) :=
      fun i =>
        if i = 0 then 1 - epsilon
        else if i = 1 then epsilon
        else 0
    IsRightUnitEigenvector (Node := Fin 3)
      (twoStepCounterexamplePropagator epsilon lambda 0) right0 ∧
      IsLeftUnitEigenvector (Node := Fin 3)
        (twoStepCounterexamplePropagator epsilon lambda 0) left0 ∧
        rowDot (Node := Fin 3) left0 right0 = 1 := by
  classical
  have hDne :=
    two_step_counterexample_tail_denominator_ne_zero
      epsilon hepsilon_pos hepsilon_lt
  have hden_ne :
      8 * epsilon ^ 2 - 10 * epsilon - 5 ≠ 0 := by
    intro hden
    apply hDne
    unfold twoStepCounterexampleTailDenominator
    nlinarith
  have hden_ne' :
      -5 - epsilon * 10 + epsilon ^ 2 * 8 ≠ 0 := by
    intro hden
    apply hden_ne
    nlinarith
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro hzero
      have hcoord := congrFun hzero (0 : Fin 3)
      norm_num at hcoord
    · funext i
      fin_cases i
      · simp [twoStepCounterexamplePropagator,
          twoStepCounterexampleLiftedStep, twoNodeCounterexamplePush,
          twoNodeCounterexamplePullA, twoNodeCounterexamplePullB,
          matrixMul, matrixMulVector, Fin.sum_univ_succ,
          Fin.sum_univ_two]
        field_simp [hden_ne, hden_ne']
        ring
      · simp [twoStepCounterexamplePropagator,
          twoStepCounterexampleLiftedStep, twoNodeCounterexamplePush,
          twoNodeCounterexamplePullA, twoNodeCounterexamplePullB,
          matrixMul, matrixMulVector, Fin.sum_univ_succ,
          Fin.sum_univ_two]
        field_simp [hden_ne, hden_ne']
        ring
      · simp [twoStepCounterexamplePropagator,
          twoStepCounterexampleLiftedStep, twoNodeCounterexamplePush,
          twoNodeCounterexamplePullA, twoNodeCounterexamplePullB,
          matrixMul, matrixMulVector, Fin.sum_univ_succ,
          Fin.sum_univ_two]
        field_simp [hden_ne, hden_ne']
        ring_nf
        exact
          two_step_counterexample_right_tracker_coordinate_identity
            epsilon lambda hden_ne'
  · refine ⟨?_, ?_⟩
    · intro hzero
      have hcoord := congrFun hzero (0 : Fin 3)
      simp at hcoord
      linarith
    · funext i
      fin_cases i <;>
        simp [twoStepCounterexamplePropagator,
          twoStepCounterexampleLiftedStep, twoNodeCounterexamplePush,
          twoNodeCounterexamplePullA, twoNodeCounterexamplePullB,
          matrixMul, rowMulMatrix, Fin.sum_univ_succ,
          Fin.sum_univ_two] <;>
        ring
  · simp [rowDot, Fin.sum_univ_succ, Fin.sum_univ_two]

/-- First coordinate of the Appendix A.1 base two-step propagator. -/
theorem two_step_counterexample_base_row0_complex
    (epsilon lambda : ℝ) (v : ComplexRowVector (Fin 3)) :
    complexMatrixMulVector (Node := Fin 3)
        (twoStepCounterexamplePropagator epsilon lambda 0) v (0 : Fin 3) =
      (((1 - 3 * epsilon / 4 : ℝ) : ℂ) * v (0 : Fin 3) +
        ((3 * epsilon / 4 : ℝ) : ℂ) * v (1 : Fin 3)) := by
  simp [complexMatrixMulVector, twoStepCounterexamplePropagator,
    twoStepCounterexampleLiftedStep, twoNodeCounterexamplePush,
    twoNodeCounterexamplePullA, matrixMul, Fin.sum_univ_succ]
  ring

/-- Tracker coordinate of the Appendix A.1 base two-step propagator. -/
theorem two_step_counterexample_base_row2_complex
    (epsilon lambda : ℝ) (v : ComplexRowVector (Fin 3)) :
    complexMatrixMulVector (Node := Fin 3)
        (twoStepCounterexamplePropagator epsilon lambda 0) v (2 : Fin 3) =
      ((lambda * (-4 * epsilon ^ 2 + 9 * epsilon - 5) / 8 : ℝ) : ℂ) *
          v (0 : Fin 3) +
        ((epsilon * lambda * (9 - 4 * epsilon) / 8 : ℝ) : ℂ) *
          v (1 : Fin 3) +
          ((((1 / 2 - epsilon) * (3 / 4 - epsilon) : ℝ) : ℂ) *
            v (2 : Fin 3)) := by
  simp [complexMatrixMulVector, twoStepCounterexamplePropagator,
    twoStepCounterexampleLiftedStep, twoNodeCounterexamplePush,
    twoNodeCounterexamplePullA, twoNodeCounterexamplePullB, matrixMul,
    Fin.sum_univ_succ]
  ring

/-- The unit eigenspace of the concrete Appendix A.1 base propagator is spanned
by the printed right unit eigenvector. -/
theorem two_step_counterexample_base_unit_eigenspace_span
    (epsilon lambda : ℝ) (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt : epsilon < 1) :
    let right0 : RowVector (Fin 3) :=
      fun i =>
        if i = 0 then 1
        else if i = 1 then 1
        else
          lambda * (8 * epsilon ^ 2 - 18 * epsilon + 5) /
            (8 * epsilon ^ 2 - 10 * epsilon - 5)
    ∀ v : ComplexRowVector (Fin 3),
      complexMatrixMulVector (Node := Fin 3)
        (twoStepCounterexamplePropagator epsilon lambda 0) v = (1 : ℂ) • v →
        ∃ c : ℂ, v = c • complexOfRealRow (Node := Fin 3) right0 := by
  classical
  have hDne :=
    two_step_counterexample_tail_denominator_ne_zero
      epsilon hepsilon_pos hepsilon_lt
  have hden_ne :
      8 * epsilon ^ 2 - 10 * epsilon - 5 ≠ 0 := by
    intro hden
    apply hDne
    unfold twoStepCounterexampleTailDenominator
    nlinarith
  have hdenC_ne : (((8 * epsilon ^ 2 - 10 * epsilon - 5 : ℝ) : ℂ) ≠ 0) := by
    exact_mod_cast hden_ne
  dsimp
  intro v hv
  have hv0 := congrFun hv (0 : Fin 3)
  rw [two_step_counterexample_base_row0_complex] at hv0
  simp only [Pi.smul_apply, one_smul] at hv0
  have h01 : v (1 : Fin 3) = v (0 : Fin 3) := by
    let a : ℂ := ((1 - 3 * epsilon / 4 : ℝ) : ℂ)
    let b : ℂ := ((3 * epsilon / 4 : ℝ) : ℂ)
    have hv0ab : a * v (0 : Fin 3) + b * v (1 : Fin 3) = v (0 : Fin 3) := by
      simpa [a, b] using hv0
    have hab : a + b = 1 := by
      dsimp [a, b]
      norm_num
    have hlin_b : b * (v (1 : Fin 3) - v (0 : Fin 3)) = 0 := by
      calc
        b * (v (1 : Fin 3) - v (0 : Fin 3)) =
            a * v (0 : Fin 3) + b * v (1 : Fin 3) -
              (a + b) * v (0 : Fin 3) := by ring
        _ =
            (a * v (0 : Fin 3) + b * v (1 : Fin 3)) -
              v (0 : Fin 3) := by rw [hab]; ring
        _ = 0 := by
          rw [hv0ab]
          ring
    have hlin : (((3 * epsilon / 4 : ℝ) : ℂ) *
        (v (1 : Fin 3) - v (0 : Fin 3))) = 0 := by
      simpa [b] using hlin_b
    have hcoef_ne : (((3 * epsilon / 4 : ℝ) : ℂ) ≠ 0) := by
      have hreal_pos : 0 < (3 * epsilon / 4 : ℝ) := by positivity
      exact_mod_cast (ne_of_gt hreal_pos)
    have hsub : v (1 : Fin 3) - v (0 : Fin 3) = 0 :=
      (mul_eq_zero.mp hlin).resolve_left hcoef_ne
    exact sub_eq_zero.mp hsub
  have hv2 := congrFun hv (2 : Fin 3)
  rw [two_step_counterexample_base_row2_complex] at hv2
  simp only [Pi.smul_apply, one_smul] at hv2
  rw [h01] at hv2
  have htracker_mul :
      (((8 * epsilon ^ 2 - 10 * epsilon - 5 : ℝ) : ℂ) *
          v (2 : Fin 3)) =
        (((lambda * (8 * epsilon ^ 2 - 18 * epsilon + 5) : ℝ) : ℂ) *
          v (0 : Fin 3)) := by
    let a : ℂ := ((lambda * (-4 * epsilon ^ 2 + 9 * epsilon - 5) / 8 : ℝ) : ℂ)
    let b : ℂ := ((epsilon * lambda * (9 - 4 * epsilon) / 8 : ℝ) : ℂ)
    let d : ℂ := (((1 / 2 - epsilon) * (3 / 4 - epsilon) : ℝ) : ℂ)
    let den : ℂ := ((8 * epsilon ^ 2 - 10 * epsilon - 5 : ℝ) : ℂ)
    let num : ℂ := ((lambda * (8 * epsilon ^ 2 - 18 * epsilon + 5) : ℝ) : ℂ)
    have hv2abd :
        a * v (0 : Fin 3) + b * v (0 : Fin 3) +
            d * v (2 : Fin 3) = v (2 : Fin 3) := by
      simpa [a, b, d] using hv2
    have hres :
        a * v (0 : Fin 3) + b * v (0 : Fin 3) +
            d * v (2 : Fin 3) - v (2 : Fin 3) = 0 := by
      rw [hv2abd]
      ring
    have hden : den = 8 * (d - 1) := by
      dsimp [den, d]
      norm_num
      ring
    have hnum : num = -8 * (a + b) := by
      dsimp [num, a, b]
      norm_num
      ring
    apply sub_eq_zero.mp
    calc
      den * v (2 : Fin 3) - num * v (0 : Fin 3) =
          8 * (a * v (0 : Fin 3) + b * v (0 : Fin 3) +
            d * v (2 : Fin 3) - v (2 : Fin 3)) := by
            rw [hden, hnum]
            ring
      _ = 0 := by rw [hres]; ring
  have htracker :
      v (2 : Fin 3) =
        (((lambda * (8 * epsilon ^ 2 - 18 * epsilon + 5) /
            (8 * epsilon ^ 2 - 10 * epsilon - 5) : ℝ) : ℂ) *
          v (0 : Fin 3)) := by
    have hquot :
        (((8 * epsilon ^ 2 - 10 * epsilon - 5 : ℝ) : ℂ)⁻¹ *
            ((lambda * (8 * epsilon ^ 2 - 18 * epsilon + 5) : ℝ) : ℂ)) =
          ((lambda * (8 * epsilon ^ 2 - 18 * epsilon + 5) /
            (8 * epsilon ^ 2 - 10 * epsilon - 5) : ℝ) : ℂ) := by
      have hquot_real :
          (8 * epsilon ^ 2 - 10 * epsilon - 5)⁻¹ *
              (lambda * (8 * epsilon ^ 2 - 18 * epsilon + 5)) =
            lambda * (8 * epsilon ^ 2 - 18 * epsilon + 5) /
              (8 * epsilon ^ 2 - 10 * epsilon - 5) := by
        field_simp [hden_ne]
      exact_mod_cast hquot_real
    calc
      v (2 : Fin 3) =
          ((8 * epsilon ^ 2 - 10 * epsilon - 5 : ℝ) : ℂ)⁻¹ *
            (((8 * epsilon ^ 2 - 10 * epsilon - 5 : ℝ) : ℂ) *
              v (2 : Fin 3)) := by
            rw [← mul_assoc, inv_mul_cancel₀ hdenC_ne, one_mul]
      _ =
          ((8 * epsilon ^ 2 - 10 * epsilon - 5 : ℝ) : ℂ)⁻¹ *
            (((lambda * (8 * epsilon ^ 2 - 18 * epsilon + 5) : ℝ) : ℂ) *
              v (0 : Fin 3)) := by rw [htracker_mul]
      _ =
          (((lambda * (8 * epsilon ^ 2 - 18 * epsilon + 5) /
            (8 * epsilon ^ 2 - 10 * epsilon - 5) : ℝ) : ℂ) *
            v (0 : Fin 3)) := by
            rw [← mul_assoc, hquot]
  refine ⟨v (0 : Fin 3), ?_⟩
  funext i
  fin_cases i
  · simp [complexOfRealRow]
  · simp [complexOfRealRow, h01]
  · simp [complexOfRealRow, htracker, mul_comm]

/-- Complex analogue of `rowDot_matrixMulVector_eq_rowMulMatrix_rowDot` when
the left row and matrix are real but the right vector is complex. -/
theorem complex_rowDot_matrixMulVector_eq_rowMulMatrix_rowDot
    (w : RowVector Node) (v : ComplexRowVector Node) (M : NodeMatrix Node) :
    (∑ i : Node, (w i : ℂ) *
        complexMatrixMulVector (Node := Node) M v i) =
      ∑ j : Node, (rowMulMatrix (Node := Node) w M j : ℂ) * v j := by
  classical
  unfold complexMatrixMulVector rowMulMatrix
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _hj
  calc
    (∑ i : Node, (w i : ℂ) * ((M i j : ℂ) * v j)) =
        (∑ i : Node, ((w i * M i j : ℝ) : ℂ)) * v j := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _hi
          norm_num
          ring
    _ = ((∑ i : Node, w i * M i j : ℝ) : ℂ) * v j := by
          norm_cast

/-- The concrete Appendix A.1 base unit eigenvalue is algebraically simple in
the custom complex row-vector API. -/
theorem two_step_counterexample_base_unit_algebraically_simple
    (epsilon lambda : ℝ) (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt : epsilon < 1) :
    let right0 : RowVector (Fin 3) :=
      fun i =>
        if i = 0 then 1
        else if i = 1 then 1
        else
          lambda * (8 * epsilon ^ 2 - 18 * epsilon + 5) /
            (8 * epsilon ^ 2 - 10 * epsilon - 5)
    UnitEigenvalueAlgebraicallySimple (Node := Fin 3)
      (twoStepCounterexamplePropagator epsilon lambda 0) right0 := by
  classical
  let A0 : NodeMatrix (Fin 3) :=
    twoStepCounterexamplePropagator epsilon lambda 0
  let right0 : RowVector (Fin 3) :=
    fun i =>
      if i = 0 then 1
      else if i = 1 then 1
      else
        lambda * (8 * epsilon ^ 2 - 18 * epsilon + 5) /
          (8 * epsilon ^ 2 - 10 * epsilon - 5)
  let left0 : RowVector (Fin 3) :=
    fun i =>
      if i = 0 then 1 - epsilon
      else if i = 1 then epsilon
      else 0
  have hbase :
      IsRightUnitEigenvector (Node := Fin 3) A0 right0 ∧
        IsLeftUnitEigenvector (Node := Fin 3) A0 left0 ∧
          rowDot (Node := Fin 3) left0 right0 = 1 := by
    simpa [A0, right0, left0] using
      two_step_counterexample_base_right_left_unit_eigen
        epsilon lambda hepsilon_pos hepsilon_lt
  have hspan :
      ∀ v : ComplexRowVector (Fin 3),
        complexMatrixMulVector (Node := Fin 3) A0 v = (1 : ℂ) • v →
          ∃ c : ℂ, v = c • complexOfRealRow (Node := Fin 3) right0 := by
    simpa [A0, right0] using
      two_step_counterexample_base_unit_eigenspace_span
        epsilon lambda hepsilon_pos hepsilon_lt
  let leftDual : Module.Dual ℂ (ComplexRowVector (Fin 3)) :=
    { toFun := fun v ↦ ∑ i : Fin 3, (left0 i : ℂ) * v i
      map_add' := by
        intro x y
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        ring }
  have hleft : rowMulMatrix (Node := Fin 3) left0 A0 = left0 := hbase.2.1.2
  have hnormalized : rowDot (Node := Fin 3) left0 right0 = 1 := hbase.2.2
  have hleftDual :
      leftDual.comp
          (Matrix.mulVecLin (fun i j : Fin 3 ↦ (A0 i j : ℂ))) =
        (1 : ℂ) • leftDual := by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply, one_smul]
    change
      (∑ i : Fin 3, (left0 i : ℂ) *
          complexMatrixMulVector (Node := Fin 3) A0 v i) =
        ∑ i : Fin 3, (left0 i : ℂ) * v i
    calc
      (∑ i : Fin 3, (left0 i : ℂ) *
          complexMatrixMulVector (Node := Fin 3) A0 v i) =
          ∑ j : Fin 3, (rowMulMatrix (Node := Fin 3) left0 A0 j : ℂ) *
            v j := by
            exact complex_rowDot_matrixMulVector_eq_rowMulMatrix_rowDot
              (Node := Fin 3) left0 v A0
      _ = ∑ j : Fin 3, (left0 j : ℂ) * v j := by rw [hleft]
  have hleftDual_normalized :
      leftDual (complexOfRealRow (Node := Fin 3) right0) = 1 := by
    have hcast := congrArg Complex.ofReal hnormalized
    simpa [leftDual, rowDot, complexOfRealRow] using hcast
  dsimp only
  simpa [UnitEigenvalueAlgebraicallySimple, IsAlgebraicallySimpleEigenpair,
    A0, right0] using
    (Module.End.isAlgebraicallySimpleEigenpair_of_eigenspace_span_of_left_eigenvector
      (A := Matrix.mulVecLin (fun i j : Fin 3 ↦ (A0 i j : ℂ)))
      (mu := (1 : ℂ)) (right := complexOfRealRow (Node := Fin 3) right0)
      (left := leftDual) hspan hleftDual hleftDual_normalized)

/-- Appendix A.1: two-step counterexample spectral coefficients. -/
theorem CounterexampleTwoStepSpectralCoefficients :
    TwoStepSpectralCoefficientStatement := by
  unfold TwoStepSpectralCoefficientStatement
  intro epsilon lambda hepsilon_pos hepsilon_lt hlambda_pos
  classical
  have hDne :
      twoStepCounterexampleTailDenominator epsilon ≠ 0 :=
    two_step_counterexample_tail_denominator_ne_zero
      epsilon hepsilon_pos hepsilon_lt
  have hslope_pos :
      0 < twoStepCounterexampleSpectralSlope epsilon :=
    two_step_counterexample_spectral_slope_pos
      epsilon hepsilon_pos hepsilon_lt
  have hnoise_pos :
      0 < twoStepCounterexampleNoiseCoefficient epsilon :=
    two_step_counterexample_noise_coefficient_pos
      epsilon hepsilon_pos hepsilon_lt
  let right0 : RowVector (Fin 3) :=
    fun i =>
      if i = 0 then 1
      else if i = 1 then 1
      else
        lambda * (8 * epsilon ^ 2 - 18 * epsilon + 5) /
          (8 * epsilon ^ 2 - 10 * epsilon - 5)
  let left0 : RowVector (Fin 3) :=
    fun i =>
      if i = 0 then 1 - epsilon
      else if i = 1 then epsilon
      else 0
  have hbaseEigen :
      IsRightUnitEigenvector (Node := Fin 3)
        (twoStepCounterexamplePropagator epsilon lambda 0) right0 ∧
        IsLeftUnitEigenvector (Node := Fin 3)
          (twoStepCounterexamplePropagator epsilon lambda 0) left0 ∧
          rowDot (Node := Fin 3) left0 right0 = 1 := by
    simpa [right0, left0] using
      two_step_counterexample_base_right_left_unit_eigen
        epsilon lambda hepsilon_pos hepsilon_lt
  have halgebraicallySimple :
      UnitEigenvalueAlgebraicallySimple (Node := Fin 3)
        (twoStepCounterexamplePropagator epsilon lambda 0) right0 := by
    simpa [right0] using
      two_step_counterexample_base_unit_algebraically_simple
        epsilon lambda hepsilon_pos hepsilon_lt
  have hspectrum :
      SimpleIsolatedUnitEigenvalueStableSpectrum (Node := Fin 3)
        (twoStepCounterexamplePropagator epsilon lambda 0) (1 / 2)
        right0 left0 := by
    refine ⟨by norm_num, by norm_num, hbaseEigen.1, hbaseEigen.2.1,
      hbaseEigen.2.2, halgebraicallySimple, ?_⟩
    exact two_step_counterexample_base_stable_spectrum_le_half
      epsilon lambda hepsilon_pos hepsilon_lt
  obtain ⟨alpha0, theta, K, gamma, P, F, _halpha0_le, hsplitting⟩ :=
    PeriodicSpectralDecomposition (Node := Fin 3)
      (fun alpha => twoStepCounterexamplePropagator epsilon lambda alpha)
      1 (1 / 2)
      (two_step_counterexample_propagator_analytic_near_zero epsilon lambda)
      right0 left0 hspectrum
  have hpair :
      ∀ Aderiv : NodeMatrix (Fin 3),
        HasDerivAt
          (fun alpha => twoStepCounterexamplePropagator epsilon lambda alpha)
          Aderiv 0 →
        rowDot (Node := Fin 3) left0
          (matrixMulVector (Node := Fin 3) Aderiv right0) =
          -2 * lambda * twoStepCounterexampleSpectralSlope epsilon := by
    simpa [right0, left0] using
      two_step_counterexample_deriv_pairing
        epsilon lambda hepsilon_pos hepsilon_lt
  have hslowO :
      Asymptotics.IsBigO (nhds 0)
        (fun alpha =>
          gamma alpha -
            twoStepSlowMultiplierApprox lambda
              (twoStepCounterexampleSpectralSlope epsilon) alpha)
        (fun alpha => alpha ^ 2) :=
    two_step_counterexample_slow_multiplier_bigO_of_deriv_pairing
      epsilon lambda alpha0 theta K right0 left0 gamma P F hsplitting hpair
  have hphaseO :
      Asymptotics.IsBigO (nhds 0)
        (fun alpha =>
          twoStepCounterexamplePhaseNoise epsilon alpha -
            twoStepPhaseNoiseApprox
              (twoStepCounterexampleNoiseCoefficient epsilon) alpha)
        (fun alpha => alpha ^ 3) :=
    two_step_counterexample_phase_noise_bigO epsilon
  let theta1 : ℝ := (theta + 1) / 2
  have hhalf_lt_theta : (1 / 2 : ℝ) < theta := hsplitting.2.1
  have htheta_pos : 0 < theta := by nlinarith
  have htheta_nonneg : 0 ≤ theta := le_of_lt htheta_pos
  have htheta_lt_one : theta < 1 := hsplitting.2.2.1
  have htheta_lt_theta1 : theta < theta1 := by
    dsimp [theta1]
    nlinarith
  have htheta_le_theta1 : theta ≤ theta1 := le_of_lt htheta_lt_theta1
  have htheta1_lt_one : theta1 < 1 := by
    dsimp [theta1]
    nlinarith
  have htheta1_pos : 0 < theta1 := by
    dsimp [theta1]
    nlinarith
  obtain ⟨Cstable, hCstable_nonneg, hstableC⟩ :=
    two_step_counterexample_stable_impulse_alpha_geometric_bound
      epsilon lambda alpha0 theta K theta1 right0 left0 gamma P F
      hepsilon_pos hepsilon_lt
      hbaseEigen hspectrum
      (two_step_counterexample_propagator_analytic_near_zero epsilon lambda)
      hsplitting htheta_lt_theta1 htheta1_lt_one
  let Kfinal : ℝ := max K Cstable
  have hK_nonneg : 0 ≤ K := hsplitting.2.2.2.1
  have hK_le_Kfinal : K ≤ Kfinal := by
    dsimp [Kfinal]
    exact le_max_left K Cstable
  have hCstable_le_Kfinal : Cstable ≤ Kfinal := by
    dsimp [Kfinal]
    exact le_max_right K Cstable
  have hKfinal_nonneg : 0 ≤ Kfinal :=
    le_trans hK_nonneg hK_le_Kfinal
  have hsplitting_final :
      PeriodicSpectralSplitting (Node := Fin 3)
        (fun alpha => twoStepCounterexamplePropagator epsilon lambda alpha)
        (1 / 2) alpha0 theta1 Kfinal right0 left0 gamma P F :=
    periodicSpectralSplitting_weaken_geometric_constants (Node := Fin 3)
      (fun alpha => twoStepCounterexamplePropagator epsilon lambda alpha)
      (1 / 2) alpha0 theta K theta1 Kfinal right0 left0 gamma P F
      hsplitting htheta_nonneg htheta_le_theta1 htheta1_lt_one
      hK_le_Kfinal hKfinal_nonneg
  refine ⟨(1 / 2 : ℝ), alpha0, Kfinal, theta1, right0, left0, gamma, P, F,
    hDne, hslope_pos, hnoise_pos, hsplitting_final, hslowO, hphaseO, ?_⟩
  intro alpha phase j halpha_nonneg halpha_le
  have htheta1_pow_nonneg : 0 ≤ theta1 ^ j :=
    pow_nonneg (le_of_lt htheta1_pos) j
  have halpha_pow_nonneg : 0 ≤ alpha * theta1 ^ j :=
    mul_nonneg halpha_nonneg htheta1_pow_nonneg
  have hconst_mul :
      Cstable * (alpha * theta1 ^ j) ≤
        Kfinal * (alpha * theta1 ^ j) :=
    mul_le_mul_of_nonneg_right hCstable_le_Kfinal halpha_pow_nonneg
  calc
    twoStepCounterexampleStableImpulseFrom F epsilon lambda alpha phase j ≤
        Cstable * alpha * theta1 ^ j :=
      hstableC alpha phase j halpha_nonneg halpha_le
    _ = Cstable * (alpha * theta1 ^ j) := by ring
    _ ≤ Kfinal * (alpha * theta1 ^ j) := hconst_mul
    _ = Kfinal * alpha * theta1 ^ j := by ring

/-- Appendix C.2 phase multiplier
`a_t(alpha)=1-alpha*lambda*c_t` for the scalar comparison process. -/
noncomputable def quadraticScalarPhaseMultiplier
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (t : ℕ) : ℝ :=
  1 - alpha * lambda * quad.scalarComparisonGain t

/-- Appendix C.2 within-period product `A_r(alpha)=prod_{j<r} a_j(alpha)`.
This is the literal finite product used in the paper before passing to block
boundaries. -/
noncomputable def quadraticScalarWithinPeriodMultiplier
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (r : ℕ) : ℝ :=
  (Finset.range r).prod fun j =>
    quadraticScalarPhaseMultiplier (Node := Node) quad lambda alpha j

/-- Appendix C.2 period multiplier `Gamma(alpha)=prod_{r=0}^{p-1}a_r(alpha)`.
The index is `Fin quad.period` so the product is exactly over one paper period. -/
noncomputable def quadraticScalarPeriodMultiplier
    (quad : Setup Node ℝ) (lambda alpha : ℝ) : ℝ :=
  ∏ r : Fin quad.period,
    quadraticScalarPhaseMultiplier (Node := Node) quad lambda alpha r.1

/-- Appendix C.2 block innovation `eta_k`, introduced as the exact AR residual
at period boundaries.  Later variance work should unfold this residual into
the finite sum of fresh within-block noises from equation (C.2). -/
noncomputable def quadraticScalarBlockNoiseInnovation
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    (noise : NoisePath Node ℝ) (k : ℕ) : ℝ :=
  quad.quadraticScalarComparisonProcess lambda alpha noise ((k + 1) * quad.period) -
    quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha *
      quad.quadraticScalarComparisonProcess lambda alpha noise (k * quad.period)

/-- Product of scalar phase multipliers over a finite window starting at
`base`.  This is the deterministic propagator used when unrolling the scalar
comparison process inside one period. -/
noncomputable def quadraticScalarWindowPhaseProduct
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (base n : ℕ) : ℝ :=
  (Finset.range n).prod fun r =>
    quadraticScalarPhaseMultiplier (Node := Node) quad lambda alpha (base + r)

/-- Propagated within-window noise sum generated by the scalar recursion.
For a window starting at `base`, this is the source object
`sum_r prod_{s>r} a_s b_r^T epsilon_{base+r}` before specializing to a full
period. -/
noncomputable def quadraticScalarWindowPropagatedNoise
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    (noise : NoisePath Node ℝ) (base : ℕ) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      quadraticScalarPhaseMultiplier (Node := Node) quad lambda alpha (base + n) *
        quadraticScalarWindowPropagatedNoise
          quad lambda alpha noise base n +
      weightedState (Node := Node) (E := ℝ)
        (quad.influence (base + n)) (noise (base + n))

/-- Deterministic propagation coefficient for the noise injected at relative
phase `r` after `n` scalar comparison steps.  It is the finite-product weight
from Appendix C.2, written recursively to keep the finite-sum unroll robust. -/
noncomputable def quadraticScalarWindowNoiseCoeff
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (base : ℕ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | n + 1, r =>
      if r = n then 1
      else
        quadraticScalarPhaseMultiplier (Node := Node) quad lambda alpha
            (base + n) *
          quadraticScalarWindowNoiseCoeff quad lambda alpha base n r

/-- Finite-sum form of the propagated within-window noise. -/
noncomputable def quadraticScalarWindowPropagatedNoiseFinset
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    (noise : NoisePath Node ℝ) (base n : ℕ) : ℝ :=
  (Finset.range n).sum fun r =>
    quadraticScalarWindowNoiseCoeff (Node := Node)
        quad lambda alpha base n r *
      weightedState (Node := Node) (E := ℝ)
        (quad.influence (base + r)) (noise (base + r))

/-- The recursively defined propagated noise is exactly the finite propagated
sum over the fresh within-window noises. -/
theorem quadraticScalarWindowPropagatedNoise_eq_finset
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    (noise : NoisePath Node ℝ) (base : ℕ) :
    ∀ n : ℕ,
      quadraticScalarWindowPropagatedNoise (Node := Node)
          quad lambda alpha noise base n =
        quadraticScalarWindowPropagatedNoiseFinset (Node := Node)
          quad lambda alpha noise base n
  | 0 => by
      simp [quadraticScalarWindowPropagatedNoise,
        quadraticScalarWindowPropagatedNoiseFinset]
  | n + 1 => by
      have hprev :=
        quadraticScalarWindowPropagatedNoise_eq_finset
          quad lambda alpha noise base n
      let a :=
        quadraticScalarPhaseMultiplier (Node := Node) quad lambda alpha
          (base + n)
      let w : ℕ → ℝ := fun r =>
        weightedState (Node := Node) (E := ℝ)
          (quad.influence (base + r)) (noise (base + r))
      have hsum :
          ((Finset.range n).sum fun r =>
              quadraticScalarWindowNoiseCoeff (Node := Node)
                  quad lambda alpha base (n + 1) r * w r) =
            a *
              ((Finset.range n).sum fun r =>
                quadraticScalarWindowNoiseCoeff (Node := Node)
                    quad lambda alpha base n r * w r) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        have hrne : r ≠ n := Nat.ne_of_lt (Finset.mem_range.mp hr)
        simp [quadraticScalarWindowNoiseCoeff, a, w, hrne, mul_assoc]
      simpa [quadraticScalarWindowPropagatedNoise,
        quadraticScalarWindowPropagatedNoiseFinset, hprev,
        Finset.sum_range_succ, quadraticScalarWindowNoiseCoeff, a, w]
        using hsum.symm

/-- The scalar comparison process starts from the paper's `x_0`. -/
theorem quadraticScalarComparisonProcess_zero
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    (noise : NoisePath Node ℝ) :
    quad.quadraticScalarComparisonProcess lambda alpha noise 0 = quad.x0 := by
  simpa [quadraticScalarComparisonProcess] using
    (SOptLib.recursiveIterateProcess_zero
      (fun t (_ : Unit) =>
        quad.quadraticScalarComparisonProcess lambda alpha noise t)
      quad.x0
      (fun k u (_ : Unit) =>
        quad.quadraticScalarComparisonStep lambda alpha noise k u)
      (by
        funext t ω
        simp [quadraticScalarComparisonProcess])
      ())

/-- One-step scalar recursion in Appendix C.2:
`u_{t+1}=a_t(alpha)u_t-alpha b_t^T epsilon_t`. -/
theorem quadraticScalarComparisonProcess_succ
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    (noise : NoisePath Node ℝ) (t : ℕ) :
    quad.quadraticScalarComparisonProcess lambda alpha noise (t + 1) =
      quadraticScalarPhaseMultiplier (Node := Node) quad lambda alpha t *
        quad.quadraticScalarComparisonProcess lambda alpha noise t -
          alpha * weightedState (Node := Node) (E := ℝ)
            (quad.influence t) (noise t) := by
  simpa [quadraticScalarComparisonProcess, quadraticScalarComparisonStep,
    quadraticScalarPhaseMultiplier] using
    (SOptLib.recursiveIterateProcess_succ
      (fun t (_ : Unit) =>
        quad.quadraticScalarComparisonProcess lambda alpha noise t)
      quad.x0
      (fun k u (_ : Unit) =>
        quad.quadraticScalarComparisonStep lambda alpha noise k u)
      (by
        funext t ω
        simp [quadraticScalarComparisonProcess])
      t ())

/-- Exact finite-window unrolling of the scalar comparison recursion.  This is
the deterministic part of Appendix C.2 before specializing `base = kp` and
`n = p`. -/
theorem quadraticScalarComparisonProcess_unroll_window
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    (noise : NoisePath Node ℝ) (base : ℕ) :
    ∀ n : ℕ,
      quad.quadraticScalarComparisonProcess lambda alpha noise (base + n) =
        quadraticScalarWindowPhaseProduct (Node := Node) quad lambda alpha base n *
          quad.quadraticScalarComparisonProcess lambda alpha noise base -
        alpha *
          quadraticScalarWindowPropagatedNoise (Node := Node)
            quad lambda alpha noise base n
  | 0 => by
      simp [quadraticScalarWindowPhaseProduct,
        quadraticScalarWindowPropagatedNoise]
  | n + 1 => by
      have hstep :=
        quadraticScalarComparisonProcess_succ
          (Node := Node) quad lambda alpha noise (base + n)
      have hprev :=
        quadraticScalarComparisonProcess_unroll_window
          quad lambda alpha noise base n
      calc
        quad.quadraticScalarComparisonProcess lambda alpha noise (base + (n + 1)) =
            quad.quadraticScalarComparisonProcess lambda alpha noise ((base + n) + 1) := by
              congr 1
        _ =
            quadraticScalarPhaseMultiplier (Node := Node)
                quad lambda alpha (base + n) *
              quad.quadraticScalarComparisonProcess lambda alpha noise (base + n) -
              alpha * weightedState (Node := Node) (E := ℝ)
                (quad.influence (base + n)) (noise (base + n)) := hstep
        _ =
            quadraticScalarWindowPhaseProduct (Node := Node)
                quad lambda alpha base (n + 1) *
              quad.quadraticScalarComparisonProcess lambda alpha noise base -
              alpha *
                quadraticScalarWindowPropagatedNoise (Node := Node)
                  quad lambda alpha noise base (n + 1) := by
              rw [hprev]
              simp [quadraticScalarWindowPhaseProduct,
                quadraticScalarWindowPropagatedNoise, Finset.prod_range_succ]
              ring

/-- Scalar phase multipliers return to the same phase at block starts. -/
theorem quadraticScalarPhaseMultiplier_blockStart_add
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (k r : ℕ) :
    quadraticScalarPhaseMultiplier (Node := Node) quad lambda alpha
        (quad.blockStart k + r) =
      quadraticScalarPhaseMultiplier (Node := Node) quad lambda alpha r := by
  unfold quadraticScalarPhaseMultiplier scalarComparisonGain
  rw [quad.influence_blockStart_add k r]

/-- The finite-window product over a complete block is the period multiplier
`Gamma(alpha)`. -/
theorem quadraticScalarWindowPhaseProduct_blockStart_period
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (k : ℕ) :
    quadraticScalarWindowPhaseProduct (Node := Node) quad lambda alpha
        (quad.blockStart k) quad.period =
      quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha := by
  classical
  rw [quadraticScalarWindowPhaseProduct, quadraticScalarPeriodMultiplier]
  rw [← Fin.prod_univ_eq_prod_range
      (fun r : ℕ =>
        quadraticScalarPhaseMultiplier (Node := Node) quad lambda alpha
          (quad.blockStart k + r)) quad.period]
  apply Finset.prod_congr rfl
  intro r _hr
  exact quadraticScalarPhaseMultiplier_blockStart_add
    (Node := Node) quad lambda alpha k r.1

/-- Window products started at a block boundary agree with the paper's
within-period multipliers for every finite phase. -/
theorem quadraticScalarWindowPhaseProduct_blockStart_eq_withinPeriod
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (k r : ℕ) :
    quadraticScalarWindowPhaseProduct (Node := Node) quad lambda alpha
        (quad.blockStart k) r =
      quadraticScalarWithinPeriodMultiplier (Node := Node)
        quad lambda alpha r := by
  classical
  rw [quadraticScalarWindowPhaseProduct,
    quadraticScalarWithinPeriodMultiplier]
  apply Finset.prod_congr rfl
  intro j _hj
  exact quadraticScalarPhaseMultiplier_blockStart_add
    (Node := Node) quad lambda alpha k j

end Setup
end Algorithms.Unverified.TimeVaryingPushPull
