import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Real.Sign
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import SOptLib.Model.Objective
import SOptLib.Model.StochasticOracle
import SOptLib.Layer0.Objective
import SOptLib.Layer0.Oracle
import Algorithms.Unverified.Muon.Part002

/-!
Complete-paper Muon task. See TASK.md and paper/Muon/source_manifest.json.

This Phase 0 file exposes the paper's object layer: matrix objectives, the
SVD/polar update direction used by Muon, Algorithm 1 stochastic iterates, and
Algorithm 2 deterministic iterates. Endpoint proofs are intentionally left to
later prover phases.
-/

noncomputable section

namespace SGD.Muon

open Matrix MeasureTheory Filter
open scoped BigOperators InnerProductSpace Matrix.Norms.Frobenius

theorem lambda_norm_comparisons_for_lemma_4_12 {m n : ℕ}
    {Λ : Mat n n} (hΛ : MatrixPositiveDefinite Λ) (A : Mat m n) :
    (frobeniusNorm A ≤ Real.sqrt (spectralNorm Λ) * lambdaInvNorm Λ A ∧
      lambdaNorm Λ A ≤ Real.sqrt (spectralNorm Λ) * frobeniusNorm A) ∧
    (nuclearNorm A ≤ Real.sqrt (nuclearNorm Λ) * lambdaInvNorm Λ A ∧
      lambdaNorm Λ A ≤ Real.sqrt (nuclearNorm Λ) * spectralNorm A) := by
  have hpos : Λ.PosDef := by simpa [MatrixPositiveDefinite] using hΛ
  have hherm := hpos.isHermitian
  have hinv_pos : MatrixPositiveDefinite Λ⁻¹ := by
    simpa [MatrixPositiveDefinite] using hpos.inv
  have hinvPosDef : (Λ⁻¹).PosDef := by
    simpa [MatrixPositiveDefinite] using hinv_pos
  have hquadratic_nonneg {p q : ℕ} (Q : Mat q q) (hQ : Q.PosDef)
      (B : Mat p q) : 0 ≤ frobeniusInner (B * Q) B := by
    have htransQ : Qᵀ = Q := by simpa using hQ.isHermitian.eq
    have hpsd : (B * Q * Bᵀ).PosSemidef := by
      simpa using hQ.posSemidef.mul_mul_conjTranspose_same B
    calc
      0 ≤ Matrix.trace (B * Q * Bᵀ) := hpsd.trace_nonneg
      _ = Matrix.trace (B * (Q * Bᵀ)) := by rw [Matrix.mul_assoc]
      _ = Matrix.trace ((Q * Bᵀ) * B) := Matrix.trace_mul_comm _ _
      _ = frobeniusInner (B * Q) B := by
        rw [frobeniusInner_eq_trace_transpose_mul]
        simp [Matrix.transpose_mul, htransQ, Matrix.mul_assoc]
  have hWeightedCauchy (X Y : Mat m n) :
      frobeniusInner X Y ^ 2 ≤
        frobeniusInner (X * Λ⁻¹) X * frobeniusInner (Y * Λ) Y := by
    letI : Invertible Λ := hpos.isUnit.invertible
    letI weightedNormed := Matrix.toNormedAddCommGroup Λ⁻¹ hinvPosDef
    letI weightedInner := Matrix.toInnerProductSpace Λ⁻¹ hinvPosDef.posSemidef
    let win : (Fin n → ℝ) → (Fin n → ℝ) → ℝ :=
      fun u v => (Λ⁻¹ *ᵥ v) ⬝ᵥ u
    let x : Fin m → (Fin n → ℝ) := fun i j => X i j
    let z : Fin m → (Fin n → ℝ) := fun i j => (Y * Λ) i j
    have htrans : Λᵀ = Λ := by simpa using hherm.eq
    have hz (i : Fin m) : z i = Λ *ᵥ (fun j => Y i j) := by
      ext j
      simp only [z, Matrix.mul_apply, Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro k _hk
      have hs : Λ k j = Λ j k := by simpa using hherm.apply j k
      rw [hs]
      ring
    have hwinSelfNonneg (u : Fin n → ℝ) : 0 ≤ win u u := by
      simpa [win, dotProduct, mul_comm] using
        hinvPosDef.posSemidef.re_dotProduct_nonneg u
    have hpair (i : Fin m) :
        win (x i) (z i) = ∑ j : Fin n, X i j * Y i j := by
      change (Λ⁻¹ *ᵥ z i) ⬝ᵥ x i = _
      rw [hz, Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible,
        Matrix.one_mulVec]
      simp [x, dotProduct, mul_comm]
    have hselfX (i : Fin m) :
        win (x i) (x i) = ∑ j : Fin n, (X * Λ⁻¹) i j * X i j := by
      change (Λ⁻¹ *ᵥ x i) ⬝ᵥ x i = _
      simp only [x, Matrix.mul_apply, Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _hk
      have hs : Λ⁻¹ k j = Λ⁻¹ j k := by
        simpa using hinvPosDef.isHermitian.apply j k
      rw [hs]
      ring
    have hselfZ (i : Fin m) :
        win (z i) (z i) = ∑ j : Fin n, (Y * Λ) i j * Y i j := by
      change (Λ⁻¹ *ᵥ z i) ⬝ᵥ z i = _
      rw [hz, Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible,
        Matrix.one_mulVec]
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _hk
      have hs : Λ k j = Λ j k := by simpa using hherm.apply j k
      rw [hs]
      ring
    have hrowAbs (i : Fin m) :
        |win (x i) (z i)| ≤
          Real.sqrt (win (x i) (x i)) * Real.sqrt (win (z i) (z i)) := by
      have ha : 0 ≤ win (x i) (x i) := by
        exact hwinSelfNonneg (x i)
      have hb : 0 ≤ win (z i) (z i) := by
        exact hwinSelfNonneg (z i)
      have hcs := @real_inner_mul_inner_self_le (Fin n → ℝ)
        weightedNormed.toSeminormedAddCommGroup weightedInner (x i) (z i)
      change win (x i) (z i) * win (x i) (z i) ≤
        win (x i) (x i) * win (z i) (z i) at hcs
      have hsquare :
          (Real.sqrt (win (x i) (x i)) * Real.sqrt (win (z i) (z i))) ^ 2 =
            win (x i) (x i) * win (z i) (z i) := by
        rw [mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb]
      apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _)
        (Real.sqrt_nonneg _))).mp
      rw [sq_abs, hsquare]
      simpa [pow_two] using hcs
    have habs :
        |frobeniusInner X Y| ≤
          Real.sqrt (∑ i : Fin m, win (x i) (x i)) *
            Real.sqrt (∑ i : Fin m, win (z i) (z i)) := by
      calc
        |frobeniusInner X Y| = |∑ i : Fin m, win (x i) (z i)| := by
          congr 1
          unfold frobeniusInner
          exact Finset.sum_congr rfl (fun i _hi => (hpair i).symm)
        _ ≤ ∑ i : Fin m, |win (x i) (z i)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i : Fin m,
            Real.sqrt (win (x i) (x i)) * Real.sqrt (win (z i) (z i)) := by
          exact Finset.sum_le_sum (fun i _hi => hrowAbs i)
        _ ≤ Real.sqrt (∑ i : Fin m, win (x i) (x i)) *
            Real.sqrt (∑ i : Fin m, win (z i) (z i)) := by
          exact Real.sum_sqrt_mul_sqrt_le Finset.univ
            (fun i => hwinSelfNonneg (x i))
            (fun i => hwinSelfNonneg (z i))
    have hsx : 0 ≤ ∑ i : Fin m, win (x i) (x i) :=
      Finset.sum_nonneg (fun i _hi => hwinSelfNonneg (x i))
    have hsz : 0 ≤ ∑ i : Fin m, win (z i) (z i) :=
      Finset.sum_nonneg (fun i _hi => hwinSelfNonneg (z i))
    have hsq := (sq_le_sq₀ (abs_nonneg (frobeniusInner X Y))
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2 habs
    have hrootSq :
        (Real.sqrt (∑ i : Fin m, win (x i) (x i)) *
          Real.sqrt (∑ i : Fin m, win (z i) (z i))) ^ 2 =
            (∑ i : Fin m, win (x i) (x i)) *
              (∑ i : Fin m, win (z i) (z i)) := by
      rw [mul_pow, Real.sq_sqrt hsx, Real.sq_sqrt hsz]
    have hsq' := hsq.trans_eq hrootSq
    rw [sq_abs] at hsq'
    have hsumX :
        (∑ i : Fin m, win (x i) (x i)) = frobeniusInner (X * Λ⁻¹) X := by
      unfold frobeniusInner
      exact Finset.sum_congr rfl (fun i _hi => hselfX i)
    have hsumZ :
        (∑ i : Fin m, win (z i) (z i)) = frobeniusInner (Y * Λ) Y := by
      unfold frobeniusInner
      exact Finset.sum_congr rfl (fun i _hi => hselfZ i)
    rw [hsumX, hsumZ] at hsq'
    exact hsq'
  let L := (Matrix.toEuclideanLin (𝕜 := ℝ) Λ).toContinuousLinearMap
  have hEq9Sq :
      frobeniusInner (A * Λ) A ≤ spectralNorm Λ * frobeniusNorm A ^ 2 := by
    have hrow (i : Fin m) :
        (∑ j : Fin n, (A * Λ) i j * A i j) ≤
          spectralNorm Λ * ∑ j : Fin n, A i j ^ 2 := by
      let x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun j => A i j)
      have hinner :
          (∑ j : Fin n, (A * Λ) i j * A i j) = ⟪x, L x⟫_ℝ := by
        simp [x, L, Matrix.mul_apply,
          Matrix.toEuclideanLin_apply_piLp_toLp, PiLp.inner_apply,
          dotProduct, real_inner_eq_re_inner, RCLike.inner_apply]
        change
          (∑ j : Fin n, (∑ k : Fin n, A i k * Λ k j) * A i j) =
            ∑ j : Fin n, (∑ k : Fin n, Λ j k * A i k) * A i j
        apply Finset.sum_congr rfl
        intro j _hj
        rw [Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _hk
        have hs : Λ k j = Λ j k := by
          simpa using hherm.apply j k
        rw [hs]
        ring
      have hnormx : ‖x‖ ^ 2 = ∑ j : Fin n, A i j ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        simp [x, Real.norm_eq_abs, sq_abs]
      rw [hinner, ← hnormx]
      calc
        ⟪x, L x⟫_ℝ ≤ |⟪x, L x⟫_ℝ| := le_abs_self _
        _ ≤ ‖x‖ * ‖L x‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖x‖ * (‖L‖ * ‖x‖) :=
          mul_le_mul_of_nonneg_left (L.le_opNorm x) (norm_nonneg x)
        _ = spectralNorm Λ * ‖x‖ ^ 2 := by
          simp only [L, spectralNorm]
          ring
    unfold frobeniusInner
    calc
      (∑ i : Fin m, ∑ j : Fin n, (A * Λ) i j * A i j) ≤
          ∑ i : Fin m, spectralNorm Λ * ∑ j : Fin n, A i j ^ 2 := by
            exact Finset.sum_le_sum (fun i _hi => hrow i)
      _ = spectralNorm Λ * frobeniusNorm A ^ 2 := by
            rw [frobeniusNorm_sq_eq_sum_entries_sq, ← Finset.mul_sum]
            exact congrArg (fun z : ℝ => spectralNorm Λ * z) Finset.sum_comm
  have hself : frobeniusInner A A = frobeniusNorm A ^ 2 := by
    calc
      frobeniusInner A A = ∑ i : Fin m, ∑ j : Fin n, A i j ^ 2 := by
        simp [frobeniusInner, pow_two]
      _ = ∑ j : Fin n, ∑ i : Fin m, A i j ^ 2 := Finset.sum_comm
      _ = frobeniusNorm A ^ 2 := (frobeniusNorm_sq_eq_sum_entries_sq A).symm
  have hEq8Sq :
      frobeniusNorm A ^ 2 ≤
        spectralNorm Λ * frobeniusInner (A * Λ⁻¹) A := by
    have hcs := hWeightedCauchy A A
    rw [hself] at hcs
    have hqinv : 0 ≤ frobeniusInner (A * Λ⁻¹) A :=
      hquadratic_nonneg Λ⁻¹ hinvPosDef A
    have hprod :
        frobeniusInner (A * Λ⁻¹) A * frobeniusInner (A * Λ) A ≤
          frobeniusInner (A * Λ⁻¹) A *
            (spectralNorm Λ * frobeniusNorm A ^ 2) :=
      mul_le_mul_of_nonneg_left hEq9Sq hqinv
    by_cases hzero : frobeniusNorm A = 0
    · rw [hzero]
      simpa using mul_nonneg (spectralNorm_nonneg Λ) hqinv
    · have hFpos : 0 < frobeniusNorm A :=
        lt_of_le_of_ne (by simp [frobeniusNorm]) (Ne.symm hzero)
      have hSpos : 0 < frobeniusNorm A ^ 2 := sq_pos_of_pos hFpos
      have hcancel :
          frobeniusNorm A ^ 2 * frobeniusNorm A ^ 2 ≤
            (spectralNorm Λ * frobeniusInner (A * Λ⁻¹) A) *
              frobeniusNorm A ^ 2 := by
        simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using
          (le_trans hcs hprod)
      nlinarith
  have htrans : Λᵀ = Λ := by
    simpa using hherm.eq
  have htraceCycle (B : Mat m n) :
      frobeniusInner (B * Λ) B = frobeniusInner Λ (Bᵀ * B) := by
    rw [frobeniusInner_eq_trace_transpose_mul,
      frobeniusInner_eq_trace_transpose_mul]
    simp [Matrix.transpose_mul, htrans, Matrix.mul_assoc]
  have hspectralGram (B : Mat m n) :
      spectralNorm (Bᵀ * B) = spectralNorm B ^ 2 := by
    simpa [spectralNorm, Matrix.l2_opNorm_def, pow_two] using
      (Matrix.l2_opNorm_conjTranspose_mul_self B)
  have hEq10SqFor (B : Mat m n) :
      frobeniusInner (B * Λ) B ≤ nuclearNorm Λ * spectralNorm B ^ 2 := by
    rw [htraceCycle B]
    calc
      frobeniusInner Λ (Bᵀ * B) ≤ |frobeniusInner Λ (Bᵀ * B)| := le_abs_self _
      _ ≤ nuclearNorm Λ * spectralNorm (Bᵀ * B) :=
        abs_frobeniusInner_le_nuclearNorm_mul_spectralNorm Λ (Bᵀ * B)
      _ = nuclearNorm Λ * spectralNorm B ^ 2 := by rw [hspectralGram B]
  have hEq10Sq :
      frobeniusInner (A * Λ) A ≤ nuclearNorm Λ * spectralNorm A ^ 2 :=
    hEq10SqFor A
  have hEq9 :
      lambdaNorm Λ A ≤ Real.sqrt (spectralNorm Λ) * frobeniusNorm A := by
    unfold lambdaNorm
    rw [Real.sqrt_le_iff]
    refine ⟨mul_nonneg (Real.sqrt_nonneg _) (by simp [frobeniusNorm]), ?_⟩
    calc
      frobeniusInner (A * Λ) A ≤
          spectralNorm Λ * frobeniusNorm A ^ 2 := hEq9Sq
      _ = (Real.sqrt (spectralNorm Λ) * frobeniusNorm A) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (spectralNorm_nonneg Λ)]
  have hEq8 :
      frobeniusNorm A ≤ Real.sqrt (spectralNorm Λ) * lambdaInvNorm Λ A := by
    have hqinv : 0 ≤ frobeniusInner (A * Λ⁻¹) A :=
      hquadratic_nonneg Λ⁻¹ hinvPosDef A
    have hInvSq :
        lambdaInvNorm Λ A ^ 2 = frobeniusInner (A * Λ⁻¹) A := by
      unfold lambdaInvNorm lambdaNorm
      exact Real.sq_sqrt hqinv
    have hRhsSq :
        (Real.sqrt (spectralNorm Λ) * lambdaInvNorm Λ A) ^ 2 =
          spectralNorm Λ * frobeniusInner (A * Λ⁻¹) A := by
      rw [mul_pow, Real.sq_sqrt (spectralNorm_nonneg Λ), hInvSq]
    have hsq :
        frobeniusNorm A ^ 2 ≤
          (Real.sqrt (spectralNorm Λ) * lambdaInvNorm Λ A) ^ 2 := by
      rw [hRhsSq]
      exact hEq8Sq
    have hleft : 0 ≤ frobeniusNorm A := by simp [frobeniusNorm]
    have hright :
        0 ≤ Real.sqrt (spectralNorm Λ) * lambdaInvNorm Λ A := by
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith
  have hEq10 :
      lambdaNorm Λ A ≤ Real.sqrt (nuclearNorm Λ) * spectralNorm A := by
    unfold lambdaNorm
    rw [Real.sqrt_le_iff]
    refine ⟨mul_nonneg (Real.sqrt_nonneg _) (spectralNorm_nonneg A), ?_⟩
    calc
      frobeniusInner (A * Λ) A ≤
          nuclearNorm Λ * spectralNorm A ^ 2 := hEq10Sq
      _ = (Real.sqrt (nuclearNorm Λ) * spectralNorm A) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (nuclearNorm_nonneg Λ)]
  let P : Mat m n := orthogonalizedDirection A
  have hPspec : spectralNorm P ≤ 1 := by
    rcases orthogonalizedDirection_isThinSVDWithPolar A with
      ⟨U, V, s, hU, hV, hs, hAfac, hPfac⟩
    rw [show P = U * Vᵀ by simpa [P] using hPfac]
    exact spectralNorm_mul_transpose_le_one_of_orthonormalColumns U V hU hV
  have hEqA1Sq :
      nuclearNorm A ^ 2 ≤
        nuclearNorm Λ * frobeniusInner (A * Λ⁻¹) A := by
    have hcs := hWeightedCauchy A P
    have hpair : frobeniusInner A P = nuclearNorm A := by
      simpa [P] using orthogonalizedDirection_frobeniusInner_eq_nuclearNorm A
    rw [hpair] at hcs
    have hPspecSq : spectralNorm P ^ 2 ≤ 1 := by
      nlinarith [spectralNorm_nonneg P]
    have hqP : frobeniusInner (P * Λ) P ≤ nuclearNorm Λ := by
      calc
        frobeniusInner (P * Λ) P ≤
            nuclearNorm Λ * spectralNorm P ^ 2 := hEq10SqFor P
        _ ≤ nuclearNorm Λ * 1 :=
          mul_le_mul_of_nonneg_left hPspecSq (nuclearNorm_nonneg Λ)
        _ = nuclearNorm Λ := by ring
    have hqinv : 0 ≤ frobeniusInner (A * Λ⁻¹) A :=
      hquadratic_nonneg Λ⁻¹ hinvPosDef A
    have hmul := mul_le_mul_of_nonneg_left hqP hqinv
    exact le_trans hcs (by simpa [mul_comm] using hmul)
  have hEqA1 :
      nuclearNorm A ≤ Real.sqrt (nuclearNorm Λ) * lambdaInvNorm Λ A := by
    have hqinv : 0 ≤ frobeniusInner (A * Λ⁻¹) A :=
      hquadratic_nonneg Λ⁻¹ hinvPosDef A
    have hInvSq :
        lambdaInvNorm Λ A ^ 2 = frobeniusInner (A * Λ⁻¹) A := by
      unfold lambdaInvNorm lambdaNorm
      exact Real.sq_sqrt hqinv
    have hRhsSq :
        (Real.sqrt (nuclearNorm Λ) * lambdaInvNorm Λ A) ^ 2 =
          nuclearNorm Λ * frobeniusInner (A * Λ⁻¹) A := by
      rw [mul_pow, Real.sq_sqrt (nuclearNorm_nonneg Λ), hInvSq]
    have hsq :
        nuclearNorm A ^ 2 ≤
          (Real.sqrt (nuclearNorm Λ) * lambdaInvNorm Λ A) ^ 2 := by
      rw [hRhsSq]
      exact hEqA1Sq
    have hleft : 0 ≤ nuclearNorm A := nuclearNorm_nonneg A
    have hright :
        0 ≤ Real.sqrt (nuclearNorm Λ) * lambdaInvNorm Λ A := by
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith
  -- Appendix A.1/A.2: diagonalize the positive definite matrix and compare the
  -- resulting weighted column-square sums with the Frobenius, spectral, and
  -- nuclear singular-value norms.
  exact ⟨⟨hEq8, hEq9⟩, hEqA1, hEq10⟩

theorem proposition_3_6 {m n : ℕ} (P : Objective m n) (ε : ℝ) (W : Mat m n) :
    (IsNuclearStationary P ε W → IsFrobeniusStationary P ε W) ∧
      (IsFrobeniusStationary P ε W →
        IsNuclearStationary P (Real.sqrt (matrixRankBound m n : ℝ) * ε) W) := by
  constructor
  · intro hN
    unfold IsNuclearStationary IsFrobeniusStationary at *
    exact le_trans (frobeniusNorm_le_nuclearNorm (P.grad W)) hN
  · intro hF
    unfold IsNuclearStationary IsFrobeniusStationary at *
    exact le_trans
      (nuclearNorm_le_sqrt_rankBound_mul_frobeniusNorm (P.grad W))
      (mul_le_mul_of_nonneg_left hF (Real.sqrt_nonneg _))

theorem theorem_4_1 {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (L σ η : ℝ)
    (_hη : ∀ t ∈ Finset.range T, cfg.eta t = η)
    (_hsmooth : FrobeniusSmooth P.objective L)
    (_hvariance : BoundedVariance P σ) :
    theorem_4_1_statement P cfg T L σ η := by
  constructor
  · exact theorem_4_1_source_domain_obligation
      P cfg T L σ η _hη _hsmooth _hvariance
  · intro hsrc
    rcases theorem_4_1_downstream_phase2_boundary_of_sourceDomain
        P cfg T L σ η hsrc _hη _hsmooth _hvariance with
      ⟨hbasic, hdom, _hηpos⟩
    rcases hdom with
      ⟨hT, hdrop, hsNoise, hsBatchNoise, hqBatchNoise, hsRank, hsBatch,
        hqTail, hqMomentum⟩
    refine ⟨hbasic,
      ⟨hT, hdrop, hsNoise, hsBatchNoise, hqBatchNoise, hsRank, hsBatch,
        hqTail, hqMomentum⟩, ?_⟩
    have hbound := theorem_4_1_source_average_bound_at_horizon_sourceRhs
      P cfg T L σ η hsrc _hη _hsmooth _hvariance
    simpa [stochasticAverageNuclearGradientRealized,
      stochasticAverageNuclearGradient, stochasticExpectedObjectiveDropRealized,
      stochasticExpectedObjectiveDrop, realizedExpectation, theorem_4_1_rhs,
      theorem_4_1_sourceRhs, realizedSourceQuot, sourceQuot,
      realizedSourceSqrt, sourceSqrt] using hbound

theorem stochastic_expected_objective_drop_le_source_initial_gap
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n) (T : ℕ)
    (hfinite : P.objective.HasFiniteInfimum)
    (hwd : stochasticExpectedObjectiveDropWellDefined P cfg T) :
    stochasticExpectedObjectiveDrop P cfg T ≤
      sourceObjectiveInitialGap P.objective cfg.W0 hfinite := by
  let μ := samplePathLaw P cfg.batchSize
  letI : IsProbabilityMeasure P.sampleLaw := P.isProbability_sampleLaw
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, samplePathLaw]
    infer_instance
  have hdrop_int : Integrable
      (fun ω => P.objective.f cfg.W0 -
        P.objective.f (stochasticMuonState P cfg ω T).W) μ := by
    simpa [μ, stochasticExpectedObjectiveDropWellDefined,
      SOptLib.expectationWellDefined] using hwd
  have hlower (ω : SamplePath ξ cfg.batchSize) :
      P.objective.sourceFStar hfinite ≤
        P.objective.f (stochasticMuonState P cfg ω T).W := by
    simpa [Objective.sourceFStar, Objective.fStar] using
      (csInf_le hfinite (show
        P.objective.f (stochasticMuonState P cfg ω T).W ∈
          Set.range P.objective.f from
        ⟨(stochasticMuonState P cfg ω T).W, rfl⟩))
  have hint :
      (∫ ω, P.objective.f cfg.W0 -
          P.objective.f (stochasticMuonState P cfg ω T).W ∂μ) ≤
        ∫ _ω, sourceObjectiveInitialGap P.objective cfg.W0 hfinite ∂μ := by
    apply integral_mono hdrop_int (integrable_const _)
    intro ω
    dsimp [sourceObjectiveInitialGap]
    linarith [hlower ω]
  simpa [stochasticExpectedObjectiveDrop, μ, integral_const,
    measureReal_univ_eq_one] using hint

set_option maxHeartbeats 800000 in
theorem corollary_4_2_stochastic_schedule_scalar_bound
    {m n T : ℕ} {L σ Δ : ℝ}
    (hreg : corollary_4_2_stochasticRegime m n L σ Δ)
    (hT : corollary_4_2_stochasticRateDomain m n T L σ Δ) :
    let q := corollary_4_2_stochasticOneMinusBeta T L σ Δ
    let η := corollary_4_2_stochasticEta m n T L σ Δ
    Δ / ((T : ℝ) * η) +
        L * (matrixRankBound m n : ℝ) * η / 2 +
        (2 * σ * Real.sqrt ((matrixRankBound m n : ℝ) * q)) /
          Real.sqrt (2 - q) +
        (2 * σ * Real.sqrt (matrixRankBound m n : ℝ)) /
          (q * (T : ℝ)) +
        (2 * (matrixRankBound m n : ℝ) * η * (1 - q) * L) / q ≤
      10 * corollary_4_2_stochasticRateRealized m n T L σ Δ hT := by
  dsimp only
  unfold corollary_4_2_stochasticRegime at hreg
  rcases hreg with ⟨hrNat, hL, hσ, hΔ⟩
  let r : ℝ := matrixRankBound m n
  let τ : ℝ := T
  let q : ℝ := corollary_4_2_stochasticOneMinusBeta T L σ Δ
  let η : ℝ := corollary_4_2_stochasticEta m n T L σ Δ
  let A : ℝ := Δ / (τ * η)
  have hr : 0 < r := by
    dsimp [r]
    exact_mod_cast hrNat
  have hτ : 0 < τ := by
    dsimp [τ]
    exact_mod_cast hT.1
  have hrootLD : 0 < Real.sqrt (L * Δ) := Real.sqrt_pos.2 (mul_pos hL hΔ)
  have hrootτ : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ
  have hratio :
      0 < sourceQuot (Real.sqrt (L * Δ)) (σ * Real.sqrt τ) := by
    unfold sourceQuot
    positivity
  have hq : 0 < q := by
    dsimp [q, corollary_4_2_stochasticOneMinusBeta]
    exact lt_min hratio zero_lt_one
  have hqle : q ≤ 1 := by
    dsimp [q, corollary_4_2_stochasticOneMinusBeta]
    exact min_le_right _ _
  have hη : 0 < η := by
    dsimp [η, corollary_4_2_stochasticEta, sourceQuot]
    apply Real.sqrt_pos.2
    positivity
  have hηsq : η ^ 2 = q * Δ / (r * τ * L) := by
    dsimp [η, corollary_4_2_stochasticEta, sourceQuot, q, r, τ]
    rw [Real.sq_sqrt]
    positivity
  have hscale : r * L * η = q * A := by
    have hden : r * τ * L ≠ 0 := by positivity
    have hηpoly : η ^ 2 * (r * τ * L) = q * Δ :=
      (eq_div_iff hden).mp hηsq
    dsimp [A]
    calc
      r * L * η = (q * Δ) / (τ * η) := by
        apply (eq_div_iff (mul_ne_zero (ne_of_gt hτ) (ne_of_gt hη))).2
        ring_nf at hηpoly ⊢
        nlinarith
      _ = q * (Δ / (τ * η)) := by ring
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hsmoothEq : L * r * η / 2 = q * A / 2 := by
    rw [show L * r * η = r * L * η by ring, hscale]
  have hmomentumEq :
      (2 * r * η * (1 - q) * L) / q = 2 * (1 - q) * A := by
    apply (div_eq_iff (ne_of_gt hq)).2
    calc
      2 * r * η * (1 - q) * L = 2 * (1 - q) * (r * L * η) := by ring
      _ = 2 * (1 - q) * (q * A) := by rw [hscale]
      _ = 2 * (1 - q) * A * q := by ring
  change A + L * r * η / 2 +
        (2 * σ * Real.sqrt (r * q)) / Real.sqrt (2 - q) +
        (2 * σ * Real.sqrt r) / (q * τ) +
        (2 * r * η * (1 - q) * L) / q ≤
      10 * corollary_4_2_stochasticRateRealized m n T L σ Δ hT
  rw [hsmoothEq, hmomentumEq]
  have hdenOne : 1 ≤ Real.sqrt (2 - q) := by
    rw [Real.one_le_sqrt]
    linarith
  have hdenPos : 0 < Real.sqrt (2 - q) := lt_of_lt_of_le zero_lt_one hdenOne
  have hnoiseNonneg : 0 ≤ 2 * σ * Real.sqrt (r * q) := by positivity
  have hnoise :
      (2 * σ * Real.sqrt (r * q)) / Real.sqrt (2 - q) ≤
        2 * σ * Real.sqrt (r * q) := by
    apply (div_le_iff₀ hdenPos).2
    exact le_mul_of_one_le_right hnoiseNonneg hdenOne
  have hηexpr : η = q * A / (r * L) := by
    apply (eq_div_iff (mul_ne_zero (ne_of_gt hr) (ne_of_gt hL))).2
    nlinarith [hscale]
  have hAsq : A ^ 2 = r * L * Δ / (τ * q) := by
    have hAeq : A = Δ / (τ * (q * A / (r * L))) := by
      dsimp [A]
      rw [← hηexpr]
    have hdenA : τ * (q * A / (r * L)) ≠ 0 := by positivity
    have hApoly := (eq_div_iff hdenA).mp hAeq
    apply (eq_div_iff (mul_ne_zero (ne_of_gt hτ) (ne_of_gt hq))).2
    field_simp [ne_of_gt hr, ne_of_gt hL] at hApoly
    ring_nf at hApoly ⊢
    nlinarith
  let R₁ : ℝ := Real.sqrt (Real.sqrt ((r ^ 2 * L * Δ * σ ^ 2) / τ))
  let R₂ : ℝ := Real.sqrt ((r * L * Δ) / τ)
  let R₃ : ℝ := Real.sqrt r * σ ^ 2 / Real.sqrt (L * Δ * τ)
  have hR₁ : 0 ≤ R₁ := by dsimp [R₁]; positivity
  have hR₂ : 0 ≤ R₂ := by dsimp [R₂]; positivity
  have hR₃ : 0 ≤ R₃ := by dsimp [R₃]; positivity
  change A + q * A / 2 +
        (2 * σ * Real.sqrt (r * q)) / Real.sqrt (2 - q) +
        (2 * σ * Real.sqrt r) / (q * τ) +
        2 * (1 - q) * A ≤
      10 * (R₁ + R₂ + R₃)
  let d : ℝ := Real.sqrt (L * Δ)
  let s : ℝ := Real.sqrt τ
  have hd : 0 < d := by dsimp [d]; positivity
  have hs : 0 < s := by dsimp [s]; positivity
  have hdsq : d ^ 2 = L * Δ := by
    dsimp [d]
    exact Real.sq_sqrt (mul_nonneg hL.le hΔ.le)
  have hssq : s ^ 2 = τ := by
    dsimp [s]
    exact Real.sq_sqrt hτ.le
  by_cases ha : sourceQuot (Real.sqrt (L * Δ)) (σ * Real.sqrt τ) ≤ 1
  · have hqeq : q = d / (σ * s) := by
      dsimp [q, corollary_4_2_stochasticOneMinusBeta]
      rw [min_eq_left ha]
      rfl
    have hAsq' : A ^ 2 = r * d * σ / s := by
      rw [hAsq, hqeq]
      field_simp [ne_of_gt hσ, ne_of_gt hs, ne_of_gt hd]
      nlinarith [hdsq, hssq]
    have hrad : 0 ≤ (r ^ 2 * L * Δ * σ ^ 2) / τ := by positivity
    have hR₁four : R₁ ^ 4 = (r ^ 2 * L * Δ * σ ^ 2) / τ := by
      dsimp [R₁]
      calc
        Real.sqrt (Real.sqrt ((r ^ 2 * L * Δ * σ ^ 2) / τ)) ^ 4 =
            (Real.sqrt (Real.sqrt ((r ^ 2 * L * Δ * σ ^ 2) / τ)) ^ 2) ^ 2 := by
              ring
        _ = Real.sqrt ((r ^ 2 * L * Δ * σ ^ 2) / τ) ^ 2 := by
              rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
        _ = (r ^ 2 * L * Δ * σ ^ 2) / τ := Real.sq_sqrt hrad
    have hAfour : A ^ 4 = (r ^ 2 * L * Δ * σ ^ 2) / τ := by
      calc
        A ^ 4 = (A ^ 2) ^ 2 := by ring
        _ = (r * d * σ / s) ^ 2 := by rw [hAsq']
        _ = (r ^ 2 * d ^ 2 * σ ^ 2) / s ^ 2 := by
          field_simp [ne_of_gt hs]
        _ = (r ^ 2 * L * Δ * σ ^ 2) / τ := by
          rw [hdsq, hssq]
          ring
    have hAR₁sq : A ^ 2 = R₁ ^ 2 := by
      apply (mul_self_inj_of_nonneg (sq_nonneg A) (sq_nonneg R₁)).mp
      calc
        A ^ 2 * A ^ 2 = A ^ 4 := by ring
        _ = (r ^ 2 * L * Δ * σ ^ 2) / τ := hAfour
        _ = R₁ ^ 4 := hR₁four.symm
        _ = R₁ ^ 2 * R₁ ^ 2 := by ring
    have hAR₁ : A = R₁ := by
      apply (mul_self_inj_of_nonneg hA.le hR₁).mp
      simpa [pow_two] using hAR₁sq
    have hnoiseEq : σ * Real.sqrt (r * q) = A := by
      have hsq : (σ * Real.sqrt (r * q)) ^ 2 = A ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (mul_nonneg hr.le hq.le), hAsq', hqeq]
        field_simp [ne_of_gt hσ, ne_of_gt hs]
      apply (mul_self_inj_of_nonneg
        (mul_nonneg hσ.le (Real.sqrt_nonneg _)) hA.le).mp
      simpa [pow_two] using hsq
    have hrootProduct : Real.sqrt (L * Δ * τ) = d * s := by
      calc
        Real.sqrt (L * Δ * τ) = Real.sqrt (L * Δ) * Real.sqrt τ := by
          rw [Real.sqrt_mul (mul_nonneg hL.le hΔ.le)]
        _ = d * s := rfl
    have htailEq :
        (2 * σ * Real.sqrt r) / (q * τ) = 2 * R₃ := by
      rw [hqeq, ← hssq]
      dsimp [R₃]
      rw [hrootProduct]
      field_simp [ne_of_gt hσ, ne_of_gt hd, ne_of_gt hs]
    have hsmoothBound : q * A / 2 ≤ A / 2 := by
      exact div_le_div_of_nonneg_right
        (by simpa using mul_le_mul_of_nonneg_right hqle hA.le) (by norm_num)
    have hmomentumBound : 2 * (1 - q) * A ≤ 2 * A := by
      have hbase : (1 - q) * A ≤ A := by
        have hone : 1 - q ≤ 1 := sub_le_self 1 hq.le
        simpa using mul_le_mul_of_nonneg_right hone hA.le
      calc
        2 * (1 - q) * A = 2 * ((1 - q) * A) := by ring
        _ ≤ 2 * A := mul_le_mul_of_nonneg_left hbase (by norm_num)
    have hnoiseBound :
        (2 * σ * Real.sqrt (r * q)) / Real.sqrt (2 - q) ≤ 2 * A := by
      calc
        _ ≤ 2 * σ * Real.sqrt (r * q) := hnoise
        _ = 2 * (σ * Real.sqrt (r * q)) := by ring
        _ = 2 * A := by rw [hnoiseEq]
    have hsumBound :
        A + q * A / 2 +
            (2 * σ * Real.sqrt (r * q)) / Real.sqrt (2 - q) +
            (2 * σ * Real.sqrt r) / (q * τ) +
            2 * (1 - q) * A ≤
          (11 / 2 : ℝ) * A + 2 * R₃ := by
      rw [htailEq]
      linarith only [hsmoothBound, hmomentumBound, hnoiseBound]
    calc
      _ ≤ (11 / 2 : ℝ) * A + 2 * R₃ := hsumBound
      _ ≤ 10 * (R₁ + R₂ + R₃) := by
        rw [hAR₁]
        nlinarith only [hR₁, hR₂, hR₃]
  · have hratioOne :
        1 < sourceQuot (Real.sqrt (L * Δ)) (σ * Real.sqrt τ) :=
      lt_of_not_ge ha
    have hqeq : q = 1 := by
      dsimp [q, corollary_4_2_stochasticOneMinusBeta]
      rw [min_eq_right hratioOne.le]
    have hR₂sq : R₂ ^ 2 = (r * L * Δ) / τ := by
      dsimp [R₂]
      exact Real.sq_sqrt (by positivity)
    have hAR₂sq : A ^ 2 = R₂ ^ 2 := by
      rw [hAsq, hqeq, mul_one, hR₂sq]
    have hAR₂ : A = R₂ := by
      apply (mul_self_inj_of_nonneg hA.le hR₂).mp
      simpa [pow_two] using hAR₂sq
    have hσs : σ * s < d := by
      have hone : 1 < d / (σ * s) := by
        simpa [d, s, sourceQuot] using hratioOne
      exact (one_lt_div (mul_pos hσ hs)).mp hone
    have hσscale : σ ^ 2 * τ ≤ L * Δ := by
      have hsquare : (σ * s) ^ 2 ≤ d ^ 2 :=
        (sq_le_sq₀ (mul_nonneg hσ.le hs.le) hd.le).2 hσs.le
      simpa [mul_pow, hssq, hdsq] using hsquare
    have hnoiseBase : σ * Real.sqrt r ≤ A := by
      apply (sq_le_sq₀ (mul_nonneg hσ.le (Real.sqrt_nonneg _)) hA.le).mp
      calc
        (σ * Real.sqrt r) ^ 2 = σ ^ 2 * r := by
          rw [mul_pow, Real.sq_sqrt hr.le]
        _ ≤ (r * L * Δ) / τ := by
          apply (le_div_iff₀ hτ).2
          have hscaled := mul_le_mul_of_nonneg_left hσscale hr.le
          nlinarith
        _ = A ^ 2 := by
          rw [hAsq, hqeq, mul_one]
    have hnoiseBound :
        (2 * σ * Real.sqrt (r * q)) / Real.sqrt (2 - q) ≤ 2 * A := by
      calc
        _ ≤ 2 * σ * Real.sqrt (r * q) := hnoise
        _ = 2 * (σ * Real.sqrt r) := by rw [hqeq, mul_one]; ring
        _ ≤ 2 * A := mul_le_mul_of_nonneg_left hnoiseBase (by norm_num)
    have hτone : (1 : ℝ) ≤ τ := by
      dsimp [τ]
      exact_mod_cast hT.1
    have htailBound : (2 * σ * Real.sqrt r) / (q * τ) ≤ 2 * A := by
      rw [hqeq, one_mul]
      calc
        (2 * σ * Real.sqrt r) / τ ≤ 2 * σ * Real.sqrt r := by
          apply (div_le_iff₀ hτ).2
          exact le_mul_of_one_le_right (by positivity) hτone
        _ = 2 * (σ * Real.sqrt r) := by ring
        _ ≤ 2 * A := mul_le_mul_of_nonneg_left hnoiseBase (by norm_num)
    have hnoiseUnit : 2 * σ * Real.sqrt r ≤ 2 * A := by
      calc
        2 * σ * Real.sqrt r = 2 * (σ * Real.sqrt r) := by ring
        _ ≤ 2 * A := mul_le_mul_of_nonneg_left hnoiseBase (by norm_num)
    have htailUnit : (2 * σ * Real.sqrt r) / τ ≤ 2 * A := by
      simpa [hqeq] using htailBound
    have hsumBound :
        A + q * A / 2 +
            (2 * σ * Real.sqrt (r * q)) / Real.sqrt (2 - q) +
            (2 * σ * Real.sqrt r) / (q * τ) +
            2 * (1 - q) * A ≤ (11 / 2 : ℝ) * A := by
      rw [hqeq]
      simp only [mul_one, one_mul, sub_self, Real.sqrt_one, div_one, mul_zero,
        add_zero]
      norm_num only [Real.sqrt_one]
      simp only [div_one, zero_mul, add_zero]
      linarith only [hnoiseUnit, htailUnit]
    calc
      _ ≤ (11 / 2 : ℝ) * A := hsumBound
      _ ≤ 10 * (R₁ + R₂ + R₃) := by
        rw [hAR₂]
        nlinarith only [hR₁, hR₂, hR₃]

theorem corollary_4_2_stochastic_bound_at_realized_horizon
    {ξ : Type*} [MeasurableSpace ξ] {m n T : ℕ}
    (P : StochasticProblem ξ m n) (W0 : Mat m n) {L σ Δ : ℝ}
    (hfinite : P.objective.HasFiniteInfimum)
    (hΔeq : sourceObjectiveInitialGap P.objective W0 hfinite = Δ)
    (hsmooth : FrobeniusSmooth P.objective L)
    (hvariance : BoundedVariance P σ)
    (hreg : corollary_4_2_stochasticRegime m n L σ Δ)
    (horizon : horizonDomain T) :
    ∃ hT : corollary_4_2_stochasticSemanticHorizonDomain P W0 T L σ Δ,
      ∀ cfg : StochasticMuonConfig m n,
        ∀ hrun : corollary_4_2_stochasticRealization W0 T L σ Δ cfg,
          stochasticAverageNuclearGradientRealized P cfg T (hT.2 cfg hrun) ≤
            10 * corollary_4_2_stochasticRateRealized m n T L σ Δ hT.1.2.1 := by
  let hT := corollary_4_2_stochasticRegime_semantic
    P W0 hreg horizon hsmooth hvariance
  refine ⟨hT, ?_⟩
  intro cfg hrun
  let q := corollary_4_2_stochasticOneMinusBeta T L σ Δ
  let η := corollary_4_2_stochasticEta m n T L σ Δ
  have hηschedule : ∀ t ∈ Finset.range T, cfg.eta t = η := hrun.2.2.2.1
  have hηpos : 0 < η := by
    have hreg' := hreg
    unfold corollary_4_2_stochasticRegime at hreg'
    rcases hreg' with ⟨hrNat, hL, hσ, hΔ⟩
    have hr : 0 < (matrixRankBound m n : ℝ) := by exact_mod_cast hrNat
    have hTr : 0 < (T : ℝ) := by exact_mod_cast horizon
    have hq : 0 < q := by
      dsimp [q, corollary_4_2_stochasticOneMinusBeta, sourceQuot]
      apply lt_min
      · positivity
      · norm_num
    dsimp [η, corollary_4_2_stochasticEta, sourceQuot]
    apply Real.sqrt_pos.2
    positivity
  have hsrc : theorem_4_1_sourceDomain T η := by
    refine ⟨⟨horizon, ?_⟩, hηpos⟩
    unfold sourceQuotDomain
    exact mul_ne_zero (by exact_mod_cast ne_of_gt horizon) (ne_of_gt hηpos)
  have hresult := theorem_4_1 P cfg T L σ η hηschedule hsmooth hvariance
  rcases hresult.2 hsrc with ⟨hbasic, hdom, hbound⟩
  have hdrop : stochasticExpectedObjectiveDrop P cfg T ≤ Δ := by
    calc
      stochasticExpectedObjectiveDrop P cfg T ≤
          sourceObjectiveInitialGap P.objective cfg.W0 hfinite :=
        stochastic_expected_objective_drop_le_source_initial_gap
          P cfg T hfinite hbasic.2
      _ = Δ := by rw [hrun.2.1, hΔeq]
  have hden : 0 < (T : ℝ) * η := by
    exact mul_pos (by exact_mod_cast horizon) hηpos
  have hdropQuot :
      stochasticExpectedObjectiveDrop P cfg T / ((T : ℝ) * η) ≤
        Δ / ((T : ℝ) * η) :=
    div_le_div_of_nonneg_right hdrop hden.le
  have hbeta : cfg.beta = 1 - q := by
    dsimp [q]
    linarith [hrun.2.2.2.2]
  have hrhs :
      theorem_4_1_rhs P cfg T L σ η hbasic.2 hdom ≤
        Δ / ((T : ℝ) * η) +
          L * (matrixRankBound m n : ℝ) * η / 2 +
          (2 * σ * Real.sqrt ((matrixRankBound m n : ℝ) * q)) /
            Real.sqrt (2 - q) +
          (2 * σ * Real.sqrt (matrixRankBound m n : ℝ)) /
            (q * (T : ℝ)) +
          (2 * (matrixRankBound m n : ℝ) * η * (1 - q) * L) / q := by
    rcases hdom with
      ⟨hdomT, hdropDom, hsNoise, hsBatchNoise, hqBatchNoise, hsRank,
        hsBatch, hqTail, hqMomentum⟩
    dsimp [theorem_4_1_rhs, realizedSourceQuot, realizedSourceSqrt, sourceQuot,
      sourceSqrt]
    rw [hrun.2.2.1, hbeta]
    norm_num only [Nat.cast_one, one_mul, Real.sqrt_one, mul_one]
    rw [stochasticExpectedObjectiveDropRealized_eq_integral]
    ring_nf at hdropQuot ⊢
    linarith only [hdropQuot]
  have hscalar := corollary_4_2_stochastic_schedule_scalar_bound hreg hT.1.2.1
  exact le_trans (le_trans hbound hrhs) hscalar

theorem corollary_4_2_stochastic_asymptotic_bound
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (W0 : Mat m n) (L σ Δ : ℝ)
    (hfinite : P.objective.HasFiniteInfimum)
    (hΔeq : sourceObjectiveInitialGap P.objective W0 hfinite = Δ)
    (hsmooth : FrobeniusSmooth P.objective L)
    (hvariance : BoundedVariance P σ)
    (hreg : corollary_4_2_stochasticRegime m n L σ Δ) :
    let realizes := fun T cfg =>
      corollary_4_2_stochasticRealization W0 T L σ Δ cfg
    RealizedAsymptoticUpperNatOn
      (fun T => corollary_4_2_stochasticSemanticHorizonDomain P W0 T L σ Δ)
      (fun T _hT cfg => realizes T cfg)
      (fun T hT cfg =>
        by
          classical
          exact
            if hr : realizes T cfg then
              stochasticAverageNuclearGradientRealized P cfg T (hT.2 cfg hr)
            else 0)
      (fun T hT =>
        corollary_4_2_stochasticRateRealized m n T L σ Δ hT.1.2.1)
      (theoremScope
        "Corollary 4.2 corrected stochastic rate on admissible horizons" ["T"]) := by
  dsimp only
  unfold RealizedAsymptoticUpperNatOn
  refine ⟨10, 1, by norm_num, ?_, ?_⟩
  · simp [ConstantRespectsScope, theoremScope]
  · intro T hT _hTlarge
    rcases corollary_4_2_stochasticRealization_exists_of_admissible
        W0 T L σ Δ hT.1 with ⟨cfg, hrun⟩
    refine ⟨⟨cfg, hrun⟩, ?_⟩
    intro cfg' hrun'
    simp only [dif_pos hrun']
    rcases corollary_4_2_stochastic_bound_at_realized_horizon
        P W0 hfinite hΔeq hsmooth hvariance hreg hT.1.1.1 with
      ⟨hT', hpoint⟩
    simpa using hpoint cfg' hrun'

set_option maxHeartbeats 800000 in
theorem corollary_4_2_stochastic_rate_crossing
    {m n : ℕ} {L σ Δ : ℝ}
    (hreg : corollary_4_2_stochasticRegime m n L σ Δ) :
    ∃ horizonBound : ℝ → ℝ,
      AsymptoticUpperReal epsilonDomain horizonBound
        (corollary_4_2_stochasticComplexityRate m n L σ Δ)
        (theoremScope
          "Corollary 4.2 corrected stochastic epsilon complexity on admissible horizons"
          ["epsilon"]) ∧
      ∀ ε : ℝ, epsilonDomain ε →
        ∃ T : ℕ, ∃ hT : corollary_4_2_stochasticRateDomain m n T L σ Δ,
          (T : ℝ) ≤ horizonBound ε ∧
            10 * corollary_4_2_stochasticRateRealized m n T L σ Δ hT ≤ ε := by
  have hreg' := hreg
  unfold corollary_4_2_stochasticRegime at hreg'
  rcases hreg' with ⟨hrNat, hL, hσ, hΔ⟩
  let r : ℝ := matrixRankBound m n
  have hr : 0 < r := by dsimp [r]; exact_mod_cast hrNat
  let K : ℝ := r ^ 2 * L * Δ * σ ^ 2
  let B₄ : ℝ := 30 ^ 4 * K
  let B₂ : ℝ := 30 ^ 2 * (r * L * Δ)
  let B₃ : ℝ := 30 ^ 2 * (r * σ ^ 4 / (L * Δ))
  have hK : 0 < K := by dsimp [K]; positivity
  have hB₄ : 0 ≤ B₄ := by dsimp [B₄]; positivity
  have hB₂ : 0 ≤ B₂ := by dsimp [B₂]; positivity
  have hB₃ : 0 ≤ B₃ := by dsimp [B₃]; positivity
  let X : ℝ → ℝ := fun ε =>
    1 + B₄ * ε⁻¹ ^ 4 + B₂ * ε⁻¹ ^ 2 + B₃ * ε⁻¹ ^ 2
  let selected : ℝ → ℕ := fun ε => Nat.ceil (X ε)
  let horizonBound : ℝ → ℝ := fun ε => (selected ε : ℝ)
  refine ⟨horizonBound, ?_, ?_⟩
  · unfold AsymptoticUpperReal
    let C : ℝ := (2 + B₄ + B₂ + B₃) / K
    refine ⟨C, 1, by dsimp [C]; positivity, by norm_num, ?_, ?_⟩
    · simp [ConstantRespectsScope, theoremScope, C]
      positivity
    · intro ε _hε hεpos hεsmall
      have hinv : 0 < ε⁻¹ := inv_pos.mpr hεpos
      have hinvOne : 1 ≤ ε⁻¹ := (one_le_inv₀ hεpos).2 hεsmall
      have hinvSqOne : 1 ≤ ε⁻¹ ^ 2 := by nlinarith [sq_nonneg (ε⁻¹ - 1)]
      have hinvSqLeFour : ε⁻¹ ^ 2 ≤ ε⁻¹ ^ 4 := by
        have hmul := mul_le_mul_of_nonneg_left hinvSqOne (sq_nonneg ε⁻¹)
        nlinarith
      have honeLeFour : 1 ≤ ε⁻¹ ^ 4 := le_trans hinvSqOne hinvSqLeFour
      have hXnonneg : 0 ≤ X ε := by dsimp [X]; positivity
      have hceil : (selected ε : ℝ) < X ε + 1 := by
        dsimp [selected]
        exact Nat.ceil_lt_add_one hXnonneg
      have hB₂absorb : B₂ * ε⁻¹ ^ 2 ≤ B₂ * ε⁻¹ ^ 4 :=
        mul_le_mul_of_nonneg_left hinvSqLeFour hB₂
      have hB₃absorb : B₃ * ε⁻¹ ^ 2 ≤ B₃ * ε⁻¹ ^ 4 :=
        mul_le_mul_of_nonneg_left hinvSqLeFour hB₃
      have htwoAbsorb : (2 : ℝ) ≤ 2 * ε⁻¹ ^ 4 := by nlinarith
      calc
        horizonBound ε ≤ X ε + 1 := by
          exact le_of_lt (by simpa [horizonBound] using hceil)
        _ ≤ (2 + B₄ + B₂ + B₃) * ε⁻¹ ^ 4 := by
          dsimp [X]
          nlinarith
        _ = C * corollary_4_2_stochasticComplexityRate m n L σ Δ ε := by
          dsimp [C, corollary_4_2_stochasticComplexityRate, K, r]
          field_simp [ne_of_gt hK]
  · intro ε hε
    have hεpos : 0 < ε := hε
    have hinv : 0 < ε⁻¹ := inv_pos.mpr hεpos
    have hXpos : 0 < X ε := by dsimp [X]; positivity
    let T := selected ε
    have hTpos : horizonDomain T := by
      dsimp [T, selected, horizonDomain]
      exact Nat.ceil_pos.mpr hXpos
    have hXT : X ε ≤ (T : ℝ) := by
      dsimp [T, selected]
      exact Nat.le_ceil _
    have hrealizable := corollary_4_2_stochasticRegime_realizable hreg hTpos
    let hRate : corollary_4_2_stochasticRateDomain m n T L σ Δ :=
      hrealizable.2.1
    refine ⟨T, hRate, le_rfl, ?_⟩
    have hTr : 0 < (T : ℝ) := by exact_mod_cast hTpos
    have hbudget₄ : B₄ * ε⁻¹ ^ 4 ≤ (T : ℝ) := by
      apply le_trans _ hXT
      dsimp [X]
      nlinarith only [hB₂, hB₃, sq_nonneg (ε⁻¹)]
    have hbudget₂ : B₂ * ε⁻¹ ^ 2 ≤ (T : ℝ) := by
      apply le_trans _ hXT
      dsimp [X]
      nlinarith only [hB₄, hB₃, sq_nonneg (ε⁻¹), sq_nonneg (ε⁻¹ ^ 2)]
    have hbudget₃ : B₃ * ε⁻¹ ^ 2 ≤ (T : ℝ) := by
      apply le_trans _ hXT
      dsimp [X]
      nlinarith only [hB₄, hB₂, sq_nonneg (ε⁻¹), sq_nonneg (ε⁻¹ ^ 2)]
    let e : ℝ := ε / 30
    have he : 0 < e := by dsimp [e]; positivity
    have hfirstRad : K / (T : ℝ) ≤ e ^ 4 := by
      apply (div_le_iff₀ hTr).2
      dsimp [B₄] at hbudget₄
      dsimp [e]
      field_simp [ne_of_gt hεpos] at hbudget₄ ⊢
      nlinarith
    have hsecondRad : (r * L * Δ) / (T : ℝ) ≤ e ^ 2 := by
      apply (div_le_iff₀ hTr).2
      dsimp [B₂] at hbudget₂
      dsimp [e]
      field_simp [ne_of_gt hεpos] at hbudget₂ ⊢
      nlinarith
    have hthirdRad : (r * σ ^ 4 / (L * Δ)) / (T : ℝ) ≤ e ^ 2 := by
      apply (div_le_iff₀ hTr).2
      dsimp [B₃] at hbudget₃
      dsimp [e]
      field_simp [ne_of_gt hεpos, ne_of_gt hL, ne_of_gt hΔ] at hbudget₃ ⊢
      nlinarith
    let R₁ : ℝ := Real.sqrt (Real.sqrt (K / (T : ℝ)))
    let R₂ : ℝ := Real.sqrt ((r * L * Δ) / (T : ℝ))
    let R₃ : ℝ := Real.sqrt r * σ ^ 2 / Real.sqrt (L * Δ * (T : ℝ))
    have hR₁ : R₁ ≤ e := by
      dsimp [R₁]
      rw [Real.sqrt_le_iff]
      refine ⟨he.le, ?_⟩
      rw [Real.sqrt_le_iff]
      refine ⟨sq_nonneg e, ?_⟩
      nlinarith [hfirstRad]
    have hR₂ : R₂ ≤ e := by
      dsimp [R₂]
      rw [Real.sqrt_le_iff]
      exact ⟨he.le, hsecondRad⟩
    have hR₃sq : R₃ ^ 2 = (r * σ ^ 4 / (L * Δ)) / (T : ℝ) := by
      have hdenRoot : 0 < Real.sqrt (L * Δ * (T : ℝ)) := by positivity
      dsimp [R₃]
      field_simp [ne_of_gt hdenRoot, ne_of_gt hL, ne_of_gt hΔ, ne_of_gt hTr]
      rw [Real.sq_sqrt hr.le, Real.sq_sqrt (by positivity : 0 ≤ L * Δ * (T : ℝ))]
      ring
    have hR₃ : R₃ ≤ e := by
      apply (sq_le_sq₀ (by dsimp [R₃]; positivity) he.le).mp
      rw [hR₃sq]
      exact hthirdRad
    change 10 * (R₁ + R₂ + R₃) ≤ ε
    dsimp [e] at hR₁ hR₂ hR₃
    linarith

theorem corollary_4_2_stochastic_complexity
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (W0 : Mat m n) (L σ Δ : ℝ)
    (hfinite : P.objective.HasFiniteInfimum)
    (hΔeq : sourceObjectiveInitialGap P.objective W0 hfinite = Δ)
    (hsmooth : FrobeniusSmooth P.objective L)
    (hvariance : BoundedVariance P σ)
    (hreg : corollary_4_2_stochasticRegime m n L σ Δ) :
    let realizes := fun T cfg =>
      corollary_4_2_stochasticRealization W0 T L σ Δ cfg
    RealizedNuclearStationarityComplexityOn
      (fun T => corollary_4_2_stochasticSemanticHorizonDomain P W0 T L σ Δ)
      (fun T _hT cfg => realizes T cfg)
      (fun T hT cfg =>
        by
          classical
          exact
            if hr : realizes T cfg then
              stochasticAverageNuclearGradientRealized P cfg T (hT.2 cfg hr)
            else 0)
      (corollary_4_2_stochasticComplexityRate m n L σ Δ)
      (theoremScope
        "Corollary 4.2 corrected stochastic epsilon complexity on admissible horizons"
        ["epsilon"]) := by
  dsimp only
  unfold RealizedNuclearStationarityComplexityOn
  rcases corollary_4_2_stochastic_rate_crossing hreg with
    ⟨horizonBound, hAsymptotic, hselect⟩
  refine ⟨horizonBound, hAsymptotic, ?_⟩
  intro ε hε
  rcases hselect ε hε with ⟨T, hRate, hTbound, hrate⟩
  have hSemantic := corollary_4_2_stochasticRegime_semantic
    P W0 hreg hRate.1 hsmooth hvariance
  rcases corollary_4_2_stochasticRealization_exists_of_admissible
      W0 T L σ Δ hSemantic.1 with ⟨cfg, hrun⟩
  refine ⟨T, hSemantic, cfg, hTbound, hrun, ?_⟩
  simp only [dif_pos hrun]
  rcases corollary_4_2_stochastic_bound_at_realized_horizon
      P W0 hfinite hΔeq hsmooth hvariance hreg hRate.1 with
    ⟨hSemantic', hpoint⟩
  exact le_trans (by simpa using hpoint cfg hrun) (by simpa using hrate)

theorem objective_grad_eq_zero_of_sourceInitialGap_eq_zero
    {m n : ℕ} (P : Objective m n) (W0 : Mat m n)
    (hfinite : P.HasFiniteInfimum)
    (hgap : sourceObjectiveInitialGap P W0 hfinite = 0) :
    P.grad W0 = 0 := by
  have hfstar : P.f W0 = P.fStar := by
    dsimp [sourceObjectiveInitialGap, Objective.sourceFStar] at hgap
    linarith
  have hglobal : ∀ W : Mat m n, P.f W0 ≤ P.f W := by
    intro W
    rw [hfstar]
    exact objective_value_ge_fStar_early P hfinite W
  have hlocal : IsLocalMin P.f W0 := Filter.Eventually.of_forall hglobal
  have hfd : fderiv ℝ P.f W0 = 0 := hlocal.fderiv_eq_zero
  ext i j
  rw [Objective.grad_eq_coordinate_fderiv]
  change fderiv ℝ P.f W0 (coordinateMatrix i j) = 0
  rw [hfd]
  rfl

theorem objective_grad_eq_zero_of_frobeniusSmooth_zero
    {m n : ℕ} (P : Objective m n) (W0 : Mat m n)
    (hfinite : P.HasFiniteInfimum) (hsmooth : FrobeniusSmooth P 0) :
    P.grad W0 = 0 := by
  by_contra hgrad
  let G := P.grad W0
  let q := frobeniusNorm G ^ 2
  have hGnorm : 0 < frobeniusNorm G := by
    simpa [G, frobeniusNorm] using (norm_pos_iff.mpr hgrad)
  have hq : 0 < q := sq_pos_of_pos hGnorm
  let a := P.f W0 - P.fStar + 1
  have hgap_nonneg : 0 ≤ P.f W0 - P.fStar := by
    linarith [objective_value_ge_fStar_early P hfinite W0]
  have ha : 0 < a := by dsimp [a]; linarith
  let c := a / q
  let W' := W0 - c • G
  have hself : frobeniusInner G G = q := by
    dsimp [q]
    calc
      frobeniusInner G G = ∑ i : Fin m, ∑ j : Fin n, G i j ^ 2 := by
        simp [frobeniusInner, pow_two]
      _ = ∑ j : Fin n, ∑ i : Fin m, G i j ^ 2 := Finset.sum_comm
      _ = frobeniusNorm G ^ 2 := (frobeniusNorm_sq_eq_sum_entries_sq G).symm
  have hinner : frobeniusInner G (W' - W0) = -c * q := by
    have hdiff : W' - W0 = (-c) • G := by
      dsimp [W']
      module
    rw [hdiff]
    calc
      frobeniusInner G ((-c) • G) = (-c) * frobeniusInner G G := by
        unfold frobeniusInner
        simp only [Matrix.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      _ = -c * q := by rw [hself]
  have hupper := frobeniusSmooth_quadratic_upper_bound P hsmooth W0 W'
  rw [show P.grad W0 = G by rfl, hinner] at hupper
  simp only [zero_div, zero_mul, add_zero] at hupper
  have hlower := objective_value_ge_fStar_early P hfinite W'
  have hcq : c * q = a := by
    dsimp [c]
    field_simp [ne_of_gt hq]
  rw [show -c * q = -(c * q) by ring, hcq] at hupper
  dsimp [a] at hupper
  linarith

theorem objective_grad_eq_zero_of_rankBound_eq_zero
    {m n : ℕ} (P : Objective m n) (W0 : Mat m n)
    (hrank : matrixRankBound m n = 0) :
    P.grad W0 = 0 := by
  unfold matrixRankBound at hrank
  have hdim : m = 0 ∨ n = 0 := by
    by_cases hmn : m ≤ n
    · left
      simpa [Nat.min_eq_left hmn] using hrank
    · right
      have hnm : n ≤ m := Nat.le_of_lt (Nat.lt_of_not_ge hmn)
      simpa [Nat.min_eq_right hnm] using hrank
  rcases hdim with hm | hn
  · subst m
    ext i
    exact Fin.elim0 i
  · subst n
    ext i j
    exact Fin.elim0 j

theorem corollary_4_2_deterministicZeroMotion_of_degenerate_scale
    {m n : ℕ} (P : Objective m n) (W0 : Mat m n) (L beta : ℝ)
    (hfinite : P.HasFiniteInfimum) (hsmooth : FrobeniusSmooth P L)
    (hbeta : beta ∈ Set.Ico (0 : ℝ) 1)
    (hcoefficient : (matrixRankBound m n : ℝ) * L *
      sourceObjectiveInitialGap P W0 hfinite = 0) :
    corollary_4_2_deterministicZeroMotion P W0 L
      (sourceObjectiveInitialGap P W0 hfinite) beta hbeta := by
  have hgrad : P.grad W0 = 0 := by
    rcases mul_eq_zero.mp hcoefficient with hrL | hgap
    · rcases mul_eq_zero.mp hrL with hrank | hL
      · apply objective_grad_eq_zero_of_rankBound_eq_zero P W0
        exact_mod_cast hrank
      · apply objective_grad_eq_zero_of_frobeniusSmooth_zero P W0 hfinite
        simpa [hL] using hsmooth
    · exact objective_grad_eq_zero_of_sourceInitialGap_eq_zero P W0 hfinite hgap
  exact deterministicMomentum_zeroMotion_of_grad_eq_zero P W0 _
    (by intro T; rfl) hgrad

theorem corollary_4_2_deterministicOracle_bound_at_horizon {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMomentumMuonConfig m n)
    (T : ℕ) (L eta : ℝ)
    (hEta : ∀ t ∈ Finset.range T, cfg.eta t = eta)
    (hSmooth : FrobeniusSmooth P L) :
    theorem_4_1_sourceDomain T eta →
      ∃ hbasic : stochasticBasicExpectationsWellDefined
          (deterministicOracleProblem P) (deterministicOracleConfig cfg) T,
      ∃ hdom : theorem_4_1_rhsDomain (deterministicOracleProblem P)
          (deterministicOracleConfig cfg) T L 0 eta hbasic.2,
        deterministicMomentumAverageNuclearGradient P cfg T ≤
          theorem_4_1_rhs (deterministicOracleProblem P)
            (deterministicOracleConfig cfg) T L 0 eta hbasic.2 hdom := by
  intro hsrc
  have hresult := theorem_4_1 (deterministicOracleProblem P)
    (deterministicOracleConfig cfg) T L 0 eta
    (by simpa [deterministicOracleConfig] using hEta)
    (by simpa only [deterministicOracleProblem_objective] using hSmooth)
    (deterministicOracleProblem_boundedVariance_zero P)
  rcases hresult.2 hsrc with ⟨hbasic, hdom, hbound⟩
  refine ⟨hbasic, hdom, ?_⟩
  rw [← deterministicOracle_average_eq P cfg T hbasic.1]
  exact hbound

set_option maxHeartbeats 800000 in
theorem corollary_4_2_deterministic_rate_bound_positive
    {m n T : ℕ} (P : Objective m n) (W0 : Mat m n) (L Δ β : ℝ)
    (hfinite : P.HasFiniteInfimum)
    (hΔeq : sourceObjectiveInitialGap P W0 hfinite = Δ)
    (hsmooth : FrobeniusSmooth P L)
    (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (hcoeff : 0 < (matrixRankBound m n : ℝ) * L * Δ)
    (hT : corollary_4_2_deterministicRateDomain m n T L Δ) :
    deterministicMomentumAverageNuclearGradient P
        (corollary_4_2_deterministicConfig W0 T L Δ β hβ) T ≤
      (3 / 2 + 2 * β / (1 - β)) *
        corollary_4_2_deterministicRateRealized m n T L Δ hT := by
  let r : ℝ := matrixRankBound m n
  let τ : ℝ := T
  let η : ℝ := corollary_4_2_deterministicEta m n T L Δ
  let R : ℝ := corollary_4_2_deterministicRateRealized m n T L Δ hT
  have hcoeffr : 0 < r * L * Δ := by simpa [r] using hcoeff
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hΔ0 : 0 ≤ Δ := by
    rw [← hΔeq]
    unfold sourceObjectiveInitialGap Objective.sourceFStar
    linarith [objective_value_ge_fStar_early P hfinite W0]
  have hr : 0 < r := by
    have hrne : r ≠ 0 := by
      intro hrzero
      rw [hrzero] at hcoeffr
      norm_num at hcoeffr
    exact lt_of_le_of_ne hr0 (Ne.symm hrne)
  have hΔ : 0 < Δ := by
    have hΔne : Δ ≠ 0 := by
      intro hzero
      rw [hzero] at hcoeff
      norm_num at hcoeff
    exact lt_of_le_of_ne hΔ0 (Ne.symm hΔne)
  have hL : 0 < L := by
    by_contra hn
    have hLn : L ≤ 0 := le_of_not_gt hn
    have : r * L * Δ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hr0 hLn) hΔ0
    linarith
  have hτ : 0 < τ := by dsimp [τ]; exact_mod_cast hT.1
  have hη : 0 < η := by
    dsimp [η, corollary_4_2_deterministicEta, sourceQuot]
    apply Real.sqrt_pos.2
    positivity
  have hsrc : theorem_4_1_sourceDomain T η := by
    refine ⟨⟨hT.1, ?_⟩, hη⟩
    unfold sourceQuotDomain
    exact mul_ne_zero (by exact_mod_cast ne_of_gt hT.1) (ne_of_gt hη)
  let cfg := corollary_4_2_deterministicConfig W0 T L Δ β hβ
  rcases corollary_4_2_deterministicOracle_bound_at_horizon
      P cfg T L η (by intro t ht; rfl) hsmooth hsrc with
    ⟨hbasic, hdom, hbound⟩
  have hfiniteOracle :
      (deterministicOracleProblem P).objective.HasFiniteInfimum := by
    simpa only [deterministicOracleProblem_objective] using hfinite
  have hdrop :
      stochasticExpectedObjectiveDrop (deterministicOracleProblem P)
          (deterministicOracleConfig cfg) T ≤ Δ := by
    calc
      _ ≤ sourceObjectiveInitialGap
          (deterministicOracleProblem P).objective
          (deterministicOracleConfig cfg).W0 hfiniteOracle :=
        stochastic_expected_objective_drop_le_source_initial_gap
          (deterministicOracleProblem P) (deterministicOracleConfig cfg) T
          hfiniteOracle hbasic.2
      _ = Δ := by
        calc
          _ = sourceObjectiveInitialGap P W0 hfinite := by
            simp only [cfg, corollary_4_2_deterministicConfig,
              deterministicMomentumConstantConfig, deterministicOracleConfig,
              deterministicOracleProblem_objective]
          _ = Δ := hΔeq
  have hden : 0 < (T : ℝ) * η := mul_pos (by exact_mod_cast hT.1) hη
  have hdropQuot := div_le_div_of_nonneg_right hdrop hden.le
  have hrhs :
      theorem_4_1_rhs (deterministicOracleProblem P)
          (deterministicOracleConfig cfg) T L 0 η hbasic.2 hdom ≤
        Δ / ((T : ℝ) * η) + r * L * η / 2 +
          2 * r * η * β * L / (1 - β) := by
    rcases hdom with
      ⟨hdomT, hdropDom, hsNoise, hsBatchNoise, hqBatchNoise, hsRank,
        hsBatch, hqTail, hqMomentum⟩
    dsimp [theorem_4_1_rhs, realizedSourceQuot, realizedSourceSqrt,
      sourceQuot, sourceSqrt, deterministicOracleConfig, cfg,
      corollary_4_2_deterministicConfig, deterministicMomentumConstantConfig]
    rw [stochasticExpectedObjectiveDropRealized_eq_integral]
    dsimp [deterministicOracleConfig, cfg, corollary_4_2_deterministicConfig,
      deterministicMomentumConstantConfig, r] at hdropQuot
    dsimp [r]
    ring_nf at hdropQuot ⊢
    linarith only [hdropQuot]
  have hηsq : η ^ 2 = Δ / (r * τ * L) := by
    dsimp [η, corollary_4_2_deterministicEta, sourceQuot, r, τ]
    rw [Real.sq_sqrt]
    positivity
  have hscale : r * L * η = Δ / (τ * η) := by
    have hpoly : η ^ 2 * (r * τ * L) = Δ :=
      (eq_div_iff (by positivity : r * τ * L ≠ 0)).mp hηsq
    apply (eq_div_iff (by positivity : τ * η ≠ 0)).2
    ring_nf at hpoly ⊢
    nlinarith
  have hRsq : R ^ 2 = r * L * Δ / τ := by
    dsimp [R, corollary_4_2_deterministicRateRealized,
      realizedSourceSqrtQuot, realizedSourceQuot, realizedSourceSqrt,
      sourceSqrt, sourceQuot, r, τ]
    rw [Real.sq_sqrt]
    positivity
  have hscaleSq : (r * L * η) ^ 2 = r * L * Δ / τ := by
    rw [mul_pow, hηsq]
    field_simp [ne_of_gt hr, ne_of_gt hτ, ne_of_gt hL]
  have hscaleR : r * L * η = R := by
    apply (mul_self_inj_of_nonneg (by positivity) (by
      dsimp [R, corollary_4_2_deterministicRateRealized,
        realizedSourceSqrtQuot, realizedSourceQuot, realizedSourceSqrt,
        sourceSqrt, sourceQuot]
      positivity)).mp
    simpa [pow_two] using hscaleSq.trans hRsq.symm
  have hfirstR : Δ / (τ * η) = R := hscale.symm.trans hscaleR
  calc
    deterministicMomentumAverageNuclearGradient P cfg T ≤
        Δ / ((T : ℝ) * η) + r * L * η / 2 +
          2 * r * η * β * L / (1 - β) := le_trans hbound hrhs
    _ = (3 / 2 + 2 * β / (1 - β)) * R := by
      rw [show (T : ℝ) = τ by rfl, hfirstR, ← hscaleR]
      field_simp [ne_of_gt (sub_pos.mpr hβ.2)]
      ring

theorem corollary_4_2_deterministic_asymptotic_bound_positive
    {m n : ℕ} (P : Objective m n) (W0 : Mat m n) (L Δ β : ℝ)
    (hfinite : P.HasFiniteInfimum)
    (hΔeq : sourceObjectiveInitialGap P W0 hfinite = Δ)
    (hsmooth : FrobeniusSmooth P L)
    (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (hcoeff : 0 < (matrixRankBound m n : ℝ) * L * Δ) :
    DomainAsymptoticUpperNatOn
      (fun T => corollary_4_2_deterministicRateDomain m n T L Δ)
      (fun T _hT => deterministicMomentumAverageNuclearGradient P
        (corollary_4_2_deterministicConfig W0 T L Δ β hβ) T)
      (fun T hT => corollary_4_2_deterministicRateRealized m n T L Δ hT)
      (theoremScope "Corollary 4.2 deterministic rate" ["T"]) := by
  let C : ℝ := 3 / 2 + 2 * β / (1 - β)
  have hC : 0 < C := by
    dsimp [C]
    have hden : 0 < 1 - β := sub_pos.mpr hβ.2
    have hfrac : 0 ≤ 2 * β / (1 - β) :=
      div_nonneg (mul_nonneg (by norm_num) hβ.1) hden.le
    linarith
  unfold DomainAsymptoticUpperNatOn
  refine ⟨C, 1, hC, ?_, ?_⟩
  · simp [ConstantRespectsScope, theoremScope, hC]
  · intro T hT _hlarge
    exact corollary_4_2_deterministic_rate_bound_positive
      P W0 L Δ β hfinite hΔeq hsmooth hβ hcoeff hT

set_option maxHeartbeats 800000 in
theorem corollary_4_2_deterministic_complexity_witness
    {m n : ℕ} (P : Objective m n) (W0 : Mat m n) (L Δ β : ℝ)
    (hfinite : P.HasFiniteInfimum)
    (hΔeq : sourceObjectiveInitialGap P W0 hfinite = Δ)
    (hsmooth : FrobeniusSmooth P L)
    (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (hcoeff : 0 < (matrixRankBound m n : ℝ) * L * Δ) :
    NuclearStationarityComplexityOn
      (fun T => corollary_4_2_deterministicRateDomain m n T L Δ)
      (fun T _hT => deterministicMomentumAverageNuclearGradient P
        (corollary_4_2_deterministicConfig W0 T L Δ β hβ) T)
      (corollary_4_2_deterministicComplexityRate m n L Δ)
      (theoremScope "Corollary 4.2 deterministic epsilon complexity" ["epsilon"]) := by
  let A : ℝ := (matrixRankBound m n : ℝ) * L * Δ
  let k : ℝ := 3 / 2 + 2 * β / (1 - β)
  have hA : 0 < A := by simpa [A] using hcoeff
  have hk : 0 < k := by
    dsimp [k]
    have hden : 0 < 1 - β := sub_pos.mpr hβ.2
    have hfrac : 0 ≤ 2 * β / (1 - β) :=
      div_nonneg (mul_nonneg (by norm_num) hβ.1) hden.le
    linarith
  let X : ℝ → ℝ := fun ε => k ^ 2 * A * ε⁻¹ ^ 2
  let selected : ℝ → ℕ := fun ε => Nat.ceil (X ε)
  let horizonBound : ℝ → ℝ := fun ε => (selected ε : ℝ)
  unfold NuclearStationarityComplexityOn
  refine ⟨horizonBound, ?_, ?_⟩
  · unfold AsymptoticUpperReal
    let C : ℝ := k ^ 2 + A⁻¹
    have hC : 0 < C := by dsimp [C]; positivity
    refine ⟨C, 1, hC, by norm_num, ?_, ?_⟩
    · simp [ConstantRespectsScope, theoremScope, hC]
    · intro ε hε hεpos hεone
      have hXnonneg : 0 ≤ X ε := by dsimp [X]; positivity
      have hceil : (selected ε : ℝ) < X ε + 1 := by
        dsimp [selected]
        exact Nat.ceil_lt_add_one hXnonneg
      have hinvSq : 1 ≤ ε⁻¹ ^ 2 := by
        have hinv : 1 ≤ ε⁻¹ := (one_le_inv₀ hεpos).2 hεone
        nlinarith [sq_nonneg (ε⁻¹ - 1)]
      have hone : 1 ≤ A⁻¹ * (A * ε⁻¹ ^ 2) := by
        calc
          1 ≤ ε⁻¹ ^ 2 := hinvSq
          _ = A⁻¹ * (A * ε⁻¹ ^ 2) := by
            rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hA), one_mul]
      calc
        horizonBound ε ≤ X ε + 1 := by
          exact le_of_lt (by simpa [horizonBound] using hceil)
        _ ≤ C * corollary_4_2_deterministicComplexityRate m n L Δ ε := by
          dsimp [X, C, corollary_4_2_deterministicComplexityRate, A]
          nlinarith
  · intro ε hε
    have hεpos : 0 < ε := hε
    have hXpos : 0 < X ε := by dsimp [X]; positivity
    let T : ℕ := selected ε
    have hTpos : horizonDomain T := by
      dsimp [T, selected, horizonDomain]
      exact Nat.ceil_pos.mpr hXpos
    have hXT : X ε ≤ (T : ℝ) := by
      dsimp [T, selected]
      exact Nat.le_ceil _
    have hTr : 0 < (T : ℝ) := by exact_mod_cast hTpos
    have hT : corollary_4_2_deterministicRateDomain m n T L Δ := by
      refine ⟨hTpos, ?_⟩
      unfold sourceSqrtQuotDomain sourceQuotDomain sourceSqrtDomain sourceQuot
      constructor
      · exact ne_of_gt hTr
      · positivity
    refine ⟨T, hT, le_rfl, ?_⟩
    apply le_trans (corollary_4_2_deterministic_rate_bound_positive
      P W0 L Δ β hfinite hΔeq hsmooth hβ hcoeff hT)
    change k * Real.sqrt (A / (T : ℝ)) ≤ ε
    have hrad : A / (T : ℝ) ≤ (ε / k) ^ 2 := by
      apply (div_le_iff₀ hTr).2
      dsimp [X] at hXT
      field_simp [ne_of_gt hεpos, ne_of_gt hk] at hXT ⊢
      nlinarith
    have hsqrt : Real.sqrt (A / (T : ℝ)) ≤ ε / k := by
      rw [Real.sqrt_le_iff]
      exact ⟨(div_nonneg hεpos.le hk.le), hrad⟩
    simpa [mul_comm] using (le_div_iff₀ hk).mp hsqrt

theorem corollary_4_2_deterministic_asymptotic_bound_zero
    {m n : ℕ} (P : Objective m n) (W0 : Mat m n) (L Δ β : ℝ)
    (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (hzero : corollary_4_2_deterministicZeroMotion P W0 L Δ β hβ) :
    DomainAsymptoticUpperNatOn
      (fun T => corollary_4_2_deterministicRateDomain m n T L Δ)
      (fun T _hT => deterministicMomentumAverageNuclearGradient P
        (corollary_4_2_deterministicConfig W0 T L Δ β hβ) T)
      (fun T hT => corollary_4_2_deterministicRateRealized m n T L Δ hT)
      (theoremScope "Corollary 4.2 deterministic rate" ["T"]) := by
  unfold DomainAsymptoticUpperNatOn
  refine ⟨1, 1, by norm_num, ?_, ?_⟩
  · simp [ConstantRespectsScope, theoremScope]
  · intro T hT _hlarge
    have havg : deterministicMomentumAverageNuclearGradient P
        (corollary_4_2_deterministicConfig W0 T L Δ β hβ) T = 0 := by
      unfold deterministicMomentumAverageNuclearGradient
      rw [Finset.sum_eq_zero]
      · ring
      · intro t ht
        rw [hzero.2 T t |>.1, hzero.1]
        simp [nuclearNorm]
    dsimp only
    rw [havg]
    have hrate : 0 ≤ corollary_4_2_deterministicRateRealized m n T L Δ hT := by
      unfold corollary_4_2_deterministicRateRealized realizedSourceSqrtQuot
        realizedSourceSqrt sourceSqrt
      positivity
    simpa using hrate

theorem corollary_4_2 {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (W0 : Mat m n) (L σ : ℝ)
    (_hfinite : P.objective.HasFiniteInfimum)
    (_hsmooth : FrobeniusSmooth P.objective L)
    (_hvariance : BoundedVariance P σ) :
    corollary_4_2_statement P W0 L σ _hfinite := by
  dsimp only [corollary_4_2_statement]
  refine ⟨?_, ?_, ?_⟩
  · unfold corollary_4_2_stochastic_downstream_phase2_boundary
      corollary_4_2_stochasticSemanticSourceBoundary SourceNatDomainBoundary
    dsimp only
    constructor
    · intro T hT
      exact hT.1.1.1
    · intro T hsource
      by_cases hsemantic : corollary_4_2_stochasticSemanticHorizonDomain P W0 T L σ
          (sourceObjectiveInitialGap P.objective W0 _hfinite)
      · exact Or.inl hsemantic
      · exact Or.inr ⟨hsource, hsemantic⟩
  · intro hreg
    unfold corollary_4_2_stochastic_corrected_admissible_domain_statement
    dsimp only
    constructor
    · exact corollary_4_2_stochastic_asymptotic_bound
        P W0 L σ (sourceObjectiveInitialGap P.objective W0 _hfinite)
        _hfinite rfl _hsmooth _hvariance hreg
    · constructor
      · exact corollary_4_2_stochastic_complexity
          P W0 L σ (sourceObjectiveInitialGap P.objective W0 _hfinite)
          _hfinite rfl _hsmooth _hvariance hreg
      · intro T hT cfg hcfg ε havg
        exact stochasticGeneratedOutputGuarantee_of_average_le
          P cfg T hT.1.1.1 (hT.2 cfg hcfg) ε havg
  · intro _hσ β hβ _hβO1
    let Δ : ℝ := sourceObjectiveInitialGap P.objective W0 _hfinite
    let A : ℝ := (matrixRankBound m n : ℝ) * L * Δ
    have hΔ0 : 0 ≤ Δ := by
      dsimp [Δ, sourceObjectiveInitialGap, Objective.sourceFStar]
      linarith [objective_value_ge_fStar_early P.objective _hfinite W0]
    have hA0 : 0 ≤ A := by
      by_cases hrank : matrixRankBound m n = 0
      · simp [A, hrank]
      · have hrpos : 0 < Real.sqrt (matrixRankBound m n : ℝ) := by
          apply Real.sqrt_pos.2
          exact_mod_cast Nat.pos_of_ne_zero hrank
        have hL0 : 0 ≤ L := nonneg_of_mul_nonneg_left
          (frobeniusSmooth_mul_sqrt_rankBound_nonneg _hsmooth) hrpos
        dsimp [A]
        positivity
    by_cases hAzero : A = 0
    · have hzero : corollary_4_2_deterministicZeroMotion P.objective W0 L Δ β hβ := by
        apply corollary_4_2_deterministicZeroMotion_of_degenerate_scale
          P.objective W0 L β _hfinite _hsmooth hβ
        simpa [A, Δ] using hAzero
      refine ⟨corollary_4_2_deterministic_asymptotic_bound_zero
        P.objective W0 L Δ β hβ hzero, ?_, ?_⟩
      · intro hApos
        exact (hApos.ne' hAzero).elim
      · intro _hzero
        refine ⟨hzero, ?_⟩
        unfold IsNuclearStationary
        rw [hzero.2 1 0 |>.1, hzero.1]
        simp [nuclearNorm]
    · have hApos : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hAzero)
      refine ⟨corollary_4_2_deterministic_asymptotic_bound_positive
        P.objective W0 L Δ β _hfinite rfl _hsmooth hβ (by simpa [A] using hApos),
        ?_, ?_⟩
      · intro _hpositive
        constructor
        · exact corollary_4_2_deterministic_complexity_witness
            P.objective W0 L Δ β _hfinite rfl _hsmooth hβ (by simpa [A] using hApos)
        · simpa [deterministicMomentumAverageNuclearGradient] using
            (generatedNuclearStationarityTransfer_of_finite_average
              P.objective
              (fun T => corollary_4_2_deterministicRateDomain m n T L Δ)
              (fun T hT => hT.1)
              (fun T _hT t =>
                (deterministicMomentumMuonState P.objective
                  (corollary_4_2_deterministicConfig W0 T L Δ β hβ) t).W))
      · intro hzero
        exact (hAzero (by simpa [A] using hzero)).elim

/- Appendix C.1, step 4 at source granularity.  The selector constructs the
   logarithmic/ceiling horizon and proves the scalar formula crossing before
   any instance of Assumption 4.4 or any objective-gap estimate is supplied. -/
theorem theorem_4_5_sourceRhs_le_epsilon_at_log_horizon
    {m n : ℕ} (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (L Dop : ℝ) (hfinite : P.HasFiniteInfimum) :
    let Δ := sourceObjectiveInitialGap P cfg.W0 hfinite
    ∃ horizonBound :
        ∀ ε : ℝ, theorem_4_5_precisionDomain m n L Dop Δ ε → ℝ,
      AsymptoticUpperRealOn (theorem_4_5_precisionDomain m n L Dop Δ)
        horizonBound
        (fun ε hε => theorem_4_5_complexityRateRealized m n L Dop Δ ε hε)
        (theoremScope "Theorem 4.5 logarithmic scalar horizon" ["epsilon"]) ∧
      ∀ ε : ℝ, ∀ hε : theorem_4_5_precisionDomain m n L Dop Δ ε,
        epsilonDomain ε →
        let N := theorem_4_5_logHorizon m n L Dop Δ ε hε
        (N : ℝ) ≤ horizonBound ε hε ∧
          theorem_4_5_sourceRhs P
            (theorem_4_5_precisionConfig cfg L Dop Δ ε hε) N L Dop
            (theorem_4_5_etaRateRealized m n L Dop ε hε.2.1) ≤ ε := by
  let Δ := sourceObjectiveInitialGap P cfg.W0 hfinite
  let horizonBound :
      ∀ ε : ℝ, theorem_4_5_precisionDomain m n L Dop Δ ε → ℝ :=
    fun ε hε => (theorem_4_5_logHorizon m n L Dop Δ ε hε : ℝ)
  refine ⟨horizonBound, ?_, ?_⟩
  · unfold AsymptoticUpperRealOn
    by_cases hΔ : 0 < Δ
    · let C : ℝ := 2 + 1 / Real.log 2
      refine ⟨C, Δ / 2, ?_, div_pos hΔ (by norm_num), ?_, ?_⟩
      · dsimp [C]
        have : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
        positivity
      · simp [ConstantRespectsScope, theoremScope, C]
        have : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
        positivity
      · intro ε hε hεpos hεsmall
        have hK : (matrixRankBound m n : ℝ) * L * Dop ≠ 0 := hε.2.1
        have hηbounds := hε.2.2.2.2
        dsimp at hηbounds
        let η : ℝ := ε / ((matrixRankBound m n : ℝ) * L * Dop)
        let A : ℝ := (matrixRankBound m n : ℝ) * L * Dop ^ 2 / ε
        have hηeq : theorem_4_5_etaRateRealized m n L Dop ε hε.2.1 = η := by
          rfl
        have hηne : η ≠ 0 := by
          dsimp [η]
          exact div_ne_zero (ne_of_gt hεpos) hK
        have hηpos : 0 < η := lt_of_le_of_ne (by simpa [hηeq] using hηbounds.1)
          (Ne.symm hηne)
        have hDop : 0 < Dop := lt_of_lt_of_le hηpos (by simpa [hηeq] using hηbounds.2)
        have hAeq : A = Dop / η := by
          dsimp [A, η]
          field_simp [hK, ne_of_gt hεpos, ne_of_gt hDop]
        have hA : 1 ≤ A := by
          rw [hAeq]
          exact (one_le_div hηpos).2 (by simpa [hηeq] using hηbounds.2)
        have hratio : 2 ≤ Δ / ε := by
          apply (le_div_iff₀ hεpos).2
          linarith
        have hratioPos : 0 < Δ / ε := lt_of_lt_of_le (by norm_num) hratio
        have hlogRatioPos : 0 < Real.log (Δ / ε) :=
          Real.log_pos (lt_of_lt_of_le (by norm_num) hratio)
        have hlogTwoPos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
        have hlogTwoLe : Real.log (2 : ℝ) ≤ Real.log (Δ / ε) :=
          Real.strictMonoOn_log.monotoneOn (by norm_num) hratioPos hratio
        let rate : ℝ := theorem_4_5_complexityRateRealized m n L Dop Δ ε hε
        have hrateEq : rate = A * Real.log (Δ / ε) := by
          dsimp [rate, A, theorem_4_5_complexityRateRealized,
            realizedSourceInv, sourceInv, realizedSourceLogQuot,
            sourceLogQuot, sourceQuot]
          field_simp [ne_of_gt hεpos]
        have hratePos : 0 < rate := by rw [hrateEq]; positivity
        let X : ℝ := A * Real.log (2 * Δ / ε)
        have hlogSplit : Real.log (2 * Δ / ε) =
            Real.log 2 + Real.log (Δ / ε) := by
          rw [show 2 * Δ / ε = 2 * (Δ / ε) by ring]
          exact Real.log_mul (by norm_num) (ne_of_gt hratioPos)
        have hXnonneg : 0 ≤ X := by
          dsimp [X]
          rw [hlogSplit]
          positivity
        have hXrate : X ≤ 2 * rate := by
          dsimp [X]
          rw [hlogSplit, hrateEq]
          nlinarith [mul_le_mul_of_nonneg_left hlogTwoLe (le_trans zero_le_one hA)]
        let N := theorem_4_5_logHorizon m n L Dop Δ ε hε
        have hNupper : (N : ℝ) < X + 1 := by
          dsimp [N, theorem_4_5_logHorizon]
          simpa [X] using Nat.ceil_lt_add_one hXnonneg
        have honeRate : 1 ≤ (1 / Real.log 2) * rate := by
          have hlogRate : Real.log 2 ≤ rate := by
            rw [hrateEq]
            calc
              Real.log 2 ≤ A * Real.log 2 := by
                simpa [one_mul] using mul_le_mul_of_nonneg_right hA hlogTwoPos.le
              _ ≤ A * Real.log (Δ / ε) :=
                mul_le_mul_of_nonneg_left hlogTwoLe (le_trans zero_le_one hA)
          calc
            1 = (1 / Real.log 2) * Real.log 2 := by
              field_simp [ne_of_gt hlogTwoPos]
            _ ≤ (1 / Real.log 2) * rate :=
              mul_le_mul_of_nonneg_left hlogRate (by positivity)
        dsimp [horizonBound, N]
        dsimp [C]
        rw [show theorem_4_5_complexityRateRealized m n L Dop Δ ε hε = rate by rfl]
        linarith
    · refine ⟨1, 1, by norm_num, by norm_num, ?_, ?_⟩
      · simp [ConstantRespectsScope, theoremScope]
      · intro ε hε hεpos _hεsmall
        have hratio : 0 < Δ / ε := by
          simpa [sourceLogQuotDomain, sourceQuot] using hε.2.2.2.1.2
        have hΔpos : 0 < Δ := by
          rcases div_pos_iff.mp hratio with h | h
          · exact h.1
          · exact False.elim (not_lt_of_ge hεpos.le h.2)
        exact False.elim (hΔ hΔpos)
  · intro ε hε hεdomain
    let N := theorem_4_5_logHorizon m n L Dop Δ ε hε
    refine ⟨le_rfl, ?_⟩
    have hεpos : 0 < ε := hε.1
    have hK : (matrixRankBound m n : ℝ) * L * Dop ≠ 0 := hε.2.1
    have hηbounds := hε.2.2.2.2
    dsimp at hηbounds
    let η : ℝ := ε / ((matrixRankBound m n : ℝ) * L * Dop)
    let A : ℝ := (matrixRankBound m n : ℝ) * L * Dop ^ 2 / ε
    have hηeq : theorem_4_5_etaRateRealized m n L Dop ε hε.2.1 = η := rfl
    have hηne : η ≠ 0 := by
      dsimp [η]
      exact div_ne_zero (ne_of_gt hεpos) hK
    have hηpos : 0 < η := lt_of_le_of_ne (by simpa [hηeq] using hηbounds.1)
      (Ne.symm hηne)
    have hDop : 0 < Dop := lt_of_lt_of_le hηpos (by simpa [hηeq] using hηbounds.2)
    have hAeq : A = Dop / η := by
      dsimp [A, η]
      field_simp [hK, ne_of_gt hεpos, ne_of_gt hDop]
    have hApos : 0 < A := by rw [hAeq]; positivity
    have hA : 1 ≤ A := by
      rw [hAeq]
      exact (one_le_div hηpos).2 (by simpa [hηeq] using hηbounds.2)
    have hratioPos : 0 < Δ / ε := by
      simpa [sourceLogQuotDomain, sourceQuot] using hε.2.2.2.1.2
    have hΔpos : 0 < Δ := by
      rcases div_pos_iff.mp hratioPos with h | h
      · exact h.1
      · exact False.elim (not_lt_of_ge hεpos.le h.2)
    have hadd : (matrixRankBound m n : ℝ) * L * Dop * η / 2 = ε / 2 := by
      calc
        (matrixRankBound m n : ℝ) * L * Dop * η / 2 =
            (ε / ((matrixRankBound m n : ℝ) * L * Dop) *
              ((matrixRankBound m n : ℝ) * L * Dop)) / 2 := by
                dsimp [η]
                ring
        _ = ε / 2 := by rw [div_mul_cancel₀ ε hK]
    have hqnonneg : 0 ≤ 1 - η / Dop :=
      sub_nonneg.mpr ((div_le_one hDop).2 (by simpa [hηeq] using hηbounds.2))
    have hqle : 1 - η / Dop ≤ 1 :=
      sub_le_self _ (div_nonneg hηpos.le hDop.le)
    have hcontract : (1 - η / Dop) ^ N * Δ ≤ ε / 2 := by
      by_cases hsmall : Δ ≤ ε / 2
      · have hpow : (1 - η / Dop) ^ N ≤ 1 := pow_le_one₀ hqnonneg hqle
        have hscaled := mul_le_mul_of_nonneg_right hpow hΔpos.le
        nlinarith
      · have htwoRatio : 1 < 2 * Δ / ε := by
          apply (lt_div_iff₀ hεpos).2
          linarith
        have hlogPos : 0 < Real.log (2 * Δ / ε) := Real.log_pos htwoRatio
        let X : ℝ := A * Real.log (2 * Δ / ε)
        have hXpos : 0 < X := mul_pos hApos hlogPos
        have hXN : X ≤ (N : ℝ) := by
          dsimp [N, theorem_4_5_logHorizon]
          simpa [X] using Nat.le_ceil X
        have hNpos : 0 < (N : ℝ) := lt_of_lt_of_le hXpos hXN
        have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
        let t : ℝ := (N : ℝ) / A
        have htN : t ≤ (N : ℝ) := by
          dsimp [t]
          apply (div_le_iff₀ hApos).2
          have hscaled := mul_le_mul_of_nonneg_left hA hNpos.le
          nlinarith
        have hpow : (1 - t / (N : ℝ)) ^ N ≤ Real.exp (-t) := by
          exact Real.one_sub_div_pow_le_exp_neg htN
        have hq : 1 - t / (N : ℝ) = 1 - η / Dop := by
          dsimp [t]
          rw [hAeq]
          field_simp [hNne, hηne, ne_of_gt hDop]
        have hlogLe : Real.log (2 * Δ / ε) ≤ t := by
          dsimp [t, X] at hXN ⊢
          exact (le_div_iff₀ hApos).2 (by simpa [mul_comm] using hXN)
        have hexpLe : Real.exp (-t) ≤
            Real.exp (-Real.log (2 * Δ / ε)) :=
          Real.exp_le_exp.mpr (by linarith)
        have hexpEq : Real.exp (-Real.log (2 * Δ / ε)) = ε / (2 * Δ) := by
          rw [Real.exp_neg, Real.exp_log (lt_trans zero_lt_one htwoRatio)]
          field_simp [ne_of_gt hεpos, ne_of_gt hΔpos]
        rw [hq] at hpow
        have hscaled := mul_le_mul_of_nonneg_right
          (le_trans hpow hexpLe) hΔpos.le
        rw [hexpEq] at hscaled
        have heq : ε / (2 * Δ) * Δ = ε / 2 := by
          field_simp [ne_of_gt hΔpos]
        simpa [heq] using hscaled
    dsimp [theorem_4_5_sourceRhs]
    rw [show P.f
        (theorem_4_5_precisionConfig cfg L Dop Δ ε hε).W0 - P.fStar = Δ by
      simp [theorem_4_5_precisionConfig, deterministicConstantConfig, Δ,
        sourceObjectiveInitialGap, Objective.sourceFStar]]
    rw [hηeq, hadd]
    linarith

theorem theorem_4_5 {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (T : ℕ) (Wstar : Mat m n) (L Dop η : ℝ)
    (_hfinite : P.HasFiniteInfimum)
    (_hstar : StarConvex P Wstar)
    (_hsmooth : FrobeniusSmooth P L)
    (_hbounded : BoundedOperatorDistance P cfg T Wstar Dop)
    (_hη : ∀ t ∈ Finset.range T, cfg.eta t = η) :
    theorem_4_5_statement P cfg T Wstar L Dop η _hfinite := by
  dsimp [theorem_4_5_statement]
  refine ⟨theorem_4_5_formula_source_boundary P cfg T L Dop η, ?_, ?_, ?_⟩
  · intro hdom
    exact theorem_4_5_source_formula_bound_at_horizon
      P cfg T Wstar L Dop η _hfinite _hstar _hsmooth _hbounded hdom _hη
  · unfold AsymptoticUpperRealOn
    refine ⟨1, 1, by norm_num, by norm_num, ?_, ?_⟩
    · simp [ConstantRespectsScope, theoremScope]
    · intro ε hε _hεpos _hεsmall
      simp
  · intro hruns
    rcases theorem_4_5_sourceRhs_le_epsilon_at_log_horizon
        P cfg L Dop _hfinite with ⟨horizonBound, hrate, hselect⟩
    unfold theorem_4_5_precisionConclusion
    refine ⟨horizonBound, hrate, ?_⟩
    intro ε hε hεdomain
    let N := theorem_4_5_logHorizon m n L Dop
      (sourceObjectiveInitialGap P cfg.W0 _hfinite) ε hε
    have hrun := hruns ε hε
    have hselected := hselect ε hε hεdomain
    dsimp [N] at hrun hselected
    rcases hselected with ⟨hN, hscalar⟩
    refine ⟨N, hN, ⟨_hstar, _hsmooth, hrun⟩, ?_⟩
    have hden : (matrixRankBound m n : ℝ) * L * Dop ≠ 0 := hε.2.1
    have hDop : Dop ≠ 0 := by
      intro hzero
      apply hden
      simp [hzero]
    have hstepBounds := hε.2.2.2.2
    dsimp at hstepBounds
    have hdom : theorem_4_5_rhsDomain P
        (theorem_4_5_precisionConfig cfg L Dop
          (sourceObjectiveInitialGap P cfg.W0 _hfinite) ε hε)
        N L Dop (theorem_4_5_etaRateRealized m n L Dop ε hε.2.1) := by
      refine ⟨hDop, ?_, ?_⟩
      · simpa [theorem_4_5_etaRateRealized, realizedSourceQuot, sourceQuot] using
          hstepBounds.1
      · simpa [theorem_4_5_etaRateRealized, realizedSourceQuot, sourceQuot] using
          hstepBounds.2
    have hformula := theorem_4_5_source_formula_bound_at_horizon P
      (theorem_4_5_precisionConfig cfg L Dop
        (sourceObjectiveInitialGap P cfg.W0 _hfinite) ε hε)
      N Wstar L Dop (theorem_4_5_etaRateRealized m n L Dop ε hε.2.1)
      _hfinite _hstar _hsmooth hrun hdom (by
        intro t ht
        rfl)
    exact le_trans hformula hscalar

/- Formula-only C.2 selector.  Its hypotheses are source objects and scalar
   regularity; no run, objective-gap conclusion, or desired-complexity premise
   is accepted here. -/
theorem source_rational_rate_at_ceil
    (K Δ ε : ℝ) (hK : 0 ≤ K) (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    let N := Nat.ceil (2 * K / ε)
    (N : ℝ) ≤ 2 * K / ε + 1 ∧
      (2 * K * Δ) / (2 * K + (N : ℝ) * Δ) ≤ ε := by
  let X : ℝ := 2 * K / ε
  let N := Nat.ceil X
  have hX : 0 ≤ X := div_nonneg (mul_nonneg (by norm_num) hK) hε.le
  have hNupper : (N : ℝ) ≤ X + 1 :=
    le_of_lt (by simpa [N] using Nat.ceil_lt_add_one hX)
  refine ⟨by simpa [N, X], ?_⟩
  by_cases hKzero : K = 0
  · simpa [hKzero] using hε.le
  by_cases hΔzero : Δ = 0
  · simpa [hΔzero] using hε.le
  have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hKzero)
  have hΔpos : 0 < Δ := lt_of_le_of_ne hΔ (Ne.symm hΔzero)
  have hXN : X ≤ (N : ℝ) := by
    dsimp [N, X]
    exact Nat.le_ceil _
  have htwoK : 2 * K ≤ (N : ℝ) * ε := by
    have := (div_le_iff₀ hε).mp hXN
    nlinarith
  have hden : 0 < 2 * K + (N : ℝ) * Δ := by positivity
  apply (div_le_iff₀ hden).2
  have hscaled := mul_le_mul_of_nonneg_right htwoK hΔ
  nlinarith

theorem theorem_4_6_sourceRhs_le_epsilon_at_selected_horizon
    {m n : ℕ} (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (L Dop : ℝ) (hfinite : P.HasFiniteInfimum)
    (hsmooth : FrobeniusSmooth P L) :
    ∃ horizonBound : ∀ ε : ℝ, epsilonDomain ε → ℝ,
      AsymptoticUpperRealOn epsilonDomain horizonBound
        (fun ε hε => theorem_4_6_complexityRateRealized m n L Dop ε hε)
        (theoremScope "Theorem 4.6 selected rational horizon" ["epsilon"]) ∧
      ∀ ε : ℝ, ∀ hε : epsilonDomain ε,
        let N := theorem_4_6_selectedHorizon m n L Dop ε hε
        (N : ℝ) ≤ horizonBound ε hε ∧
          theorem_4_6_sourceRhs P cfg N L Dop ≤ ε := by
  let Δ := sourceObjectiveInitialGap P cfg.W0 hfinite
  let K : ℝ := (matrixRankBound m n : ℝ) * L * Dop ^ 2
  let horizonBound : ∀ ε : ℝ, epsilonDomain ε → ℝ :=
    fun ε hε => (theorem_4_6_selectedHorizon m n L Dop ε hε : ℝ)
  have hΔ : 0 ≤ Δ := by
    dsimp [Δ, sourceObjectiveInitialGap, Objective.sourceFStar]
    linarith [objective_terminal_lower_bound P hfinite cfg.W0]
  have hK : 0 ≤ K := by
    by_cases hr : matrixRankBound m n = 0
    · simp [K, hr]
    · have hrpos : 0 < Real.sqrt (matrixRankBound m n : ℝ) :=
        Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hr)
      have hL : 0 ≤ L := nonneg_of_mul_nonneg_left
        (frobeniusSmooth_mul_sqrt_rankBound_nonneg hsmooth) hrpos
      dsimp [K]
      positivity
  refine ⟨horizonBound, ?_, ?_⟩
  · unfold AsymptoticUpperRealOn
    by_cases hKzero : K = 0
    · refine ⟨1, 1, by norm_num, by norm_num, ?_, ?_⟩
      · simp [ConstantRespectsScope, theoremScope]
      · intro ε hε _hεpos _hεsmall
        have hscale : (matrixRankBound m n : ℝ) * L * Dop ^ 2 = 0 := by
          simpa [K] using hKzero
        have htwoscale : 2 * (matrixRankBound m n : ℝ) * L * Dop ^ 2 = 0 := by
          calc
            2 * (matrixRankBound m n : ℝ) * L * Dop ^ 2 =
                2 * ((matrixRankBound m n : ℝ) * L * Dop ^ 2) := by ring
            _ = 0 := by rw [hscale, mul_zero]
        simp [horizonBound, theorem_4_6_selectedHorizon,
          theorem_4_6_complexityRateRealized, hscale, htwoscale]
    · have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hKzero)
      refine ⟨3, K, by norm_num, hKpos, ?_, ?_⟩
      · simp [ConstantRespectsScope, theoremScope]
      · intro ε hε hεpos hεsmall
        have hX : 0 ≤ 2 * K / ε := by positivity
        have hNupper :
            (theorem_4_6_selectedHorizon m n L Dop ε hε : ℝ) <
              2 * K / ε + 1 := by
          dsimp [theorem_4_6_selectedHorizon]
          convert Nat.ceil_lt_add_one hX using 1 <;> dsimp [K] <;> ring
        have hone : 1 ≤ K / ε := (one_le_div hεpos).2 hεsmall
        have hNupper' :
            (theorem_4_6_selectedHorizon m n L Dop ε hε : ℝ) <
              2 * (K / ε) + 1 := by
          convert hNupper using 1 <;> ring
        have hrate : theorem_4_6_complexityRateRealized m n L Dop ε hε =
            K / ε := by
          dsimp [theorem_4_6_complexityRateRealized,
            realizedSourceInv, sourceInv, K]
          ring
        dsimp [horizonBound]
        rw [hrate]
        linarith
  · intro ε hε
    let N := theorem_4_6_selectedHorizon m n L Dop ε hε
    refine ⟨le_rfl, ?_⟩
    have hscalar := source_rational_rate_at_ceil K Δ ε hK hΔ hε
    convert hscalar.2 using 1 <;>
      dsimp [N, theorem_4_6_selectedHorizon, theorem_4_6_sourceRhs,
        K, Δ, sourceObjectiveInitialGap, Objective.sourceFStar] <;> ring

theorem theorem_4_6 {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (t : ℕ) (Wstar : Mat m n) (L Dop : ℝ)
    (_hfinite : P.HasFiniteInfimum)
    (_hstar : StarConvex P Wstar)
    (_hsmooth : FrobeniusSmooth P L)
    (_hbounded : BoundedOperatorDistance P cfg t Wstar Dop)
    (_hη : theorem_4_6_adaptiveSchedule P cfg t L) :
    theorem_4_6_statement P cfg t Wstar L Dop _hfinite := by
  constructor
  · intro hdom
    have hformula := theorem_4_6_source_formula_bound_at_horizon
      P cfg t Wstar L Dop _hfinite _hstar _hsmooth _hbounded _hη
    simpa [theorem_4_6_rhs, theorem_4_6_sourceRhs,
      realizedSourceQuot, sourceQuot] using hformula
  · intro hruns
    rcases theorem_4_6_sourceRhs_le_epsilon_at_selected_horizon
        P cfg L Dop _hfinite _hsmooth with ⟨horizonBound, hrate, hselect⟩
    unfold theorem_4_6_precisionConclusion
    refine ⟨horizonBound, hrate, ?_⟩
    intro ε hε _hεdomain
    let N := theorem_4_6_selectedHorizon m n L Dop ε hε
    have hrun := hruns ε hε
    have hselected := hselect ε hε
    dsimp [N] at hrun hselected
    refine ⟨N, hselected.1, ⟨_hstar, _hsmooth, hrun⟩, ?_⟩
    exact le_trans
      (theorem_4_6_source_formula_bound_at_horizon P cfg N Wstar L Dop
        _hfinite _hstar _hsmooth hrun.1 hrun.2)
      hselected.2

/- Appendix B.2's spectral-smooth two-point upper model.  The operator norm
   is packaged as a separating seminorm on the Euclidean matrix carrier, and
   its support dual is bounded by the nuclear norm through matrix duality. -/
theorem spectralSmooth_quadratic_upper_bound
    {m n : ℕ} (P : Objective m n) {Lstar : ℝ}
    (hsmooth : SpectralSmooth P Lstar) (W W' : Mat m n) :
    P.f W' ≤ P.f W + frobeniusInner (P.grad W) (W' - W) +
      (Lstar / 2) * spectralNorm (W' - W) ^ 2 := by
  let E := EuclideanSpace ℝ (Fin m × Fin n)
  let e : Mat m n ≃ₗᵢ[ℝ] E := matrixEuclideanLinearIsometryEquiv
  let toOp : E →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) :=
    { toFun := fun x =>
        (Matrix.toEuclideanLin (𝕜 := ℝ) (e.symm x)).toContinuousLinearMap
      map_add' := by
        intro x y
        ext v
        simp [e]
      map_smul' := by
        intro c x
        ext v
        simp [e] }
  let p : Seminorm ℝ E :=
    (normSeminorm ℝ
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))).comp toOp
  have hp_apply (x : E) : p x = spectralNorm (e.symm x) := by
    rfl
  have hp : p.IsSeparating := by
    intro x
    constructor
    · intro hx
      have hop : toOp x = 0 := by
        apply norm_eq_zero.mp
        change p x = 0
        exact hx
      have hlin : Matrix.toEuclideanLin (𝕜 := ℝ) (e.symm x) = 0 := by
        apply LinearMap.ext
        intro v
        exact DFunLike.congr_fun hop v
      have hmat : e.symm x = 0 := by
        apply Matrix.toEuclideanLin.injective
        simpa using hlin
      apply e.symm.injective
      simpa using hmat
    · rintro rfl
      change spectralNorm (0 : Mat m n) = 0
      change ‖(Matrix.toEuclideanLin (𝕜 := ℝ)
        (0 : Mat m n)).toContinuousLinearMap‖ = 0
      have hz : Matrix.toEuclideanLin (𝕜 := ℝ) (0 : Mat m n) = 0 := by
        simp
      rw [hz]
      simp
  let fE : E → ℝ := fun x => vectorizedObjective P (e.symm x)
  let gradE : E → E := fun x => e (P.grad (e.symm x))
  have hgrad : ∀ z ∈ (Set.univ : Set E),
      HasGradientWithinAt fE (gradE z) Set.univ z := by
    intro z _hz
    have hbase : DifferentiableAt ℝ (vectorizedObjective P) (e.symm z) :=
      (hsmooth.contDiff.differentiable (by norm_num)) (e.symm z)
    have hcomp := hbase.hasFDerivAt.comp z e.symm.hasFDerivAt
    have hat : HasGradientAt fE (gradE z) z := by
      rw [hasGradientAt_iff_hasFDerivAt]
      convert hcomp using 1
      ext H
      change ⟪e (P.grad (e.symm z)), H⟫_ℝ =
        fderiv ℝ (vectorizedObjective P) (e.symm z) (e.symm H)
      rw [objective_fderiv_apply_eq_frobeniusInner_grad]
      rw [← inner_matrixToEuclidean]
      rfl
    exact (hasGradientWithinAt_univ).2 hat
  have hdual (x y : E) :
      SOptLib.affineDirectionDualNorm (Set.univ : Set E) p
          (gradE x - gradE y) ≤
        nuclearNorm (P.grad (e.symm x) - P.grad (e.symm y)) := by
    rw [SOptLib.affineDirectionDualNorm_eq_sSup]
    apply csSup_le
    · refine ⟨0, 0, ?_, ?_, ?_⟩
      · exact (affineSpan ℝ (Set.univ : Set E)).direction.zero_mem
      · simp
      · simp
    · intro r hr
      rcases hr with ⟨d, _hd, hd, rfl⟩
      have hpair :
          |⟪gradE x - gradE y, d⟫_ℝ| ≤
            nuclearNorm (P.grad (e.symm x) - P.grad (e.symm y)) * p d := by
        have hmatrix := abs_frobeniusInner_le_nuclearNorm_mul_spectralNorm
          (P.grad (e.symm x) - P.grad (e.symm y)) (e.symm d)
        change |⟪e (P.grad (e.symm x)) - e (P.grad (e.symm y)), d⟫_ℝ| ≤
          nuclearNorm (P.grad (e.symm x) - P.grad (e.symm y)) * p d
        rw [← e.map_sub]
        conv_lhs =>
          rw [show d = e (e.symm d) by simp]
        change
          |⟪matrixToEuclidean (P.grad (e.symm x) - P.grad (e.symm y)),
            matrixToEuclidean (e.symm d)⟫_ℝ| ≤
          nuclearNorm (P.grad (e.symm x) - P.grad (e.symm y)) * p d
        rw [inner_matrixToEuclidean, hp_apply]
        exact hmatrix
      calc
        |⟪gradE x - gradE y, d⟫_ℝ| ≤
            nuclearNorm (P.grad (e.symm x) - P.grad (e.symm y)) * p d := hpair
        _ ≤ nuclearNorm (P.grad (e.symm x) - P.grad (e.symm y)) * 1 :=
          mul_le_mul_of_nonneg_left hd
            (nuclearNorm_nonneg (P.grad (e.symm x) - P.grad (e.symm y)))
        _ = nuclearNorm (P.grad (e.symm x) - P.grad (e.symm y)) := by ring
  have hmodel :=
    SOptLib.carrier_smooth_quadratic_upper_bound_of_affineDirectionDualNorm_lipschitz
      fE gradE p Lstar hp convex_univ hgrad
      (fun x _hx y _hy => by
        calc
          SOptLib.affineDirectionDualNorm (Set.univ : Set E) p
              (gradE x - gradE y) ≤
              nuclearNorm (P.grad (e.symm x) - P.grad (e.symm y)) := hdual x y
          _ ≤ Lstar * spectralNorm (e.symm x - e.symm y) :=
            hsmooth.lipschitz_grad (e.symm x) (e.symm y)
          _ = Lstar * p (x - y) := by
            rw [hp_apply, e.symm.map_sub])
      (Set.mem_univ (e W)) (Set.mem_univ (e W'))
  dsimp [fE, gradE] at hmodel
  simp only [e.symm_apply_apply] at hmodel
  change P.f W' ≤ P.f W +
      ⟪matrixToEuclidean (P.grad W),
        matrixToEuclidean W' - matrixToEuclidean W⟫_ℝ +
      (Lstar / 2) * p (e W' - e W) ^ 2 at hmodel
  rw [← matrixToEuclidean_sub, inner_matrixToEuclidean] at hmodel
  rw [hp_apply, e.symm.map_sub, e.symm_apply_apply] at hmodel
  exact hmodel

theorem orthogonalizedDirection_spectralNorm_le_one
    {m n : ℕ} (M : Mat m n) :
    spectralNorm (orthogonalizedDirection M) ≤ 1 := by
  rcases orthogonalizedDirection_isThinSVDWithPolar M with
    ⟨U, V, _s, hU, hV, _hs, _hM, hpolar⟩
  rw [hpolar]
  exact spectralNorm_mul_transpose_le_one_of_orthonormalColumns U V hU hV

theorem theorem_4_7_one_step_spectral_descent
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    {T t : ℕ} {Lstar η : ℝ}
    (ht : t ∈ Finset.range T)
    (hη : ∀ k ∈ Finset.range T, cfg.eta k = η)
    (hsmooth : SpectralSmooth P.objective Lstar)
    (ω : SamplePath ξ cfg.batchSize) :
    P.objective.f (stochasticMuonState P cfg ω t).W -
        P.objective.f (stochasticMuonState P cfg ω (t + 1)).W ≥
      η * frobeniusInner
        (P.objective.grad (stochasticMuonState P cfg ω t).W)
        (orthogonalizedDirection (stochasticMuonState P cfg ω t).M) -
      (Lstar / 2) * η ^ 2 *
        spectralNorm
          (orthogonalizedDirection (stochasticMuonState P cfg ω t).M) ^ 2 := by
  have hstep := spectralSmooth_quadratic_upper_bound P.objective hsmooth
    (stochasticMuonState P cfg ω t).W
    (stochasticMuonState P cfg ω (t + 1)).W
  rw [stochasticMuon_W_succ_eq_source_update, hη t ht] at hstep
  have hdiff :
      (stochasticMuonState P cfg ω t).W -
          η • orthogonalizedDirection (stochasticMuonState P cfg ω t).M -
          (stochasticMuonState P cfg ω t).W =
        (-η) • orthogonalizedDirection (stochasticMuonState P cfg ω t).M := by
    ext i j
    simp
  rw [hdiff] at hstep
  rw [show frobeniusInner
        (P.objective.grad (stochasticMuonState P cfg ω t).W)
        ((-η) • orthogonalizedDirection (stochasticMuonState P cfg ω t).M) =
      -η * frobeniusInner
        (P.objective.grad (stochasticMuonState P cfg ω t).W)
        (orthogonalizedDirection (stochasticMuonState P cfg ω t).M) by
      unfold frobeniusInner
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      change
        P.objective.grad (stochasticMuonState P cfg ω t).W i j *
            (-η * orthogonalizedDirection (stochasticMuonState P cfg ω t).M i j) = _
      ring] at hstep
  rw [show spectralNorm
        ((-η) • orthogonalizedDirection (stochasticMuonState P cfg ω t).M) ^ 2 =
      η ^ 2 * spectralNorm
        (orthogonalizedDirection (stochasticMuonState P cfg ω t).M) ^ 2 by
      simp [spectralNorm, norm_smul, Real.norm_eq_abs, abs_neg, mul_pow, sq_abs]] at hstep
  have hupdate :
      (stochasticMuonState P cfg ω (t + 1)).W =
        (stochasticMuonState P cfg ω t).W -
          η • orthogonalizedDirection (stochasticMuonState P cfg ω t).M := by
    rw [stochasticMuon_W_succ_eq_source_update, hη t ht]
  rw [hupdate]
  nlinarith

/- Appendix B.2, steps 1--5: spectral descent followed by the polar pairing,
   nuclear/operator duality, and the nuclear triangle replacement. -/
theorem theorem_4_7_one_step_descent_with_tracking
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    {T t : ℕ} {Lstar η : ℝ}
    (ht : t ∈ Finset.range T)
    (hη : ∀ k ∈ Finset.range T, cfg.eta k = η)
    (hηpos : 0 < η)
    (hsmooth : SpectralSmooth P.objective Lstar)
    (ω : SamplePath ξ cfg.batchSize) :
    P.objective.f (stochasticMuonState P cfg ω t).W -
        P.objective.f (stochasticMuonState P cfg ω (t + 1)).W ≥
      η * nuclearNorm
          (P.objective.grad (stochasticMuonState P cfg ω t).W) -
        (Lstar / 2) * η ^ 2 -
        2 * η * nuclearNorm
          (P.objective.grad (stochasticMuonState P cfg ω t).W -
            (stochasticMuonState P cfg ω t).M) := by
  let G := P.objective.grad (stochasticMuonState P cfg ω t).W
  let M := (stochasticMuonState P cfg ω t).M
  let D := orthogonalizedDirection M
  let E := G - M
  have hbase := theorem_4_7_one_step_spectral_descent
    P cfg ht hη hsmooth ω
  have hDnorm : spectralNorm D ≤ 1 :=
    orthogonalizedDirection_spectralNorm_le_one M
  have hDsq : spectralNorm D ^ 2 ≤ 1 := by
    nlinarith [spectralNorm_nonneg D]
  have hquad :
      (Lstar / 2) * η ^ 2 * spectralNorm D ^ 2 ≤
        (Lstar / 2) * η ^ 2 := by
    have hcoeff : 0 ≤ (Lstar / 2) * η ^ 2 :=
      mul_nonneg (div_nonneg hsmooth.nonneg (by norm_num)) (sq_nonneg η)
    simpa [mul_one] using mul_le_mul_of_nonneg_left hDsq hcoeff
  have hEpair : -nuclearNorm E ≤ frobeniusInner E D := by
    have habs := abs_frobeniusInner_orthogonalizedDirection_le_nuclearNorm E M
    nlinarith [neg_abs_le (frobeniusInner E D)]
  have hnuctri := nuclearNorm_sub_triangle G M
  have hpairM : frobeniusInner M D = nuclearNorm M :=
    orthogonalizedDirection_frobeniusInner_eq_nuclearNorm M
  have hsplit : frobeniusInner G D =
      frobeniusInner M D + frobeniusInner E D := by
    dsimp [E]
    unfold frobeniusInner
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    simp only [Matrix.sub_apply]
    ring
  have hpairG : nuclearNorm G - 2 * nuclearNorm E ≤ frobeniusInner G D := by
    rw [hsplit, hpairM]
    linarith
  change _ ≥ η * nuclearNorm G - _ - 2 * η * nuclearNorm E
  change _ ≥ η * frobeniusInner G D -
    (Lstar / 2) * η ^ 2 * spectralNorm D ^ 2 at hbase
  have hpair_scaled := mul_le_mul_of_nonneg_left hpairG hηpos.le
  linarith

/- Appendix B.2, steps 7--13: the comparator lags the true gradient in
   nuclear norm by a geometric spectral-smoothness budget, without a rank
   conversion on this deterministic term. -/
theorem theorem_4_7_comparator_lag_bound
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    {T t : ℕ} {Lstar η : ℝ}
    (ht : t ∈ Finset.range T)
    (hη : ∀ k ∈ Finset.range T, cfg.eta k = η)
    (hηpos : 0 < η)
    (hsmooth : SpectralSmooth P.objective Lstar)
    (ω : SamplePath ξ cfg.batchSize) :
    nuclearNorm
        (P.objective.grad (stochasticMuonState P cfg ω t).W -
          stochasticMuonComparator P cfg ω t) ≤
      cfg.beta * Lstar * η / (1 - cfg.beta) := by
  have hβ0 : 0 ≤ cfg.beta := cfg.beta_mem.1
  have hβ1 : cfg.beta < 1 := cfg.beta_mem.2
  have hden : 0 < 1 - cfg.beta := sub_pos.mpr hβ1
  induction t with
  | zero =>
      have hzero :
          P.objective.grad (stochasticMuonState P cfg ω 0).W -
              stochasticMuonComparator P cfg ω 0 = 0 := by
        simp [stochasticMuonState, stochasticMuonBaseState,
          stochasticMuonComparator]
      rw [hzero]
      have hnuczero : nuclearNorm (0 : Mat m n) = 0 := by
        unfold nuclearNorm
        simp
      rw [hnuczero]
      exact div_nonneg
        (mul_nonneg (mul_nonneg hβ0 hsmooth.nonneg) hηpos.le) hden.le
  | succ t ih =>
      have htT : t < T := lt_trans (Nat.lt_succ_self t) (Finset.mem_range.mp ht)
      have htmem : t ∈ Finset.range T := Finset.mem_range.mpr htT
      have hstep := hη t htmem
      let D := orthogonalizedDirection (stochasticMuonState P cfg ω t).M
      have hdir : spectralNorm D ≤ 1 :=
        orthogonalizedDirection_spectralNorm_le_one _
      have hWdiff :
          spectralNorm
              ((stochasticMuonState P cfg ω (t + 1)).W -
                (stochasticMuonState P cfg ω t).W) ≤ η := by
        rw [stochasticMuon_W_succ_eq_source_update, hstep]
        have heq :
            (stochasticMuonState P cfg ω t).W - η • D -
                (stochasticMuonState P cfg ω t).W = (-η) • D := by
          module
        rw [heq]
        have hscale : spectralNorm ((-η) • D) = η * spectralNorm D := by
          simp [spectralNorm, norm_smul, Real.norm_eq_abs, abs_neg,
            abs_of_pos hηpos]
        rw [hscale]
        simpa using mul_le_mul_of_nonneg_left hdir hηpos.le
      have hgrad :
          nuclearNorm
              (P.objective.grad (stochasticMuonState P cfg ω (t + 1)).W -
                P.objective.grad (stochasticMuonState P cfg ω t).W) ≤
            Lstar * η := by
        exact le_trans (hsmooth.lipschitz_grad _ _)
          (mul_le_mul_of_nonneg_left hWdiff hsmooth.nonneg)
      have hlag_triangle :
          nuclearNorm
              (P.objective.grad (stochasticMuonState P cfg ω (t + 1)).W -
                stochasticMuonComparator P cfg ω t) ≤
            nuclearNorm
                (P.objective.grad (stochasticMuonState P cfg ω (t + 1)).W -
                  P.objective.grad (stochasticMuonState P cfg ω t).W) +
              nuclearNorm
                (P.objective.grad (stochasticMuonState P cfg ω t).W -
                  stochasticMuonComparator P cfg ω t) := by
        simpa [sub_add_sub_cancel] using nuclearNorm_add_le
          (P.objective.grad (stochasticMuonState P cfg ω (t + 1)).W -
            P.objective.grad (stochasticMuonState P cfg ω t).W)
          (P.objective.grad (stochasticMuonState P cfg ω t).W -
            stochasticMuonComparator P cfg ω t)
      rw [stochasticMuonComparator_succ]
      have hfactor :
          P.objective.grad (stochasticMuonState P cfg ω (t + 1)).W -
              (cfg.beta • stochasticMuonComparator P cfg ω t +
                (1 - cfg.beta) •
                  P.objective.grad (stochasticMuonState P cfg ω (t + 1)).W) =
            cfg.beta •
              (P.objective.grad (stochasticMuonState P cfg ω (t + 1)).W -
                stochasticMuonComparator P cfg ω t) := by
        module
      rw [hfactor]
      have hscale := nuclearNorm_smul_le_of_nonneg cfg.beta
        (P.objective.grad (stochasticMuonState P cfg ω (t + 1)).W -
          stochasticMuonComparator P cfg ω t) hβ0
      have hpre :
          nuclearNorm
              (P.objective.grad (stochasticMuonState P cfg ω (t + 1)).W -
                stochasticMuonComparator P cfg ω t) ≤
            Lstar * η + cfg.beta * Lstar * η / (1 - cfg.beta) :=
        le_trans hlag_triangle (add_le_add hgrad (ih htmem))
      have hmul := mul_le_mul_of_nonneg_left hpre hβ0
      calc
        nuclearNorm
            (cfg.beta •
              (P.objective.grad (stochasticMuonState P cfg ω (t + 1)).W -
                stochasticMuonComparator P cfg ω t)) ≤
            cfg.beta * nuclearNorm
              (P.objective.grad (stochasticMuonState P cfg ω (t + 1)).W -
                stochasticMuonComparator P cfg ω t) := hscale
        _ ≤ cfg.beta *
            (Lstar * η + cfg.beta * Lstar * η / (1 - cfg.beta)) := hmul
        _ = cfg.beta * Lstar * η / (1 - cfg.beta) := by
          field_simp [ne_of_gt hden]
          ring

/- Appendix B.2, steps 6 and 14.  Lemma A.4 controls the stochastic
   comparator error in Frobenius norm; the rank comparison is applied only to
   that term, while the deterministic comparator lag remains rank-free. -/
theorem theorem_4_7_combined_nuclear_tracking_bound
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    {T t : ℕ} {Lstar σ η : ℝ}
    (ht : t ∈ Finset.range T)
    (hη : ∀ k ∈ Finset.range T, cfg.eta k = η)
    (hηpos : 0 < η)
    (hsmooth : SpectralSmooth P.objective Lstar)
    (hvariance : BoundedVariance P σ) :
    Integrable (fun ω =>
        nuclearNorm
          (P.objective.grad (stochasticMuonState P cfg ω t).W -
            (stochasticMuonState P cfg ω t).M))
      (samplePathLaw P cfg.batchSize) ∧
      (∫ ω,
        nuclearNorm
          (P.objective.grad (stochasticMuonState P cfg ω t).W -
            (stochasticMuonState P cfg ω t).M)
        ∂(samplePathLaw P cfg.batchSize)) ≤
      Real.sqrt (matrixRankBound m n : ℝ) *
          (Real.sqrt ((1 - cfg.beta) / (1 + cfg.beta)) * σ /
              Real.sqrt (cfg.batchSize.val : ℝ) +
            cfg.beta ^ t * σ / Real.sqrt (cfg.batchSize.val : ℝ)) +
        cfg.beta * Lstar * η / (1 - cfg.beta) := by
  let μ := samplePathLaw P cfg.batchSize
  let D : SamplePath ξ cfg.batchSize → Mat m n := fun ω =>
    P.objective.grad (stochasticMuonState P cfg ω t).W -
      stochasticMuonComparator P cfg ω t
  let E : SamplePath ξ cfg.batchSize → Mat m n := fun ω =>
    stochasticMuonComparator P cfg ω t - (stochasticMuonState P cfg ω t).M
  let Z : SamplePath ξ cfg.batchSize → Mat m n := fun ω =>
    P.objective.grad (stochasticMuonState P cfg ω t).W -
      (stochasticMuonState P cfg ω t).M
  let rroot : ℝ := Real.sqrt (matrixRankBound m n : ℝ)
  let K : ℝ := cfg.beta * Lstar * η / (1 - cfg.beta)
  letI : IsProbabilityMeasure P.sampleLaw := P.isProbability_sampleLaw
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, samplePathLaw]
    infer_instance
  have hpast_le : stochasticSampleStrictPast cfg.batchSize (t + 1) ≤
      (by infer_instance : MeasurableSpace (SamplePath ξ cfg.batchSize)) := by
    unfold stochasticSampleStrictPast
    refine iSup_le fun q => iSup_le fun _hq => ?_
    have hcoord : Measurable
        (fun ω : SamplePath ξ cfg.batchSize => ω q.1 q.2) :=
      (measurable_pi_apply q.2).comp (measurable_pi_apply q.1)
    exact hcoord.comap_le
  have hC_meas : Measurable
      (fun ω : SamplePath ξ cfg.batchSize => stochasticMuonComparator P cfg ω t) :=
    (stochasticMuonComparator_strictPast_measurable P cfg t).mono hpast_le le_rfl
  have hD_meas : Measurable D := by
    exact (P.objective.grad_measurable.comp
      (stochasticMuon_W_measurable P cfg t)).sub hC_meas
  have hE_meas : Measurable E := by
    exact hC_meas.sub (stochasticMuon_M_measurable P cfg t)
  have hZ_meas : Measurable Z := by
    exact (P.objective.grad_measurable.comp
      (stochasticMuon_W_measurable P cfg t)).sub
        (stochasticMuon_M_measurable P cfg t)
  have hlag : ∀ ω, nuclearNorm (D ω) ≤ K := by
    intro ω
    exact theorem_4_7_comparator_lag_bound P cfg ht hη hηpos hsmooth ω
  have hK : 0 ≤ K := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg cfg.beta_mem.1 hsmooth.nonneg) hηpos.le)
      (sub_nonneg.mpr cfg.beta_mem.2.le)
  have hDnorm_int : Integrable (fun ω => nuclearNorm (D ω)) μ := by
    apply Integrable.of_bound
      (nuclearNorm_measurable.comp hD_meas).aestronglyMeasurable K
    exact Filter.Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (nuclearNorm_nonneg (D ω))] using hlag ω
  have hEsq :=
    (stochasticMuon_comparatorError_sq_integrable_and_bound
      P cfg t σ hvariance).1
  have hE_int : Integrable E μ := by
    apply integrable_of_integrable_norm_sq hE_meas.aestronglyMeasurable
    simpa [E, μ, frobeniusNorm, norm_matrixToEuclidean] using hEsq
  have herr_int : Integrable (fun ω => frobeniusNorm (E ω)) μ := by
    simpa [frobeniusNorm] using hE_int.norm
  have hmajorant_int : Integrable
      (fun ω => nuclearNorm (D ω) + rroot * frobeniusNorm (E ω)) μ :=
    hDnorm_int.add (herr_int.const_mul rroot)
  have hpoint (ω : SamplePath ξ cfg.batchSize) :
      nuclearNorm (Z ω) ≤
        nuclearNorm (D ω) + rroot * frobeniusNorm (E ω) := by
    have htri := nuclearNorm_sub_triangle (Z ω) (D ω)
    have hdiff : Z ω - D ω = E ω := by
      dsimp [Z, D, E]
      module
    rw [hdiff] at htri
    exact htri.trans (add_le_add le_rfl (by
      simpa [rroot] using
        nuclearNorm_le_sqrt_rankBound_mul_frobeniusNorm (E ω)))
  have hZnorm_int : Integrable (fun ω => nuclearNorm (Z ω)) μ := by
    refine Integrable.mono' hmajorant_int
      (nuclearNorm_measurable.comp hZ_meas).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun ω => by
      have hZ_nonneg : 0 ≤ nuclearNorm (Z ω) := nuclearNorm_nonneg _
      have hmajorant_nonneg :
          0 ≤ nuclearNorm (D ω) + rroot * frobeniusNorm (E ω) :=
        hZ_nonneg.trans (hpoint ω)
      simpa [Real.norm_eq_abs, abs_of_nonneg hZ_nonneg,
        abs_of_nonneg hmajorant_nonneg] using hpoint ω
  have hintegral :
      (∫ ω, nuclearNorm (Z ω) ∂μ) ≤
        ∫ ω, nuclearNorm (D ω) + rroot * frobeniusNorm (E ω) ∂μ :=
    integral_mono hZnorm_int hmajorant_int hpoint
  have hadd :
      (∫ ω, nuclearNorm (D ω) + rroot * frobeniusNorm (E ω) ∂μ) =
        (∫ ω, nuclearNorm (D ω) ∂μ) +
          rroot * ∫ ω, frobeniusNorm (E ω) ∂μ := by
    rw [integral_add hDnorm_int (herr_int.const_mul rroot), integral_const_mul]
  rw [hadd] at hintegral
  have hD_integral : (∫ ω, nuclearNorm (D ω) ∂μ) ≤ K := by
    calc
      (∫ ω, nuclearNorm (D ω) ∂μ) ≤ ∫ _ω, K ∂μ := by
        apply integral_mono hDnorm_int (integrable_const K)
        exact hlag
      _ = K := by simp
  have hA4 := stochasticMuonLemmaA4Bound_of_source_assumptions
    P cfg t σ hvariance
  have herr_integral :
      (∫ ω, frobeniusNorm (E ω) ∂μ) ≤
        Real.sqrt ((1 - cfg.beta) / (1 + cfg.beta)) * σ /
            Real.sqrt (cfg.batchSize.val : ℝ) +
          cfg.beta ^ t * σ / Real.sqrt (cfg.batchSize.val : ℝ) := by
    simpa [stochasticMuonLemmaA4Bound, E, μ] using hA4
  have herr_scaled := mul_le_mul_of_nonneg_left herr_integral
    (Real.sqrt_nonneg (matrixRankBound m n : ℝ))
  have hcombined := hintegral.trans
    (add_le_add hD_integral herr_scaled)
  refine ⟨?_, ?_⟩
  · simpa [Z, μ] using hZnorm_int
  · dsimp [Z, D, E, μ, rroot, K] at hcombined ⊢
    linarith

/- Appendix B.2, steps 15--16: integrate the pathwise descent inequality,
   telescope objective values, sum the geometric noise tail, and normalize by
   the positive horizon/stepsize product. -/
theorem theorem_4_7_source_average_bound_at_horizon
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (Lstar σ η : ℝ)
    (hsrc : theorem_4_7_sourceDomain T η)
    (hη : ∀ k ∈ Finset.range T, cfg.eta k = η)
    (hsmooth : SpectralSmooth P.objective Lstar)
    (hvariance : BoundedVariance P σ) :
    stochasticAverageNuclearGradient P cfg T ≤
      stochasticExpectedObjectiveDrop P cfg T / ((T : ℝ) * η) +
        Lstar * η / 2 +
        2 * Real.sqrt (matrixRankBound m n : ℝ) *
          (Real.sqrt ((1 - cfg.beta) / (1 + cfg.beta)) * σ /
            Real.sqrt (cfg.batchSize.val : ℝ)) +
        2 * Real.sqrt (matrixRankBound m n : ℝ) * σ /
          ((1 - cfg.beta) * (T : ℝ) * Real.sqrt (cfg.batchSize.val : ℝ)) +
        2 * η * cfg.beta * Lstar / (1 - cfg.beta) := by
  let μ := samplePathLaw P cfg.batchSize
  let g : ℕ → SamplePath ξ cfg.batchSize → ℝ := fun t ω =>
    nuclearNorm (P.objective.grad (stochasticMuonState P cfg ω t).W)
  let e : ℕ → SamplePath ξ cfg.batchSize → ℝ := fun t ω =>
    nuclearNorm
      (P.objective.grad (stochasticMuonState P cfg ω t).W -
        (stochasticMuonState P cfg ω t).M)
  let d : ℕ → SamplePath ξ cfg.batchSize → ℝ := fun t ω =>
    P.objective.f (stochasticMuonState P cfg ω t).W -
      P.objective.f (stochasticMuonState P cfg ω (t + 1)).W
  let rroot : ℝ := Real.sqrt (matrixRankBound m n : ℝ)
  let B : ℝ := cfg.batchSize.val
  let A : ℝ := Real.sqrt ((1 - cfg.beta) / (1 + cfg.beta)) * σ / Real.sqrt B
  let C : ℝ := σ / Real.sqrt B
  let K : ℝ := cfg.beta * Lstar * η / (1 - cfg.beta)
  let a : ℝ := Lstar / 2 * η ^ 2
  let c : ℝ := 2 * η
  letI : IsProbabilityMeasure P.sampleLaw := P.isProbability_sampleLaw
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, samplePathLaw]
    infer_instance
  let hregularity : StochasticObjectiveRegularity P.objective :=
    Or.inr (Or.inl ⟨Lstar, hsmooth⟩)
  have hsumg_int : Integrable (fun ω => ∑ t ∈ Finset.range T, g t ω) μ := by
    simpa [g, μ, stochasticAverageNuclearGradientWellDefined,
      SOptLib.expectationWellDefined] using
      (stochasticAverageNuclearGradient_wellDefined_of_source_assumptions
        P cfg T σ hregularity hvariance)
  have hg_int : ∀ t ∈ Finset.range T, Integrable (g t) μ := by
    intro t ht
    have hgmeas : Measurable (g t) := by
      exact nuclearNorm_measurable.comp
        (P.objective.grad_measurable.comp (stochasticMuon_W_measurable P cfg t))
    apply hsumg_int.mono' hgmeas.aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (nuclearNorm_nonneg_early _)]
    simpa [g] using Finset.single_le_sum
      (fun k _hk => nuclearNorm_nonneg_early
        (P.objective.grad (stochasticMuonState P cfg ω k).W)) ht
  have hdrop_int : ∀ t ∈ Finset.range T, Integrable (d t) μ := by
    intro t ht
    have htlt : t < T := Finset.mem_range.mp ht
    have hleft := stochasticExpectedObjectiveDrop_wellDefined_of_source_assumptions
      P cfg t σ hregularity hvariance
    have hright := stochasticExpectedObjectiveDrop_wellDefined_of_source_assumptions
      P cfg (t + 1) σ hregularity hvariance
    have hleft' : Integrable
        (fun ω => P.objective.f cfg.W0 -
          P.objective.f (stochasticMuonState P cfg ω t).W) μ := by
      simpa [μ, stochasticExpectedObjectiveDropWellDefined,
        SOptLib.expectationWellDefined] using hleft
    have hright' : Integrable
        (fun ω => P.objective.f cfg.W0 -
          P.objective.f (stochasticMuonState P cfg ω (t + 1)).W) μ := by
      simpa [μ, stochasticExpectedObjectiveDropWellDefined,
        SOptLib.expectationWellDefined] using hright
    apply (hright'.sub hleft').congr
    filter_upwards [] with ω
    dsimp [d]
    ring
  have he_data : ∀ t ∈ Finset.range T,
      Integrable (e t) μ ∧
        ∫ ω, e t ω ∂μ ≤ rroot * (A + cfg.beta ^ t * C) + K := by
    intro t ht
    have htrack := theorem_4_7_combined_nuclear_tracking_bound
      P cfg ht hη hsrc.2 hsmooth hvariance
    refine ⟨by simpa [e, μ] using htrack.1, ?_⟩
    dsimp [e, μ, rroot, A, C, K, B]
    convert htrack.2 using 1 <;> ring
  have hstep : ∀ t ∈ Finset.range T,
      η * (∫ ω, g t ω ∂μ) ≤
        (∫ ω, d t ω ∂μ) + a +
          c * (rroot * (A + cfg.beta ^ t * C) + K) := by
    intro t ht
    have hpoint : ∀ ω, η * g t ω ≤ d t ω + a + c * e t ω := by
      intro ω
      have hs := theorem_4_7_one_step_descent_with_tracking
        P cfg ht hη hsrc.2 hsmooth ω
      dsimp [g, d, e, a, c]
      linarith
    have hint : (∫ ω, η * g t ω ∂μ) ≤
        ∫ ω, d t ω + a + c * e t ω ∂μ := by
      apply integral_mono ((hg_int t ht).const_mul η)
        (((hdrop_int t ht).add (integrable_const a)).add
          ((he_data t ht).1.const_mul c))
      exact hpoint
    rw [integral_const_mul] at hint
    have hrhs :
        (∫ ω, d t ω + a + c * e t ω ∂μ) =
          (∫ ω, d t ω ∂μ) + a + c * (∫ ω, e t ω ∂μ) := by
      calc
        _ = (∫ ω, d t ω + a ∂μ) + ∫ ω, c * e t ω ∂μ := by
          exact integral_add ((hdrop_int t ht).add (integrable_const a))
            ((he_data t ht).1.const_mul c)
        _ = _ := by
          rw [integral_add (hdrop_int t ht) (integrable_const a),
            integral_const, measureReal_univ_eq_one, one_smul, integral_const_mul]
    rw [hrhs] at hint
    have hc : 0 ≤ c := by
      dsimp [c]
      exact mul_nonneg (by norm_num) hsrc.2.le
    have herr := mul_le_mul_of_nonneg_left (he_data t ht).2 hc
    exact le_trans hint (by linarith)
  have hsum := Finset.sum_le_sum hstep
  have hsum_g :
      ∑ t ∈ Finset.range T, η * (∫ ω, g t ω ∂μ) =
        η * ∫ ω, ∑ t ∈ Finset.range T, g t ω ∂μ := by
    rw [integral_finset_sum _ hg_int, Finset.mul_sum]
  have hsum_d :
      ∑ t ∈ Finset.range T, (∫ ω, d t ω ∂μ) =
        stochasticExpectedObjectiveDrop P cfg T := by
    rw [← integral_finset_sum _ hdrop_int]
    apply integral_congr_ae
    filter_upwards [] with ω
    dsimp [d, stochasticExpectedObjectiveDrop]
    simpa [stochasticMuonState, stochasticMuonBaseState] using
      (Finset.sum_range_sub'
        (fun t => P.objective.f (stochasticMuonState P cfg ω t).W) T)
  rw [hsum_g] at hsum
  have hgeom : (∑ t ∈ Finset.range T, cfg.beta ^ t) ≤ 1 / (1 - cfg.beta) := by
    have hmul := geom_sum_mul_neg cfg.beta T
    have hpow : 0 ≤ cfg.beta ^ T := pow_nonneg cfg.beta_mem.1 T
    have hden : 0 < 1 - cfg.beta := sub_pos.mpr cfg.beta_mem.2
    apply (le_div_iff₀ hden).2
    rw [hmul]
    linarith
  have hC : 0 ≤ C := by
    dsimp [C, B]
    exact div_nonneg hvariance.nonneg (Real.sqrt_nonneg _)
  have hnoise_sum :
      ∑ t ∈ Finset.range T,
          (a + c * (rroot * (A + cfg.beta ^ t * C) + K)) ≤
        (T : ℝ) * a +
          c * (rroot * ((T : ℝ) * A + C / (1 - cfg.beta)) +
            (T : ℝ) * K) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    have hgeomC : (∑ t ∈ Finset.range T, cfg.beta ^ t) * C ≤
        (1 / (1 - cfg.beta)) * C :=
      mul_le_mul_of_nonneg_right hgeom hC
    rw [← Finset.mul_sum]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    have hc : 0 ≤ c := by
      dsimp [c]
      exact mul_nonneg (by norm_num) hsrc.2.le
    have hrroot : 0 ≤ rroot := Real.sqrt_nonneg _
    have hgeomC' : (∑ t ∈ Finset.range T, cfg.beta ^ t) * C ≤
        C / (1 - cfg.beta) := by
      simpa [div_eq_mul_inv, mul_comm] using hgeomC
    have hinner :
        rroot * ((T : ℝ) * A +
            (∑ x ∈ Finset.range T, cfg.beta ^ x) * C) + (T : ℝ) * K ≤
          rroot * ((T : ℝ) * A + C / (1 - cfg.beta)) + (T : ℝ) * K := by
      have hinside :
          (T : ℝ) * A + (∑ x ∈ Finset.range T, cfg.beta ^ x) * C ≤
            (T : ℝ) * A + C / (1 - cfg.beta) :=
        by simpa [add_comm] using add_le_add_left hgeomC' ((T : ℝ) * A)
      nlinarith [mul_le_mul_of_nonneg_left hinside hrroot]
    have hsum_expand :
        (∑ x ∈ Finset.range T, rroot * (A + cfg.beta ^ x * C)) =
          rroot * ((T : ℝ) * A +
            (∑ x ∈ Finset.range T, cfg.beta ^ x) * C) := by
      calc
        _ = ∑ x ∈ Finset.range T,
            (rroot * A + rroot * (cfg.beta ^ x * C)) := by
              apply Finset.sum_congr rfl
              intro x _hx
              ring
        _ = (T : ℝ) * (rroot * A) +
            ∑ x ∈ Finset.range T, rroot * (cfg.beta ^ x * C) := by
              rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
              simp only [Finset.card_range]
        _ = _ := by
              rw [← Finset.mul_sum]
              rw [Finset.sum_mul]
              ring
    rw [hsum_expand]
    nlinarith [mul_le_mul_of_nonneg_left hinner hc]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsum_d] at hsum
  have hnum :
      η * ∫ ω, ∑ t ∈ Finset.range T, g t ω ∂μ ≤
        stochasticExpectedObjectiveDrop P cfg T +
          (T : ℝ) * a +
          c * (rroot * ((T : ℝ) * A + C / (1 - cfg.beta)) +
            (T : ℝ) * K) := by
    have hnoise_sum' :
        (∑ x ∈ Finset.range T, a) +
            ∑ x ∈ Finset.range T,
              c * (rroot * (A + cfg.beta ^ x * C) + K) ≤
          (T : ℝ) * a +
            c * (rroot * ((T : ℝ) * A + C / (1 - cfg.beta)) +
              (T : ℝ) * K) := by
      simpa [Finset.sum_add_distrib, add_assoc] using hnoise_sum
    exact le_trans hsum (by
      simpa [add_assoc] using
        add_le_add_left hnoise_sum' (stochasticExpectedObjectiveDrop P cfg T))
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast hsrc.1.1
  have hTηpos : 0 < (T : ℝ) * η := mul_pos hTpos hsrc.2
  let S : ℝ := ∫ ω, ∑ t ∈ Finset.range T, g t ω ∂μ
  let N : ℝ := stochasticExpectedObjectiveDrop P cfg T +
    (T : ℝ) * a +
    c * (rroot * ((T : ℝ) * A + C / (1 - cfg.beta)) + (T : ℝ) * K)
  have hnormalized : (T : ℝ)⁻¹ * S ≤ N / ((T : ℝ) * η) := by
    apply (le_div_iff₀ hTηpos).2
    calc
      ((T : ℝ)⁻¹ * S) * ((T : ℝ) * η) = η * S := by
        field_simp [ne_of_gt hTpos]
      _ ≤ N := by simpa [S, N] using hnum
  have heq : N / ((T : ℝ) * η) =
      stochasticExpectedObjectiveDrop P cfg T / ((T : ℝ) * η) +
        Lstar * η / 2 +
        2 * Real.sqrt (matrixRankBound m n : ℝ) *
          (Real.sqrt ((1 - cfg.beta) / (1 + cfg.beta)) * σ /
            Real.sqrt (cfg.batchSize.val : ℝ)) +
        2 * Real.sqrt (matrixRankBound m n : ℝ) * σ /
          ((1 - cfg.beta) * (T : ℝ) * Real.sqrt (cfg.batchSize.val : ℝ)) +
        2 * η * cfg.beta * Lstar / (1 - cfg.beta) := by
    have hsqrtB : 0 < Real.sqrt (cfg.batchSize.val : ℝ) := by
      exact Real.sqrt_pos.2 (by exact_mod_cast cfg.batchSize.positive)
    dsimp [N, a, c, rroot, A, C, K, B]
    field_simp [ne_of_gt hTpos, ne_of_gt hsrc.2,
      ne_of_gt (sub_pos.mpr cfg.beta_mem.2), ne_of_gt hsqrtB]
    ring
  change (T : ℝ)⁻¹ * S ≤ _
  exact hnormalized.trans_eq heq

theorem theorem_4_7_source_average_bound_at_horizon_sourceRhs
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (Lstar σ η : ℝ)
    (hsrc : theorem_4_7_sourceDomain T η)
    (hη : ∀ k ∈ Finset.range T, cfg.eta k = η)
    (hsmooth : SpectralSmooth P.objective Lstar)
    (hvariance : BoundedVariance P σ) :
    stochasticAverageNuclearGradient P cfg T ≤
      theorem_4_7_sourceRhs P cfg T Lstar σ η := by
  have hbound := theorem_4_7_source_average_bound_at_horizon
    P cfg T Lstar σ η hsrc hη hsmooth hvariance
  have hr : 0 ≤ (matrixRankBound m n : ℝ) := by positivity
  have hB : 0 < (cfg.batchSize.val : ℝ) := by
    exact_mod_cast cfg.batchSize.positive
  have hminus : 0 ≤ 1 - cfg.beta := by linarith [cfg.beta_mem.2]
  have hplus : 0 < 1 + cfg.beta := by linarith [cfg.beta_mem.1]
  have hnoise :
      2 * Real.sqrt (matrixRankBound m n : ℝ) *
          (Real.sqrt ((1 - cfg.beta) / (1 + cfg.beta)) * σ /
            Real.sqrt (cfg.batchSize.val : ℝ)) =
        (2 * σ * Real.sqrt
            ((matrixRankBound m n : ℝ) * (1 - cfg.beta))) /
          Real.sqrt ((1 + cfg.beta) * (cfg.batchSize.val : ℝ)) := by
    rw [Real.sqrt_mul hr, Real.sqrt_mul (le_of_lt hplus),
      Real.sqrt_div hminus]
    field_simp [ne_of_gt (Real.sqrt_pos.2 hB),
      ne_of_gt (Real.sqrt_pos.2 hplus)]
  unfold theorem_4_7_sourceRhs
  dsimp
  rw [← hnoise]
  convert hbound using 1 <;> ring

theorem theorem_4_7 {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (Lstar σ η : ℝ)
    (_hη : ∀ t ∈ Finset.range T, cfg.eta t = η)
    (_hsmooth : SpectralSmooth P.objective Lstar)
    (_hvariance : BoundedVariance P σ) :
    theorem_4_7_statement P cfg T Lstar σ η := by
  constructor
  · exact theorem_4_7_source_domain_obligation
      P cfg T Lstar σ η _hη _hsmooth _hvariance
  · intro hsrc
    rcases theorem_4_7_downstream_phase2_boundary_of_sourceDomain
        P cfg T Lstar σ η hsrc _hη _hsmooth _hvariance with
      ⟨hbasic, hdom, _hηpos⟩
    rcases hdom with
      ⟨hT, hdrop, hsNoise, hsBatchNoise, hqBatchNoise, hsRank, hsBatch,
        hqTail, hqMomentum⟩
    refine ⟨hbasic,
      ⟨hT, hdrop, hsNoise, hsBatchNoise, hqBatchNoise, hsRank, hsBatch,
        hqTail, hqMomentum⟩, ?_⟩
    have hbound := theorem_4_7_source_average_bound_at_horizon_sourceRhs
      P cfg T Lstar σ η hsrc _hη _hsmooth _hvariance
    simpa [stochasticAverageNuclearGradientRealized,
      stochasticAverageNuclearGradient, stochasticExpectedObjectiveDropRealized,
      stochasticExpectedObjectiveDrop, realizedExpectation, theorem_4_7_rhs,
      theorem_4_7_sourceRhs, realizedSourceQuot, sourceQuot,
      realizedSourceSqrt, sourceSqrt] using hbound

theorem corollary_4_8_deterministicZeroMotion_of_degenerate_scale
    {m n : ℕ} (P : Objective m n) (W0 : Mat m n) (Lstar beta : ℝ)
    (hfinite : P.HasFiniteInfimum) (hsmooth : SpectralSmooth P Lstar)
    (hbeta : beta ∈ Set.Ico (0 : ℝ) 1)
    (hcoefficient : Lstar * sourceObjectiveInitialGap P W0 hfinite = 0) :
    corollary_4_8_deterministicZeroMotion P W0 Lstar
      (sourceObjectiveInitialGap P W0 hfinite) beta hbeta := by
  have hgrad : P.grad W0 = 0 := by
    rcases mul_eq_zero.mp hcoefficient with hLstar | hgap
    · have hfrobenius : FrobeniusSmooth P 0 := by
        refine ⟨hsmooth.contDiff, ?_⟩
        intro W W'
        have hdual := frobeniusNorm_le_nuclearNorm (P.grad W - P.grad W')
        have hspectral := hsmooth.lipschitz_grad W W'
        simpa [hLstar] using hdual.trans hspectral
      exact objective_grad_eq_zero_of_frobeniusSmooth_zero
        P W0 hfinite hfrobenius
    · exact objective_grad_eq_zero_of_sourceInitialGap_eq_zero P W0 hfinite hgap
  exact deterministicMomentum_zeroMotion_of_grad_eq_zero P W0 _
    (by intro T; rfl) hgrad

theorem corollary_4_8_deterministicOracle_bound_at_horizon {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMomentumMuonConfig m n)
    (T : ℕ) (Lstar eta : ℝ)
    (hEta : ∀ t ∈ Finset.range T, cfg.eta t = eta)
    (hSmooth : SpectralSmooth P Lstar) :
    theorem_4_7_sourceDomain T eta →
      ∃ hbasic : stochasticBasicExpectationsWellDefined
          (deterministicOracleProblem P) (deterministicOracleConfig cfg) T,
      ∃ hdom : theorem_4_7_rhsDomain (deterministicOracleProblem P)
          (deterministicOracleConfig cfg) T Lstar 0 eta hbasic.2,
        deterministicMomentumAverageNuclearGradient P cfg T ≤
          theorem_4_7_rhs (deterministicOracleProblem P)
            (deterministicOracleConfig cfg) T Lstar 0 eta hbasic.2 hdom := by
  intro hsrc
  have hresult := theorem_4_7 (deterministicOracleProblem P)
    (deterministicOracleConfig cfg) T Lstar 0 eta
    (by simpa [deterministicOracleConfig] using hEta)
    (by simpa only [deterministicOracleProblem_objective] using hSmooth)
    (deterministicOracleProblem_boundedVariance_zero P)
  rcases hresult.2 hsrc with ⟨hbasic, hdom, hbound⟩
  refine ⟨hbasic, hdom, ?_⟩
  rw [← deterministicOracle_average_eq P cfg T hbasic.1]
  exact hbound

set_option maxHeartbeats 800000 in
theorem corollary_4_8_stochastic_schedule_scalar_bound
    {m n T : ℕ} {Lstar σ Δ : ℝ}
    (hreg : corollary_4_8_stochasticRegime m n Lstar σ Δ)
    (hT : corollary_4_8_stochasticRateDomain m n T Lstar σ Δ) :
    let q := corollary_4_8_stochasticOneMinusBeta m n T Lstar σ Δ
    let η := corollary_4_8_stochasticEta m n T Lstar σ Δ
    Δ / ((T : ℝ) * η) +
        Lstar * η / 2 +
        (2 * σ * Real.sqrt ((matrixRankBound m n : ℝ) * q)) /
          Real.sqrt (2 - q) +
        (2 * σ * Real.sqrt (matrixRankBound m n : ℝ)) /
          (q * (T : ℝ)) +
        (2 * η * (1 - q) * Lstar) / q ≤
      10 * corollary_4_8_stochasticRateRealized m n T Lstar σ Δ hT := by
  dsimp only
  unfold corollary_4_8_stochasticRegime at hreg
  rcases hreg with ⟨hrNat, hL, hσ, hΔ⟩
  let r : ℝ := matrixRankBound m n
  let τ : ℝ := T
  let q : ℝ := corollary_4_8_stochasticOneMinusBeta m n T Lstar σ Δ
  let η : ℝ := corollary_4_8_stochasticEta m n T Lstar σ Δ
  let A : ℝ := Δ / (τ * η)
  have hr : 0 < r := by
    dsimp [r]
    exact_mod_cast hrNat
  have hτ : 0 < τ := by
    dsimp [τ]
    exact_mod_cast hT.1
  have hratio :
      0 < sourceQuot (Real.sqrt (Lstar * Δ))
        (σ * Real.sqrt (r * τ)) := by
    unfold sourceQuot
    positivity
  have hq : 0 < q := by
    dsimp [q, corollary_4_8_stochasticOneMinusBeta, r, τ]
    exact lt_min hratio zero_lt_one
  have hqle : q ≤ 1 := by
    dsimp [q, corollary_4_8_stochasticOneMinusBeta]
    exact min_le_right _ _
  have hη : 0 < η := by
    dsimp [η, corollary_4_8_stochasticEta, sourceQuot]
    apply Real.sqrt_pos.2
    positivity
  have hηsq : η ^ 2 = q * Δ / (τ * Lstar) := by
    dsimp [η, corollary_4_8_stochasticEta, sourceQuot, q, τ]
    rw [Real.sq_sqrt]
    positivity
  have hscale : Lstar * η = q * A := by
    have hden : τ * Lstar ≠ 0 := by positivity
    have hηpoly : η ^ 2 * (τ * Lstar) = q * Δ :=
      (eq_div_iff hden).mp hηsq
    dsimp [A]
    calc
      Lstar * η = (q * Δ) / (τ * η) := by
        apply (eq_div_iff (mul_ne_zero (ne_of_gt hτ) (ne_of_gt hη))).2
        ring_nf at hηpoly ⊢
        nlinarith
      _ = q * (Δ / (τ * η)) := by ring
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hsmoothEq : Lstar * η / 2 = q * A / 2 := by rw [hscale]
  have hmomentumEq :
      (2 * η * (1 - q) * Lstar) / q = 2 * (1 - q) * A := by
    apply (div_eq_iff (ne_of_gt hq)).2
    calc
      2 * η * (1 - q) * Lstar = 2 * (1 - q) * (Lstar * η) := by ring
      _ = 2 * (1 - q) * (q * A) := by rw [hscale]
      _ = 2 * (1 - q) * A * q := by ring
  change A + Lstar * η / 2 +
        (2 * σ * Real.sqrt (r * q)) / Real.sqrt (2 - q) +
        (2 * σ * Real.sqrt r) / (q * τ) +
        (2 * η * (1 - q) * Lstar) / q ≤
      10 * corollary_4_8_stochasticRateRealized m n T Lstar σ Δ hT
  rw [hsmoothEq, hmomentumEq]
  have hdenOne : 1 ≤ Real.sqrt (2 - q) := by
    rw [Real.one_le_sqrt]
    linarith
  have hdenPos : 0 < Real.sqrt (2 - q) := lt_of_lt_of_le zero_lt_one hdenOne
  have hnoiseNonneg : 0 ≤ 2 * σ * Real.sqrt (r * q) := by positivity
  have hnoise :
      (2 * σ * Real.sqrt (r * q)) / Real.sqrt (2 - q) ≤
        2 * σ * Real.sqrt (r * q) := by
    apply (div_le_iff₀ hdenPos).2
    exact le_mul_of_one_le_right hnoiseNonneg hdenOne
  have hηexpr : η = q * A / Lstar := by
    apply (eq_div_iff (ne_of_gt hL)).2
    nlinarith [hscale]
  have hAsq : A ^ 2 = Lstar * Δ / (τ * q) := by
    have hAeq : A = Δ / (τ * (q * A / Lstar)) := by
      dsimp [A]
      rw [← hηexpr]
    have hdenA : τ * (q * A / Lstar) ≠ 0 := by positivity
    have hApoly := (eq_div_iff hdenA).mp hAeq
    apply (eq_div_iff (mul_ne_zero (ne_of_gt hτ) (ne_of_gt hq))).2
    field_simp [ne_of_gt hL] at hApoly
    ring_nf at hApoly ⊢
    nlinarith
  let R₁ : ℝ := Real.sqrt (Real.sqrt ((r * Lstar * Δ * σ ^ 2) / τ))
  let R₂ : ℝ := Real.sqrt ((Lstar * Δ) / τ)
  let R₃ : ℝ := r * σ ^ 2 / Real.sqrt (Lstar * Δ * τ)
  have hR₁ : 0 ≤ R₁ := by dsimp [R₁]; positivity
  have hR₂ : 0 ≤ R₂ := by dsimp [R₂]; positivity
  have hR₃ : 0 ≤ R₃ := by dsimp [R₃]; positivity
  change A + q * A / 2 +
        (2 * σ * Real.sqrt (r * q)) / Real.sqrt (2 - q) +
        (2 * σ * Real.sqrt r) / (q * τ) +
        2 * (1 - q) * A ≤ 10 * (R₁ + R₂ + R₃)
  let d : ℝ := Real.sqrt (Lstar * Δ)
  let s : ℝ := Real.sqrt (r * τ)
  let u : ℝ := Real.sqrt τ
  have hd : 0 < d := by dsimp [d]; positivity
  have hs : 0 < s := by dsimp [s]; positivity
  have hu : 0 < u := by dsimp [u]; positivity
  have hdsq : d ^ 2 = Lstar * Δ := by
    dsimp [d]
    exact Real.sq_sqrt (mul_nonneg hL.le hΔ.le)
  have hssq : s ^ 2 = r * τ := by
    dsimp [s]
    exact Real.sq_sqrt (mul_nonneg hr.le hτ.le)
  have husq : u ^ 2 = τ := by
    dsimp [u]
    exact Real.sq_sqrt hτ.le
  have hrootRankTime : Real.sqrt r * s = r * u := by
    apply (mul_self_inj_of_nonneg (by positivity) (by positivity)).mp
    rw [show Real.sqrt r * s * (Real.sqrt r * s) =
          (Real.sqrt r) ^ 2 * s ^ 2 by ring,
        show r * u * (r * u) = r ^ 2 * u ^ 2 by ring,
        Real.sq_sqrt hr.le, hssq, husq]
    ring
  by_cases ha : sourceQuot (Real.sqrt (Lstar * Δ))
      (σ * Real.sqrt (r * τ)) ≤ 1
  · have hqeq : q = d / (σ * s) := by
      dsimp [q, corollary_4_8_stochasticOneMinusBeta, r, τ]
      rw [min_eq_left ha]
      rfl
    have hAsq' : A ^ 2 = d * σ * s / τ := by
      rw [hAsq, hqeq]
      field_simp [ne_of_gt hσ, ne_of_gt hs, ne_of_gt hd, ne_of_gt hτ]
      nlinarith [hdsq]
    have hrad : 0 ≤ (r * Lstar * Δ * σ ^ 2) / τ := by positivity
    have hR₁four : R₁ ^ 4 = (r * Lstar * Δ * σ ^ 2) / τ := by
      dsimp [R₁]
      calc
        Real.sqrt (Real.sqrt ((r * Lstar * Δ * σ ^ 2) / τ)) ^ 4 =
            (Real.sqrt (Real.sqrt ((r * Lstar * Δ * σ ^ 2) / τ)) ^ 2) ^ 2 := by ring
        _ = Real.sqrt ((r * Lstar * Δ * σ ^ 2) / τ) ^ 2 := by
          rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
        _ = (r * Lstar * Δ * σ ^ 2) / τ := Real.sq_sqrt hrad
    have hAfour : A ^ 4 = (r * Lstar * Δ * σ ^ 2) / τ := by
      calc
        A ^ 4 = (A ^ 2) ^ 2 := by ring
        _ = (d * σ * s / τ) ^ 2 := by rw [hAsq']
        _ = (r * Lstar * Δ * σ ^ 2) / τ := by
          field_simp [ne_of_gt hτ]
          rw [hdsq, hssq]
          ring
    have hAR₁sq : A ^ 2 = R₁ ^ 2 := by
      apply (mul_self_inj_of_nonneg (sq_nonneg A) (sq_nonneg R₁)).mp
      calc
        A ^ 2 * A ^ 2 = A ^ 4 := by ring
        _ = (r * Lstar * Δ * σ ^ 2) / τ := hAfour
        _ = R₁ ^ 4 := hR₁four.symm
        _ = R₁ ^ 2 * R₁ ^ 2 := by ring
    have hAR₁ : A = R₁ := by
      apply (mul_self_inj_of_nonneg hA.le hR₁).mp
      simpa [pow_two] using hAR₁sq
    have hnoiseEq : σ * Real.sqrt (r * q) = A := by
      have hsq : (σ * Real.sqrt (r * q)) ^ 2 = A ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (mul_nonneg hr.le hq.le), hAsq', hqeq]
        field_simp [ne_of_gt hσ, ne_of_gt hs, ne_of_gt hτ]
        nlinarith [hssq]
      apply (mul_self_inj_of_nonneg
        (mul_nonneg hσ.le (Real.sqrt_nonneg _)) hA.le).mp
      simpa [pow_two] using hsq
    have hrootProduct : Real.sqrt (Lstar * Δ * τ) = d * u := by
      calc
        Real.sqrt (Lstar * Δ * τ) = Real.sqrt (Lstar * Δ) * Real.sqrt τ := by
          rw [Real.sqrt_mul (mul_nonneg hL.le hΔ.le)]
        _ = d * u := rfl
    have htailEq : (2 * σ * Real.sqrt r) / (q * τ) = 2 * R₃ := by
      rw [hqeq]
      dsimp [R₃]
      rw [hrootProduct]
      field_simp [ne_of_gt hσ, ne_of_gt hd, ne_of_gt hs, ne_of_gt hu,
        ne_of_gt hτ]
      rw [hrootRankTime]
      calc
        r * u * u = r * (u ^ 2) := by ring
        _ = r * τ := by rw [husq]
        _ = τ * r := by ring
    have hsmoothBound : q * A / 2 ≤ A / 2 := by
      exact div_le_div_of_nonneg_right
        (by simpa using mul_le_mul_of_nonneg_right hqle hA.le) (by norm_num)
    have hmomentumBound : 2 * (1 - q) * A ≤ 2 * A := by
      have hbase : (1 - q) * A ≤ A := by
        have hone : 1 - q ≤ 1 := sub_le_self 1 hq.le
        simpa using mul_le_mul_of_nonneg_right hone hA.le
      calc
        2 * (1 - q) * A = 2 * ((1 - q) * A) := by ring
        _ ≤ 2 * A := mul_le_mul_of_nonneg_left hbase (by norm_num)
    have hnoiseBound :
        (2 * σ * Real.sqrt (r * q)) / Real.sqrt (2 - q) ≤ 2 * A := by
      calc
        _ ≤ 2 * σ * Real.sqrt (r * q) := hnoise
        _ = 2 * (σ * Real.sqrt (r * q)) := by ring
        _ = 2 * A := by rw [hnoiseEq]
    have hsumBound :
        A + q * A / 2 +
            (2 * σ * Real.sqrt (r * q)) / Real.sqrt (2 - q) +
            (2 * σ * Real.sqrt r) / (q * τ) +
            2 * (1 - q) * A ≤ (11 / 2 : ℝ) * A + 2 * R₃ := by
      rw [htailEq]
      linarith only [hsmoothBound, hmomentumBound, hnoiseBound]
    calc
      _ ≤ (11 / 2 : ℝ) * A + 2 * R₃ := hsumBound
      _ ≤ 10 * (R₁ + R₂ + R₃) := by
        rw [hAR₁]
        nlinarith only [hR₁, hR₂, hR₃]
  · have hratioOne :
        1 < sourceQuot (Real.sqrt (Lstar * Δ))
          (σ * Real.sqrt (r * τ)) := lt_of_not_ge ha
    have hqeq : q = 1 := by
      dsimp [q, corollary_4_8_stochasticOneMinusBeta, r, τ]
      rw [min_eq_right hratioOne.le]
    have hR₂sq : R₂ ^ 2 = (Lstar * Δ) / τ := by
      dsimp [R₂]
      exact Real.sq_sqrt (by positivity)
    have hAR₂sq : A ^ 2 = R₂ ^ 2 := by
      rw [hAsq, hqeq, mul_one, hR₂sq]
    have hAR₂ : A = R₂ := by
      apply (mul_self_inj_of_nonneg hA.le hR₂).mp
      simpa [pow_two] using hAR₂sq
    have hσs : σ * s < d := by
      have hone : 1 < d / (σ * s) := by
        simpa [d, s, sourceQuot] using hratioOne
      exact (one_lt_div (mul_pos hσ hs)).mp hone
    have hσscale : σ ^ 2 * r * τ ≤ Lstar * Δ := by
      have hsquare : (σ * s) ^ 2 ≤ d ^ 2 :=
        (sq_le_sq₀ (mul_nonneg hσ.le hs.le) hd.le).2 hσs.le
      simpa [mul_pow, hssq, hdsq, mul_assoc] using hsquare
    have hnoiseBase : σ * Real.sqrt r ≤ A := by
      apply (sq_le_sq₀ (mul_nonneg hσ.le (Real.sqrt_nonneg _)) hA.le).mp
      calc
        (σ * Real.sqrt r) ^ 2 = σ ^ 2 * r := by
          rw [mul_pow, Real.sq_sqrt hr.le]
        _ ≤ (Lstar * Δ) / τ := by
          apply (le_div_iff₀ hτ).2
          nlinarith [hσscale]
        _ = A ^ 2 := by rw [hAsq, hqeq, mul_one]
    have hnoiseBound :
        (2 * σ * Real.sqrt (r * q)) / Real.sqrt (2 - q) ≤ 2 * A := by
      calc
        _ ≤ 2 * σ * Real.sqrt (r * q) := hnoise
        _ = 2 * (σ * Real.sqrt r) := by rw [hqeq, mul_one]; ring
        _ ≤ 2 * A := mul_le_mul_of_nonneg_left hnoiseBase (by norm_num)
    have hτone : (1 : ℝ) ≤ τ := by
      dsimp [τ]
      exact_mod_cast hT.1
    have htailBound : (2 * σ * Real.sqrt r) / (q * τ) ≤ 2 * A := by
      rw [hqeq, one_mul]
      calc
        (2 * σ * Real.sqrt r) / τ ≤ 2 * σ * Real.sqrt r := by
          apply (div_le_iff₀ hτ).2
          exact le_mul_of_one_le_right (by positivity) hτone
        _ = 2 * (σ * Real.sqrt r) := by ring
        _ ≤ 2 * A := mul_le_mul_of_nonneg_left hnoiseBase (by norm_num)
    have hnoiseUnit : 2 * σ * Real.sqrt r ≤ 2 * A := by
      calc
        2 * σ * Real.sqrt r = 2 * (σ * Real.sqrt r) := by ring
        _ ≤ 2 * A := mul_le_mul_of_nonneg_left hnoiseBase (by norm_num)
    have htailUnit : (2 * σ * Real.sqrt r) / τ ≤ 2 * A := by
      simpa [hqeq] using htailBound
    have hsumBound :
        A + q * A / 2 +
            (2 * σ * Real.sqrt (r * q)) / Real.sqrt (2 - q) +
            (2 * σ * Real.sqrt r) / (q * τ) +
            2 * (1 - q) * A ≤ (11 / 2 : ℝ) * A := by
      rw [hqeq]
      simp only [mul_one, one_mul, sub_self, Real.sqrt_one, div_one, mul_zero,
        add_zero]
      norm_num only [Real.sqrt_one]
      simp only [div_one, zero_mul, add_zero]
      linarith only [hnoiseUnit, htailUnit]
    calc
      _ ≤ (11 / 2 : ℝ) * A := hsumBound
      _ ≤ 10 * (R₁ + R₂ + R₃) := by
        rw [hAR₂]
        nlinarith only [hR₁, hR₂, hR₃]

theorem corollary_4_8_stochastic_bound_at_realized_horizon
    {ξ : Type*} [MeasurableSpace ξ] {m n T : ℕ}
    (P : StochasticProblem ξ m n) (W0 : Mat m n) {Lstar σ Δ : ℝ}
    (hfinite : P.objective.HasFiniteInfimum)
    (hΔeq : sourceObjectiveInitialGap P.objective W0 hfinite = Δ)
    (hsmooth : SpectralSmooth P.objective Lstar)
    (hvariance : BoundedVariance P σ)
    (hreg : corollary_4_8_stochasticRegime m n Lstar σ Δ)
    (horizon : horizonDomain T) :
    ∃ hT : corollary_4_8_stochasticSemanticHorizonDomain
        P W0 T Lstar σ Δ,
      ∀ cfg : StochasticMuonConfig m n,
        ∀ hrun : corollary_4_8_stochasticRealization W0 T Lstar σ Δ cfg,
          stochasticAverageNuclearGradientRealized P cfg T (hT.2 cfg hrun) ≤
            10 * corollary_4_8_stochasticRateRealized
              m n T Lstar σ Δ hT.1.2.1 := by
  let hT := corollary_4_8_stochasticRegime_semantic
    P W0 hreg horizon hsmooth hvariance
  refine ⟨hT, ?_⟩
  intro cfg hrun
  let q := corollary_4_8_stochasticOneMinusBeta m n T Lstar σ Δ
  let η := corollary_4_8_stochasticEta m n T Lstar σ Δ
  have hηschedule : ∀ t ∈ Finset.range T, cfg.eta t = η := hrun.2.2.2.1
  have hηpos : 0 < η := by
    have hreg' := hreg
    unfold corollary_4_8_stochasticRegime at hreg'
    rcases hreg' with ⟨hrNat, hL, hσ, hΔ⟩
    have hr : 0 < (matrixRankBound m n : ℝ) := by exact_mod_cast hrNat
    have hTr : 0 < (T : ℝ) := by exact_mod_cast horizon
    have hq : 0 < q := by
      dsimp [q, corollary_4_8_stochasticOneMinusBeta, sourceQuot]
      apply lt_min
      · positivity
      · norm_num
    dsimp [η, corollary_4_8_stochasticEta, sourceQuot]
    apply Real.sqrt_pos.2
    positivity
  have hsrc : theorem_4_7_sourceDomain T η := by
    refine ⟨⟨horizon, ?_⟩, hηpos⟩
    unfold sourceQuotDomain
    exact mul_ne_zero (by exact_mod_cast ne_of_gt horizon) (ne_of_gt hηpos)
  have hresult := theorem_4_7 P cfg T Lstar σ η hηschedule hsmooth hvariance
  rcases hresult.2 hsrc with ⟨hbasic, hdom, hbound⟩
  have hdrop : stochasticExpectedObjectiveDrop P cfg T ≤ Δ := by
    calc
      stochasticExpectedObjectiveDrop P cfg T ≤
          sourceObjectiveInitialGap P.objective cfg.W0 hfinite :=
        stochastic_expected_objective_drop_le_source_initial_gap
          P cfg T hfinite hbasic.2
      _ = Δ := by rw [hrun.2.1, hΔeq]
  have hden : 0 < (T : ℝ) * η := by
    exact mul_pos (by exact_mod_cast horizon) hηpos
  have hdropQuot :
      stochasticExpectedObjectiveDrop P cfg T / ((T : ℝ) * η) ≤
        Δ / ((T : ℝ) * η) :=
    div_le_div_of_nonneg_right hdrop hden.le
  have hbeta : cfg.beta = 1 - q := by
    dsimp [q]
    linarith [hrun.2.2.2.2]
  have hrhs :
      theorem_4_7_rhs P cfg T Lstar σ η hbasic.2 hdom ≤
        Δ / ((T : ℝ) * η) +
          Lstar * η / 2 +
          (2 * σ * Real.sqrt ((matrixRankBound m n : ℝ) * q)) /
            Real.sqrt (2 - q) +
          (2 * σ * Real.sqrt (matrixRankBound m n : ℝ)) /
            (q * (T : ℝ)) +
          (2 * η * (1 - q) * Lstar) / q := by
    rcases hdom with
      ⟨hdomT, hdropDom, hsNoise, hsBatchNoise, hqBatchNoise, hsRank,
        hsBatch, hqTail, hqMomentum⟩
    dsimp [theorem_4_7_rhs, realizedSourceQuot, realizedSourceSqrt, sourceQuot,
      sourceSqrt]
    rw [hrun.2.2.1, hbeta]
    norm_num only [Nat.cast_one, one_mul, Real.sqrt_one, mul_one]
    rw [stochasticExpectedObjectiveDropRealized_eq_integral]
    ring_nf at hdropQuot ⊢
    linarith only [hdropQuot]
  have hscalar := corollary_4_8_stochastic_schedule_scalar_bound hreg hT.1.2.1
  exact le_trans (le_trans hbound hrhs) hscalar

theorem corollary_4_8_stochastic_asymptotic_bound
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (W0 : Mat m n) (Lstar σ Δ : ℝ)
    (hfinite : P.objective.HasFiniteInfimum)
    (hΔeq : sourceObjectiveInitialGap P.objective W0 hfinite = Δ)
    (hsmooth : SpectralSmooth P.objective Lstar)
    (hvariance : BoundedVariance P σ)
    (hreg : corollary_4_8_stochasticRegime m n Lstar σ Δ) :
    let realizes := fun T cfg =>
      corollary_4_8_stochasticRealization W0 T Lstar σ Δ cfg
    RealizedAsymptoticUpperNatOn
      (fun T => corollary_4_8_stochasticSemanticHorizonDomain
        P W0 T Lstar σ Δ)
      (fun T _hT cfg => realizes T cfg)
      (fun T hT cfg =>
        by
          classical
          exact
            if hr : realizes T cfg then
              stochasticAverageNuclearGradientRealized P cfg T (hT.2 cfg hr)
            else 0)
      (fun T hT =>
        corollary_4_8_stochasticRateRealized m n T Lstar σ Δ hT.1.2.1)
      (theoremScope
        "Corollary 4.8 corrected stochastic rate on admissible horizons" ["T"]) := by
  dsimp only
  unfold RealizedAsymptoticUpperNatOn
  refine ⟨10, 1, by norm_num, ?_, ?_⟩
  · simp [ConstantRespectsScope, theoremScope]
  · intro T hT _hTlarge
    rcases corollary_4_8_stochasticRealization_exists_of_admissible
        W0 T Lstar σ Δ hT.1 with ⟨cfg, hrun⟩
    refine ⟨⟨cfg, hrun⟩, ?_⟩
    intro cfg' hrun'
    simp only [dif_pos hrun']
    rcases corollary_4_8_stochastic_bound_at_realized_horizon
        P W0 hfinite hΔeq hsmooth hvariance hreg hT.1.1.1 with
      ⟨hT', hpoint⟩
    simpa using hpoint cfg' hrun'

set_option maxHeartbeats 800000 in
theorem corollary_4_8_stochastic_rate_crossing
    {m n : ℕ} {Lstar σ Δ : ℝ}
    (hreg : corollary_4_8_stochasticRegime m n Lstar σ Δ) :
    ∃ horizonBound : ℝ → ℝ,
      AsymptoticUpperReal epsilonDomain horizonBound
        (corollary_4_8_stochasticComplexityRate m n Lstar σ Δ)
        (theoremScope
          "Corollary 4.8 corrected stochastic epsilon complexity on admissible horizons"
          ["epsilon"]) ∧
      ∀ ε : ℝ, epsilonDomain ε →
        ∃ T : ℕ, ∃ hT : corollary_4_8_stochasticRateDomain
            m n T Lstar σ Δ,
          (T : ℝ) ≤ horizonBound ε ∧
            10 * corollary_4_8_stochasticRateRealized
              m n T Lstar σ Δ hT ≤ ε := by
  have hreg' := hreg
  unfold corollary_4_8_stochasticRegime at hreg'
  rcases hreg' with ⟨hrNat, hL, hσ, hΔ⟩
  let r : ℝ := matrixRankBound m n
  have hr : 0 < r := by dsimp [r]; exact_mod_cast hrNat
  let K : ℝ := r * Lstar * Δ * σ ^ 2
  let B₄ : ℝ := 30 ^ 4 * K
  let B₂ : ℝ := 30 ^ 2 * (Lstar * Δ)
  let B₃ : ℝ := 30 ^ 2 * (r ^ 2 * σ ^ 4 / (Lstar * Δ))
  have hK : 0 < K := by dsimp [K]; positivity
  have hB₄ : 0 ≤ B₄ := by dsimp [B₄]; positivity
  have hB₂ : 0 ≤ B₂ := by dsimp [B₂]; positivity
  have hB₃ : 0 ≤ B₃ := by dsimp [B₃]; positivity
  let X : ℝ → ℝ := fun ε =>
    1 + B₄ * ε⁻¹ ^ 4 + B₂ * ε⁻¹ ^ 2 + B₃ * ε⁻¹ ^ 2
  let selected : ℝ → ℕ := fun ε => Nat.ceil (X ε)
  let horizonBound : ℝ → ℝ := fun ε => (selected ε : ℝ)
  refine ⟨horizonBound, ?_, ?_⟩
  · unfold AsymptoticUpperReal
    let C : ℝ := (2 + B₄ + B₂ + B₃) / K
    refine ⟨C, 1, by dsimp [C]; positivity, by norm_num, ?_, ?_⟩
    · simp [ConstantRespectsScope, theoremScope, C]
      positivity
    · intro ε _hε hεpos hεsmall
      have hinv : 0 < ε⁻¹ := inv_pos.mpr hεpos
      have hinvOne : 1 ≤ ε⁻¹ := (one_le_inv₀ hεpos).2 hεsmall
      have hinvSqOne : 1 ≤ ε⁻¹ ^ 2 := by
        nlinarith [sq_nonneg (ε⁻¹ - 1)]
      have hinvSqLeFour : ε⁻¹ ^ 2 ≤ ε⁻¹ ^ 4 := by
        have hmul := mul_le_mul_of_nonneg_left hinvSqOne (sq_nonneg ε⁻¹)
        nlinarith
      have honeLeFour : 1 ≤ ε⁻¹ ^ 4 := le_trans hinvSqOne hinvSqLeFour
      have hXnonneg : 0 ≤ X ε := by dsimp [X]; positivity
      have hceil : (selected ε : ℝ) < X ε + 1 := by
        dsimp [selected]
        exact Nat.ceil_lt_add_one hXnonneg
      have hB₂absorb : B₂ * ε⁻¹ ^ 2 ≤ B₂ * ε⁻¹ ^ 4 :=
        mul_le_mul_of_nonneg_left hinvSqLeFour hB₂
      have hB₃absorb : B₃ * ε⁻¹ ^ 2 ≤ B₃ * ε⁻¹ ^ 4 :=
        mul_le_mul_of_nonneg_left hinvSqLeFour hB₃
      have htwoAbsorb : (2 : ℝ) ≤ 2 * ε⁻¹ ^ 4 := by nlinarith
      calc
        horizonBound ε ≤ X ε + 1 := by
          exact le_of_lt (by simpa [horizonBound] using hceil)
        _ ≤ (2 + B₄ + B₂ + B₃) * ε⁻¹ ^ 4 := by
          dsimp [X]
          nlinarith
        _ = C * corollary_4_8_stochasticComplexityRate
            m n Lstar σ Δ ε := by
          dsimp [C, corollary_4_8_stochasticComplexityRate, K, r]
          field_simp [ne_of_gt hK]
  · intro ε hε
    have hεpos : 0 < ε := hε
    have hinv : 0 < ε⁻¹ := inv_pos.mpr hεpos
    have hXpos : 0 < X ε := by dsimp [X]; positivity
    let T := selected ε
    have hTpos : horizonDomain T := by
      dsimp [T, selected, horizonDomain]
      exact Nat.ceil_pos.mpr hXpos
    have hXT : X ε ≤ (T : ℝ) := by
      dsimp [T, selected]
      exact Nat.le_ceil _
    have hrealizable := corollary_4_8_stochasticRegime_realizable hreg hTpos
    let hRate : corollary_4_8_stochasticRateDomain m n T Lstar σ Δ :=
      hrealizable.2.1
    refine ⟨T, hRate, le_rfl, ?_⟩
    have hTr : 0 < (T : ℝ) := by exact_mod_cast hTpos
    have hbudget₄ : B₄ * ε⁻¹ ^ 4 ≤ (T : ℝ) := by
      apply le_trans _ hXT
      dsimp [X]
      nlinarith only [hB₂, hB₃, sq_nonneg (ε⁻¹)]
    have hbudget₂ : B₂ * ε⁻¹ ^ 2 ≤ (T : ℝ) := by
      apply le_trans _ hXT
      dsimp [X]
      nlinarith only [hB₄, hB₃, sq_nonneg (ε⁻¹), sq_nonneg (ε⁻¹ ^ 2)]
    have hbudget₃ : B₃ * ε⁻¹ ^ 2 ≤ (T : ℝ) := by
      apply le_trans _ hXT
      dsimp [X]
      nlinarith only [hB₄, hB₂, sq_nonneg (ε⁻¹), sq_nonneg (ε⁻¹ ^ 2)]
    let e : ℝ := ε / 30
    have he : 0 < e := by dsimp [e]; positivity
    have hfirstRad : K / (T : ℝ) ≤ e ^ 4 := by
      apply (div_le_iff₀ hTr).2
      dsimp [B₄] at hbudget₄
      dsimp [e]
      field_simp [ne_of_gt hεpos] at hbudget₄ ⊢
      nlinarith
    have hsecondRad : (Lstar * Δ) / (T : ℝ) ≤ e ^ 2 := by
      apply (div_le_iff₀ hTr).2
      dsimp [B₂] at hbudget₂
      dsimp [e]
      field_simp [ne_of_gt hεpos] at hbudget₂ ⊢
      nlinarith
    have hthirdRad : (r ^ 2 * σ ^ 4 / (Lstar * Δ)) / (T : ℝ) ≤ e ^ 2 := by
      apply (div_le_iff₀ hTr).2
      dsimp [B₃] at hbudget₃
      dsimp [e]
      field_simp [ne_of_gt hεpos, ne_of_gt hL, ne_of_gt hΔ] at hbudget₃ ⊢
      nlinarith
    let R₁ : ℝ := Real.sqrt (Real.sqrt (K / (T : ℝ)))
    let R₂ : ℝ := Real.sqrt ((Lstar * Δ) / (T : ℝ))
    let R₃ : ℝ := r * σ ^ 2 / Real.sqrt (Lstar * Δ * (T : ℝ))
    have hR₁ : R₁ ≤ e := by
      dsimp [R₁]
      rw [Real.sqrt_le_iff]
      refine ⟨he.le, ?_⟩
      rw [Real.sqrt_le_iff]
      refine ⟨sq_nonneg e, ?_⟩
      nlinarith [hfirstRad]
    have hR₂ : R₂ ≤ e := by
      dsimp [R₂]
      rw [Real.sqrt_le_iff]
      exact ⟨he.le, hsecondRad⟩
    have hR₃sq : R₃ ^ 2 =
        (r ^ 2 * σ ^ 4 / (Lstar * Δ)) / (T : ℝ) := by
      have hdenRoot : 0 < Real.sqrt (Lstar * Δ * (T : ℝ)) := by positivity
      dsimp [R₃]
      field_simp [ne_of_gt hdenRoot, ne_of_gt hL, ne_of_gt hΔ, ne_of_gt hTr]
      rw [Real.sq_sqrt (by positivity : 0 ≤ Lstar * Δ * (T : ℝ))]
    have hR₃ : R₃ ≤ e := by
      apply (sq_le_sq₀ (by dsimp [R₃]; positivity) he.le).mp
      rw [hR₃sq]
      exact hthirdRad
    change 10 * (R₁ + R₂ + R₃) ≤ ε
    dsimp [e] at hR₁ hR₂ hR₃
    linarith

theorem corollary_4_8_stochastic_complexity
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (W0 : Mat m n) (Lstar σ Δ : ℝ)
    (hfinite : P.objective.HasFiniteInfimum)
    (hΔeq : sourceObjectiveInitialGap P.objective W0 hfinite = Δ)
    (hsmooth : SpectralSmooth P.objective Lstar)
    (hvariance : BoundedVariance P σ)
    (hreg : corollary_4_8_stochasticRegime m n Lstar σ Δ) :
    let realizes := fun T cfg =>
      corollary_4_8_stochasticRealization W0 T Lstar σ Δ cfg
    RealizedNuclearStationarityComplexityOn
      (fun T => corollary_4_8_stochasticSemanticHorizonDomain
        P W0 T Lstar σ Δ)
      (fun T _hT cfg => realizes T cfg)
      (fun T hT cfg =>
        by
          classical
          exact
            if hr : realizes T cfg then
              stochasticAverageNuclearGradientRealized P cfg T (hT.2 cfg hr)
            else 0)
      (corollary_4_8_stochasticComplexityRate m n Lstar σ Δ)
      (theoremScope
        "Corollary 4.8 corrected stochastic epsilon complexity on admissible horizons"
        ["epsilon"]) := by
  dsimp only
  unfold RealizedNuclearStationarityComplexityOn
  rcases corollary_4_8_stochastic_rate_crossing hreg with
    ⟨horizonBound, hAsymptotic, hselect⟩
  refine ⟨horizonBound, hAsymptotic, ?_⟩
  intro ε hε
  rcases hselect ε hε with ⟨T, hRate, hTbound, hrate⟩
  have hSemantic := corollary_4_8_stochasticRegime_semantic
    P W0 hreg hRate.1 hsmooth hvariance
  rcases corollary_4_8_stochasticRealization_exists_of_admissible
      W0 T Lstar σ Δ hSemantic.1 with ⟨cfg, hrun⟩
  refine ⟨T, hSemantic, cfg, hTbound, hrun, ?_⟩
  simp only [dif_pos hrun]
  rcases corollary_4_8_stochastic_bound_at_realized_horizon
      P W0 hfinite hΔeq hsmooth hvariance hreg hRate.1 with
    ⟨hSemantic', hpoint⟩
  exact le_trans (by simpa using hpoint cfg hrun) (by simpa using hrate)

set_option maxHeartbeats 800000 in
theorem corollary_4_8_deterministic_rate_bound_positive
    {m n T : ℕ} (P : Objective m n) (W0 : Mat m n) (Lstar Δ β : ℝ)
    (hfinite : P.HasFiniteInfimum)
    (hΔeq : sourceObjectiveInitialGap P W0 hfinite = Δ)
    (hsmooth : SpectralSmooth P Lstar)
    (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (hcoeff : 0 < Lstar * Δ)
    (hT : corollary_4_8_deterministicRateDomain m n T Lstar Δ) :
    deterministicMomentumAverageNuclearGradient P
        (corollary_4_8_deterministicConfig W0 T Lstar Δ β hβ) T ≤
      (3 / 2 + 2 * β / (1 - β)) *
        corollary_4_8_deterministicRateRealized m n T Lstar Δ hT := by
  let τ : ℝ := T
  let η : ℝ := corollary_4_8_deterministicEta m n T Lstar Δ
  let R : ℝ := corollary_4_8_deterministicRateRealized m n T Lstar Δ hT
  have hΔ0 : 0 ≤ Δ := by
    rw [← hΔeq]
    unfold sourceObjectiveInitialGap Objective.sourceFStar
    linarith [objective_value_ge_fStar_early P hfinite W0]
  have hΔ : 0 < Δ := by
    have hΔne : Δ ≠ 0 := by
      intro hzero
      rw [hzero] at hcoeff
      norm_num at hcoeff
    exact lt_of_le_of_ne hΔ0 (Ne.symm hΔne)
  have hL : 0 < Lstar := by
    by_contra hn
    have hLn : Lstar ≤ 0 := le_of_not_gt hn
    have : Lstar * Δ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hLn hΔ0
    linarith
  have hτ : 0 < τ := by dsimp [τ]; exact_mod_cast hT.1
  have hη : 0 < η := by
    dsimp [η, corollary_4_8_deterministicEta, sourceQuot]
    apply Real.sqrt_pos.2
    positivity
  have hsrc : theorem_4_7_sourceDomain T η := by
    refine ⟨⟨hT.1, ?_⟩, hη⟩
    unfold sourceQuotDomain
    exact mul_ne_zero (by exact_mod_cast ne_of_gt hT.1) (ne_of_gt hη)
  let cfg := corollary_4_8_deterministicConfig W0 T Lstar Δ β hβ
  rcases corollary_4_8_deterministicOracle_bound_at_horizon
      P cfg T Lstar η (by intro t ht; rfl) hsmooth hsrc with
    ⟨hbasic, hdom, hbound⟩
  have hfiniteOracle :
      (deterministicOracleProblem P).objective.HasFiniteInfimum := by
    simpa only [deterministicOracleProblem_objective] using hfinite
  have hdrop :
      stochasticExpectedObjectiveDrop (deterministicOracleProblem P)
          (deterministicOracleConfig cfg) T ≤ Δ := by
    calc
      _ ≤ sourceObjectiveInitialGap
          (deterministicOracleProblem P).objective
          (deterministicOracleConfig cfg).W0 hfiniteOracle :=
        stochastic_expected_objective_drop_le_source_initial_gap
          (deterministicOracleProblem P) (deterministicOracleConfig cfg) T
          hfiniteOracle hbasic.2
      _ = Δ := by
        calc
          _ = sourceObjectiveInitialGap P W0 hfinite := by
            simp only [cfg, corollary_4_8_deterministicConfig,
              deterministicMomentumConstantConfig, deterministicOracleConfig,
              deterministicOracleProblem_objective]
          _ = Δ := hΔeq
  have hden : 0 < (T : ℝ) * η := mul_pos (by exact_mod_cast hT.1) hη
  have hdropQuot := div_le_div_of_nonneg_right hdrop hden.le
  have hrhs :
      theorem_4_7_rhs (deterministicOracleProblem P)
          (deterministicOracleConfig cfg) T Lstar 0 η hbasic.2 hdom ≤
        Δ / ((T : ℝ) * η) + Lstar * η / 2 +
          2 * η * β * Lstar / (1 - β) := by
    rcases hdom with
      ⟨hdomT, hdropDom, hsNoise, hsBatchNoise, hqBatchNoise, hsRank,
        hsBatch, hqTail, hqMomentum⟩
    dsimp [theorem_4_7_rhs, realizedSourceQuot, realizedSourceSqrt,
      sourceQuot, sourceSqrt, deterministicOracleConfig, cfg,
      corollary_4_8_deterministicConfig, deterministicMomentumConstantConfig]
    rw [stochasticExpectedObjectiveDropRealized_eq_integral]
    dsimp [deterministicOracleConfig, cfg, corollary_4_8_deterministicConfig,
      deterministicMomentumConstantConfig] at hdropQuot
    ring_nf at hdropQuot ⊢
    linarith only [hdropQuot]
  have hηsq : η ^ 2 = Δ / (τ * Lstar) := by
    dsimp [η, corollary_4_8_deterministicEta, sourceQuot, τ]
    rw [Real.sq_sqrt]
    positivity
  have hscale : Lstar * η = Δ / (τ * η) := by
    have hpoly : η ^ 2 * (τ * Lstar) = Δ :=
      (eq_div_iff (by positivity : τ * Lstar ≠ 0)).mp hηsq
    apply (eq_div_iff (by positivity : τ * η ≠ 0)).2
    ring_nf at hpoly ⊢
    nlinarith
  have hRsq : R ^ 2 = Lstar * Δ / τ := by
    dsimp [R, corollary_4_8_deterministicRateRealized,
      realizedSourceSqrtQuot, realizedSourceQuot, realizedSourceSqrt,
      sourceSqrt, sourceQuot, τ]
    rw [Real.sq_sqrt]
    positivity
  have hscaleSq : (Lstar * η) ^ 2 = Lstar * Δ / τ := by
    rw [mul_pow, hηsq]
    field_simp [ne_of_gt hτ, ne_of_gt hL]
  have hscaleR : Lstar * η = R := by
    apply (mul_self_inj_of_nonneg (by positivity) (by
      dsimp [R, corollary_4_8_deterministicRateRealized,
        realizedSourceSqrtQuot, realizedSourceQuot, realizedSourceSqrt,
        sourceSqrt, sourceQuot]
      positivity)).mp
    simpa [pow_two] using hscaleSq.trans hRsq.symm
  have hfirstR : Δ / (τ * η) = R := hscale.symm.trans hscaleR
  calc
    deterministicMomentumAverageNuclearGradient P cfg T ≤
        Δ / ((T : ℝ) * η) + Lstar * η / 2 +
          2 * η * β * Lstar / (1 - β) := le_trans hbound hrhs
    _ = (3 / 2 + 2 * β / (1 - β)) * R := by
      rw [show (T : ℝ) = τ by rfl, hfirstR, ← hscaleR]
      field_simp [ne_of_gt (sub_pos.mpr hβ.2)]
      ring

theorem corollary_4_8_deterministic_asymptotic_bound_positive
    {m n : ℕ} (P : Objective m n) (W0 : Mat m n) (Lstar Δ β : ℝ)
    (hfinite : P.HasFiniteInfimum)
    (hΔeq : sourceObjectiveInitialGap P W0 hfinite = Δ)
    (hsmooth : SpectralSmooth P Lstar)
    (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (hcoeff : 0 < Lstar * Δ) :
    DomainAsymptoticUpperNatOn
      (fun T => corollary_4_8_deterministicRateDomain m n T Lstar Δ)
      (fun T _hT => deterministicMomentumAverageNuclearGradient P
        (corollary_4_8_deterministicConfig W0 T Lstar Δ β hβ) T)
      (fun T hT => corollary_4_8_deterministicRateRealized m n T Lstar Δ hT)
      (theoremScope "Corollary 4.8 deterministic rate" ["T"]) := by
  let C : ℝ := 3 / 2 + 2 * β / (1 - β)
  have hC : 0 < C := by
    dsimp [C]
    have hden : 0 < 1 - β := sub_pos.mpr hβ.2
    have hfrac : 0 ≤ 2 * β / (1 - β) :=
      div_nonneg (mul_nonneg (by norm_num) hβ.1) hden.le
    linarith
  unfold DomainAsymptoticUpperNatOn
  refine ⟨C, 1, hC, ?_, ?_⟩
  · simp [ConstantRespectsScope, theoremScope, hC]
  · intro T hT _hlarge
    exact corollary_4_8_deterministic_rate_bound_positive
      P W0 Lstar Δ β hfinite hΔeq hsmooth hβ hcoeff hT

set_option maxHeartbeats 800000 in
theorem corollary_4_8_deterministic_complexity_witness
    {m n : ℕ} (P : Objective m n) (W0 : Mat m n) (Lstar Δ β : ℝ)
    (hfinite : P.HasFiniteInfimum)
    (hΔeq : sourceObjectiveInitialGap P W0 hfinite = Δ)
    (hsmooth : SpectralSmooth P Lstar)
    (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (hcoeff : 0 < Lstar * Δ) :
    NuclearStationarityComplexityOn
      (fun T => corollary_4_8_deterministicRateDomain m n T Lstar Δ)
      (fun T _hT => deterministicMomentumAverageNuclearGradient P
        (corollary_4_8_deterministicConfig W0 T Lstar Δ β hβ) T)
      (corollary_4_8_deterministicComplexityRate m n Lstar Δ)
      (theoremScope "Corollary 4.8 deterministic epsilon complexity" ["epsilon"]) := by
  let A : ℝ := Lstar * Δ
  let k : ℝ := 3 / 2 + 2 * β / (1 - β)
  have hA : 0 < A := by simpa [A] using hcoeff
  have hk : 0 < k := by
    dsimp [k]
    have hden : 0 < 1 - β := sub_pos.mpr hβ.2
    have hfrac : 0 ≤ 2 * β / (1 - β) :=
      div_nonneg (mul_nonneg (by norm_num) hβ.1) hden.le
    linarith
  let X : ℝ → ℝ := fun ε => k ^ 2 * A * ε⁻¹ ^ 2
  let selected : ℝ → ℕ := fun ε => Nat.ceil (X ε)
  let horizonBound : ℝ → ℝ := fun ε => (selected ε : ℝ)
  unfold NuclearStationarityComplexityOn
  refine ⟨horizonBound, ?_, ?_⟩
  · unfold AsymptoticUpperReal
    let C : ℝ := k ^ 2 + A⁻¹
    have hC : 0 < C := by dsimp [C]; positivity
    refine ⟨C, 1, hC, by norm_num, ?_, ?_⟩
    · simp [ConstantRespectsScope, theoremScope, hC]
    · intro ε hε hεpos hεone
      have hXnonneg : 0 ≤ X ε := by dsimp [X]; positivity
      have hceil : (selected ε : ℝ) < X ε + 1 := by
        dsimp [selected]
        exact Nat.ceil_lt_add_one hXnonneg
      have hinvSq : 1 ≤ ε⁻¹ ^ 2 := by
        have hinv : 1 ≤ ε⁻¹ := (one_le_inv₀ hεpos).2 hεone
        nlinarith [sq_nonneg (ε⁻¹ - 1)]
      have hone : 1 ≤ A⁻¹ * (A * ε⁻¹ ^ 2) := by
        calc
          1 ≤ ε⁻¹ ^ 2 := hinvSq
          _ = A⁻¹ * (A * ε⁻¹ ^ 2) := by
            rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hA), one_mul]
      calc
        horizonBound ε ≤ X ε + 1 := by
          exact le_of_lt (by simpa [horizonBound] using hceil)
        _ ≤ C * corollary_4_8_deterministicComplexityRate
            m n Lstar Δ ε := by
          dsimp [X, C, corollary_4_8_deterministicComplexityRate, A]
          nlinarith
  · intro ε hε
    have hεpos : 0 < ε := hε
    have hXpos : 0 < X ε := by dsimp [X]; positivity
    let T : ℕ := selected ε
    have hTpos : horizonDomain T := by
      dsimp [T, selected, horizonDomain]
      exact Nat.ceil_pos.mpr hXpos
    have hXT : X ε ≤ (T : ℝ) := by
      dsimp [T, selected]
      exact Nat.le_ceil _
    have hTr : 0 < (T : ℝ) := by exact_mod_cast hTpos
    have hT : corollary_4_8_deterministicRateDomain m n T Lstar Δ := by
      refine ⟨hTpos, ?_⟩
      unfold sourceSqrtQuotDomain sourceQuotDomain sourceSqrtDomain sourceQuot
      constructor
      · exact ne_of_gt hTr
      · positivity
    refine ⟨T, hT, le_rfl, ?_⟩
    apply le_trans (corollary_4_8_deterministic_rate_bound_positive
      P W0 Lstar Δ β hfinite hΔeq hsmooth hβ hcoeff hT)
    change k * Real.sqrt (A / (T : ℝ)) ≤ ε
    have hrad : A / (T : ℝ) ≤ (ε / k) ^ 2 := by
      apply (div_le_iff₀ hTr).2
      dsimp [X] at hXT
      field_simp [ne_of_gt hεpos, ne_of_gt hk] at hXT ⊢
      nlinarith
    have hsqrt : Real.sqrt (A / (T : ℝ)) ≤ ε / k := by
      rw [Real.sqrt_le_iff]
      exact ⟨(div_nonneg hεpos.le hk.le), hrad⟩
    simpa [mul_comm] using (le_div_iff₀ hk).mp hsqrt

theorem corollary_4_8_deterministic_asymptotic_bound_zero
    {m n : ℕ} (P : Objective m n) (W0 : Mat m n) (Lstar Δ β : ℝ)
    (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (hzero : corollary_4_8_deterministicZeroMotion P W0 Lstar Δ β hβ) :
    DomainAsymptoticUpperNatOn
      (fun T => corollary_4_8_deterministicRateDomain m n T Lstar Δ)
      (fun T _hT => deterministicMomentumAverageNuclearGradient P
        (corollary_4_8_deterministicConfig W0 T Lstar Δ β hβ) T)
      (fun T hT => corollary_4_8_deterministicRateRealized m n T Lstar Δ hT)
      (theoremScope "Corollary 4.8 deterministic rate" ["T"]) := by
  unfold DomainAsymptoticUpperNatOn
  refine ⟨1, 1, by norm_num, ?_, ?_⟩
  · simp [ConstantRespectsScope, theoremScope]
  · intro T hT _hlarge
    have havg : deterministicMomentumAverageNuclearGradient P
        (corollary_4_8_deterministicConfig W0 T Lstar Δ β hβ) T = 0 := by
      unfold deterministicMomentumAverageNuclearGradient
      rw [Finset.sum_eq_zero]
      · ring
      · intro t ht
        rw [hzero.2 T t |>.1, hzero.1]
        simp [nuclearNorm]
    dsimp only
    rw [havg]
    have hrate : 0 ≤
        corollary_4_8_deterministicRateRealized m n T Lstar Δ hT := by
      unfold corollary_4_8_deterministicRateRealized realizedSourceSqrtQuot
        realizedSourceSqrt sourceSqrt
      positivity
    simpa using hrate

theorem corollary_4_8 {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (W0 : Mat m n) (Lstar σ : ℝ)
    (_hfinite : P.objective.HasFiniteInfimum)
    (_hsmooth : SpectralSmooth P.objective Lstar)
    (_hvariance : BoundedVariance P σ) :
    corollary_4_8_statement P W0 Lstar σ _hfinite := by
  dsimp only [corollary_4_8_statement]
  refine ⟨?_, ?_, ?_⟩
  · unfold corollary_4_8_stochastic_downstream_phase2_boundary
      corollary_4_8_stochasticSemanticSourceBoundary SourceNatDomainBoundary
    dsimp only
    constructor
    · intro T hT
      exact hT.1.1.1
    · intro T hsource
      by_cases hsemantic : corollary_4_8_stochasticSemanticHorizonDomain
          P W0 T Lstar σ (sourceObjectiveInitialGap P.objective W0 _hfinite)
      · exact Or.inl hsemantic
      · exact Or.inr ⟨hsource, hsemantic⟩
  · intro hreg
    unfold corollary_4_8_stochastic_corrected_admissible_domain_statement
    dsimp only
    constructor
    · exact corollary_4_8_stochastic_asymptotic_bound
        P W0 Lstar σ (sourceObjectiveInitialGap P.objective W0 _hfinite)
        _hfinite rfl _hsmooth _hvariance hreg
    · constructor
      · exact corollary_4_8_stochastic_complexity
          P W0 Lstar σ (sourceObjectiveInitialGap P.objective W0 _hfinite)
          _hfinite rfl _hsmooth _hvariance hreg
      · intro T hT cfg hcfg ε havg
        exact stochasticGeneratedOutputGuarantee_of_average_le
          P cfg T hT.1.1.1 (hT.2 cfg hcfg) ε havg
  · intro _hσ β hβ _hβO1
    let Δ : ℝ := sourceObjectiveInitialGap P.objective W0 _hfinite
    let A : ℝ := Lstar * Δ
    have hΔ0 : 0 ≤ Δ := by
      dsimp [Δ, sourceObjectiveInitialGap, Objective.sourceFStar]
      linarith [objective_value_ge_fStar_early P.objective _hfinite W0]
    have hL0 : 0 ≤ Lstar := _hsmooth.nonneg
    have hA0 : 0 ≤ A := by dsimp [A]; positivity
    by_cases hAzero : A = 0
    · have hzero : corollary_4_8_deterministicZeroMotion
          P.objective W0 Lstar Δ β hβ := by
        apply corollary_4_8_deterministicZeroMotion_of_degenerate_scale
          P.objective W0 Lstar β _hfinite _hsmooth hβ
        simpa [A, Δ] using hAzero
      refine ⟨corollary_4_8_deterministic_asymptotic_bound_zero
        P.objective W0 Lstar Δ β hβ hzero, ?_, ?_⟩
      · intro hApos
        exact (hApos.ne' hAzero).elim
      · intro _hzero
        refine ⟨hzero, ?_⟩
        unfold IsNuclearStationary
        rw [hzero.2 1 0 |>.1, hzero.1]
        simp [nuclearNorm]
    · have hApos : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hAzero)
      refine ⟨corollary_4_8_deterministic_asymptotic_bound_positive
        P.objective W0 Lstar Δ β _hfinite rfl _hsmooth hβ
          (by simpa [A] using hApos), ?_, ?_⟩
      · intro _hpositive
        constructor
        · exact corollary_4_8_deterministic_complexity_witness
            P.objective W0 Lstar Δ β _hfinite rfl _hsmooth hβ
              (by simpa [A] using hApos)
        · simpa [deterministicMomentumAverageNuclearGradient] using
            (generatedNuclearStationarityTransfer_of_finite_average
              P.objective
              (fun T => corollary_4_8_deterministicRateDomain m n T Lstar Δ)
              (fun T hT => hT.1)
              (fun T _hT t =>
                (deterministicMomentumMuonState P.objective
                  (corollary_4_8_deterministicConfig W0 T Lstar Δ β hβ) t).W))
      · intro hzero
        exact (hAzero (by simpa [A] using hzero)).elim

/- Appendix C.3, Eq. (19) plus Eq. (20), exposed as one fixed-horizon
   source-formula supplier.  The affine recurrence is an implementation edge,
   not a public run-family contract. -/
theorem theorem_4_9_source_formula_bound_at_horizon
    {m n : ℕ} (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (T : ℕ) (Wstar : Mat m n) (Lstar Dop η : ℝ)
    (hfinite : P.HasFiniteInfimum)
    (hstar : StarConvex P Wstar)
    (hsmooth : SpectralSmooth P Lstar)
    (hbounded : BoundedOperatorDistance P cfg T Wstar Dop)
    (hdom : theorem_4_9_rhsDomain P cfg T Lstar Dop η)
    (hη : ∀ t ∈ Finset.range T, cfg.eta t = η) :
    sourceObjectiveGapAt P cfg T hfinite ≤
      theorem_4_9_sourceRhs P cfg T Lstar Dop η := by
  have hDop : 0 < Dop := by
    rcases hdom with ⟨hDopNe, hηnonneg, hηDop⟩
    exact lt_of_le_of_ne (le_trans hηnonneg hηDop) (Ne.symm hDopNe)
  by_cases hηzero : η = 0
  · have hW : (deterministicMuonState P cfg T).W = cfg.W0 := by
      have hWprefix : ∀ k : ℕ, k ≤ T →
          (deterministicMuonState P cfg k).W = cfg.W0 := by
        intro k hk
        induction k with
        | zero => rfl
        | succ k ih =>
          rw [deterministicMuon_W_succ_eq_source_update]
          have hstep : cfg.eta k = 0 := by
            rw [hη k (Finset.mem_range.mpr (by omega)), hηzero]
          rw [hstep, zero_smul, sub_zero]
          exact ih (by omega)
      exact hWprefix T le_rfl
    rw [hηzero]
    simp [sourceObjectiveGapAt, theorem_4_9_sourceRhs, hW,
      Objective.sourceFStar, hDop.ne']
  · have hηpos : 0 < η := lt_of_le_of_ne hdom.2.1 (Ne.symm hηzero)
    let q : ℝ := 1 - η / Dop
    let x : ℕ → ℝ := fun t =>
      P.f ((deterministicMuonState P cfg t).W) - P.fStar
    let a : ℝ := Lstar * η ^ 2 / 2
    have hq : 0 ≤ q := by
      dsimp [q]
      exact sub_nonneg.mpr ((div_le_one hDop).2 hdom.2.2)
    have ha : 0 ≤ a := by
      dsimp [a]
      exact div_nonneg (mul_nonneg hsmooth.nonneg (sq_nonneg η)) (by norm_num)
    have hrec : ∀ t ∈ Finset.range T, x (t + 1) ≤ q * x t + a := by
      intro t ht
      let Wt := (deterministicMuonState P cfg t).W
      let Wnext := (deterministicMuonState P cfg (t + 1)).W
      let Gt := P.grad Wt
      let Dt := orthogonalizedDirection Gt
      have hG : (deterministicMuonState P cfg t).G = Gt := by
        simpa [Gt, Wt, deterministicGradient] using
          deterministicMuon_G_eq_gradient P cfg t
      have hupdate : Wnext = Wt - η • Dt := by
        simpa [Wnext, Wt, Dt, hG, hη t ht] using
          deterministicMuon_W_succ_eq_source_update P cfg t
      have hsmoothStep := spectralSmooth_quadratic_upper_bound P hsmooth Wt Wnext
      have hdiff : Wnext - Wt = (-η) • Dt := by
        rw [hupdate]
        ext i j
        simp
      rw [hdiff] at hsmoothStep
      have hpair : frobeniusInner Gt ((-η) • Dt) =
          -η * nuclearNorm Gt := by
        rw [show frobeniusInner Gt ((-η) • Dt) =
            -η * frobeniusInner Gt Dt by
          unfold frobeniusInner
          simp only [Matrix.smul_apply, smul_eq_mul]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _hi
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _hj
          ring]
        rw [orthogonalizedDirection_frobeniusInner_eq_nuclearNorm]
      have hnorm : spectralNorm ((-η) • Dt) ^ 2 =
          η ^ 2 * spectralNorm Dt ^ 2 := by
        simp [spectralNorm, norm_smul, Real.norm_eq_abs, abs_neg, mul_pow, sq_abs]
      rw [hpair, hnorm] at hsmoothStep
      have hDnorm : spectralNorm Dt ≤ 1 :=
        orthogonalizedDirection_spectralNorm_le_one Gt
      have hDsq : spectralNorm Dt ^ 2 ≤ 1 := by
        nlinarith [spectralNorm_nonneg Dt]
      have hquad : (Lstar / 2) * (η ^ 2 * spectralNorm Dt ^ 2) ≤ a := by
        have hcoef : 0 ≤ (Lstar / 2) * η ^ 2 :=
          mul_nonneg (div_nonneg hsmooth.nonneg (by norm_num)) (sq_nonneg η)
        have hscale := mul_le_mul_of_nonneg_left hDsq hcoef
        dsimp [a]
        nlinarith
      have ht' : t ∈ Finset.range (T + 1) :=
        Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp ht) (by omega))
      have hgap := theorem_4_16_star_gradient_lower_bound_at
        P cfg T t Wstar Dop hstar hbounded ht'
      have hgapDiv : x t / Dop ≤ nuclearNorm Gt := by
        apply (div_le_iff₀ hDop).2
        simpa [x, Gt, Wt, mul_comm] using hgap
      have hscaled := mul_le_mul_of_nonneg_left hgapDiv hηpos.le
      have hscaled' : η / Dop * x t ≤ η * nuclearNorm Gt := by
        convert hscaled using 1 <;> ring
      dsimp [x, q, a, Wnext, Wt, Gt] at hsmoothStep hquad hscaled' ⊢
      linarith
    have hunroll := affine_recurrence_unroll q x (fun _ => a) T hq hrec
    let S : ℝ := ∑ t ∈ Finset.range T, q ^ (T - 1 - t)
    have hsum : (∑ t ∈ Finset.range T, q ^ (T - 1 - t) * a) = a * S := by
      dsimp [S]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _ht
      ring
    have hSreflect : S = ∑ t ∈ Finset.range T, q ^ t := by
      dsimp [S]
      exact Finset.sum_range_reflect (fun t => q ^ t) T
    have hq_lt : q < 1 := by
      dsimp [q]
      exact sub_lt_self _ (div_pos hηpos hDop)
    have hone_sub_q : 0 < 1 - q := sub_pos.mpr hq_lt
    have hgeom : (∑ t ∈ Finset.range T, q ^ t) * (1 - q) = 1 - q ^ T :=
      geom_sum_mul_neg q T
    have hS_le_inv : S ≤ 1 / (1 - q) := by
      rw [hSreflect]
      apply (le_div_iff₀ hone_sub_q).2
      rw [hgeom]
      nlinarith [pow_nonneg hq T]
    have hSinv : 1 / (1 - q) = Dop / η := by
      dsimp [q]
      field_simp [hDop.ne', hηzero]
      ring
    have hS_le : S ≤ Dop / η := by simpa [hSinv] using hS_le_inv
    have haS : a * S ≤ Lstar * Dop * η / 2 := by
      have hscaled := mul_le_mul_of_nonneg_left hS_le ha
      dsimp [a] at hscaled ⊢
      field_simp [hηzero] at hscaled ⊢
      nlinarith
    rw [hsum] at hunroll
    have hxzero : x 0 = P.f cfg.W0 - P.fStar := by
      simp [x, deterministicMuonState, deterministicMuonBaseState]
    rw [hxzero] at hunroll
    dsimp [sourceObjectiveGapAt, Objective.sourceFStar,
      theorem_4_9_sourceRhs, q, x]
    dsimp [x, q] at hunroll
    exact le_trans hunroll (by linarith [haS])

/- Formula-only C.3 logarithmic selector. -/
theorem theorem_4_9_sourceRhs_le_epsilon_at_log_horizon
    {m n : ℕ} (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (Lstar Dop : ℝ) (hfinite : P.HasFiniteInfimum)
    (hsmooth : SpectralSmooth P Lstar) :
    let Δ := sourceObjectiveInitialGap P cfg.W0 hfinite
    ∃ horizonBound :
        ∀ ε : ℝ, theorem_4_9_precisionDomain m n Lstar Dop Δ ε → ℝ,
      AsymptoticUpperRealOn (theorem_4_9_precisionDomain m n Lstar Dop Δ)
        horizonBound
        (fun ε hε => theorem_4_9_complexityRateRealized m n Lstar Dop Δ ε hε)
        (theoremScope "Theorem 4.9 selected logarithmic horizon" ["epsilon"]) ∧
      ∀ ε : ℝ, ∀ hε : theorem_4_9_precisionDomain m n Lstar Dop Δ ε,
        let N := theorem_4_9_logHorizon m n Lstar Dop Δ ε hε
        (N : ℝ) ≤ horizonBound ε hε ∧
          theorem_4_9_sourceRhs P
            (theorem_4_9_precisionConfig cfg Lstar Dop Δ ε hε) N Lstar Dop
            (theorem_4_9_etaRateRealized m n Lstar Dop ε hε.2.1) ≤ ε := by
  let Δ := sourceObjectiveInitialGap P cfg.W0 hfinite
  let horizonBound :
      ∀ ε : ℝ, theorem_4_9_precisionDomain m n Lstar Dop Δ ε → ℝ :=
    fun ε hε => (theorem_4_9_logHorizon m n Lstar Dop Δ ε hε : ℝ)
  refine ⟨horizonBound, ?_, ?_⟩
  · unfold AsymptoticUpperRealOn
    by_cases hΔ : 0 < Δ
    · let C : ℝ := 2 + 1 / Real.log 2
      refine ⟨C, Δ / 2, ?_, div_pos hΔ (by norm_num), ?_, ?_⟩
      · dsimp [C]
        have : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
        positivity
      · simp [ConstantRespectsScope, theoremScope, C]
        have : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
        positivity
      · intro ε hε hεpos hεsmall
        have hK : Lstar * Dop ≠ 0 := hε.2.1
        have hηbounds := hε.2.2.2.2
        dsimp at hηbounds
        let η : ℝ := ε / (Lstar * Dop)
        let A : ℝ := Lstar * Dop ^ 2 / ε
        have hηeq : theorem_4_9_etaRateRealized m n Lstar Dop ε hε.2.1 = η := rfl
        have hηne : η ≠ 0 := by
          dsimp [η]
          exact div_ne_zero (ne_of_gt hεpos) hK
        have hηpos : 0 < η :=
          lt_of_le_of_ne (by simpa [hηeq] using hηbounds.1) (Ne.symm hηne)
        have hDop : 0 < Dop :=
          lt_of_lt_of_le hηpos (by simpa [hηeq] using hηbounds.2)
        have hAeq : A = Dop / η := by
          dsimp [A, η]
          field_simp [hK, ne_of_gt hεpos, ne_of_gt hDop]
        have hA : 1 ≤ A := by
          rw [hAeq]
          exact (one_le_div hηpos).2 (by simpa [hηeq] using hηbounds.2)
        have hratio : 2 ≤ Δ / ε := by
          apply (le_div_iff₀ hεpos).2
          linarith
        have hratioPos : 0 < Δ / ε := lt_of_lt_of_le (by norm_num) hratio
        have hlogRatioPos : 0 < Real.log (Δ / ε) :=
          Real.log_pos (lt_of_lt_of_le (by norm_num) hratio)
        have hlogTwoPos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
        have hlogTwoLe : Real.log (2 : ℝ) ≤ Real.log (Δ / ε) :=
          Real.strictMonoOn_log.monotoneOn (by norm_num) hratioPos hratio
        let rate : ℝ := theorem_4_9_complexityRateRealized m n Lstar Dop Δ ε hε
        have hrateEq : rate = A * Real.log (Δ / ε) := by
          dsimp [rate, A, theorem_4_9_complexityRateRealized,
            realizedSourceInv, sourceInv, realizedSourceLogQuot,
            sourceLogQuot, sourceQuot]
          field_simp [ne_of_gt hεpos]
        have hratePos : 0 < rate := by rw [hrateEq]; positivity
        let X : ℝ := A * Real.log (2 * Δ / ε)
        have hlogSplit : Real.log (2 * Δ / ε) =
            Real.log 2 + Real.log (Δ / ε) := by
          rw [show 2 * Δ / ε = 2 * (Δ / ε) by ring]
          exact Real.log_mul (by norm_num) (ne_of_gt hratioPos)
        have hXnonneg : 0 ≤ X := by
          dsimp [X]
          rw [hlogSplit]
          positivity
        have hXrate : X ≤ 2 * rate := by
          dsimp [X]
          rw [hlogSplit, hrateEq]
          nlinarith [mul_le_mul_of_nonneg_left hlogTwoLe (le_trans zero_le_one hA)]
        let N := theorem_4_9_logHorizon m n Lstar Dop Δ ε hε
        have hNupper : (N : ℝ) < X + 1 := by
          dsimp [N, theorem_4_9_logHorizon]
          simpa [X] using Nat.ceil_lt_add_one hXnonneg
        have honeRate : 1 ≤ (1 / Real.log 2) * rate := by
          have hlogRate : Real.log 2 ≤ rate := by
            rw [hrateEq]
            calc
              Real.log 2 ≤ A * Real.log 2 := by
                simpa [one_mul] using mul_le_mul_of_nonneg_right hA hlogTwoPos.le
              _ ≤ A * Real.log (Δ / ε) :=
                mul_le_mul_of_nonneg_left hlogTwoLe (le_trans zero_le_one hA)
          calc
            1 = (1 / Real.log 2) * Real.log 2 := by
              field_simp [ne_of_gt hlogTwoPos]
            _ ≤ (1 / Real.log 2) * rate :=
              mul_le_mul_of_nonneg_left hlogRate (by positivity)
        dsimp [horizonBound, N]
        dsimp [C]
        rw [show theorem_4_9_complexityRateRealized m n Lstar Dop Δ ε hε =
          rate by rfl]
        linarith
    · refine ⟨1, 1, by norm_num, by norm_num, ?_, ?_⟩
      · simp [ConstantRespectsScope, theoremScope]
      · intro ε hε hεpos _hεsmall
        have hratio : 0 < Δ / ε := by
          simpa [sourceLogQuotDomain, sourceQuot] using hε.2.2.2.1.2
        have hΔpos : 0 < Δ := by
          rcases div_pos_iff.mp hratio with h | h
          · exact h.1
          · exact False.elim (not_lt_of_ge hεpos.le h.2)
        exact False.elim (hΔ hΔpos)
  · intro ε hε
    let N := theorem_4_9_logHorizon m n Lstar Dop Δ ε hε
    refine ⟨le_rfl, ?_⟩
    have hεpos : 0 < ε := hε.1
    have hK : Lstar * Dop ≠ 0 := hε.2.1
    have hηbounds := hε.2.2.2.2
    dsimp at hηbounds
    let η : ℝ := ε / (Lstar * Dop)
    let A : ℝ := Lstar * Dop ^ 2 / ε
    have hηeq : theorem_4_9_etaRateRealized m n Lstar Dop ε hε.2.1 = η := rfl
    have hηne : η ≠ 0 := by
      dsimp [η]
      exact div_ne_zero (ne_of_gt hεpos) hK
    have hηpos : 0 < η :=
      lt_of_le_of_ne (by simpa [hηeq] using hηbounds.1) (Ne.symm hηne)
    have hDop : 0 < Dop :=
      lt_of_lt_of_le hηpos (by simpa [hηeq] using hηbounds.2)
    have hAeq : A = Dop / η := by
      dsimp [A, η]
      field_simp [hK, ne_of_gt hεpos, ne_of_gt hDop]
    have hApos : 0 < A := by rw [hAeq]; positivity
    have hA : 1 ≤ A := by
      rw [hAeq]
      exact (one_le_div hηpos).2 (by simpa [hηeq] using hηbounds.2)
    have hratioPos : 0 < Δ / ε := by
      simpa [sourceLogQuotDomain, sourceQuot] using hε.2.2.2.1.2
    have hΔpos : 0 < Δ := by
      rcases div_pos_iff.mp hratioPos with h | h
      · exact h.1
      · exact False.elim (not_lt_of_ge hεpos.le h.2)
    have hadd : Lstar * Dop * η / 2 = ε / 2 := by
      calc
        Lstar * Dop * η / 2 =
            (ε / (Lstar * Dop) * (Lstar * Dop)) / 2 := by
              dsimp [η]
              ring
        _ = ε / 2 := by rw [div_mul_cancel₀ ε hK]
    have hqnonneg : 0 ≤ 1 - η / Dop :=
      sub_nonneg.mpr ((div_le_one hDop).2 (by simpa [hηeq] using hηbounds.2))
    have hqle : 1 - η / Dop ≤ 1 :=
      sub_le_self _ (div_nonneg hηpos.le hDop.le)
    have hcontract : (1 - η / Dop) ^ N * Δ ≤ ε / 2 := by
      by_cases hsmall : Δ ≤ ε / 2
      · have hpow : (1 - η / Dop) ^ N ≤ 1 := pow_le_one₀ hqnonneg hqle
        have hscaled := mul_le_mul_of_nonneg_right hpow hΔpos.le
        nlinarith
      · have htwoRatio : 1 < 2 * Δ / ε := by
          apply (lt_div_iff₀ hεpos).2
          linarith
        have hlogPos : 0 < Real.log (2 * Δ / ε) := Real.log_pos htwoRatio
        let X : ℝ := A * Real.log (2 * Δ / ε)
        have hXpos : 0 < X := mul_pos hApos hlogPos
        have hXN : X ≤ (N : ℝ) := by
          dsimp [N, theorem_4_9_logHorizon]
          simpa [X] using Nat.le_ceil X
        have hNpos : 0 < (N : ℝ) := lt_of_lt_of_le hXpos hXN
        have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
        let t : ℝ := (N : ℝ) / A
        have htN : t ≤ (N : ℝ) := by
          dsimp [t]
          apply (div_le_iff₀ hApos).2
          have hscaled := mul_le_mul_of_nonneg_left hA hNpos.le
          nlinarith
        have hpow : (1 - t / (N : ℝ)) ^ N ≤ Real.exp (-t) :=
          Real.one_sub_div_pow_le_exp_neg htN
        have hq : 1 - t / (N : ℝ) = 1 - η / Dop := by
          dsimp [t]
          rw [hAeq]
          field_simp [hNne, hηne, ne_of_gt hDop]
        have hlogLe : Real.log (2 * Δ / ε) ≤ t := by
          dsimp [t, X] at hXN ⊢
          exact (le_div_iff₀ hApos).2 (by simpa [mul_comm] using hXN)
        have hexpLe : Real.exp (-t) ≤
            Real.exp (-Real.log (2 * Δ / ε)) :=
          Real.exp_le_exp.mpr (by linarith)
        have hexpEq : Real.exp (-Real.log (2 * Δ / ε)) = ε / (2 * Δ) := by
          rw [Real.exp_neg, Real.exp_log (lt_trans zero_lt_one htwoRatio)]
          field_simp [ne_of_gt hεpos, ne_of_gt hΔpos]
        rw [hq] at hpow
        have hscaled := mul_le_mul_of_nonneg_right
          (le_trans hpow hexpLe) hΔpos.le
        rw [hexpEq] at hscaled
        have heq : ε / (2 * Δ) * Δ = ε / 2 := by
          field_simp [ne_of_gt hΔpos]
        simpa [heq] using hscaled
    dsimp [theorem_4_9_sourceRhs]
    rw [show P.f
        (theorem_4_9_precisionConfig cfg Lstar Dop Δ ε hε).W0 - P.fStar = Δ by
      simp [theorem_4_9_precisionConfig, deterministicConstantConfig, Δ,
        sourceObjectiveInitialGap, Objective.sourceFStar]]
    rw [hηeq, hadd]
    linarith

/- Appendix C.4, Eq. (21) plus Eq. (22), at one fixed horizon.  Degenerate
   printed denominators are handled by Lean's totalized source expression and
   are not exported as false `rhsDomain` witnesses. -/
theorem objective_gap_eq_zero_of_spectralSmooth_zero
    {m n : ℕ} (P : Objective m n) (Wstar W : Mat m n)
    (hfinite : P.HasFiniteInfimum) (hstar : StarConvex P Wstar)
    (hsmooth : SpectralSmooth P 0) :
    P.f W - P.fStar = 0 := by
  have hupper := spectralSmooth_quadratic_upper_bound P hsmooth Wstar W
  have hgrad := objective_grad_eq_zero_at_starMinimizer P Wstar hfinite hstar
  rw [hgrad] at hupper
  simp only [frobeniusInner, Matrix.zero_apply, zero_mul, Finset.sum_const_zero,
    add_zero, zero_div] at hupper
  have hlower := objective_value_ge_fStar_early P hfinite W
  rw [hstar.1] at hupper
  linarith

theorem theorem_4_10_source_formula_bound_at_horizon
    {m n : ℕ} (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (t : ℕ) (Wstar : Mat m n) (Lstar Dop : ℝ)
    (hfinite : P.HasFiniteInfimum)
    (hstar : StarConvex P Wstar)
    (hsmooth : SpectralSmooth P Lstar)
    (hbounded : BoundedOperatorDistance P cfg t Wstar Dop)
    (hη : theorem_4_10_adaptiveSchedule P cfg t Lstar) :
    sourceObjectiveGapAt P cfg t hfinite ≤
      theorem_4_10_sourceRhs P cfg t Lstar Dop := by
  let K : ℝ := Lstar * Dop ^ 2
  let x : ℕ → ℝ := fun k =>
    P.f ((deterministicMuonState P cfg k).W) - P.fStar
  have hx : ∀ k ∈ Finset.range (t + 1), 0 ≤ x k := by
    intro k _hk
    dsimp [x]
    linarith [objective_value_ge_fStar_early P hfinite
      (deterministicMuonState P cfg k).W]
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg hsmooth.nonneg (sq_nonneg Dop)
  by_cases hKzero : K = 0
  · have hgapzero : x t = 0 := by
      have hprod : Lstar * Dop ^ 2 = 0 := by simpa [K] using hKzero
      rcases mul_eq_zero.mp hprod with hLzero | hDopSq
      · have hsmooth0 : SpectralSmooth P 0 := by
          simpa [hLzero] using hsmooth
        exact objective_gap_eq_zero_of_spectralSmooth_zero
          P Wstar (deterministicMuonState P cfg t).W hfinite hstar hsmooth0
      · have hDopzero : Dop = 0 := (sq_eq_zero_iff).mp hDopSq
        have hbounded0 : BoundedOperatorDistance P cfg t Wstar 0 := by
          simpa [hDopzero] using hbounded
        have hstate := state_eq_star_of_bounded_zero P cfg t t Wstar hbounded0 (by simp)
        dsimp [x]
        rw [hstate, hstar.1]
        ring
    rw [sourceObjectiveGapAt_eq_objectiveGapAt]
    change x t ≤ theorem_4_10_sourceRhs P cfg t Lstar Dop
    rw [hgapzero]
    dsimp [theorem_4_10_sourceRhs, K] at hKzero ⊢
    have hnum :
        2 * Lstar * (P.f cfg.W0 - P.fStar) * Dop ^ 2 = 0 := by
      calc
        _ = 2 * (Lstar * Dop ^ 2) * (P.f cfg.W0 - P.fStar) := by ring
        _ = 0 := by rw [hKzero]; ring
    rw [hnum]
    simp
  · have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hKzero)
    have hLpos : 0 < Lstar := by
      by_contra h
      have hL : Lstar ≤ 0 := le_of_not_gt h
      have : Lstar = 0 := le_antisymm hL hsmooth.nonneg
      apply hKzero
      simp [K, this]
    have hDopnonneg : 0 ≤ Dop := by
      have hdist := hbounded 0 (by simp)
      exact le_trans (by unfold spectralNorm; exact norm_nonneg _) hdist
    have hDoppos : 0 < Dop := by
      by_contra h
      have : Dop = 0 := le_antisymm (le_of_not_gt h) hDopnonneg
      apply hKzero
      simp [K, this]
    have hrec : ∀ k ∈ Finset.range t,
        x (k + 1) ≤ x k - x k ^ 2 / (2 * K) := by
      intro k hk
      let Wk := (deterministicMuonState P cfg k).W
      let Wnext := (deterministicMuonState P cfg (k + 1)).W
      let Gk := P.grad Wk
      let Dk := orthogonalizedDirection Gk
      let g : ℝ := nuclearNorm Gk
      let ηk : ℝ := g / Lstar
      rcases hη k hk with ⟨hdom, heta⟩
      have heta' : cfg.eta k = ηk := by
        simpa [ηk, g, realizedSourceQuot, sourceQuot] using heta
      have hG : (deterministicMuonState P cfg k).G = Gk := by
        simpa [Gk, Wk, deterministicGradient] using
          deterministicMuon_G_eq_gradient P cfg k
      have hupdate : Wnext = Wk - ηk • Dk := by
        simpa [Wnext, Wk, Dk, hG, heta'] using
          deterministicMuon_W_succ_eq_source_update P cfg k
      have hsmoothStep := spectralSmooth_quadratic_upper_bound P hsmooth Wk Wnext
      have hdiff : Wnext - Wk = (-ηk) • Dk := by
        rw [hupdate]
        ext i j
        simp
      rw [hdiff] at hsmoothStep
      have hpair : frobeniusInner Gk ((-ηk) • Dk) = -ηk * g := by
        rw [show frobeniusInner Gk ((-ηk) • Dk) =
            -ηk * frobeniusInner Gk Dk by
          unfold frobeniusInner
          simp only [Matrix.smul_apply, smul_eq_mul]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _hi
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _hj
          ring]
        rw [orthogonalizedDirection_frobeniusInner_eq_nuclearNorm]
      have hnorm : spectralNorm ((-ηk) • Dk) ^ 2 =
          ηk ^ 2 * spectralNorm Dk ^ 2 := by
        simp [spectralNorm, norm_smul, Real.norm_eq_abs, abs_neg, mul_pow, sq_abs]
      rw [hpair, hnorm] at hsmoothStep
      have hDnorm : spectralNorm Dk ≤ 1 :=
        orthogonalizedDirection_spectralNorm_le_one Gk
      have hDsq : spectralNorm Dk ^ 2 ≤ 1 := by
        nlinarith [spectralNorm_nonneg Dk]
      have hcoef : 0 ≤ (Lstar / 2) * ηk ^ 2 := by positivity
      have hquad := mul_le_mul_of_nonneg_left hDsq hcoef
      have hdescent : P.f Wnext ≤ P.f Wk - g ^ 2 / (2 * Lstar) := by
        have heta_g : ηk * g = g ^ 2 / Lstar := by
          dsimp [ηk]
          field_simp [ne_of_gt hLpos]
        have hquadval : (Lstar / 2) * ηk ^ 2 =
            g ^ 2 / (2 * Lstar) := by
          dsimp [ηk]
          field_simp [ne_of_gt hLpos]
        have hquad' : (Lstar / 2) *
            (ηk ^ 2 * spectralNorm Dk ^ 2) ≤ g ^ 2 / (2 * Lstar) := by
          calc
            _ = (Lstar / 2) * ηk ^ 2 * spectralNorm Dk ^ 2 := by ring
            _ ≤ (Lstar / 2) * ηk ^ 2 * 1 := hquad
            _ = _ := by simpa using hquadval
        have hlinear : ηk * g = 2 * (g ^ 2 / (2 * Lstar)) := by
          rw [heta_g]
          field_simp [ne_of_gt hLpos]
        change P.f Wnext ≤ P.f Wk + -ηk * g +
          (Lstar / 2) * (ηk ^ 2 * spectralNorm Dk ^ 2) at hsmoothStep
        linarith [hsmoothStep, hquad', hlinear]
      have hk' : k ∈ Finset.range (t + 1) :=
        Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp hk) (by omega))
      have hgap := theorem_4_16_star_gradient_lower_bound_at
        P cfg t k Wstar Dop hstar hbounded hk'
      have hgapDiv : x k / Dop ≤ g := by
        apply (div_le_iff₀ hDoppos).2
        simpa [x, g, Gk, Wk, mul_comm] using hgap
      have hsquare : (x k / Dop) ^ 2 ≤ g ^ 2 := by
        exact (sq_le_sq₀ (div_nonneg (hx k hk') hDopnonneg)
          (nuclearNorm_nonneg_early Gk)).2 hgapDiv
      have hscaled := div_le_div_of_nonneg_right hsquare
        (by positivity : 0 ≤ 2 * Lstar)
      have hquadGap : x k ^ 2 / (2 * K) ≤ g ^ 2 / (2 * Lstar) := by
        dsimp [K]
        field_simp [ne_of_gt hDoppos, ne_of_gt hLpos] at hscaled ⊢
        nlinarith
      dsimp [x, Wnext, Wk] at hdescent ⊢
      linarith
    have hbound := quadratic_descent_recurrence_rational_bound x t K hKpos hx hrec
    rw [sourceObjectiveGapAt_eq_objectiveGapAt]
    change x t ≤ theorem_4_10_sourceRhs P cfg t Lstar Dop
    have hxzero : x 0 = P.f cfg.W0 - P.fStar := by
      simp [x, deterministicMuonState, deterministicMuonBaseState]
    rw [hxzero] at hbound
    dsimp [theorem_4_10_sourceRhs, K] at hbound ⊢
    convert hbound using 1 <;> ring

/- Formula-only C.4 selector. -/
theorem theorem_4_10_sourceRhs_le_epsilon_at_selected_horizon
    {m n : ℕ} (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (Lstar Dop : ℝ) (hfinite : P.HasFiniteInfimum)
    (hsmooth : SpectralSmooth P Lstar) :
    ∃ horizonBound : ∀ ε : ℝ, epsilonDomain ε → ℝ,
      AsymptoticUpperRealOn epsilonDomain horizonBound
        (fun ε hε => theorem_4_10_complexityRateRealized m n Lstar Dop ε hε)
        (theoremScope "Theorem 4.10 selected rational horizon" ["epsilon"]) ∧
      ∀ ε : ℝ, ∀ hε : epsilonDomain ε,
        let N := theorem_4_10_selectedHorizon m n Lstar Dop ε hε
        (N : ℝ) ≤ horizonBound ε hε ∧
          theorem_4_10_sourceRhs P cfg N Lstar Dop ≤ ε := by
  let Δ := sourceObjectiveInitialGap P cfg.W0 hfinite
  let K : ℝ := Lstar * Dop ^ 2
  let horizonBound : ∀ ε : ℝ, epsilonDomain ε → ℝ :=
    fun ε hε => (theorem_4_10_selectedHorizon m n Lstar Dop ε hε : ℝ)
  have hΔ : 0 ≤ Δ := by
    dsimp [Δ, sourceObjectiveInitialGap, Objective.sourceFStar]
    linarith [objective_terminal_lower_bound P hfinite cfg.W0]
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg hsmooth.nonneg (sq_nonneg Dop)
  refine ⟨horizonBound, ?_, ?_⟩
  · unfold AsymptoticUpperRealOn
    by_cases hKzero : K = 0
    · refine ⟨1, 1, by norm_num, by norm_num, ?_, ?_⟩
      · simp [ConstantRespectsScope, theoremScope]
      · intro ε hε _hεpos _hεsmall
        have hscale : Lstar * Dop ^ 2 = 0 := by simpa [K] using hKzero
        have htwoscale : 2 * Lstar * Dop ^ 2 = 0 := by
          calc
            2 * Lstar * Dop ^ 2 = 2 * (Lstar * Dop ^ 2) := by ring
            _ = 0 := by rw [hscale, mul_zero]
        simp [horizonBound, theorem_4_10_selectedHorizon,
          theorem_4_10_complexityRateRealized, hscale, htwoscale]
    · have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hKzero)
      refine ⟨3, K, by norm_num, hKpos, ?_, ?_⟩
      · simp [ConstantRespectsScope, theoremScope]
      · intro ε hε hεpos hεsmall
        have hX : 0 ≤ 2 * K / ε := by positivity
        have hNupper :
            (theorem_4_10_selectedHorizon m n Lstar Dop ε hε : ℝ) <
              2 * K / ε + 1 := by
          dsimp [theorem_4_10_selectedHorizon]
          convert Nat.ceil_lt_add_one hX using 1 <;> dsimp [K] <;> ring
        have hNupper' :
            (theorem_4_10_selectedHorizon m n Lstar Dop ε hε : ℝ) <
              2 * (K / ε) + 1 := by
          convert hNupper using 1 <;> ring
        have hone : 1 ≤ K / ε := (one_le_div hεpos).2 hεsmall
        have hrate : theorem_4_10_complexityRateRealized m n Lstar Dop ε hε =
            K / ε := by
          dsimp [theorem_4_10_complexityRateRealized,
            realizedSourceInv, sourceInv, K]
          ring
        dsimp [horizonBound]
        rw [hrate]
        linarith
  · intro ε hε
    let N := theorem_4_10_selectedHorizon m n Lstar Dop ε hε
    refine ⟨le_rfl, ?_⟩
    have hscalar := source_rational_rate_at_ceil K Δ ε hK hΔ hε
    convert hscalar.2 using 1 <;>
      dsimp [N, theorem_4_10_selectedHorizon, theorem_4_10_sourceRhs,
        K, Δ, sourceObjectiveInitialGap, Objective.sourceFStar] <;> ring

theorem theorem_4_9 {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (T : ℕ) (Wstar : Mat m n) (Lstar Dop η : ℝ)
    (_hfinite : P.HasFiniteInfimum)
    (_hstar : StarConvex P Wstar)
    (_hsmooth : SpectralSmooth P Lstar)
    (_hbounded : BoundedOperatorDistance P cfg T Wstar Dop)
    (_hη : ∀ t ∈ Finset.range T, cfg.eta t = η) :
    theorem_4_9_statement P cfg T Wstar Lstar Dop η _hfinite := by
  dsimp [theorem_4_9_statement]
  refine ⟨theorem_4_9_formula_source_boundary P cfg T Lstar Dop η, ?_, ?_, ?_⟩
  · intro hdom
    exact theorem_4_9_source_formula_bound_at_horizon
      P cfg T Wstar Lstar Dop η _hfinite _hstar _hsmooth _hbounded hdom _hη
  · unfold AsymptoticUpperRealOn
    refine ⟨1, 1, by norm_num, by norm_num, ?_, ?_⟩
    · simp [ConstantRespectsScope, theoremScope]
    · intro ε hε _hεpos _hεsmall
      simp
  · intro hruns
    rcases theorem_4_9_sourceRhs_le_epsilon_at_log_horizon
        P cfg Lstar Dop _hfinite _hsmooth with ⟨horizonBound, hrate, hselect⟩
    unfold theorem_4_9_precisionConclusion
    refine ⟨horizonBound, hrate, ?_⟩
    intro ε hε hεdomain
    let Δ := sourceObjectiveInitialGap P cfg.W0 _hfinite
    let N := theorem_4_9_logHorizon m n Lstar Dop Δ ε hε
    have hrun := hruns ε hε
    have hselected := hselect ε hε
    dsimp [N, Δ] at hrun hselected
    refine ⟨N, hselected.1, ⟨_hstar, _hsmooth, hrun⟩, ?_⟩
    have hden : Lstar * Dop ≠ 0 := hε.2.1
    have hDop : Dop ≠ 0 := by
      intro hzero
      apply hden
      simp [hzero]
    have hstepBounds := hε.2.2.2.2
    dsimp at hstepBounds
    have hdom : theorem_4_9_rhsDomain P
        (theorem_4_9_precisionConfig cfg Lstar Dop Δ ε hε)
        N Lstar Dop (theorem_4_9_etaRateRealized m n Lstar Dop ε hε.2.1) := by
      refine ⟨hDop, ?_, ?_⟩
      · simpa [theorem_4_9_etaRateRealized, realizedSourceQuot, sourceQuot] using
          hstepBounds.1
      · simpa [theorem_4_9_etaRateRealized, realizedSourceQuot, sourceQuot] using
          hstepBounds.2
    exact le_trans
      (theorem_4_9_source_formula_bound_at_horizon P
        (theorem_4_9_precisionConfig cfg Lstar Dop Δ ε hε)
        N Wstar Lstar Dop
        (theorem_4_9_etaRateRealized m n Lstar Dop ε hε.2.1)
        _hfinite _hstar _hsmooth hrun hdom (by intro k hk; rfl))
      hselected.2

theorem theorem_4_10 {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (t : ℕ) (Wstar : Mat m n) (Lstar Dop : ℝ)
    (_hfinite : P.HasFiniteInfimum)
    (_hstar : StarConvex P Wstar)
    (_hsmooth : SpectralSmooth P Lstar)
    (_hbounded : BoundedOperatorDistance P cfg t Wstar Dop)
    (_hη : theorem_4_10_adaptiveSchedule P cfg t Lstar) :
    theorem_4_10_statement P cfg t Wstar Lstar Dop _hfinite := by
  constructor
  · intro hdom
    have hformula := theorem_4_10_source_formula_bound_at_horizon
      P cfg t Wstar Lstar Dop _hfinite _hstar _hsmooth _hbounded _hη
    simpa [theorem_4_10_rhs, theorem_4_10_sourceRhs,
      realizedSourceQuot, sourceQuot] using hformula
  · intro hruns
    rcases theorem_4_10_sourceRhs_le_epsilon_at_selected_horizon
        P cfg Lstar Dop _hfinite _hsmooth with ⟨horizonBound, hrate, hselect⟩
    unfold theorem_4_10_precisionConclusion
    refine ⟨horizonBound, hrate, ?_⟩
    intro ε hε _hεdomain
    let N := theorem_4_10_selectedHorizon m n Lstar Dop ε hε
    have hrun := hruns ε hε
    have hselected := hselect ε hε
    dsimp [N] at hrun hselected
    refine ⟨N, hselected.1, ⟨_hstar, _hsmooth, hrun⟩, ?_⟩
    exact le_trans
      (theorem_4_10_source_formula_bound_at_horizon P cfg N Wstar Lstar Dop
        _hfinite _hstar _hsmooth hrun.1 hrun.2)
      hselected.2

theorem lemma_4_12 {m n : ℕ}
    (P : Objective m n) (Λ : Mat n n) :
    LambdaSmooth P Λ →
      FrobeniusSmooth P (spectralNorm Λ) ∧ SpectralSmooth P (nuclearNorm Λ) := by
  intro hΛ
  constructor
  · refine ⟨hΛ.contDiff, ?_⟩
    intro W W'
    let G : Mat m n := P.grad W - P.grad W'
    let D : Mat m n := W - W'
    have hleft :
        frobeniusNorm G ≤
          Real.sqrt (spectralNorm Λ) * lambdaInvNorm Λ G :=
      (lambda_norm_comparisons_for_lemma_4_12
        (Λ := Λ) (A := G) hΛ.positiveDefinite).1.1
    have hgrad : lambdaInvNorm Λ G ≤ lambdaNorm Λ D := by
      simpa [G, D] using hΛ.lipschitz_grad W W'
    have hright :
        lambdaNorm Λ D ≤
          Real.sqrt (spectralNorm Λ) * frobeniusNorm D :=
      (lambda_norm_comparisons_for_lemma_4_12
        (Λ := Λ) (A := D) hΛ.positiveDefinite).1.2
    have hchain :
        frobeniusNorm G ≤
          Real.sqrt (spectralNorm Λ) *
            (Real.sqrt (spectralNorm Λ) * frobeniusNorm D) := by
      calc
        frobeniusNorm G
            ≤ Real.sqrt (spectralNorm Λ) * lambdaInvNorm Λ G := hleft
        _ ≤ Real.sqrt (spectralNorm Λ) * lambdaNorm Λ D :=
            mul_le_mul_of_nonneg_left hgrad (Real.sqrt_nonneg _)
        _ ≤ Real.sqrt (spectralNorm Λ) *
              (Real.sqrt (spectralNorm Λ) * frobeniusNorm D) :=
            mul_le_mul_of_nonneg_left hright (Real.sqrt_nonneg _)
    exact le_trans hchain
      (sqrt_constant_absorption (spectralNorm Λ) (frobeniusNorm D)
        (spectralNorm_nonneg Λ))
  · refine ⟨nuclearNorm_nonneg Λ, hΛ.contDiff, ?_⟩
    intro W W'
    let G : Mat m n := P.grad W - P.grad W'
    let D : Mat m n := W - W'
    have hleft :
        nuclearNorm G ≤
          Real.sqrt (nuclearNorm Λ) * lambdaInvNorm Λ G :=
      (lambda_norm_comparisons_for_lemma_4_12
        (Λ := Λ) (A := G) hΛ.positiveDefinite).2.1
    have hgrad : lambdaInvNorm Λ G ≤ lambdaNorm Λ D := by
      simpa [G, D] using hΛ.lipschitz_grad W W'
    have hright :
        lambdaNorm Λ D ≤
          Real.sqrt (nuclearNorm Λ) * spectralNorm D :=
      (lambda_norm_comparisons_for_lemma_4_12
        (Λ := Λ) (A := D) hΛ.positiveDefinite).2.2
    have hchain :
        nuclearNorm G ≤
          Real.sqrt (nuclearNorm Λ) *
            (Real.sqrt (nuclearNorm Λ) * spectralNorm D) := by
      calc
        nuclearNorm G
            ≤ Real.sqrt (nuclearNorm Λ) * lambdaInvNorm Λ G := hleft
        _ ≤ Real.sqrt (nuclearNorm Λ) * lambdaNorm Λ D :=
            mul_le_mul_of_nonneg_left hgrad (Real.sqrt_nonneg _)
        _ ≤ Real.sqrt (nuclearNorm Λ) *
              (Real.sqrt (nuclearNorm Λ) * spectralNorm D) :=
            mul_le_mul_of_nonneg_left hright (Real.sqrt_nonneg _)
    exact le_trans hchain
      (sqrt_constant_absorption (nuclearNorm Λ) (spectralNorm D)
        (nuclearNorm_nonneg Λ))

theorem theorem_4_14 {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (T : ℕ) (s η : ℝ)
    (_hfinite : P.HasFiniteInfimum)
    (_hthird : ThirdDerivativeBounded P s)
    (_hη : ∀ t ∈ Finset.range T, cfg.eta t = η) :
    theorem_4_14_statement P cfg T s η _hfinite := by
  unfold theorem_4_14_statement
  constructor
  · exact theorem_4_14_source_domain_obligation P cfg T s η _hthird _hη
  · constructor
    · intro hsrc
      obtain ⟨hdom, _⟩ :=
        theorem_4_14_downstream_phase2_boundary_of_sourceDomain
          P cfg T s η hsrc _hthird _hη
      refine ⟨hdom, ?_⟩
      exact theorem_4_14_source_average_bound_at_horizon
        P cfg T s η _hthird _hη hdom
    · exact theorem_4_14_source_rate_consequences_of_source_assumptions
        P cfg s _hfinite

/- Appendix B.4's fixed-horizon positive-`Jstar` substitution.  The run
   witness fixes the exact schedule and the realized curvature value, while
   the constant is uniform in the horizon. -/
set_option maxHeartbeats 800000 in
theorem theorem_4_15_positive_source_rate_bound_at_horizon
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n)
    (cfgForHorizon : ℕ → StochasticMuonConfig m n)
    (W0 : Mat m n) (Jstar σ Δ s : ℝ) (N : ℕ)
    (hfinite : P.objective.HasFiniteInfimum)
    (hthird : ThirdDerivativeBounded P.objective s)
    (hvariance : BoundedVariance P σ)
    (hDelta : sourceObjectiveInitialGap P.objective W0 hfinite = Δ)
    (hN : theorem_4_15_positiveRunRealizedForHorizon
      P cfgForHorizon W0 Jstar σ Δ s N) :
    theorem_4_15_positiveRunAverageRealized
        P cfgForHorizon W0 Jstar σ Δ s N hN ≤
      10 * theorem_4_15_positiveRunBranchRateRealized
        P cfgForHorizon W0 Jstar σ Δ s N hN := by
  unfold theorem_4_15_positiveRunRealizedForHorizon at hN
  dsimp at hN
  rcases hN with ⟨hNpos, hwd, hW0, hJstar, hschedule, hsource⟩
  rcases hschedule with ⟨hscheduleDom, hbatch, heta, hbeta⟩
  rcases hscheduleDom with
    ⟨_horizon, hJDeltaDom, hrNDom, hbetaQuotDom, hetaDom, hrateDom⟩
  let cfgN := cfgForHorizon N
  let etaN := Real.sqrt
    (sourceQuot ((1 - cfgN.beta) * Δ) ((N : ℝ) * Jstar))
  have hformula := theorem_4_15_source_formula_bound
    P cfgN N s σ etaN hfinite hsource hthird hvariance heta
  have hcurvature := theorem_4_15_positive_run_curvature_control
    P cfgForHorizon W0 Jstar σ Δ s N
      ⟨hNpos, hwd, hW0, hJstar,
        ⟨⟨_horizon, hJDeltaDom, hrNDom, hbetaQuotDom, hetaDom, hrateDom⟩,
          hbatch, heta, hbeta⟩, hsource⟩
  have hraw := theorem_4_15_source_average_bound_at_horizon
    P cfgN N s σ etaN hsource hthird hvariance heta
  rcases hrateDom with
    ⟨_hNrate, hrateFirst, hrateSecond, hprodDom, hrateThird,
      hrankCube, hrateCurvature⟩
  let r : ℝ := matrixRankBound m n
  let q : ℝ := Real.sqrt (r ^ 3)
  let x : ℝ := Real.sqrt (Jstar * Δ) / (σ * Real.sqrt (r * (N : ℝ)))
  let a : ℝ := 1 - cfgN.beta
  let A : ℝ := Real.sqrt (Real.sqrt ((r * Jstar * Δ * σ ^ 2) / (N : ℝ)))
  let B : ℝ := Real.sqrt ((Jstar * Δ) / (N : ℝ))
  let D : ℝ := r * σ ^ 2 / Real.sqrt (Jstar * Δ * (N : ℝ))
  let E : ℝ := s * q * Δ / (Jstar * (N : ℝ))
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hJN_nonneg : 0 ≤ Jstar * Δ * (N : ℝ) := by
    simpa [sourceSqrtDomain] using hprodDom
  have hJN_ne : Jstar * Δ * (N : ℝ) ≠ 0 := by
    intro hz
    have hsqrt_zero : Real.sqrt (Jstar * Δ * (N : ℝ)) = 0 := by simp [hz]
    exact hrateThird (by simpa [sourceQuotDomain] using hsqrt_zero)
  have hJN_pos : 0 < Jstar * Δ * (N : ℝ) :=
    lt_of_le_of_ne hJN_nonneg (Ne.symm hJN_ne)
  have hJDelta_pos : 0 < Jstar * Δ := by nlinarith
  have hgap_nonneg : 0 ≤ sourceObjectiveInitialGap P.objective W0 hfinite := by
    unfold sourceObjectiveInitialGap Objective.sourceFStar
    have hlower : P.objective.fStar ≤ P.objective.f W0 := by
      simpa [Objective.fStar] using
        (csInf_le hfinite
          (show P.objective.f W0 ∈ Set.range P.objective.f from ⟨W0, rfl⟩))
    linarith
  have hΔ_nonneg : 0 ≤ Δ := by simpa [hDelta] using hgap_nonneg
  have hΔ_pos : 0 < Δ := by
    by_contra hn
    have : Δ = 0 := le_antisymm (le_of_not_gt hn) hΔ_nonneg
    simp [this] at hJDelta_pos
  have hJ_pos : 0 < Jstar := by nlinarith
  have hden_ne : σ * Real.sqrt (r * (N : ℝ)) ≠ 0 := by
    simpa [cfgN, r, sourceQuotDomain] using hbetaQuotDom
  have hσ_ne : σ ≠ 0 := (mul_ne_zero_iff.mp hden_ne).1
  have hσ_pos : 0 < σ := lt_of_le_of_ne hvariance.nonneg (Ne.symm hσ_ne)
  have hrN_nonneg : 0 ≤ r * (N : ℝ) := by
    simpa [r, sourceSqrtDomain] using hrNDom
  have hrN_ne : r * (N : ℝ) ≠ 0 := by
    have hsqrt_ne := (mul_ne_zero_iff.mp hden_ne).2
    intro hz
    exact hsqrt_ne (by simp [hz])
  have hrN_pos : 0 < r * (N : ℝ) :=
    lt_of_le_of_ne hrN_nonneg (Ne.symm hrN_ne)
  have hr_pos : 0 < r := by nlinarith
  have hs_nonneg : 0 ≤ s := le_trans (norm_nonneg _) (hthird.bound W0)
  have hq_pos : 0 < q := by
    dsimp [q]
    exact Real.sqrt_pos.2 (pow_pos hr_pos 3)
  have heta_pos : 0 < etaN := hsource.2
  have ha_pos : 0 < a := by dsimp [a]; exact sub_pos.mpr cfgN.beta_mem.2
  have ha_le : a ≤ 1 := by dsimp [a]; linarith [cfgN.beta_mem.1]
  have heta_sq : etaN ^ 2 = a * Δ / ((N : ℝ) * Jstar) := by
    dsimp [etaN, a, sourceQuot]
    apply Real.sq_sqrt
    rw [hbeta]
    simpa [cfgN, sourceSqrtQuotDomain, sourceQuot,
      Real.sqrt_mul (show 0 ≤ r from hr_pos.le)] using hetaDom.2
  have hdrop : stochasticExpectedObjectiveDrop P cfgN N ≤ Δ := by
    let mu := samplePathLaw P cfgN.batchSize
    letI : IsProbabilityMeasure P.sampleLaw := P.isProbability_sampleLaw
    letI : IsProbabilityMeasure mu := by
      dsimp [mu, samplePathLaw]
      infer_instance
    let hregularity : StochasticObjectiveRegularity P.objective :=
      Or.inr (Or.inr ⟨s, hthird⟩)
    have hdrop_int : Integrable
        (fun omega => P.objective.f cfgN.W0 -
          P.objective.f (stochasticMuonState P cfgN omega N).W) mu := by
      simpa [mu, stochasticExpectedObjectiveDropWellDefined,
        SOptLib.expectationWellDefined] using
        (stochasticExpectedObjectiveDrop_wellDefined_of_source_assumptions
          P cfgN N σ hregularity hvariance)
    have hlower (omega : SamplePath ξ cfgN.batchSize) :
        P.objective.sourceFStar hfinite ≤
          P.objective.f (stochasticMuonState P cfgN omega N).W := by
      simpa [Objective.sourceFStar, Objective.fStar] using
        (csInf_le hfinite (show
          P.objective.f (stochasticMuonState P cfgN omega N).W ∈
            Set.range P.objective.f from
          ⟨(stochasticMuonState P cfgN omega N).W, rfl⟩))
    have hint :
        (∫ omega, P.objective.f cfgN.W0 -
            P.objective.f (stochasticMuonState P cfgN omega N).W ∂mu) ≤
          ∫ _omega, Δ ∂mu := by
      apply integral_mono hdrop_int (integrable_const Δ)
      intro omega
      calc
        P.objective.f cfgN.W0 -
            P.objective.f (stochasticMuonState P cfgN omega N).W ≤
            P.objective.f cfgN.W0 - P.objective.sourceFStar hfinite :=
          sub_le_sub_left (hlower omega) _
        _ = Δ := by simpa [cfgN, hW0, sourceObjectiveInitialGap] using hDelta
    simpa [stochasticExpectedObjectiveDrop, mu, integral_const,
      measureReal_univ_eq_one] using hint
  have hJsource : stochasticHessianJstar P cfgN N = Jstar := by
    simpa [cfgN, stochasticHessianJstarRealized, stochasticHessianJstar,
      stochasticHessianDirectionalAverageRealized,
      stochasticHessianDirectionalAverage,
      stochasticHessianCrossAverageRealized, stochasticHessianCrossAverage,
      realizedExpectation] using hcurvature
  have hJdir : stochasticHessianDirectionalAverage P cfgN N ≤ Jstar := by
    rw [← hJsource, stochasticHessianJstar_eq_source_max]
    exact le_max_right _ _
  have hJcross : stochasticHessianCrossAverage P cfgN N ≤ Jstar := by
    rw [← hJsource, stochasticHessianJstar_eq_source_max]
    exact le_max_left _ _
  have hdropFirst :
      stochasticExpectedObjectiveDrop P cfgN N / ((N : ℝ) * etaN) ≤
        Δ / ((N : ℝ) * etaN) :=
    div_le_div_of_nonneg_right hdrop (mul_pos hNreal heta_pos).le
  have hdirTerm :
      etaN / 2 * stochasticHessianDirectionalAverage P cfgN N ≤
        etaN / 2 * Jstar :=
    mul_le_mul_of_nonneg_left hJdir (by positivity)
  have hcrossCoeff : 0 ≤ 2 * etaN * cfgN.beta / a := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) heta_pos.le) cfgN.beta_mem.1)
      ha_pos.le
  have hcrossTerm :
      2 * etaN * cfgN.beta / a *
          stochasticHessianCrossAverage P cfgN N ≤
        2 * etaN * cfgN.beta / a * Jstar :=
    mul_le_mul_of_nonneg_left hJcross hcrossCoeff
  have hraw' : stochasticAverageNuclearGradient P cfgN N ≤
      stochasticExpectedObjectiveDrop P cfgN N / ((N : ℝ) * etaN) +
        etaN / 2 * stochasticHessianDirectionalAverage P cfgN N +
        2 * Real.sqrt r *
          (Real.sqrt (a / (1 + cfgN.beta)) * σ) +
        2 * Real.sqrt r * σ / (a * (N : ℝ)) +
        2 * etaN * cfgN.beta / a *
          stochasticHessianCrossAverage P cfgN N +
        s * etaN ^ 2 * q / 6 +
        2 * s * etaN ^ 2 * q * cfgN.beta / a := by
    simpa [cfgN, r, q, a, hbatch] using hraw
  have hscalar :
      Δ / ((N : ℝ) * etaN) + etaN / 2 * Jstar +
          2 * Real.sqrt r * (Real.sqrt (a / (1 + cfgN.beta)) * σ) +
          2 * Real.sqrt r * σ / (a * (N : ℝ)) +
          2 * etaN * cfgN.beta / a * Jstar +
          s * etaN ^ 2 * q / 6 +
          2 * s * etaN ^ 2 * q * cfgN.beta / a ≤
        10 * (A + B + D + E) := by
    have hA_nonneg : 0 ≤ A := by dsimp [A]; positivity
    have hB_nonneg : 0 ≤ B := by dsimp [B]; positivity
    have hD_nonneg : 0 ≤ D := by dsimp [D]; positivity
    have hE_nonneg : 0 ≤ E := by dsimp [E]; positivity
    have hB_sq : B ^ 2 = Jstar * Δ / (N : ℝ) := by
      dsimp [B]
      exact Real.sq_sqrt (div_nonneg hJDelta_pos.le hNreal.le)
    have hetaJ_sq : (etaN * Jstar) ^ 2 =
        a * (Jstar * Δ / (N : ℝ)) := by
      rw [mul_pow, heta_sq]
      field_simp [ne_of_gt hJ_pos, ne_of_gt hNreal]
    have hetaJ_nonneg : 0 ≤ etaN * Jstar := by positivity
    have hetaJ_le : etaN * Jstar ≤ B := by
      apply (sq_le_sq₀ hetaJ_nonneg hB_nonneg).mp
      rw [hetaJ_sq, hB_sq]
      exact mul_le_of_le_one_left (div_nonneg hJDelta_pos.le hNreal.le) ha_le
    have hdir_le : etaN / 2 * Jstar ≤ B / 2 := by nlinarith
    have hrem1 : s * etaN ^ 2 * q / 6 ≤ E / 6 := by
      rw [heta_sq]
      have haE : a * E ≤ E := mul_le_of_le_one_left hE_nonneg ha_le
      have heq : s * (a * Δ / ((N : ℝ) * Jstar)) * q = a * E := by
        dsimp [E]
        field_simp [ne_of_gt hJ_pos, ne_of_gt hNreal]
      rw [heq]
      nlinarith
    have hrem2 : 2 * s * etaN ^ 2 * q * cfgN.beta / a ≤ 2 * E := by
      rw [heta_sq]
      have hbeta_le : cfgN.beta ≤ 1 := cfgN.beta_mem.2.le
      have heq : 2 * s * (a * Δ / ((N : ℝ) * Jstar)) * q * cfgN.beta / a =
          2 * cfgN.beta * E := by
        dsimp [E]
        field_simp [ne_of_gt hJ_pos, ne_of_gt hNreal, ne_of_gt ha_pos]
      rw [heq]
      nlinarith
    have ha_min : a = min x 1 := by
      simpa [a, x, cfgN, sourceQuot] using hbeta
    have hN_one : 1 ≤ (N : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hNpos))
    have hsqrtr_sq : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt hr_pos.le
    have hsqrt_rN_sq : (Real.sqrt (r * (N : ℝ))) ^ 2 = r * (N : ℝ) :=
      Real.sq_sqrt hrN_pos.le
    have hsqrt_JΔ_sq : (Real.sqrt (Jstar * Δ)) ^ 2 = Jstar * Δ :=
      Real.sq_sqrt hJDelta_pos.le
    have hrad_nonneg :
        0 ≤ (r * Jstar * Δ * σ ^ 2) / (N : ℝ) := by positivity
    have hA_sq :
        A ^ 2 = Real.sqrt ((r * Jstar * Δ * σ ^ 2) / (N : ℝ)) := by
      dsimp [A]
      exact Real.sq_sqrt (Real.sqrt_nonneg _)
    have hA_four : A ^ 4 = (r * Jstar * Δ * σ ^ 2) / (N : ℝ) := by
      calc
        A ^ 4 = (A ^ 2) ^ 2 := by ring
        _ = (Real.sqrt ((r * Jstar * Δ * σ ^ 2) / (N : ℝ))) ^ 2 := by
          rw [hA_sq]
        _ = (r * Jstar * Δ * σ ^ 2) / (N : ℝ) :=
          Real.sq_sqrt hrad_nonneg
    have heta_sq_clear :
        etaN ^ 2 * ((N : ℝ) * Jstar) = a * Δ := by
      exact (eq_div_iff (mul_ne_zero (ne_of_gt hNreal) (ne_of_gt hJ_pos))).mp heta_sq
    have hfirst_eq :
        Δ / ((N : ℝ) * etaN) = etaN * Jstar / a := by
      field_simp [ne_of_gt hNreal, ne_of_gt heta_pos, ne_of_gt hJ_pos,
        ne_of_gt ha_pos]
      nlinarith only [heta_sq_clear]
    by_cases hx : x ≤ 1
    · have ha_x : a = x := ha_min.trans (min_eq_left hx)
      have ha_x' :
          a = Real.sqrt (Jstar * Δ) /
            (σ * Real.sqrt (r * (N : ℝ))) := by
        simpa [x] using ha_x
      have ha_sq :
          a ^ 2 = (Jstar * Δ) / (σ ^ 2 * (r * (N : ℝ))) := by
        rw [ha_x', div_pow, mul_pow, hsqrt_JΔ_sq, hsqrt_rN_sq]
      have ha_sq_clear :
          a ^ 2 * (σ ^ 2 * (r * (N : ℝ))) = Jstar * Δ := by
        exact (eq_div_iff (mul_ne_zero (pow_ne_zero 2 (ne_of_gt hσ_pos))
          (ne_of_gt hrN_pos))).mp ha_sq
      have hmomentum_sq :
          (etaN * Jstar / a) ^ 2 = (Jstar * Δ) / (a * (N : ℝ)) := by
        field_simp [ne_of_gt ha_pos, ne_of_gt hNreal, ne_of_gt hJ_pos]
        nlinarith only [heta_sq_clear]
      have hscale_nonneg : 0 ≤ (Jstar * Δ) / (a * (N : ℝ)) := by positivity
      have hscale_sq :
          ((Jstar * Δ) / (a * (N : ℝ))) ^ 2 =
            (r * Jstar * Δ * σ ^ 2) / (N : ℝ) := by
        field_simp [ne_of_gt ha_pos, ne_of_gt hNreal, ne_of_gt hJ_pos,
          ne_of_gt hΔ_pos, ne_of_gt hσ_pos, ne_of_gt hr_pos]
        nlinarith only [ha_sq_clear]
      have hmomentumA : etaN * Jstar / a ≤ A := by
        have hroot_nonneg :
            0 ≤ Real.sqrt ((r * Jstar * Δ * σ ^ 2) / (N : ℝ)) :=
          Real.sqrt_nonneg _
        have hscale_eq :
            (Jstar * Δ) / (a * (N : ℝ)) =
              Real.sqrt ((r * Jstar * Δ * σ ^ 2) / (N : ℝ)) := by
          nlinarith only [hscale_sq, Real.sq_sqrt hrad_nonneg,
            hscale_nonneg, hroot_nonneg]
        have hmomentum_nonneg : 0 ≤ etaN * Jstar / a := by positivity
        nlinarith only [hmomentum_sq, hA_sq, hscale_eq,
          hmomentum_nonneg, hA_nonneg]
      have hfirstA : Δ / ((N : ℝ) * etaN) ≤ A := by
        rw [hfirst_eq]
        exact hmomentumA
      have hbeta_a : cfgN.beta = 1 - a := by
        dsimp [a]
        ring
      have hdenom_one : 1 ≤ 1 + cfgN.beta := by
        linarith [cfgN.beta_mem.1]
      have hratio_le : a / (1 + cfgN.beta) ≤ a := by
        apply (div_le_iff₀ (by linarith [cfgN.beta_mem.1])).2
        simpa using (mul_le_mul_of_nonneg_left hdenom_one ha_pos.le)
      have hratio_nonneg : 0 ≤ a / (1 + cfgN.beta) := by positivity
      have hsqrt_ratio_le :
          Real.sqrt (a / (1 + cfgN.beta)) ≤ Real.sqrt a :=
        Real.sqrt_le_sqrt hratio_le
      have hnoise_base_nonneg :
          0 ≤ Real.sqrt r * (Real.sqrt a * σ) := by positivity
      have hnoise_base_four :
          (Real.sqrt r * (Real.sqrt a * σ)) ^ 4 =
            (r * Jstar * Δ * σ ^ 2) / (N : ℝ) := by
        have hsqrta_sq : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha_pos.le
        have hsqrtr_four : (Real.sqrt r) ^ 4 = r ^ 2 := by
          calc
            (Real.sqrt r) ^ 4 = ((Real.sqrt r) ^ 2) ^ 2 := by ring
            _ = r ^ 2 := by rw [hsqrtr_sq]
        have hsqrta_four : (Real.sqrt a) ^ 4 = a ^ 2 := by
          calc
            (Real.sqrt a) ^ 4 = ((Real.sqrt a) ^ 2) ^ 2 := by ring
            _ = a ^ 2 := by rw [hsqrta_sq]
        field_simp [ne_of_gt hNreal, ne_of_gt hσ_pos, ne_of_gt hr_pos]
        rw [hsqrtr_four, hsqrta_four]
        linear_combination r * ha_sq_clear
      have hnoise_baseA : Real.sqrt r * (Real.sqrt a * σ) ≤ A := by
        have heq : Real.sqrt r * (Real.sqrt a * σ) = A :=
          (pow_left_inj₀ hnoise_base_nonneg hA_nonneg
            (by norm_num : (4 : ℕ) ≠ 0)).mp (hnoise_base_four.trans hA_four.symm)
        exact heq.le
      have hnoiseA :
          Real.sqrt r * (Real.sqrt (a / (1 + cfgN.beta)) * σ) ≤ A := by
        calc
          Real.sqrt r * (Real.sqrt (a / (1 + cfgN.beta)) * σ)
              ≤ Real.sqrt r * (Real.sqrt a * σ) := by
                gcongr
          _ ≤ A := hnoise_baseA
      have hfinite_sq :
          (Real.sqrt r * σ / (a * (N : ℝ))) ^ 2 = D ^ 2 := by
        dsimp [D]
        have hsqrt_JΔN_sq :
            (Real.sqrt (Jstar * Δ * (N : ℝ))) ^ 2 =
              Jstar * Δ * (N : ℝ) := Real.sq_sqrt hJN_pos.le
        have hsqrt_NJΔ_sq :
            (Real.sqrt ((N : ℝ) * Jstar * Δ)) ^ 2 =
              (N : ℝ) * Jstar * Δ := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hsqrt_JΔN_sq
        field_simp [ne_of_gt ha_pos, ne_of_gt hNreal, ne_of_gt hJ_pos,
          ne_of_gt hΔ_pos, ne_of_gt hσ_pos, ne_of_gt hr_pos,
          Real.sqrt_ne_zero'.mpr hJN_pos]
        rw [hsqrtr_sq, hsqrt_NJΔ_sq]
        linear_combination -(r * (N : ℝ)) * ha_sq_clear
      have hfinite_nonneg :
          0 ≤ Real.sqrt r * σ / (a * (N : ℝ)) := by positivity
      have hfiniteD : Real.sqrt r * σ / (a * (N : ℝ)) ≤ D := by
        have heq : Real.sqrt r * σ / (a * (N : ℝ)) = D :=
          (pow_left_inj₀ hfinite_nonneg hD_nonneg
            (by norm_num : (2 : ℕ) ≠ 0)).mp hfinite_sq
        exact heq.le
      have hcrossA : 2 * etaN * cfgN.beta / a * Jstar ≤ 2 * A := by
        have hbeta_le : cfgN.beta ≤ 1 := cfgN.beta_mem.2.le
        have hmomentum_nonneg' : 0 ≤ etaN * Jstar / a := by positivity
        have hrewrite : 2 * etaN * cfgN.beta / a * Jstar =
            2 * cfgN.beta * (etaN * Jstar / a) := by ring
        rw [hrewrite]
        have hbeta_momentum :
            cfgN.beta * (etaN * Jstar / a) ≤ etaN * Jstar / a := by
          simpa using (mul_le_mul_of_nonneg_right hbeta_le hmomentum_nonneg')
        linarith only [hbeta_momentum, hmomentumA]
      have hlower :
          Δ / ((N : ℝ) * etaN) + etaN / 2 * Jstar +
              2 * Real.sqrt r * (Real.sqrt (a / (1 + cfgN.beta)) * σ) +
              2 * Real.sqrt r * σ / (a * (N : ℝ)) +
              2 * etaN * cfgN.beta / a * Jstar +
              s * etaN ^ 2 * q / 6 +
              2 * s * etaN ^ 2 * q * cfgN.beta / a ≤
            5 * A + B / 2 + 2 * D + (13 / 6 : ℝ) * E := by
        linear_combination hfirstA + hdir_le + 2 * hnoiseA +
          2 * hfiniteD + hcrossA + hrem1 + hrem2
      linarith only [hlower, hA_nonneg, hB_nonneg, hD_nonneg, hE_nonneg]
    · have hx_one : 1 ≤ x := le_of_not_ge hx
      have ha_one : a = 1 := ha_min.trans (min_eq_right hx_one)
      have hbeta_zero : cfgN.beta = 0 := by
        dsimp [a] at ha_one
        linarith
      have hfirstB : Δ / ((N : ℝ) * etaN) ≤ B := by
        rw [hfirst_eq, ha_one, div_one]
        exact hetaJ_le
      have hx_one' :
          1 ≤ Real.sqrt (Jstar * Δ) /
            (σ * Real.sqrt (r * (N : ℝ))) := by simpa [x] using hx_one
      have hquot_clear :
          σ * Real.sqrt (r * (N : ℝ)) ≤ Real.sqrt (Jstar * Δ) := by
        simpa using
          ((le_div_iff₀ (mul_pos hσ_pos (Real.sqrt_pos.2 hrN_pos))).mp hx_one')
      have hsigma_sq_le : r * σ ^ 2 ≤ Jstar * Δ / (N : ℝ) := by
        have hsquare := mul_self_le_mul_self (by positivity :
          0 ≤ σ * Real.sqrt (r * (N : ℝ))) hquot_clear
        have hsquare_clear : σ ^ 2 * (r * (N : ℝ)) ≤ Jstar * Δ := by
          nlinarith only [hsquare, hsqrt_rN_sq, hsqrt_JΔ_sq]
        apply (le_div_iff₀ hNreal).2
        nlinarith only [hsquare_clear]
      have hsigmaB : Real.sqrt r * σ ≤ B := by
        have hsigma_nonneg : 0 ≤ Real.sqrt r * σ := by positivity
        have hsigma_sq : (Real.sqrt r * σ) ^ 2 = r * σ ^ 2 := by
          rw [mul_pow, hsqrtr_sq]
        apply (sq_le_sq₀ hsigma_nonneg hB_nonneg).mp
        rw [hsigma_sq, hB_sq]
        exact hsigma_sq_le
      have hfiniteB : Real.sqrt r * σ / (a * (N : ℝ)) ≤ B := by
        rw [ha_one, one_mul]
        calc
          Real.sqrt r * σ / (N : ℝ) ≤ Real.sqrt r * σ := by
            have hv : 0 ≤ Real.sqrt r * σ := by positivity
            apply (div_le_iff₀ hNreal).2
            simpa using (mul_le_mul_of_nonneg_left hN_one hv)
          _ ≤ B := hsigmaB
      have hfiniteB' : Real.sqrt r * σ / (N : ℝ) ≤ B := by
        simpa [ha_one] using hfiniteB
      have hunit :
          Δ / ((N : ℝ) * etaN) + etaN / 2 * Jstar +
              2 * Real.sqrt r * (Real.sqrt (a / (1 + cfgN.beta)) * σ) +
              2 * Real.sqrt r * σ / (a * (N : ℝ)) +
              2 * etaN * cfgN.beta / a * Jstar +
              s * etaN ^ 2 * q / 6 +
              2 * s * etaN ^ 2 * q * cfgN.beta / a ≤
            (11 / 2 : ℝ) * B + (13 / 6 : ℝ) * E := by
        rw [ha_one, hbeta_zero]
        norm_num
        linear_combination hfirstB + hdir_le + 2 * hsigmaB +
          2 * hfiniteB' + hrem1 + 2 * hE_nonneg
      linarith only [hunit, hA_nonneg, hB_nonneg, hD_nonneg, hE_nonneg]
  have havg : stochasticAverageNuclearGradient P cfgN N ≤
      10 * (A + B + D + E) := by
    linarith only [hraw', hdropFirst, hdirTerm, hcrossTerm, hscalar]
  have hbranch_irrel
      (h₁ h₂ : theorem_4_15_positiveBranchRateDomain m n N Jstar σ Δ s) :
      theorem_4_15_branchRate m n Jstar σ Δ s N h₁ =
        theorem_4_15_branchRate m n Jstar σ Δ s N h₂ := by
    have hp : h₁ = h₂ := Subsingleton.elim _ _
    subst h₂
    rfl
  have hrate : theorem_4_15_positiveRunBranchRateRealized
        P cfgForHorizon W0 Jstar σ Δ s N
          ⟨hNpos, hwd, hW0, hJstar,
            ⟨⟨_horizon, hJDeltaDom, hrNDom, hbetaQuotDom, hetaDom,
                ⟨_hNrate, hrateFirst, hrateSecond, hprodDom, hrateThird,
                  hrankCube, hrateCurvature⟩⟩,
              hbatch, heta, hbeta⟩, hsource⟩ = A + B + D + E := by
    unfold theorem_4_15_positiveRunBranchRateRealized
    change theorem_4_15_branchRate m n Jstar σ Δ s N _ = A + B + D + E
    rw [hbranch_irrel _ ⟨_hNrate, hrateFirst, hrateSecond, hprodDom,
      hrateThird, hrankCube, hrateCurvature⟩]
    unfold theorem_4_15_branchRate
    simp [A, B, D, E, r, q, realizedSourceSqrtQuot,
      realizedSourceSqrt, realizedSourceQuot, sourceSqrt, sourceQuot]
  rw [hrate]
  simpa [theorem_4_15_positiveRunAverageRealized,
    stochasticAverageNuclearGradientRealized,
    stochasticAverageNuclearGradient, realizedExpectation, cfgN] using havg

theorem theorem_4_15_positive_branch_rate_from_source_assumptions
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (Jstar σ Δ s : ℝ)
    (hfinite : P.objective.HasFiniteInfimum)
    (hthird : ThirdDerivativeBounded P.objective s)
    (hvariance : BoundedVariance P σ)
    (hDelta : sourceObjectiveInitialGap P.objective cfg.W0 hfinite = Δ)
    (cfgForHorizon : ℕ → StochasticMuonConfig m n)
    (hruns : ∀ N : ℕ, horizonDomain N →
      theorem_4_15_positiveRunRealizedForHorizon
        P cfgForHorizon cfg.W0 Jstar σ Δ s N) :
    DomainAsymptoticUpperNatOn
      (fun N => theorem_4_15_positiveRunRealizedForHorizon
        P cfgForHorizon cfg.W0 Jstar σ Δ s N)
      (fun N hN => theorem_4_15_positiveRunAverageRealized
        P cfgForHorizon cfg.W0 Jstar σ Δ s N hN)
      (fun N hN => theorem_4_15_positiveRunBranchRateRealized
        P cfgForHorizon cfg.W0 Jstar σ Δ s N hN)
      (theoremScope "Theorem 4.15 fixed-Jstar positive branch rate" ["T"]) := by
  refine ⟨10, 1, by norm_num, ?_, ?_⟩
  · simp [ConstantRespectsScope, theoremScope]
  · intro N hN _hNlarge
    exact theorem_4_15_positive_source_rate_bound_at_horizon
      P cfgForHorizon cfg.W0 Jstar σ Δ s N hfinite hthird hvariance hDelta hN

/- Scalar extraction of the four displayed positive-branch rate terms.  The
   four coefficient hypotheses are exactly the horizon-independent budgets
   later enforced by the single constant `H`. -/
theorem theorem_4_15_positive_rate_le_accuracy_at_complexity_horizon
    (m n : ℕ) (Jstar σ Δ s H ε : ℝ) (N : ℕ)
    (hJ : 0 < Jstar) (hσ : 0 < σ) (hΔ : 0 < Δ) (hs : 0 ≤ s)
    (hr : 0 < (matrixRankBound m n : ℝ))
    (hε : epsilonDomain ε) (hεone : ε ≤ 1) (hN : horizonDomain N)
    (hHfirst : (40 : ℝ) ^ 4 ≤ H)
    (hHsecond :
      (1600 : ℝ) * (Jstar * Δ) ≤
        H * ((matrixRankBound m n : ℝ) * Jstar * σ ^ 2 * Δ))
    (hHthird :
      (1600 : ℝ) * ((matrixRankBound m n : ℝ) ^ 2 * σ ^ 4) ≤
        H * ((matrixRankBound m n : ℝ) * Jstar * σ ^ 2 * Δ) *
          (Jstar * Δ))
    (hHfourth :
      (40 : ℝ) *
          (s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Δ) ≤
        H * ((matrixRankBound m n : ℝ) * Jstar * σ ^ 2 * Δ) * Jstar)
    (hNlarge :
      H * theorem_4_15_complexityRate m n Jstar σ Δ ε ≤ (N : ℝ)) :
    10 * theorem_4_15_sourceBranchRate m n Jstar σ Δ s N ≤ ε := by
  let r : ℝ := matrixRankBound m n
  let q : ℝ := Real.sqrt (r ^ 3)
  let base : ℝ := r * Jstar * Δ * σ ^ 2
  let A : ℝ := Real.sqrt (Real.sqrt (base / (N : ℝ)))
  let B : ℝ := Real.sqrt (Jstar * Δ / (N : ℝ))
  let D : ℝ := r * σ ^ 2 / Real.sqrt (Jstar * Δ * (N : ℝ))
  let E : ℝ := s * q * Δ / (Jstar * (N : ℝ))
  have hr_nonneg : 0 ≤ r := by dsimp [r]; positivity
  have hr_pos : 0 < r := by simpa [r] using hr
  have hq_nonneg : 0 ≤ q := by dsimp [q]; positivity
  have hbase_pos : 0 < base := by dsimp [base]; positivity
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hεsq_le : ε ^ 2 ≤ ε := by
    have hp : 0 ≤ ε * (1 - ε) :=
      mul_nonneg hε.le (sub_nonneg.mpr hεone)
    nlinarith
  have hεfour_le_sq : ε ^ 4 ≤ ε ^ 2 := by
    have hsquare := (sq_le_sq₀ (sq_nonneg ε) hε.le).2 hεsq_le
    convert hsquare using 1 <;> ring
  have hεfour_le : ε ^ 4 ≤ ε := le_trans hεfour_le_sq hεsq_le
  have hbudget : H * base ≤ (N : ℝ) * ε ^ 4 := by
    have hlarge' : H * base / ε ^ 4 ≤ (N : ℝ) := by
      convert hNlarge using 1 <;>
        simp [theorem_4_15_complexityRate, base, r, div_eq_mul_inv,
          inv_pow] <;> ring
    exact (div_le_iff₀ (pow_pos hε 4)).mp hlarge'
  have hA_nonneg : 0 ≤ A := by dsimp [A]; positivity
  have hB_nonneg : 0 ≤ B := by dsimp [B]; positivity
  have hD_nonneg : 0 ≤ D := by dsimp [D]; positivity
  have hE_nonneg : 0 ≤ E := by dsimp [E]; positivity
  have ht_nonneg : 0 ≤ ε / 40 := div_nonneg hε.le (by norm_num)
  have hA_four : A ^ 4 = base / (N : ℝ) := by
    dsimp [A]
    calc
      Real.sqrt (Real.sqrt (base / (N : ℝ))) ^ 4 =
          (Real.sqrt (Real.sqrt (base / (N : ℝ))) ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (base / (N : ℝ))) ^ 2 := by
        rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
      _ = base / (N : ℝ) := Real.sq_sqrt (div_nonneg hbase_pos.le hNreal.le)
  have hA_cross : (40 : ℝ) ^ 4 * base ≤ (N : ℝ) * ε ^ 4 := by
    exact le_trans (mul_le_mul_of_nonneg_right hHfirst hbase_pos.le) hbudget
  have hA_ratio : base / (N : ℝ) ≤ (ε / 40) ^ 4 := by
    apply (div_le_iff₀ hNreal).2
    have hscaled : base ≤ ((N : ℝ) * ε ^ 4) / (40 : ℝ) ^ 4 :=
      (le_div_iff₀ (by positivity : (0 : ℝ) < 40 ^ 4)).2 (by
        simpa [mul_comm] using hA_cross)
    calc
      base ≤ ((N : ℝ) * ε ^ 4) / (40 : ℝ) ^ 4 := hscaled
      _ = (ε / 40) ^ 4 * (N : ℝ) := by ring
  have hA : A ≤ ε / 40 := by
    exact le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) ht_nonneg
      (by simpa [hA_four] using hA_ratio)
  have hB_sq : B ^ 2 = Jstar * Δ / (N : ℝ) := by
    dsimp [B]
    exact Real.sq_sqrt (by positivity)
  have hB_cross :
      (1600 : ℝ) * (Jstar * Δ) ≤ (N : ℝ) * ε ^ 2 := by
    have hHsecond' :
        (1600 : ℝ) * (Jstar * Δ) ≤ H * base := by
      dsimp [base, r]
      convert hHsecond using 1 <;> ring
    have htofour := le_trans hHsecond' hbudget
    have htosq := mul_le_mul_of_nonneg_left hεfour_le_sq hNreal.le
    exact le_trans htofour (by simpa [mul_comm] using htosq)
  have hB_ratio : Jstar * Δ / (N : ℝ) ≤ (ε / 40) ^ 2 := by
    apply (div_le_iff₀ hNreal).2
    have hscaled : Jstar * Δ ≤ ((N : ℝ) * ε ^ 2) / 1600 :=
      (le_div_iff₀ (by norm_num : (0 : ℝ) < 1600)).2 (by
        simpa [mul_comm] using hB_cross)
    calc
      Jstar * Δ ≤ ((N : ℝ) * ε ^ 2) / 1600 := hscaled
      _ = (ε / 40) ^ 2 * (N : ℝ) := by ring
  have hB : B ≤ ε / 40 := by
    exact (sq_le_sq₀ hB_nonneg ht_nonneg).mp (by simpa [hB_sq] using hB_ratio)
  have hroot_sq :
      (Real.sqrt (Jstar * Δ * (N : ℝ))) ^ 2 =
        Jstar * Δ * (N : ℝ) := Real.sq_sqrt (by positivity)
  have hD_sq :
      D ^ 2 = (r ^ 2 * σ ^ 4) / (Jstar * Δ * (N : ℝ)) := by
    dsimp [D]
    rw [div_pow, mul_pow, hroot_sq]
    ring
  have hD_budget :
      (1600 : ℝ) * (r ^ 2 * σ ^ 4) ≤
        Jstar * Δ * (N : ℝ) * ε ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hbudget (mul_pos hJ hΔ).le
    have htofour :
        (1600 : ℝ) * (r ^ 2 * σ ^ 4) ≤
          (N : ℝ) * ε ^ 4 * (Jstar * Δ) :=
      le_trans (by
        dsimp [r, base]
        convert hHthird using 1 <;> ring) hmul
    have htosq := mul_le_mul_of_nonneg_left hεfour_le_sq
      (mul_nonneg hNreal.le (mul_pos hJ hΔ).le)
    exact le_trans (by simpa [mul_assoc, mul_left_comm, mul_comm] using htofour)
      (by simpa [mul_assoc, mul_left_comm, mul_comm] using htosq)
  have hD_ratio :
      (r ^ 2 * σ ^ 4) / (Jstar * Δ * (N : ℝ)) ≤ (ε / 40) ^ 2 := by
    apply (div_le_iff₀ (by positivity : 0 < Jstar * Δ * (N : ℝ))).2
    have hscaled : r ^ 2 * σ ^ 4 ≤
        (Jstar * Δ * (N : ℝ) * ε ^ 2) / 1600 :=
      (le_div_iff₀ (by norm_num : (0 : ℝ) < 1600)).2 (by
        simpa [mul_comm] using hD_budget)
    calc
      r ^ 2 * σ ^ 4 ≤
          (Jstar * Δ * (N : ℝ) * ε ^ 2) / 1600 := hscaled
      _ = (ε / 40) ^ 2 * (Jstar * Δ * (N : ℝ)) := by ring
  have hD : D ≤ ε / 40 := by
    exact (sq_le_sq₀ hD_nonneg ht_nonneg).mp (by simpa [hD_sq] using hD_ratio)
  have hE_budget :
      (40 : ℝ) * (s * q * Δ) ≤ Jstar * (N : ℝ) * ε := by
    have hmul := mul_le_mul_of_nonneg_right hbudget hJ.le
    have htofour :
        (40 : ℝ) * (s * q * Δ) ≤ (N : ℝ) * ε ^ 4 * Jstar :=
      le_trans (by
        dsimp [r, q, base]
        convert hHfourth using 1 <;> ring) hmul
    have htoeps := mul_le_mul_of_nonneg_left hεfour_le
      (mul_nonneg hNreal.le hJ.le)
    exact le_trans (by simpa [mul_assoc, mul_left_comm, mul_comm] using htofour)
      (by simpa [mul_assoc, mul_left_comm, mul_comm] using htoeps)
  have hE : E ≤ ε / 40 := by
    dsimp [E]
    apply (div_le_iff₀ (mul_pos hJ hNreal)).2
    have hscaled : s * q * Δ ≤ (Jstar * (N : ℝ) * ε) / 40 :=
      (le_div_iff₀ (by norm_num : (0 : ℝ) < 40)).2 (by
        simpa [mul_comm] using hE_budget)
    calc
      s * q * Δ ≤ (Jstar * (N : ℝ) * ε) / 40 := hscaled
      _ = ε / 40 * (Jstar * (N : ℝ)) := by ring
  change 10 * (A + B + D + E) ≤ ε
  linarith

/- Ceiling selection turns the positive-branch horizon rate into the stated
   epsilon complexity.  Positivity of every denominator is extracted from the
   pointwise branch premise and the realized run at horizon one. -/
theorem theorem_4_15_positive_complexity_witness
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (Jstar σ Δ s : ℝ)
    (hfinite : P.objective.HasFiniteInfimum)
    (hthird : ThirdDerivativeBounded P.objective s)
    (hvariance : BoundedVariance P σ)
    (hDelta : sourceObjectiveInitialGap P.objective cfg.W0 hfinite = Δ)
    (hpointwise : theorem_4_15_positiveBranchPointwisePremise m n Jstar σ Δ)
    (cfgForHorizon : ℕ → StochasticMuonConfig m n)
    (hruns : ∀ N : ℕ, horizonDomain N →
      theorem_4_15_positiveRunRealizedForHorizon
        P cfgForHorizon cfg.W0 Jstar σ Δ s N) :
    HorizonNuclearStationarityComplexityWithHorizonRateOn
      (fun N => theorem_4_15_positiveRunRealizedForHorizon
        P cfgForHorizon cfg.W0 Jstar σ Δ s N)
      (fun N hN => theorem_4_15_positiveRunAverageRealized
        P cfgForHorizon cfg.W0 Jstar σ Δ s N hN)
      (fun _N _hN ε => theorem_4_15_complexityRate m n Jstar σ Δ ε)
      (theoremScope "Theorem 4.15 fixed-Jstar epsilon complexity" ["epsilon"]) := by
  let r : ℝ := matrixRankBound m n
  let q : ℝ := Real.sqrt (r ^ 3)
  have hrunOne := hruns 1 (by norm_num [horizonDomain])
  have hrunOne' := hrunOne
  unfold theorem_4_15_positiveRunRealizedForHorizon at hrunOne'
  dsimp at hrunOne'
  rcases hrunOne' with
    ⟨_hOne, _hwdOne, _hW0One, _hJOne, hscheduleOne, _hsourceOne⟩
  rcases hscheduleOne with
    ⟨hscheduleDomOne, _hbatchOne, _hetaOne, _hbetaOne⟩
  rcases hscheduleDomOne with
    ⟨_horizonOne, _hJDeltaSqrtOne, _hrankSqrtOne, hbetaQuotOne,
      _hetaDomOne, _hrateDomOne⟩
  have hdenOne :
      σ * Real.sqrt ((matrixRankBound m n : ℝ) * (1 : ℝ)) ≠ 0 := by
    simpa [sourceQuotDomain] using hbetaQuotOne
  have hσne : σ ≠ 0 := (mul_ne_zero_iff.mp hdenOne).1
  have hσpos : 0 < σ :=
    lt_of_le_of_ne hvariance.nonneg (Ne.symm hσne)
  have hr_nonneg : 0 ≤ r := by dsimp [r]; positivity
  have hr_ne : r ≠ 0 := by
    intro hrzero
    apply hdenOne
    simp [r, hrzero]
  have hr_pos : 0 < r := lt_of_le_of_ne hr_nonneg (Ne.symm hr_ne)
  have hq_pos : 0 < q := by
    dsimp [q]
    exact Real.sqrt_pos.2 (pow_pos hr_pos 3)
  rcases hpointwise with ⟨εpoint, hεpoint, hpointwiseAt⟩
  rcases hpointwiseAt εpoint hεpoint le_rfl with
    ⟨_hεpoint', hregDom, c, hc, hcJ⟩
  have hΔne : Δ ≠ 0 := by
    simpa [theorem_4_15_branchRegimeThresholdDomain, sourceInvDomain] using hregDom
  have hgap_nonneg :
      0 ≤ sourceObjectiveInitialGap P.objective cfg.W0 hfinite := by
    unfold sourceObjectiveInitialGap Objective.sourceFStar
    have hlower : P.objective.fStar ≤ P.objective.f cfg.W0 := by
      simpa [Objective.fStar] using
        (csInf_le hfinite
          (show P.objective.f cfg.W0 ∈ Set.range P.objective.f from ⟨cfg.W0, rfl⟩))
    linarith
  have hΔ_nonneg : 0 ≤ Δ := by simpa [hDelta] using hgap_nonneg
  have hΔpos : 0 < Δ := lt_of_le_of_ne hΔ_nonneg (Ne.symm hΔne)
  have hthresholdPos :
      0 < theorem_4_15_branchRegimeThreshold m n σ Δ εpoint hregDom := by
    dsimp [theorem_4_15_branchRegimeThreshold, realizedSourceSqrt,
      realizedSourceInv, sourceSqrt, sourceInv]
    positivity
  have hJpos : 0 < Jstar :=
    lt_of_lt_of_le (mul_pos hc hthresholdPos) hcJ
  have hs_nonneg : 0 ≤ s :=
    le_trans (norm_nonneg _) (hthird.bound cfg.W0)
  let H : ℝ :=
    max ((40 : ℝ) ^ 4)
      (max ((1600 : ℝ) / (r * σ ^ 2))
        (max ((1600 : ℝ) * r * σ ^ 2 / (Jstar ^ 2 * Δ ^ 2))
          ((40 : ℝ) * s * q / (r * Jstar ^ 2 * σ ^ 2))))
  have hHfirst : (40 : ℝ) ^ 4 ≤ H := by
    dsimp [H]
    exact le_max_left _ _
  have hHsecondRaw : (1600 : ℝ) / (r * σ ^ 2) ≤ H := by
    dsimp [H]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hHthirdRaw :
      (1600 : ℝ) * r * σ ^ 2 / (Jstar ^ 2 * Δ ^ 2) ≤ H := by
    dsimp [H]
    exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_max_right _ _)
  have hHfourthRaw :
      (40 : ℝ) * s * q / (r * Jstar ^ 2 * σ ^ 2) ≤ H := by
    dsimp [H]
    exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
      (le_max_right _ _)
  have hHpos : 0 < H := lt_of_lt_of_le (by norm_num) hHfirst
  have hHsecond :
      (1600 : ℝ) * (Jstar * Δ) ≤
        H * ((matrixRankBound m n : ℝ) * Jstar * σ ^ 2 * Δ) := by
    have hclear := (div_le_iff₀ (mul_pos hr_pos (sq_pos_of_pos hσpos))).mp
      hHsecondRaw
    have hmul := mul_le_mul_of_nonneg_right hclear (mul_pos hJpos hΔpos).le
    dsimp [r] at hmul
    nlinarith
  have hHthird :
      (1600 : ℝ) * ((matrixRankBound m n : ℝ) ^ 2 * σ ^ 4) ≤
        H * ((matrixRankBound m n : ℝ) * Jstar * σ ^ 2 * Δ) *
          (Jstar * Δ) := by
    have hclear :=
      (div_le_iff₀ (mul_pos (sq_pos_of_pos hJpos) (sq_pos_of_pos hΔpos))).mp
        hHthirdRaw
    have hmul := mul_le_mul_of_nonneg_right hclear
      (mul_pos hr_pos (sq_pos_of_pos hσpos)).le
    dsimp [r] at hmul
    nlinarith
  have hHfourth :
      (40 : ℝ) *
          (s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Δ) ≤
        H * ((matrixRankBound m n : ℝ) * Jstar * σ ^ 2 * Δ) * Jstar := by
    have hclear :=
      (div_le_iff₀ (mul_pos (mul_pos hr_pos (sq_pos_of_pos hJpos))
        (sq_pos_of_pos hσpos))).mp hHfourthRaw
    have hmul := mul_le_mul_of_nonneg_right hclear hΔpos.le
    dsimp [r, q] at hmul
    nlinarith
  let base : ℝ := r * Jstar * σ ^ 2 * Δ
  have hbase_pos : 0 < base := by dsimp [base]; positivity
  unfold HorizonNuclearStationarityComplexityWithHorizonRateOn
  refine ⟨2 * H, min 1 (H * base), by positivity,
    lt_min (by norm_num) (mul_pos hHpos hbase_pos), ?_, ?_⟩
  · simp [ConstantRespectsScope, theoremScope, hHpos]
  · intro ε hε hεsmall
    have hεone : ε ≤ 1 := le_trans hεsmall (min_le_left _ _)
    have hεbase : ε ≤ H * base := le_trans hεsmall (min_le_right _ _)
    have hεfour_le : ε ^ 4 ≤ ε := by
      have hp : 0 ≤ ε * (1 - ε) :=
        mul_nonneg hε.le (sub_nonneg.mpr hεone)
      have hsq : ε ^ 2 ≤ ε := by nlinarith
      have hfour : ε ^ 4 ≤ ε ^ 2 := by
        have hsquare := (sq_le_sq₀ (sq_nonneg ε) hε.le).2 hsq
        convert hsquare using 1 <;> ring
      exact le_trans hfour hsq
    let rate : ℝ := theorem_4_15_complexityRate m n Jstar σ Δ ε
    have hrate_pos : 0 < rate := by
      dsimp [rate, theorem_4_15_complexityRate]
      have hεpos : 0 < ε := hε
      positivity
    have hHrate_one : 1 ≤ H * rate := by
      have hbase_le : ε ^ 4 ≤ H * base := le_trans hεfour_le hεbase
      have hdiv : 1 ≤ H * base / ε ^ 4 :=
        (le_div_iff₀ (pow_pos hε 4)).2 (by simpa using hbase_le)
      have heq : H * rate = H * base / ε ^ 4 := by
        dsimp [rate, base, r, theorem_4_15_complexityRate]
        field_simp [ne_of_gt hε]
      simpa [heq] using hdiv
    let N : ℕ := max 1 (Nat.ceil (H * rate))
    have hN : horizonDomain N := by
      dsimp [horizonDomain, N]
      omega
    have hNlower : H * rate ≤ (N : ℝ) := by
      have hceil : H * rate ≤ (Nat.ceil (H * rate) : ℕ) := Nat.le_ceil _
      have hceilmax : Nat.ceil (H * rate) ≤ N := by
        dsimp [N]
        exact le_max_right _ _
      exact le_trans hceil (by exact_mod_cast hceilmax)
    have hceilOne : 1 ≤ Nat.ceil (H * rate) := by
      have hceil := Nat.le_ceil (H * rate)
      exact_mod_cast le_trans hHrate_one hceil
    have hNeq : N = Nat.ceil (H * rate) := by
      dsimp [N]
      exact max_eq_right hceilOne
    have hNupper : (N : ℝ) ≤ 2 * (H * rate) := by
      rw [hNeq]
      have hceilLt := Nat.ceil_lt_add_one (mul_nonneg hHpos.le hrate_pos.le)
      exact le_trans hceilLt.le (by linarith)
    have hrun := hruns N hN
    have havgBound := theorem_4_15_positive_source_rate_bound_at_horizon
      P cfgForHorizon cfg.W0 Jstar σ Δ s N
      hfinite hthird hvariance hDelta hrun
    have hscalar :=
      theorem_4_15_positive_rate_le_accuracy_at_complexity_horizon
        m n Jstar σ Δ s H ε N hJpos hσpos hΔpos hs_nonneg hr_pos
        hε hεone hN hHfirst hHsecond hHthird hHfourth (by simpa [rate] using hNlower)
    have hbranchSource
        (hdom : theorem_4_15_positiveBranchRateDomain m n N Jstar σ Δ s) :
        theorem_4_15_branchRate m n Jstar σ Δ s N hdom =
          theorem_4_15_sourceBranchRate m n Jstar σ Δ s N := by
      rcases hdom with
        ⟨_horizon, hfirst, hsecond, hthirdSqrt, hthirdQuot,
          hrankCube, hcurvature⟩
      simp [theorem_4_15_branchRate, theorem_4_15_sourceBranchRate,
        realizedSourceSqrtQuot, realizedSourceSqrt, realizedSourceQuot,
        sourceSqrt, sourceQuot]
    have hrateEq :
        theorem_4_15_positiveRunBranchRateRealized
            P cfgForHorizon cfg.W0 Jstar σ Δ s N hrun =
          theorem_4_15_sourceBranchRate m n Jstar σ Δ s N := by
      unfold theorem_4_15_positiveRunBranchRateRealized
      dsimp
      exact hbranchSource _
    refine ⟨N, hrun, ?_, ?_⟩
    · exact le_trans havgBound (by simpa [hrateEq] using hscalar)
    · simpa [rate, mul_assoc] using hNupper

/- The requested accuracy in the public complexity clause is reindexed to the
   internal accuracy used by the Appendix B.4 schedule.  The scale absorbs the
   exact coefficient in the formula-level otherwise-branch estimate. -/
/- A source-small-`J` run cannot make the selected horizon and stepsize
   independently small.  Multiplying the two lower theta bounds and then
   using the printed Appendix B.4 scales gives the exact travel budget below.
   This is a source-derived Track-A invariant: it uses neither the cross/Jstar
   estimate nor an average-gradient conclusion. -/
theorem theorem_4_15_otherwise_source_small_j_generated_run_travel_budget
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n)
    (cfgForAccuracyHorizon : ℝ → ℕ → StochasticMuonConfig m n)
    (W0 : Mat m n) (σ Δ ε C s : ℝ)
    (betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ)
    (N : ℕ)
    (hN : theorem_4_15_otherwiseSourceSmallJGeneratedRunForAccuracyHorizon P
      cfgForAccuracyHorizon W0 σ Δ ε C s
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N) :
    horizonLower * etaLower *
        Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) ^ 2 * Δ / ε ≤
      (N : ℝ) * (cfgForAccuracyHorizon ε N).eta 0 := by
  rcases hN with
    ⟨_horizon, hfinite, hDelta, _hthird, hvariance, _hwd, _hW0, hschedule,
      _hsource, hHorizon, _hregDom, hregime⟩
  rcases hschedule with
    ⟨hscheduleDom, _hbatch, _hbeta, heta, _hconstEta⟩
  rcases hscheduleDom with ⟨_horizon', _hbetaDom, _hrankDom, hetaDom⟩
  rcases heta with ⟨hetaLowerPos, _hetaOrder, hetaLowerBound, _hetaUpperBound⟩
  rcases hHorizon with
    ⟨_horizonLowerPos, _horizonOrder, horizonLowerBound, _horizonUpperBound⟩
  have hσne : σ ≠ 0 := by
    simpa [sourceQuotDomain] using hetaDom
  have hεne : ε ≠ 0 := ne_of_gt hregime.1
  have hσpos : 0 < σ := lt_of_le_of_ne hvariance.nonneg (Ne.symm hσne)
  have hΔnonneg : 0 ≤ Δ := by
    rw [← hDelta]
    unfold sourceObjectiveInitialGap Objective.sourceFStar
    linarith [objective_value_ge_fStar_early P.objective hfinite W0]
  have hetaRateNonneg :
      0 ≤ theorem_4_15_otherwiseEtaRate m n σ Δ ε N := by
    unfold theorem_4_15_otherwiseEtaRate sourceQuot
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) hΔnonneg)
        (sq_nonneg ε))
      (by positivity)
  have hproduct :
      (horizonLower * theorem_4_15_otherwiseComplexityRate m n σ ε) *
          (etaLower * theorem_4_15_otherwiseEtaRate m n σ Δ ε N) ≤
        (N : ℝ) * (cfgForAccuracyHorizon ε N).eta 0 :=
    calc
      (horizonLower * theorem_4_15_otherwiseComplexityRate m n σ ε) *
            (etaLower * theorem_4_15_otherwiseEtaRate m n σ Δ ε N) ≤
          (N : ℝ) *
            (etaLower * theorem_4_15_otherwiseEtaRate m n σ Δ ε N) :=
        mul_le_mul_of_nonneg_right horizonLowerBound (by
          exact mul_nonneg hetaLowerPos.le hetaRateNonneg)
      _ ≤ (N : ℝ) * (cfgForAccuracyHorizon ε N).eta 0 :=
        mul_le_mul_of_nonneg_left hetaLowerBound (by positivity)
  rw [mul_mul_mul_comm,
    theorem_4_15_otherwise_horizon_eta_product m n σ Δ ε N hσne hεne] at hproduct
  simpa [div_eq_mul_inv, mul_assoc] using hproduct

/- Assumption 3.3 is monotone in its advertised noise scale.  This elementary
   bridge matters for the source-boundary investigation because the printed
   otherwise schedule requires a positive `sigma`, while a deterministic
   oracle has actual variance zero.  Enlarging that valid upper bound does not
   introduce stochastic noise or assume any generated-process conclusion. -/
theorem BoundedVariance.mono_noiseScale
    {xi : Type*} [MeasurableSpace xi] {m n : ℕ}
    {P : StochasticProblem xi m n} {sigma tau : ℝ}
    (hvariance : BoundedVariance P sigma) (hscale : sigma ≤ tau) :
    BoundedVariance P tau := by
  constructor
  · exact hvariance.nonneg.trans hscale
  · exact hvariance.unbiased
  · intro W
    obtain ⟨hwd, hbound⟩ := hvariance.variance W
    refine ⟨hwd, hbound.trans ?_⟩
    nlinarith [hvariance.nonneg]

theorem deterministicOracleProblem_boundedVariance_of_nonneg
    {m n : ℕ} (P : Objective m n) {sigma : ℝ} (hsigma : 0 ≤ sigma) :
    BoundedVariance (deterministicOracleProblem P) sigma := by
  exact (deterministicOracleProblem_boundedVariance_zero P).mono_noiseScale hsigma

/- For a deterministic oracle, the two stochastic Hessian averages occurring
   at the exact Theorem 4.15 boundary reduce to finite sums on the generated
   deterministic-momentum Algorithm 1 states.  These are definitional process
   transfers, not bounds: in particular, the directional and cross objects
   remain distinct after the reduction. -/
def deterministicMomentumHessianDirectionalTerm {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMomentumMuonConfig m n)
    (t : ℕ) : ℝ :=
  let state := deterministicMomentumMuonState P cfg t
  let D := orthogonalizedDirection state.M
  hessianBilinear P state.W D D

def deterministicMomentumHessianDirectionalAverage {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMomentumMuonConfig m n)
    (T : ℕ) : ℝ :=
  ((T : ℝ)⁻¹) * Finset.sum (Finset.range T)
    (fun t => deterministicMomentumHessianDirectionalTerm P cfg t)

def deterministicMomentumHessianCrossTerm {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMomentumMuonConfig m n)
    (t : ℕ) : ℝ :=
  let state := deterministicMomentumMuonState P cfg t
  let nextState := deterministicMomentumMuonState P cfg (t + 1)
  let Dg := orthogonalizedDirection (P.grad state.W - P.grad nextState.W)
  let D := orthogonalizedDirection state.M
  hessianBilinear P state.W Dg D

def deterministicMomentumHessianCrossAverage {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMomentumMuonConfig m n)
    (T : ℕ) : ℝ :=
  ((T : ℝ)⁻¹) * Finset.sum (Finset.range (T - 1))
    (fun t => deterministicMomentumHessianCrossTerm P cfg t)

theorem deterministicOracle_hessianDirectionalTerm_eq
    {m n : ℕ} (P : Objective m n)
    (cfg : DeterministicMomentumMuonConfig m n)
    (omega : SamplePath Unit (deterministicOracleConfig cfg).batchSize)
    (t : ℕ) :
    stochasticHessianDirectionalTerm (deterministicOracleProblem P)
        (deterministicOracleConfig cfg) omega t =
      deterministicMomentumHessianDirectionalTerm P cfg t := by
  unfold stochasticHessianDirectionalTerm stochasticMuonDirection
    deterministicMomentumHessianDirectionalTerm
  rw [deterministicOracleProblem_objective,
    deterministicOracle_state_eq]

theorem deterministicOracle_hessianCrossTerm_eq
    {m n : ℕ} (P : Objective m n)
    (cfg : DeterministicMomentumMuonConfig m n)
    (omega : SamplePath Unit (deterministicOracleConfig cfg).batchSize)
    (t : ℕ) :
    stochasticHessianCrossTerm (deterministicOracleProblem P)
        (deterministicOracleConfig cfg) omega t =
      deterministicMomentumHessianCrossTerm P cfg t := by
  unfold stochasticHessianCrossTerm stochasticGradientDifferenceDirection
    stochasticMuonDirection deterministicMomentumHessianCrossTerm
  rw [deterministicOracleProblem_objective,
    deterministicOracle_state_eq, deterministicOracle_state_eq]

theorem deterministicOracle_hessianDirectionalAverageRealized_eq
    {m n : ℕ} (P : Objective m n)
    (cfg : DeterministicMomentumMuonConfig m n) (T : ℕ)
    (hwd : stochasticHessianDirectionalAverageWellDefined
      (deterministicOracleProblem P) (deterministicOracleConfig cfg) T) :
    stochasticHessianDirectionalAverageRealized (deterministicOracleProblem P)
        (deterministicOracleConfig cfg) T hwd =
      deterministicMomentumHessianDirectionalAverage P cfg T := by
  letI : IsProbabilityMeasure (deterministicOracleProblem P).sampleLaw :=
    (deterministicOracleProblem P).isProbability_sampleLaw
  letI : IsProbabilityMeasure
      (samplePathLaw (deterministicOracleProblem P)
        (deterministicOracleConfig cfg).batchSize) := by
    dsimp [samplePathLaw]
    infer_instance
  unfold stochasticHessianDirectionalAverageRealized
    deterministicMomentumHessianDirectionalAverage realizedExpectation
  have hconstant :
      (fun omega : SamplePath Unit (deterministicOracleConfig cfg).batchSize =>
        Finset.sum (Finset.range T)
          (fun t => stochasticHessianDirectionalTerm
            (deterministicOracleProblem P) (deterministicOracleConfig cfg) omega t)) =
      (fun _ => Finset.sum (Finset.range T)
        (fun t => deterministicMomentumHessianDirectionalTerm P cfg t)) := by
    funext omega
    apply Finset.sum_congr rfl
    intro t _ht
    exact deterministicOracle_hessianDirectionalTerm_eq P cfg omega t
  rw [hconstant, integral_const, measureReal_univ_eq_one, one_smul]

theorem deterministicOracle_hessianCrossAverageRealized_eq
    {m n : ℕ} (P : Objective m n)
    (cfg : DeterministicMomentumMuonConfig m n) (T : ℕ)
    (hwd : stochasticHessianCrossAverageWellDefined
      (deterministicOracleProblem P) (deterministicOracleConfig cfg) T) :
    stochasticHessianCrossAverageRealized (deterministicOracleProblem P)
        (deterministicOracleConfig cfg) T hwd =
      deterministicMomentumHessianCrossAverage P cfg T := by
  letI : IsProbabilityMeasure (deterministicOracleProblem P).sampleLaw :=
    (deterministicOracleProblem P).isProbability_sampleLaw
  letI : IsProbabilityMeasure
      (samplePathLaw (deterministicOracleProblem P)
        (deterministicOracleConfig cfg).batchSize) := by
    dsimp [samplePathLaw]
    infer_instance
  unfold stochasticHessianCrossAverageRealized
    deterministicMomentumHessianCrossAverage realizedExpectation
  have hconstant :
      (fun omega : SamplePath Unit (deterministicOracleConfig cfg).batchSize =>
        Finset.sum (Finset.range (T - 1))
          (fun t => stochasticHessianCrossTerm
            (deterministicOracleProblem P) (deterministicOracleConfig cfg) omega t)) =
      (fun _ => Finset.sum (Finset.range (T - 1))
        (fun t => deterministicMomentumHessianCrossTerm P cfg t)) := by
    funext omega
    apply Finset.sum_congr rfl
    intro t _ht
    exact deterministicOracle_hessianCrossTerm_eq P cfg omega t
  rw [hconstant, integral_const, measureReal_univ_eq_one, one_smul]

theorem deterministicOracle_hessianJstarRealized_eq
    {m n : ℕ} (P : Objective m n)
    (cfg : DeterministicMomentumMuonConfig m n) (T : ℕ)
    (hwd : stochasticHessianJstarWellDefined
      (deterministicOracleProblem P) (deterministicOracleConfig cfg) T) :
    stochasticHessianJstarRealized (deterministicOracleProblem P)
        (deterministicOracleConfig cfg) T hwd =
      max (deterministicMomentumHessianCrossAverage P cfg T)
        (deterministicMomentumHessianDirectionalAverage P cfg T) := by
  unfold stochasticHessianJstarRealized
  rw [deterministicOracle_hessianCrossAverageRealized_eq,
    deterministicOracle_hessianDirectionalAverageRealized_eq]

/- The fixed nonperiodic counterexample documented in the root Muon module is
   built from the following positive-ray data.  Keeping these scalar pieces
   separate records the exact candidate before the smooth negative-half-line
   extension is chosen: no arbitrary trajectory or source conclusion is
   packaged into these definitions. -/
def theorem_4_15_nonperiodicCandidateQ (x : ℝ) : ℝ :=
  (1 + x) ^ (-(6 : ℝ) / 5)

def theorem_4_15_nonperiodicCandidatePhase (x : ℝ) : ℝ :=
  (12 : ℝ) / 7 * ((1 + x) ^ ((7 : ℝ) / 5) - 1)

def theorem_4_15_nonperiodicCandidateP (x : ℝ) : ℝ :=
  theorem_4_15_nonperiodicCandidateQ x *
    (2 + Real.sin (theorem_4_15_nonperiodicCandidatePhase x))

def theorem_4_15_nonperiodicCandidatePositiveProfile (x : ℝ) : ℝ :=
  2 - theorem_4_15_nonperiodicCandidateP x -
    ∫ u in 0..x, theorem_4_15_nonperiodicCandidateP u

/- A global positive replacement for `1+x`.  It equals `1+x` on the whole
   generated ray `x ≥ 0`, is exactly `1` on `x ≤ -1`, and stays positive in
   the transition region.  Substituting it into the positive-ray formulas
   gives a fixed smooth negative-half-line extension without a nonsmooth
   piecewise boundary. -/
def theorem_4_15_nonperiodicCandidateGlobalZ (x : ℝ) : ℝ :=
  1 + x * Real.smoothTransition (x + 1)

def theorem_4_15_nonperiodicCandidateGlobalQ (x : ℝ) : ℝ :=
  theorem_4_15_nonperiodicCandidateGlobalZ x ^ (-(6 : ℝ) / 5)

def theorem_4_15_nonperiodicCandidateGlobalPhase (x : ℝ) : ℝ :=
  (12 : ℝ) / 7 *
    (theorem_4_15_nonperiodicCandidateGlobalZ x ^ ((7 : ℝ) / 5) - 1)

def theorem_4_15_nonperiodicCandidateGlobalP (x : ℝ) : ℝ :=
  theorem_4_15_nonperiodicCandidateGlobalQ x *
    (2 + Real.sin (theorem_4_15_nonperiodicCandidateGlobalPhase x))

def theorem_4_15_nonperiodicCandidateGlobalProfile (x : ℝ) : ℝ :=
  2 - theorem_4_15_nonperiodicCandidateGlobalP x -
    ∫ u in 0..x, theorem_4_15_nonperiodicCandidateGlobalP u

theorem theorem_4_15_nonperiodicCandidateGlobalZ_pos (x : ℝ) :
    0 < theorem_4_15_nonperiodicCandidateGlobalZ x := by
  rcases le_or_gt x (-1) with hx | hx
  · rw [theorem_4_15_nonperiodicCandidateGlobalZ,
      Real.smoothTransition.zero_of_nonpos (by linarith)]
    norm_num
  · rcases le_or_gt 0 x with hx0 | hx0
    · have ht := Real.smoothTransition.nonneg (x + 1)
      unfold theorem_4_15_nonperiodicCandidateGlobalZ
      positivity
    · have ht : x ≤ x * Real.smoothTransition (x + 1) := by
        simpa using mul_le_mul_of_nonpos_left
          (Real.smoothTransition.le_one (x + 1)) hx0.le
      unfold theorem_4_15_nonperiodicCandidateGlobalZ
      linarith

theorem theorem_4_15_smoothTransition_one_half :
    Real.smoothTransition ((1 : ℝ) / 2) = 1 / 2 := by
  unfold Real.smoothTransition
  norm_num
  have ha : 0 < expNegInvGlue ((1 : ℝ) / 2) :=
    expNegInvGlue.pos_of_pos (by norm_num)
  apply (div_eq_iff (ne_of_gt (add_pos ha ha))).2
  ring

/- The global cutoff base is not merely pointwise positive: it stays uniformly
   away from zero.  This quantitative form is what makes all negative powers
   and their derivatives uniformly bounded on the compact transition region. -/
theorem theorem_4_15_nonperiodicCandidateGlobalZ_lower (x : ℝ) :
    (1 : ℝ) / 2 ≤ theorem_4_15_nonperiodicCandidateGlobalZ x := by
  rcases le_or_gt x (-1) with hx | hx
  · rw [theorem_4_15_nonperiodicCandidateGlobalZ,
      Real.smoothTransition.zero_of_nonpos (by linarith)]
    norm_num
  · rcases le_or_gt x (-(1 : ℝ) / 2) with hxhalf | hxhalf
    · have hxnonpos : x ≤ 0 := by linarith
      have hxlower : -(1 : ℝ) < x := hx
      have ht_nonneg := Real.smoothTransition.nonneg (x + 1)
      have ht_half : Real.smoothTransition (x + 1) ≤ (1 : ℝ) / 2 := by
        rw [← theorem_4_15_smoothTransition_one_half]
        exact Real.smoothTransition.monotone (by linarith)
      have hmul : -(1 : ℝ) / 2 ≤
          x * Real.smoothTransition (x + 1) := by
        have hxmul : -Real.smoothTransition (x + 1) ≤
            x * Real.smoothTransition (x + 1) := by
          nlinarith
        linarith
      unfold theorem_4_15_nonperiodicCandidateGlobalZ
      linarith
    · have hxlower : -(1 : ℝ) / 2 ≤ x := hxhalf.le
      have ht_nonneg := Real.smoothTransition.nonneg (x + 1)
      have ht_one := Real.smoothTransition.le_one (x + 1)
      rcases le_or_gt 0 x with hx0 | hx0
      · unfold theorem_4_15_nonperiodicCandidateGlobalZ
        have hmul : 0 ≤ x * Real.smoothTransition (x + 1) :=
          mul_nonneg hx0 ht_nonneg
        linarith
      · have hmul : -(1 : ℝ) / 2 ≤
            x * Real.smoothTransition (x + 1) := by
          nlinarith
        unfold theorem_4_15_nonperiodicCandidateGlobalZ
        linarith

theorem theorem_4_15_nonperiodicCandidateGlobalQ_upper (x : ℝ) :
    theorem_4_15_nonperiodicCandidateGlobalQ x ≤
      ((1 : ℝ) / 2) ^ (-(6 : ℝ) / 5) := by
  unfold theorem_4_15_nonperiodicCandidateGlobalQ
  exact Real.rpow_le_rpow_of_nonpos (by norm_num)
    (theorem_4_15_nonperiodicCandidateGlobalZ_lower x) (by norm_num)

theorem theorem_4_15_nonperiodicCandidateGlobalP_nonneg (x : ℝ) :
    0 ≤ theorem_4_15_nonperiodicCandidateGlobalP x := by
  unfold theorem_4_15_nonperiodicCandidateGlobalP
  have hq : 0 ≤ theorem_4_15_nonperiodicCandidateGlobalQ x :=
    Real.rpow_nonneg (le_of_lt (theorem_4_15_nonperiodicCandidateGlobalZ_pos x)) _
  have hs : (0 : ℝ) ≤
      2 + Real.sin (theorem_4_15_nonperiodicCandidateGlobalPhase x) := by
    linarith [Real.neg_one_le_sin
      (theorem_4_15_nonperiodicCandidateGlobalPhase x)]
  positivity

theorem theorem_4_15_nonperiodicCandidateGlobalP_upper (x : ℝ) :
    theorem_4_15_nonperiodicCandidateGlobalP x ≤
      3 * (((1 : ℝ) / 2) ^ (-(6 : ℝ) / 5)) := by
  unfold theorem_4_15_nonperiodicCandidateGlobalP
  have hq_nonneg : 0 ≤ theorem_4_15_nonperiodicCandidateGlobalQ x :=
    Real.rpow_nonneg (le_of_lt (theorem_4_15_nonperiodicCandidateGlobalZ_pos x)) _
  have hosc : 2 + Real.sin
      (theorem_4_15_nonperiodicCandidateGlobalPhase x) ≤ (3 : ℝ) := by
    linarith [Real.sin_le_one
      (theorem_4_15_nonperiodicCandidateGlobalPhase x)]
  calc
    theorem_4_15_nonperiodicCandidateGlobalQ x *
          (2 + Real.sin (theorem_4_15_nonperiodicCandidateGlobalPhase x))
        ≤ theorem_4_15_nonperiodicCandidateGlobalQ x * 3 :=
          mul_le_mul_of_nonneg_left hosc hq_nonneg
    _ ≤ (((1 : ℝ) / 2) ^ (-(6 : ℝ) / 5)) * 3 :=
      mul_le_mul_of_nonneg_right
        (theorem_4_15_nonperiodicCandidateGlobalQ_upper x) (by norm_num)
    _ = 3 * (((1 : ℝ) / 2) ^ (-(6 : ℝ) / 5)) := by ring

theorem theorem_4_15_nonperiodicCandidateGlobalZ_eq {x : ℝ} (hx : 0 ≤ x) :
    theorem_4_15_nonperiodicCandidateGlobalZ x = 1 + x := by
  rw [theorem_4_15_nonperiodicCandidateGlobalZ,
    Real.smoothTransition.one_of_one_le (by linarith)]
  ring

theorem theorem_4_15_nonperiodicCandidateGlobalZ_contDiff_three :
    ContDiff ℝ 3 theorem_4_15_nonperiodicCandidateGlobalZ := by
  unfold theorem_4_15_nonperiodicCandidateGlobalZ
  fun_prop

theorem theorem_4_15_nonperiodicCandidateGlobalQ_contDiff_three :
    ContDiff ℝ 3 theorem_4_15_nonperiodicCandidateGlobalQ := by
  unfold theorem_4_15_nonperiodicCandidateGlobalQ
  exact theorem_4_15_nonperiodicCandidateGlobalZ_contDiff_three.rpow_const_of_ne
    (fun x => ne_of_gt (theorem_4_15_nonperiodicCandidateGlobalZ_pos x))

theorem theorem_4_15_nonperiodicCandidateGlobalPhase_contDiff_three :
    ContDiff ℝ 3 theorem_4_15_nonperiodicCandidateGlobalPhase := by
  unfold theorem_4_15_nonperiodicCandidateGlobalPhase
  exact contDiff_const.mul
    ((theorem_4_15_nonperiodicCandidateGlobalZ_contDiff_three.rpow_const_of_ne
      (fun x => ne_of_gt (theorem_4_15_nonperiodicCandidateGlobalZ_pos x))).sub
        contDiff_const)

theorem theorem_4_15_nonperiodicCandidateGlobalP_contDiff_three :
    ContDiff ℝ 3 theorem_4_15_nonperiodicCandidateGlobalP := by
  unfold theorem_4_15_nonperiodicCandidateGlobalP
  exact theorem_4_15_nonperiodicCandidateGlobalQ_contDiff_three.mul
    (contDiff_const.add theorem_4_15_nonperiodicCandidateGlobalPhase_contDiff_three.sin)

theorem theorem_4_15_nonperiodicCandidateGlobalIntegral_hasDerivAt (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => ∫ u in 0..y, theorem_4_15_nonperiodicCandidateGlobalP u)
      (theorem_4_15_nonperiodicCandidateGlobalP x) x := by
  have hcont := theorem_4_15_nonperiodicCandidateGlobalP_contDiff_three.continuous
  exact intervalIntegral.integral_hasDerivAt_right
    (hcont.intervalIntegrable 0 x)
    (hcont.stronglyMeasurableAtFilter volume (nhds x)) hcont.continuousAt

theorem theorem_4_15_nonperiodicCandidateGlobalIntegral_contDiff_three :
    ContDiff ℝ 3
      (fun x : ℝ => ∫ u in 0..x, theorem_4_15_nonperiodicCandidateGlobalP u) := by
  rw [show (3 : WithTop ℕ∞) = 2 + 1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun x =>
      (theorem_4_15_nonperiodicCandidateGlobalIntegral_hasDerivAt x).differentiableAt,
    ?_, ?_⟩
  · intro h
    norm_num at h
  · have hderiv :
        deriv (fun x : ℝ =>
          ∫ u in 0..x, theorem_4_15_nonperiodicCandidateGlobalP u) =
          theorem_4_15_nonperiodicCandidateGlobalP := by
      funext x
      exact (theorem_4_15_nonperiodicCandidateGlobalIntegral_hasDerivAt x).deriv
    rw [hderiv]
    exact theorem_4_15_nonperiodicCandidateGlobalP_contDiff_three.of_le (by norm_num)

theorem theorem_4_15_nonperiodicCandidateGlobalProfile_contDiff_three :
    ContDiff ℝ 3 theorem_4_15_nonperiodicCandidateGlobalProfile := by
  unfold theorem_4_15_nonperiodicCandidateGlobalProfile
  exact (contDiff_const.sub
    theorem_4_15_nonperiodicCandidateGlobalP_contDiff_three).sub
      theorem_4_15_nonperiodicCandidateGlobalIntegral_contDiff_three

theorem theorem_4_15_nonperiodicCandidateGlobalP_eq {x : ℝ} (hx : 0 ≤ x) :
    theorem_4_15_nonperiodicCandidateGlobalP x =
      theorem_4_15_nonperiodicCandidateP x := by
  simp [theorem_4_15_nonperiodicCandidateGlobalP,
    theorem_4_15_nonperiodicCandidateGlobalQ,
    theorem_4_15_nonperiodicCandidateGlobalPhase,
    theorem_4_15_nonperiodicCandidateP,
    theorem_4_15_nonperiodicCandidateQ,
    theorem_4_15_nonperiodicCandidatePhase,
    theorem_4_15_nonperiodicCandidateGlobalZ_eq hx]

theorem theorem_4_15_nonperiodicCandidateGlobalProfile_eq
    {x : ℝ} (hx : 0 ≤ x) :
    theorem_4_15_nonperiodicCandidateGlobalProfile x =
      theorem_4_15_nonperiodicCandidatePositiveProfile x := by
  have hint :
      (∫ u in 0..x, theorem_4_15_nonperiodicCandidateGlobalP u) =
        ∫ u in 0..x, theorem_4_15_nonperiodicCandidateP u := by
    apply intervalIntegral.integral_congr
    intro u hu
    apply theorem_4_15_nonperiodicCandidateGlobalP_eq
    rw [Set.mem_uIcc] at hu
    rcases hu with hu | hu <;> linarith
  simp [theorem_4_15_nonperiodicCandidateGlobalProfile,
    theorem_4_15_nonperiodicCandidatePositiveProfile,
    theorem_4_15_nonperiodicCandidateGlobalP_eq hx, hint]

theorem theorem_4_15_nonperiodicCandidateQ_integrableOn_Ioi :
    IntegrableOn theorem_4_15_nonperiodicCandidateQ (Set.Ioi 0) := by
  change IntegrableOn (fun x : ℝ => (1 + x) ^ (-(6 : ℝ) / 5)) (Set.Ioi 0)
  simpa only [add_comm] using
    (integrableOn_add_rpow_Ioi_of_lt
      (a := (-(6 : ℝ) / 5)) (c := (0 : ℝ)) (m := (1 : ℝ))
      (by norm_num) (by norm_num))

theorem theorem_4_15_nonperiodicCandidateGlobalP_integrableOn_Ioi :
    IntegrableOn theorem_4_15_nonperiodicCandidateGlobalP (Set.Ioi 0) := by
  have hmajorant : IntegrableOn
      (fun x : ℝ => 3 * theorem_4_15_nonperiodicCandidateQ x) (Set.Ioi 0) := by
    simpa [smul_eq_mul] using
      theorem_4_15_nonperiodicCandidateQ_integrableOn_Ioi.const_mul 3
  refine Integrable.mono' hmajorant
    theorem_4_15_nonperiodicCandidateGlobalP_contDiff_three.continuous.aestronglyMeasurable
    ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 ≤ x := hx.le
  rw [Real.norm_eq_abs,
    abs_of_nonneg (theorem_4_15_nonperiodicCandidateGlobalP_nonneg x),
    theorem_4_15_nonperiodicCandidateGlobalP_eq hx0]
  have hq : 0 ≤ theorem_4_15_nonperiodicCandidateQ x :=
    Real.rpow_nonneg (by linarith : 0 ≤ 1 + x) _
  have hosc : 2 + Real.sin
      (theorem_4_15_nonperiodicCandidatePhase x) ≤ (3 : ℝ) := by
    linarith [Real.sin_le_one (theorem_4_15_nonperiodicCandidatePhase x)]
  simpa [theorem_4_15_nonperiodicCandidateP, mul_comm] using
    mul_le_mul_of_nonneg_left hosc hq

theorem theorem_4_15_nonperiodicCandidateGlobalP_integrableOn_Ici :
    IntegrableOn theorem_4_15_nonperiodicCandidateGlobalP (Set.Ici 0) := by
  exact theorem_4_15_nonperiodicCandidateGlobalP_integrableOn_Ioi.congr_set_ae
    Ioi_ae_eq_Ici.symm

/- The positive ray contributes only a finite total amount because `P` is
   dominated by the integrable `(1+x)^(-6/5)` envelope.  On the negative ray,
   orientation of the interval integral makes the same term nonnegative.
   Together with the global pointwise bound on `P`, this gives an explicit
   global lower bound for the fixed objective profile. -/
theorem theorem_4_15_nonperiodicCandidateGlobalProfile_lower (x : ℝ) :
    2 - 3 * (((1 : ℝ) / 2) ^ (-(6 : ℝ) / 5)) -
        (∫ u in Set.Ici (0 : ℝ),
          theorem_4_15_nonperiodicCandidateGlobalP u) ≤
      theorem_4_15_nonperiodicCandidateGlobalProfile x := by
  let C : ℝ := 3 * (((1 : ℝ) / 2) ^ (-(6 : ℝ) / 5))
  have hPupper : theorem_4_15_nonperiodicCandidateGlobalP x ≤ C := by
    simpa [C] using theorem_4_15_nonperiodicCandidateGlobalP_upper x
  have htotal_nonneg : 0 ≤
      ∫ u in Set.Ici (0 : ℝ), theorem_4_15_nonperiodicCandidateGlobalP u :=
    MeasureTheory.setIntegral_nonneg_of_ae
      (Filter.Eventually.of_forall
        theorem_4_15_nonperiodicCandidateGlobalP_nonneg)
  rcases le_or_gt 0 x with hx | hx
  · have hint_le :
        (∫ u in 0..x, theorem_4_15_nonperiodicCandidateGlobalP u) ≤
          ∫ u in Set.Ici (0 : ℝ),
            theorem_4_15_nonperiodicCandidateGlobalP u := by
      rw [intervalIntegral.integral_of_le hx]
      exact MeasureTheory.setIntegral_mono_set
        theorem_4_15_nonperiodicCandidateGlobalP_integrableOn_Ici
        (Filter.Eventually.of_forall
          theorem_4_15_nonperiodicCandidateGlobalP_nonneg)
        (Filter.Eventually.of_forall fun u hu => hu.1.le)
    unfold theorem_4_15_nonperiodicCandidateGlobalProfile
    dsimp [C] at hPupper
    linarith
  · have hint_nonpos :
        (∫ u in 0..x, theorem_4_15_nonperiodicCandidateGlobalP u) ≤ 0 := by
      rw [intervalIntegral.integral_symm]
      have hnonneg : 0 ≤
          ∫ u in x..0, theorem_4_15_nonperiodicCandidateGlobalP u :=
        intervalIntegral.integral_nonneg_of_forall hx.le
          theorem_4_15_nonperiodicCandidateGlobalP_nonneg
      linarith
    unfold theorem_4_15_nonperiodicCandidateGlobalProfile
    dsimp [C] at hPupper
    linarith

def theorem_4_15_nonperiodicCandidateObjective : Objective 1 1 :=
  ⟨fun W => theorem_4_15_nonperiodicCandidateGlobalProfile
    (theorem_4_5_counterexampleEntry W)⟩

theorem theorem_4_15_nonperiodicCandidateObjective_contDiff_three :
    ContDiff ℝ 3
      (vectorizedObjective theorem_4_15_nonperiodicCandidateObjective) := by
  simpa [vectorizedObjective, theorem_4_15_nonperiodicCandidateObjective] using
    theorem_4_15_nonperiodicCandidateGlobalProfile_contDiff_three.comp
      theorem_4_5_counterexampleEntry.contDiff

theorem theorem_4_15_nonperiodicCandidateObjective_hasFiniteInfimum :
    theorem_4_15_nonperiodicCandidateObjective.HasFiniteInfimum := by
  refine ⟨2 - 3 * (((1 : ℝ) / 2) ^ (-(6 : ℝ) / 5)) -
      (∫ u in Set.Ici (0 : ℝ),
        theorem_4_15_nonperiodicCandidateGlobalP u), ?_⟩
  rintro y ⟨W, rfl⟩
  exact theorem_4_15_nonperiodicCandidateGlobalProfile_lower
    (theorem_4_5_counterexampleEntry W)

theorem theorem_4_15_nonperiodicCandidateObjective_eq_positiveProfile
    {W : Mat 1 1} (hW : 0 ≤ theorem_4_5_counterexampleEntry W) :
    theorem_4_15_nonperiodicCandidateObjective.f W =
      theorem_4_15_nonperiodicCandidatePositiveProfile
        (theorem_4_5_counterexampleEntry W) := by
  exact theorem_4_15_nonperiodicCandidateGlobalProfile_eq hW

theorem theorem_4_15_nonperiodicCandidateQ_pos {x : ℝ} (hx : -1 < x) :
    0 < theorem_4_15_nonperiodicCandidateQ x := by
  exact Real.rpow_pos_of_pos (by linarith) _

theorem theorem_4_15_nonperiodicCandidateP_envelope {x : ℝ} (hx : -1 < x) :
    theorem_4_15_nonperiodicCandidateQ x ≤
        theorem_4_15_nonperiodicCandidateP x ∧
      theorem_4_15_nonperiodicCandidateP x ≤
        3 * theorem_4_15_nonperiodicCandidateQ x := by
  have hq : 0 ≤ theorem_4_15_nonperiodicCandidateQ x :=
    (theorem_4_15_nonperiodicCandidateQ_pos hx).le
  have hoscLower : (1 : ℝ) ≤
      2 + Real.sin (theorem_4_15_nonperiodicCandidatePhase x) := by
    linarith [Real.neg_one_le_sin (theorem_4_15_nonperiodicCandidatePhase x)]
  have hoscUpper :
      2 + Real.sin (theorem_4_15_nonperiodicCandidatePhase x) ≤ (3 : ℝ) := by
    linarith [Real.sin_le_one (theorem_4_15_nonperiodicCandidatePhase x)]
  constructor
  · simpa [theorem_4_15_nonperiodicCandidateP] using
      mul_le_mul_of_nonneg_left hoscLower hq
  · simpa [theorem_4_15_nonperiodicCandidateP, mul_comm] using
      mul_le_mul_of_nonneg_left hoscUpper hq

theorem theorem_4_15_nonperiodicCandidateP_pos {x : ℝ} (hx : -1 < x) :
    0 < theorem_4_15_nonperiodicCandidateP x :=
  (theorem_4_15_nonperiodicCandidateQ_pos hx).trans_le
    (theorem_4_15_nonperiodicCandidateP_envelope hx).1

theorem theorem_4_15_nonperiodicCandidateQ_hasDerivAt
    {x : ℝ} (hx : -1 < x) :
    HasDerivAt theorem_4_15_nonperiodicCandidateQ
      ((-(6 : ℝ) / 5) * (1 + x) ^ (-(11 : ℝ) / 5)) x := by
  have hz : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
    simpa using (hasDerivAt_const (x := x) (1 : ℝ)).add
      (hasDerivAt_id (x := x))
  convert hz.rpow_const (p := (-(6 : ℝ) / 5))
      (Or.inl (ne_of_gt (by linarith))) using 1 <;>
    norm_num [theorem_4_15_nonperiodicCandidateQ] <;> ring

theorem theorem_4_15_nonperiodicCandidatePhase_hasDerivAt
    {x : ℝ} (hx : -1 < x) :
    HasDerivAt theorem_4_15_nonperiodicCandidatePhase
      (((12 : ℝ) / 5) * (1 + x) ^ ((2 : ℝ) / 5)) x := by
  have hz : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
    simpa using (hasDerivAt_const (x := x) (1 : ℝ)).add
      (hasDerivAt_id (x := x))
  have hpow := hz.rpow_const (p := ((7 : ℝ) / 5))
    (Or.inl (ne_of_gt (by linarith)))
  convert (hpow.sub_const 1).const_mul ((12 : ℝ) / 7) using 1 <;>
    norm_num [theorem_4_15_nonperiodicCandidatePhase] <;> ring

theorem theorem_4_15_nonperiodicCandidateP_hasDerivAt
    {x : ℝ} (hx : -1 < x) :
    HasDerivAt theorem_4_15_nonperiodicCandidateP
      (((-(6 : ℝ) / 5) * (1 + x) ^ (-(11 : ℝ) / 5)) *
          (2 + Real.sin (theorem_4_15_nonperiodicCandidatePhase x)) +
        theorem_4_15_nonperiodicCandidateQ x *
          (Real.cos (theorem_4_15_nonperiodicCandidatePhase x) *
            (((12 : ℝ) / 5) * (1 + x) ^ ((2 : ℝ) / 5)))) x := by
  have hq := theorem_4_15_nonperiodicCandidateQ_hasDerivAt hx
  have hphase := theorem_4_15_nonperiodicCandidatePhase_hasDerivAt hx
  convert hq.mul ((hasDerivAt_const (x := x) (2 : ℝ)).add hphase.sin) using 1 <;>
    simp [theorem_4_15_nonperiodicCandidateP] <;> ring

/- Explicit derivative data for the positive ray.  These functions are kept
   separate so that the eventual global third-derivative estimate can combine
   an elementary tail bound with compactness on the cutoff transition. -/
def theorem_4_15_nonperiodicCandidateQFirst (x : ℝ) : ℝ :=
  (-(6 : ℝ) / 5) * (1 + x) ^ (-(11 : ℝ) / 5)

def theorem_4_15_nonperiodicCandidateQSecond (x : ℝ) : ℝ :=
  (-(6 : ℝ) / 5) * (-(11 : ℝ) / 5) *
    (1 + x) ^ (-(16 : ℝ) / 5)

def theorem_4_15_nonperiodicCandidateQThird (x : ℝ) : ℝ :=
  (-(6 : ℝ) / 5) * (-(11 : ℝ) / 5) * (-(16 : ℝ) / 5) *
    (1 + x) ^ (-(21 : ℝ) / 5)

def theorem_4_15_nonperiodicCandidatePhaseFirst (x : ℝ) : ℝ :=
  (12 : ℝ) / 5 * (1 + x) ^ ((2 : ℝ) / 5)

def theorem_4_15_nonperiodicCandidatePhaseSecond (x : ℝ) : ℝ :=
  (12 : ℝ) / 5 * ((2 : ℝ) / 5) * (1 + x) ^ (-(3 : ℝ) / 5)

def theorem_4_15_nonperiodicCandidatePhaseThird (x : ℝ) : ℝ :=
  (12 : ℝ) / 5 * ((2 : ℝ) / 5) * (-(3 : ℝ) / 5) *
    (1 + x) ^ (-(8 : ℝ) / 5)

theorem theorem_4_15_nonperiodicCandidate_rpow_hasDerivAt
    (a : ℝ) {x : ℝ} (hx : -1 < x) :
    HasDerivAt (fun y : ℝ => (1 + y) ^ a)
      (a * (1 + x) ^ (a - 1)) x := by
  have hz : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
    simpa using (hasDerivAt_const (x := x) (1 : ℝ)).add
      (hasDerivAt_id (x := x))
  convert hz.rpow_const (p := a) (Or.inl (ne_of_gt (by linarith))) using 1 <;>
    ring

theorem theorem_4_15_nonperiodicCandidateQFirst_hasDerivAt
    {x : ℝ} (hx : -1 < x) :
    HasDerivAt theorem_4_15_nonperiodicCandidateQFirst
      (theorem_4_15_nonperiodicCandidateQSecond x) x := by
  have h := (theorem_4_15_nonperiodicCandidate_rpow_hasDerivAt
    (-(11 : ℝ) / 5) hx).const_mul (-(6 : ℝ) / 5)
  convert h using 1 <;>
    norm_num [theorem_4_15_nonperiodicCandidateQFirst,
      theorem_4_15_nonperiodicCandidateQSecond] <;> ring

theorem theorem_4_15_nonperiodicCandidateQSecond_hasDerivAt
    {x : ℝ} (hx : -1 < x) :
    HasDerivAt theorem_4_15_nonperiodicCandidateQSecond
      (theorem_4_15_nonperiodicCandidateQThird x) x := by
  have h := (theorem_4_15_nonperiodicCandidate_rpow_hasDerivAt
    (-(16 : ℝ) / 5) hx).const_mul
      ((-(6 : ℝ) / 5) * (-(11 : ℝ) / 5))
  convert h using 1 <;>
    norm_num [theorem_4_15_nonperiodicCandidateQSecond,
      theorem_4_15_nonperiodicCandidateQThird] <;> ring

theorem theorem_4_15_nonperiodicCandidatePhaseFirst_hasDerivAt
    {x : ℝ} (hx : -1 < x) :
    HasDerivAt theorem_4_15_nonperiodicCandidatePhaseFirst
      (theorem_4_15_nonperiodicCandidatePhaseSecond x) x := by
  have h := (theorem_4_15_nonperiodicCandidate_rpow_hasDerivAt
    ((2 : ℝ) / 5) hx).const_mul ((12 : ℝ) / 5)
  convert h using 1 <;>
    norm_num [theorem_4_15_nonperiodicCandidatePhaseFirst,
      theorem_4_15_nonperiodicCandidatePhaseSecond] <;> ring

theorem theorem_4_15_nonperiodicCandidatePhaseSecond_hasDerivAt
    {x : ℝ} (hx : -1 < x) :
    HasDerivAt theorem_4_15_nonperiodicCandidatePhaseSecond
      (theorem_4_15_nonperiodicCandidatePhaseThird x) x := by
  have h := (theorem_4_15_nonperiodicCandidate_rpow_hasDerivAt
    (-(3 : ℝ) / 5) hx).const_mul
      (((12 : ℝ) / 5) * ((2 : ℝ) / 5))
  convert h using 1 <;>
    norm_num [theorem_4_15_nonperiodicCandidatePhaseSecond,
      theorem_4_15_nonperiodicCandidatePhaseThird] <;> ring

def theorem_4_15_nonperiodicCandidateOscillation (x : ℝ) : ℝ :=
  2 + Real.sin (theorem_4_15_nonperiodicCandidatePhase x)

def theorem_4_15_nonperiodicCandidateOscillationFirst (x : ℝ) : ℝ :=
  Real.cos (theorem_4_15_nonperiodicCandidatePhase x) *
    theorem_4_15_nonperiodicCandidatePhaseFirst x

def theorem_4_15_nonperiodicCandidateOscillationSecond (x : ℝ) : ℝ :=
  (-Real.sin (theorem_4_15_nonperiodicCandidatePhase x) *
      theorem_4_15_nonperiodicCandidatePhaseFirst x) *
        theorem_4_15_nonperiodicCandidatePhaseFirst x +
    Real.cos (theorem_4_15_nonperiodicCandidatePhase x) *
      theorem_4_15_nonperiodicCandidatePhaseSecond x

def theorem_4_15_nonperiodicCandidateOscillationThird (x : ℝ) : ℝ :=
  -Real.cos (theorem_4_15_nonperiodicCandidatePhase x) *
      theorem_4_15_nonperiodicCandidatePhaseFirst x ^ 3 -
    3 * Real.sin (theorem_4_15_nonperiodicCandidatePhase x) *
      theorem_4_15_nonperiodicCandidatePhaseFirst x *
      theorem_4_15_nonperiodicCandidatePhaseSecond x +
    Real.cos (theorem_4_15_nonperiodicCandidatePhase x) *
      theorem_4_15_nonperiodicCandidatePhaseThird x

theorem theorem_4_15_nonperiodicCandidateOscillation_hasDerivAt
    {x : ℝ} (hx : -1 < x) :
    HasDerivAt theorem_4_15_nonperiodicCandidateOscillation
      (theorem_4_15_nonperiodicCandidateOscillationFirst x) x := by
  have hphase := theorem_4_15_nonperiodicCandidatePhase_hasDerivAt hx
  simpa [theorem_4_15_nonperiodicCandidateOscillation,
    theorem_4_15_nonperiodicCandidateOscillationFirst] using
      (hasDerivAt_const (x := x) (2 : ℝ)).add hphase.sin

theorem theorem_4_15_nonperiodicCandidateOscillationFirst_hasDerivAt
    {x : ℝ} (hx : -1 < x) :
    HasDerivAt theorem_4_15_nonperiodicCandidateOscillationFirst
      (theorem_4_15_nonperiodicCandidateOscillationSecond x) x := by
  have hphase := theorem_4_15_nonperiodicCandidatePhase_hasDerivAt hx
  have hphaseFirst := theorem_4_15_nonperiodicCandidatePhaseFirst_hasDerivAt hx
  convert hphase.cos.mul hphaseFirst using 1 <;>
    simp [theorem_4_15_nonperiodicCandidateOscillationFirst,
      theorem_4_15_nonperiodicCandidateOscillationSecond,
      theorem_4_15_nonperiodicCandidatePhaseFirst] <;> ring

theorem theorem_4_15_nonperiodicCandidateOscillationSecond_hasDerivAt
    {x : ℝ} (hx : -1 < x) :
    HasDerivAt theorem_4_15_nonperiodicCandidateOscillationSecond
      (theorem_4_15_nonperiodicCandidateOscillationThird x) x := by
  have hphase := theorem_4_15_nonperiodicCandidatePhase_hasDerivAt hx
  have hphase' : HasDerivAt theorem_4_15_nonperiodicCandidatePhase
      (theorem_4_15_nonperiodicCandidatePhaseFirst x) x := by
    simpa [theorem_4_15_nonperiodicCandidatePhaseFirst] using hphase
  have hphaseFirst := theorem_4_15_nonperiodicCandidatePhaseFirst_hasDerivAt hx
  have hphaseSecond := theorem_4_15_nonperiodicCandidatePhaseSecond_hasDerivAt hx
  have hfirst : HasDerivAt
      (fun y => -Real.sin (theorem_4_15_nonperiodicCandidatePhase y) *
        theorem_4_15_nonperiodicCandidatePhaseFirst y)
      ((-Real.cos (theorem_4_15_nonperiodicCandidatePhase x) *
          theorem_4_15_nonperiodicCandidatePhaseFirst x) *
          theorem_4_15_nonperiodicCandidatePhaseFirst x -
        Real.sin (theorem_4_15_nonperiodicCandidatePhase x) *
          theorem_4_15_nonperiodicCandidatePhaseSecond x) x := by
    convert hphase'.sin.neg.mul hphaseFirst using 1 <;> simp <;> ring
  convert (hfirst.mul hphaseFirst).add (hphase'.cos.mul hphaseSecond) using 1 <;>
    simp [theorem_4_15_nonperiodicCandidateOscillationSecond,
      theorem_4_15_nonperiodicCandidateOscillationThird] <;> ring

def theorem_4_15_nonperiodicCandidatePFirst (x : ℝ) : ℝ :=
  theorem_4_15_nonperiodicCandidateQFirst x *
      theorem_4_15_nonperiodicCandidateOscillation x +
    theorem_4_15_nonperiodicCandidateQ x *
      theorem_4_15_nonperiodicCandidateOscillationFirst x

def theorem_4_15_nonperiodicCandidatePSecond (x : ℝ) : ℝ :=
  theorem_4_15_nonperiodicCandidateQSecond x *
      theorem_4_15_nonperiodicCandidateOscillation x +
    2 * theorem_4_15_nonperiodicCandidateQFirst x *
      theorem_4_15_nonperiodicCandidateOscillationFirst x +
    theorem_4_15_nonperiodicCandidateQ x *
      theorem_4_15_nonperiodicCandidateOscillationSecond x

def theorem_4_15_nonperiodicCandidatePThird (x : ℝ) : ℝ :=
  theorem_4_15_nonperiodicCandidateQThird x *
      theorem_4_15_nonperiodicCandidateOscillation x +
    3 * theorem_4_15_nonperiodicCandidateQSecond x *
      theorem_4_15_nonperiodicCandidateOscillationFirst x +
    3 * theorem_4_15_nonperiodicCandidateQFirst x *
      theorem_4_15_nonperiodicCandidateOscillationSecond x +
    theorem_4_15_nonperiodicCandidateQ x *
      theorem_4_15_nonperiodicCandidateOscillationThird x

theorem theorem_4_15_nonperiodicCandidateP_hasDerivAt_first
    {x : ℝ} (hx : -1 < x) :
    HasDerivAt theorem_4_15_nonperiodicCandidateP
      (theorem_4_15_nonperiodicCandidatePFirst x) x := by
  simpa [theorem_4_15_nonperiodicCandidatePFirst,
    theorem_4_15_nonperiodicCandidateQFirst,
    theorem_4_15_nonperiodicCandidateOscillation,
    theorem_4_15_nonperiodicCandidateOscillationFirst,
    theorem_4_15_nonperiodicCandidatePhaseFirst] using
      theorem_4_15_nonperiodicCandidateP_hasDerivAt hx

theorem theorem_4_15_nonperiodicCandidatePFirst_hasDerivAt
    {x : ℝ} (hx : -1 < x) :
    HasDerivAt theorem_4_15_nonperiodicCandidatePFirst
      (theorem_4_15_nonperiodicCandidatePSecond x) x := by
  have hq := theorem_4_15_nonperiodicCandidateQ_hasDerivAt hx
  have hqFirst := theorem_4_15_nonperiodicCandidateQFirst_hasDerivAt hx
  have hosc := theorem_4_15_nonperiodicCandidateOscillation_hasDerivAt hx
  have hoscFirst :=
    theorem_4_15_nonperiodicCandidateOscillationFirst_hasDerivAt hx
  convert (hqFirst.mul hosc).add (hq.mul hoscFirst) using 1 <;>
    simp [theorem_4_15_nonperiodicCandidatePFirst,
      theorem_4_15_nonperiodicCandidatePSecond,
      theorem_4_15_nonperiodicCandidateQFirst] <;> ring

theorem theorem_4_15_nonperiodicCandidatePSecond_hasDerivAt
    {x : ℝ} (hx : -1 < x) :
    HasDerivAt theorem_4_15_nonperiodicCandidatePSecond
      (theorem_4_15_nonperiodicCandidatePThird x) x := by
  have hq := theorem_4_15_nonperiodicCandidateQ_hasDerivAt hx
  have hq' : HasDerivAt theorem_4_15_nonperiodicCandidateQ
      (theorem_4_15_nonperiodicCandidateQFirst x) x := by
    simpa [theorem_4_15_nonperiodicCandidateQFirst] using hq
  have hqFirst := theorem_4_15_nonperiodicCandidateQFirst_hasDerivAt hx
  have hqSecond := theorem_4_15_nonperiodicCandidateQSecond_hasDerivAt hx
  have hosc := theorem_4_15_nonperiodicCandidateOscillation_hasDerivAt hx
  have hoscFirst :=
    theorem_4_15_nonperiodicCandidateOscillationFirst_hasDerivAt hx
  have hoscSecond :=
    theorem_4_15_nonperiodicCandidateOscillationSecond_hasDerivAt hx
  convert ((hqSecond.mul hosc).add
      ((hqFirst.const_mul 2).mul hoscFirst)).add
        (hq'.mul hoscSecond) using 1 <;>
    simp [theorem_4_15_nonperiodicCandidatePSecond,
      theorem_4_15_nonperiodicCandidatePThird,
      theorem_4_15_nonperiodicCandidateQFirst] <;> ring

theorem theorem_4_15_nonperiodicCandidatePositiveProfile_hasDerivAt
    {x : ℝ} (hx : -1 < x) :
    HasDerivAt theorem_4_15_nonperiodicCandidatePositiveProfile
      (-(((-(6 : ℝ) / 5) * (1 + x) ^ (-(11 : ℝ) / 5)) *
            (2 + Real.sin (theorem_4_15_nonperiodicCandidatePhase x)) +
          theorem_4_15_nonperiodicCandidateQ x *
            (Real.cos (theorem_4_15_nonperiodicCandidatePhase x) *
              (((12 : ℝ) / 5) * (1 + x) ^ ((2 : ℝ) / 5)))) -
        theorem_4_15_nonperiodicCandidateP x) x := by
  have hp := theorem_4_15_nonperiodicCandidateP_hasDerivAt hx
  have hcontOn : ContinuousOn theorem_4_15_nonperiodicCandidateP
      (Set.Ioi (-1 : ℝ)) := by
    intro y hy
    exact (theorem_4_15_nonperiodicCandidateP_hasDerivAt
      (Set.mem_Ioi.mp hy)).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable theorem_4_15_nonperiodicCandidateP volume 0 x := by
    apply ContinuousOn.intervalIntegrable
    intro y hy
    rw [Set.mem_uIcc] at hy
    have hy' : -1 < y := by
      rcases hy with hy | hy <;> linarith
    exact (theorem_4_15_nonperiodicCandidateP_hasDerivAt hy').continuousAt.continuousWithinAt
  have hmeas : StronglyMeasurableAtFilter theorem_4_15_nonperiodicCandidateP
      (nhds x) volume :=
    hcontOn.stronglyMeasurableAtFilter isOpen_Ioi x (Set.mem_Ioi.mpr hx)
  have hi : HasDerivAt
      (fun y : ℝ => ∫ u in 0..y, theorem_4_15_nonperiodicCandidateP u)
      (theorem_4_15_nonperiodicCandidateP x) x :=
    intervalIntegral.integral_hasDerivAt_right hint hmeas hp.continuousAt
  convert ((hasDerivAt_const (x := x) (2 : ℝ)).sub hp).sub hi using 1 <;>
    simp [theorem_4_15_nonperiodicCandidatePositiveProfile] <;> ring

def theorem_4_15_nonperiodicCandidatePositiveProfileFirst (x : ℝ) : ℝ :=
  -theorem_4_15_nonperiodicCandidatePFirst x -
    theorem_4_15_nonperiodicCandidateP x

/- The slowly decaying term in the positive-ray gradient.  Its exponent is
   the exact cancellation `Q * phase' = (12/5) * (1+x)^(-4/5)`; the remaining
   gradient terms decay at least as `(1+x)^(-6/5)` and are summable. -/
def theorem_4_15_nonperiodicCandidateGradientLeading (x : ℝ) : ℝ :=
  (12 : ℝ) / 5 * (1 + x) ^ (-(4 : ℝ) / 5) *
    Real.cos (theorem_4_15_nonperiodicCandidatePhase x)

def theorem_4_15_nonperiodicCandidatePositiveProfileSecond (x : ℝ) : ℝ :=
  -theorem_4_15_nonperiodicCandidatePSecond x -
    theorem_4_15_nonperiodicCandidatePFirst x

def theorem_4_15_nonperiodicCandidatePositiveProfileThird (x : ℝ) : ℝ :=
  -theorem_4_15_nonperiodicCandidatePThird x -
    theorem_4_15_nonperiodicCandidatePSecond x

theorem theorem_4_15_nonperiodicCandidatePositiveProfile_hasDerivAt_first
    {x : ℝ} (hx : -1 < x) :
    HasDerivAt theorem_4_15_nonperiodicCandidatePositiveProfile
      (theorem_4_15_nonperiodicCandidatePositiveProfileFirst x) x := by
  simpa [theorem_4_15_nonperiodicCandidatePositiveProfileFirst,
    theorem_4_15_nonperiodicCandidatePFirst,
    theorem_4_15_nonperiodicCandidateQFirst,
    theorem_4_15_nonperiodicCandidateOscillation,
    theorem_4_15_nonperiodicCandidateOscillationFirst,
    theorem_4_15_nonperiodicCandidatePhaseFirst] using
      theorem_4_15_nonperiodicCandidatePositiveProfile_hasDerivAt hx

theorem theorem_4_15_nonperiodicCandidatePositiveProfileFirst_hasDerivAt
    {x : ℝ} (hx : -1 < x) :
    HasDerivAt theorem_4_15_nonperiodicCandidatePositiveProfileFirst
      (theorem_4_15_nonperiodicCandidatePositiveProfileSecond x) x := by
  simpa [theorem_4_15_nonperiodicCandidatePositiveProfileFirst,
    theorem_4_15_nonperiodicCandidatePositiveProfileSecond] using
      (theorem_4_15_nonperiodicCandidatePFirst_hasDerivAt hx).neg.sub
        (theorem_4_15_nonperiodicCandidateP_hasDerivAt_first hx)

theorem theorem_4_15_nonperiodicCandidatePositiveProfileSecond_hasDerivAt
    {x : ℝ} (hx : -1 < x) :
    HasDerivAt theorem_4_15_nonperiodicCandidatePositiveProfileSecond
      (theorem_4_15_nonperiodicCandidatePositiveProfileThird x) x := by
  simpa [theorem_4_15_nonperiodicCandidatePositiveProfileSecond,
    theorem_4_15_nonperiodicCandidatePositiveProfileThird] using
      (theorem_4_15_nonperiodicCandidatePSecond_hasDerivAt hx).neg.sub
        (theorem_4_15_nonperiodicCandidatePFirst_hasDerivAt hx)

theorem theorem_4_15_nonperiodicCandidatePositiveProfile_iteratedDeriv_three
    {x : ℝ} (hx : -1 < x) :
    iteratedDeriv 3 theorem_4_15_nonperiodicCandidatePositiveProfile x =
      theorem_4_15_nonperiodicCandidatePositiveProfileThird x := by
  have hfirstLocal :
      deriv theorem_4_15_nonperiodicCandidatePositiveProfile =ᶠ[nhds x]
        theorem_4_15_nonperiodicCandidatePositiveProfileFirst := by
    filter_upwards [isOpen_Ioi.eventually_mem hx] with y hy
    exact (theorem_4_15_nonperiodicCandidatePositiveProfile_hasDerivAt_first
      (Set.mem_Ioi.mp hy)).deriv
  have hsecondLocal :
      deriv (deriv theorem_4_15_nonperiodicCandidatePositiveProfile) =ᶠ[nhds x]
        theorem_4_15_nonperiodicCandidatePositiveProfileSecond := by
    filter_upwards [isOpen_Ioi.eventually_mem hx] with y hy
    have hfirstAtY :
        deriv theorem_4_15_nonperiodicCandidatePositiveProfile =ᶠ[nhds y]
          theorem_4_15_nonperiodicCandidatePositiveProfileFirst := by
      filter_upwards [isOpen_Ioi.eventually_mem (Set.mem_Ioi.mp hy)] with z hz
      exact (theorem_4_15_nonperiodicCandidatePositiveProfile_hasDerivAt_first
        (Set.mem_Ioi.mp hz)).deriv
    calc
      deriv (deriv theorem_4_15_nonperiodicCandidatePositiveProfile) y =
          deriv theorem_4_15_nonperiodicCandidatePositiveProfileFirst y :=
        hfirstAtY.deriv_eq
      _ = theorem_4_15_nonperiodicCandidatePositiveProfileSecond y :=
        (theorem_4_15_nonperiodicCandidatePositiveProfileFirst_hasDerivAt
          (Set.mem_Ioi.mp hy)).deriv
  rw [show 3 = 2 + 1 by norm_num, iteratedDeriv_succ,
    show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  calc
    deriv (deriv (deriv theorem_4_15_nonperiodicCandidatePositiveProfile)) x =
        deriv theorem_4_15_nonperiodicCandidatePositiveProfileSecond x :=
      hsecondLocal.deriv_eq
    _ = theorem_4_15_nonperiodicCandidatePositiveProfileThird x :=
      (theorem_4_15_nonperiodicCandidatePositiveProfileSecond_hasDerivAt hx).deriv

/- On the generated positive ray, every growing phase derivative is paired
   with enough decay from `Q`.  The following elementary power bounds keep
   that cancellation explicit, rather than bounding the factors separately. -/
theorem theorem_4_15_nonperiodicCandidate_rpow_mul_abs_le_one
    {x a b : ℝ} (hx : 0 ≤ x) (hab : a + b ≤ 0) :
    |(1 + x) ^ a * (1 + x) ^ b| ≤ 1 := by
  have hz : 0 < 1 + x := by linarith
  rw [abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hz.le _)
    (Real.rpow_nonneg hz.le _)), ← Real.rpow_add hz]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) hab

theorem theorem_4_15_nonperiodicCandidate_rpow_abs_le_one
    {x a : ℝ} (hx : 0 ≤ x) (ha : a ≤ 0) :
    |(1 + x) ^ a| ≤ 1 := by
  have hz : 0 < 1 + x := by linarith
  rw [abs_of_nonneg (Real.rpow_nonneg hz.le _)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) ha

theorem theorem_4_15_nonperiodicCandidate_rpow_mul_three_abs_le_one
    {x a b c : ℝ} (hx : 0 ≤ x) (habc : a + b + c ≤ 0) :
    |(1 + x) ^ a * (1 + x) ^ b * (1 + x) ^ c| ≤ 1 := by
  have hz : 0 < 1 + x := by linarith
  rw [abs_of_nonneg (mul_nonneg
    (mul_nonneg (Real.rpow_nonneg hz.le _) (Real.rpow_nonneg hz.le _))
    (Real.rpow_nonneg hz.le _)), ← Real.rpow_add hz, ← Real.rpow_add hz]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) habc

theorem theorem_4_15_nonperiodicCandidate_rpow_mul_four_abs_le_one
    {x a b c d : ℝ} (hx : 0 ≤ x) (habcd : a + b + c + d ≤ 0) :
    |(1 + x) ^ a * (1 + x) ^ b * (1 + x) ^ c * (1 + x) ^ d| ≤ 1 := by
  have hz : 0 < 1 + x := by linarith
  rw [abs_of_nonneg (mul_nonneg
    (mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hz.le _) (Real.rpow_nonneg hz.le _))
      (Real.rpow_nonneg hz.le _)) (Real.rpow_nonneg hz.le _)),
    ← Real.rpow_add hz, ← Real.rpow_add hz, ← Real.rpow_add hz]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) habcd

theorem theorem_4_15_nonperiodicCandidateOscillation_abs_le_three (x : ℝ) :
    |theorem_4_15_nonperiodicCandidateOscillation x| ≤ 3 := by
  rw [abs_le]
  constructor <;>
    simp only [theorem_4_15_nonperiodicCandidateOscillation] <;>
    linarith [Real.neg_one_le_sin (theorem_4_15_nonperiodicCandidatePhase x),
      Real.sin_le_one (theorem_4_15_nonperiodicCandidatePhase x)]

theorem theorem_4_15_nonperiodicCandidateQ_abs_le_one
    {x : ℝ} (hx : 0 ≤ x) :
    |theorem_4_15_nonperiodicCandidateQ x| ≤ 1 := by
  simpa [theorem_4_15_nonperiodicCandidateQ] using
    (theorem_4_15_nonperiodicCandidate_rpow_abs_le_one
      (x := x) (a := (-(6 : ℝ) / 5)) hx (by norm_num))

theorem theorem_4_15_nonperiodicCandidateQFirst_abs_le
    {x : ℝ} (hx : 0 ≤ x) :
    |theorem_4_15_nonperiodicCandidateQFirst x| ≤ (6 : ℝ) / 5 := by
  have hp := theorem_4_15_nonperiodicCandidate_rpow_abs_le_one
    (x := x) (a := (-(11 : ℝ) / 5)) hx (by norm_num)
  rw [theorem_4_15_nonperiodicCandidateQFirst, abs_mul]
  norm_num at ⊢
  nlinarith

theorem theorem_4_15_nonperiodicCandidateQSecond_abs_le
    {x : ℝ} (hx : 0 ≤ x) :
    |theorem_4_15_nonperiodicCandidateQSecond x| ≤ (66 : ℝ) / 25 := by
  have hp := theorem_4_15_nonperiodicCandidate_rpow_abs_le_one
    (x := x) (a := (-(16 : ℝ) / 5)) hx (by norm_num)
  rw [theorem_4_15_nonperiodicCandidateQSecond, abs_mul, abs_mul]
  norm_num at ⊢
  nlinarith

theorem theorem_4_15_nonperiodicCandidateQThird_abs_le
    {x : ℝ} (hx : 0 ≤ x) :
    |theorem_4_15_nonperiodicCandidateQThird x| ≤ (1056 : ℝ) / 125 := by
  have hp := theorem_4_15_nonperiodicCandidate_rpow_abs_le_one
    (x := x) (a := (-(21 : ℝ) / 5)) hx (by norm_num)
  rw [theorem_4_15_nonperiodicCandidateQThird, abs_mul, abs_mul, abs_mul]
  norm_num at ⊢
  nlinarith

theorem theorem_4_15_nonperiodicCandidateQSecond_mul_phaseFirst_abs_le
    {x : ℝ} (hx : 0 ≤ x) :
    |theorem_4_15_nonperiodicCandidateQSecond x *
        theorem_4_15_nonperiodicCandidatePhaseFirst x| ≤
      (792 : ℝ) / 125 := by
  have hp := theorem_4_15_nonperiodicCandidate_rpow_mul_abs_le_one
    (x := x) (a := (-(16 : ℝ) / 5)) (b := ((2 : ℝ) / 5)) hx (by norm_num)
  calc
    |theorem_4_15_nonperiodicCandidateQSecond x *
        theorem_4_15_nonperiodicCandidatePhaseFirst x| =
        792 / 125 *
          |(1 + x) ^ (-(16 : ℝ) / 5) * (1 + x) ^ ((2 : ℝ) / 5)| := by
            rw [theorem_4_15_nonperiodicCandidateQSecond,
              theorem_4_15_nonperiodicCandidatePhaseFirst]
            rw [abs_mul, abs_mul, abs_mul, abs_mul]
            norm_num
            ring
    _ ≤ 792 / 125 * 1 :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = 792 / 125 := by ring

theorem theorem_4_15_nonperiodicCandidateQ_mul_phaseFirst_sq_abs_le
    {x : ℝ} (hx : 0 ≤ x) :
    |theorem_4_15_nonperiodicCandidateQ x *
        theorem_4_15_nonperiodicCandidatePhaseFirst x ^ 2| ≤
      (144 : ℝ) / 25 := by
  have hp := theorem_4_15_nonperiodicCandidate_rpow_mul_three_abs_le_one
    (x := x) (a := (-(6 : ℝ) / 5))
      (b := ((2 : ℝ) / 5)) (c := ((2 : ℝ) / 5)) hx (by norm_num)
  calc
    |theorem_4_15_nonperiodicCandidateQ x *
        theorem_4_15_nonperiodicCandidatePhaseFirst x ^ 2| =
        144 / 25 * |(1 + x) ^ (-(6 : ℝ) / 5) *
          (1 + x) ^ ((2 : ℝ) / 5) * (1 + x) ^ ((2 : ℝ) / 5)| := by
            rw [theorem_4_15_nonperiodicCandidateQ,
              theorem_4_15_nonperiodicCandidatePhaseFirst, pow_two]
            rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul]
            norm_num
            ring
    _ ≤ 144 / 25 * 1 :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = 144 / 25 := by ring

theorem theorem_4_15_nonperiodicCandidateQFirst_mul_phaseFirst_sq_abs_le
    {x : ℝ} (hx : 0 ≤ x) :
    |theorem_4_15_nonperiodicCandidateQFirst x *
        theorem_4_15_nonperiodicCandidatePhaseFirst x ^ 2| ≤
      (864 : ℝ) / 125 := by
  have hp := theorem_4_15_nonperiodicCandidate_rpow_mul_three_abs_le_one
    (x := x) (a := (-(11 : ℝ) / 5))
      (b := ((2 : ℝ) / 5)) (c := ((2 : ℝ) / 5)) hx (by norm_num)
  calc
    |theorem_4_15_nonperiodicCandidateQFirst x *
        theorem_4_15_nonperiodicCandidatePhaseFirst x ^ 2| =
        864 / 125 * |(1 + x) ^ (-(11 : ℝ) / 5) *
          (1 + x) ^ ((2 : ℝ) / 5) * (1 + x) ^ ((2 : ℝ) / 5)| := by
            rw [theorem_4_15_nonperiodicCandidateQFirst,
              theorem_4_15_nonperiodicCandidatePhaseFirst, pow_two]
            rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul]
            norm_num
            ring
    _ ≤ 864 / 125 * 1 :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = 864 / 125 := by ring

theorem theorem_4_15_nonperiodicCandidateQ_mul_phaseFirst_cube_abs_le
    {x : ℝ} (hx : 0 ≤ x) :
    |theorem_4_15_nonperiodicCandidateQ x *
        theorem_4_15_nonperiodicCandidatePhaseFirst x ^ 3| ≤
      (1728 : ℝ) / 125 := by
  have hp := theorem_4_15_nonperiodicCandidate_rpow_mul_four_abs_le_one
    (x := x) (a := (-(6 : ℝ) / 5)) (b := ((2 : ℝ) / 5))
      (c := ((2 : ℝ) / 5)) (d := ((2 : ℝ) / 5)) hx (by norm_num)
  calc
    |theorem_4_15_nonperiodicCandidateQ x *
        theorem_4_15_nonperiodicCandidatePhaseFirst x ^ 3| =
        1728 / 125 * |(1 + x) ^ (-(6 : ℝ) / 5) *
          (1 + x) ^ ((2 : ℝ) / 5) * (1 + x) ^ ((2 : ℝ) / 5) *
            (1 + x) ^ ((2 : ℝ) / 5)| := by
            rw [theorem_4_15_nonperiodicCandidateQ,
              theorem_4_15_nonperiodicCandidatePhaseFirst, pow_three]
            rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul]
            norm_num
            ring
    _ ≤ 1728 / 125 * 1 :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = 1728 / 125 := by ring

theorem theorem_4_15_nonperiodicCandidateQ_mul_phaseSecond_abs_le
    {x : ℝ} (hx : 0 ≤ x) :
    |theorem_4_15_nonperiodicCandidateQ x *
        theorem_4_15_nonperiodicCandidatePhaseSecond x| ≤
      (24 : ℝ) / 25 := by
  have hp := theorem_4_15_nonperiodicCandidate_rpow_mul_abs_le_one
    (x := x) (a := (-(6 : ℝ) / 5)) (b := (-(3 : ℝ) / 5)) hx (by norm_num)
  calc
    |theorem_4_15_nonperiodicCandidateQ x *
        theorem_4_15_nonperiodicCandidatePhaseSecond x| =
        24 / 25 * |(1 + x) ^ (-(6 : ℝ) / 5) *
          (1 + x) ^ (-(3 : ℝ) / 5)| := by
            rw [theorem_4_15_nonperiodicCandidateQ,
              theorem_4_15_nonperiodicCandidatePhaseSecond]
            rw [abs_mul, abs_mul, abs_mul, abs_mul]
            norm_num
            ring
    _ ≤ 24 / 25 * 1 := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = 24 / 25 := by ring

theorem theorem_4_15_nonperiodicCandidateQFirst_mul_phaseSecond_abs_le
    {x : ℝ} (hx : 0 ≤ x) :
    |theorem_4_15_nonperiodicCandidateQFirst x *
        theorem_4_15_nonperiodicCandidatePhaseSecond x| ≤
      (144 : ℝ) / 125 := by
  have hp := theorem_4_15_nonperiodicCandidate_rpow_mul_abs_le_one
    (x := x) (a := (-(11 : ℝ) / 5)) (b := (-(3 : ℝ) / 5)) hx (by norm_num)
  calc
    |theorem_4_15_nonperiodicCandidateQFirst x *
        theorem_4_15_nonperiodicCandidatePhaseSecond x| =
        144 / 125 * |(1 + x) ^ (-(11 : ℝ) / 5) *
          (1 + x) ^ (-(3 : ℝ) / 5)| := by
            rw [theorem_4_15_nonperiodicCandidateQFirst,
              theorem_4_15_nonperiodicCandidatePhaseSecond]
            rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul]
            norm_num
            ring
    _ ≤ 144 / 125 * 1 := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = 144 / 125 := by ring

theorem theorem_4_15_nonperiodicCandidateQ_mul_phaseFirst_mul_phaseSecond_abs_le
    {x : ℝ} (hx : 0 ≤ x) :
    |theorem_4_15_nonperiodicCandidateQ x *
        theorem_4_15_nonperiodicCandidatePhaseFirst x *
          theorem_4_15_nonperiodicCandidatePhaseSecond x| ≤
      (288 : ℝ) / 125 := by
  have hp := theorem_4_15_nonperiodicCandidate_rpow_mul_three_abs_le_one
    (x := x) (a := (-(6 : ℝ) / 5))
      (b := ((2 : ℝ) / 5)) (c := (-(3 : ℝ) / 5)) hx (by norm_num)
  calc
    |theorem_4_15_nonperiodicCandidateQ x *
        theorem_4_15_nonperiodicCandidatePhaseFirst x *
          theorem_4_15_nonperiodicCandidatePhaseSecond x| =
        288 / 125 * |(1 + x) ^ (-(6 : ℝ) / 5) *
          (1 + x) ^ ((2 : ℝ) / 5) * (1 + x) ^ (-(3 : ℝ) / 5)| := by
            rw [theorem_4_15_nonperiodicCandidateQ,
              theorem_4_15_nonperiodicCandidatePhaseFirst,
              theorem_4_15_nonperiodicCandidatePhaseSecond]
            rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul]
            norm_num
            ring
    _ ≤ 288 / 125 * 1 := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = 288 / 125 := by ring

theorem theorem_4_15_nonperiodicCandidateQ_mul_phaseThird_abs_le
    {x : ℝ} (hx : 0 ≤ x) :
    |theorem_4_15_nonperiodicCandidateQ x *
        theorem_4_15_nonperiodicCandidatePhaseThird x| ≤
      (72 : ℝ) / 125 := by
  have hp := theorem_4_15_nonperiodicCandidate_rpow_mul_abs_le_one
    (x := x) (a := (-(6 : ℝ) / 5)) (b := (-(8 : ℝ) / 5)) hx (by norm_num)
  calc
    |theorem_4_15_nonperiodicCandidateQ x *
        theorem_4_15_nonperiodicCandidatePhaseThird x| =
        72 / 125 * |(1 + x) ^ (-(6 : ℝ) / 5) *
          (1 + x) ^ (-(8 : ℝ) / 5)| := by
            rw [theorem_4_15_nonperiodicCandidateQ,
              theorem_4_15_nonperiodicCandidatePhaseThird]
            rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul]
            norm_num
            ring
    _ ≤ 72 / 125 * 1 := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = 72 / 125 := by ring

theorem theorem_4_15_nonperiodicCandidateQFirst_mul_oscillationFirst_abs_le
    {x : ℝ} (hx : 0 ≤ x) :
    |theorem_4_15_nonperiodicCandidateQFirst x *
        theorem_4_15_nonperiodicCandidateOscillationFirst x| ≤
      (72 : ℝ) / 25 := by
  have hp := theorem_4_15_nonperiodicCandidate_rpow_mul_abs_le_one
    (x := x) (a := (-(11 : ℝ) / 5)) (b := ((2 : ℝ) / 5)) hx (by norm_num)
  have hc := Real.abs_cos_le_one
    (theorem_4_15_nonperiodicCandidatePhase x)
  rw [theorem_4_15_nonperiodicCandidateQFirst,
    theorem_4_15_nonperiodicCandidateOscillationFirst,
    theorem_4_15_nonperiodicCandidatePhaseFirst]
  rw [abs_mul, abs_mul, abs_mul]
  norm_num at ⊢ hp
  calc
    6 / 5 * |(1 + x) ^ (-(11 / 5 : ℝ))| *
          (|Real.cos (theorem_4_15_nonperiodicCandidatePhase x)| *
            (12 / 5 * |(1 + x) ^ (2 / 5 : ℝ)|)) =
        72 / 25 *
          ((|(1 + x) ^ (-(11 / 5 : ℝ))| *
              |(1 + x) ^ (2 / 5 : ℝ)|) *
            |Real.cos (theorem_4_15_nonperiodicCandidatePhase x)|) := by ring
    _ ≤ 72 / 25 * 1 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      calc
        (|(1 + x) ^ (-(11 / 5 : ℝ))| *
              |(1 + x) ^ (2 / 5 : ℝ)|) *
            |Real.cos (theorem_4_15_nonperiodicCandidatePhase x)| ≤
            1 * |Real.cos (theorem_4_15_nonperiodicCandidatePhase x)| :=
          mul_le_mul_of_nonneg_right hp (abs_nonneg _)
        _ ≤ 1 := by simpa using hc
    _ = 72 / 25 := by ring

theorem theorem_4_15_nonperiodicCandidateQ_mul_oscillationFirst_abs_le
    {x : ℝ} (hx : 0 ≤ x) :
    |theorem_4_15_nonperiodicCandidateQ x *
        theorem_4_15_nonperiodicCandidateOscillationFirst x| ≤
      (12 : ℝ) / 5 := by
  have hp := theorem_4_15_nonperiodicCandidate_rpow_mul_abs_le_one
    (x := x) (a := (-(6 : ℝ) / 5)) (b := ((2 : ℝ) / 5)) hx (by norm_num)
  have hc := Real.abs_cos_le_one
    (theorem_4_15_nonperiodicCandidatePhase x)
  rw [theorem_4_15_nonperiodicCandidateQ,
    theorem_4_15_nonperiodicCandidateOscillationFirst,
    theorem_4_15_nonperiodicCandidatePhaseFirst]
  rw [abs_mul, abs_mul, abs_mul]
  norm_num at ⊢ hp
  calc
    |(1 + x) ^ (-(6 / 5 : ℝ))| *
          (|Real.cos (theorem_4_15_nonperiodicCandidatePhase x)| *
            (12 / 5 * |(1 + x) ^ (2 / 5 : ℝ)|)) =
        12 / 5 *
          ((|(1 + x) ^ (-(6 / 5 : ℝ))| *
              |(1 + x) ^ (2 / 5 : ℝ)|) *
            |Real.cos (theorem_4_15_nonperiodicCandidatePhase x)|) := by ring
    _ ≤ 12 / 5 * 1 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      calc
        (|(1 + x) ^ (-(6 / 5 : ℝ))| *
              |(1 + x) ^ (2 / 5 : ℝ)|) *
            |Real.cos (theorem_4_15_nonperiodicCandidatePhase x)| ≤
            1 * |Real.cos (theorem_4_15_nonperiodicCandidatePhase x)| :=
          mul_le_mul_of_nonneg_right hp (abs_nonneg _)
        _ ≤ 1 := by simpa using hc
    _ = 12 / 5 := by ring

theorem theorem_4_15_nonperiodicCandidateQSecond_mul_oscillationFirst_abs_le
    {x : ℝ} (hx : 0 ≤ x) :
    |theorem_4_15_nonperiodicCandidateQSecond x *
        theorem_4_15_nonperiodicCandidateOscillationFirst x| ≤
      (792 : ℝ) / 125 := by
  have hmono := theorem_4_15_nonperiodicCandidateQSecond_mul_phaseFirst_abs_le hx
  have hcos := Real.abs_cos_le_one
    (theorem_4_15_nonperiodicCandidatePhase x)
  rw [theorem_4_15_nonperiodicCandidateOscillationFirst, abs_mul, abs_mul]
  calc
    |theorem_4_15_nonperiodicCandidateQSecond x| *
        (|Real.cos (theorem_4_15_nonperiodicCandidatePhase x)| *
          |theorem_4_15_nonperiodicCandidatePhaseFirst x|) =
        |Real.cos (theorem_4_15_nonperiodicCandidatePhase x)| *
          |theorem_4_15_nonperiodicCandidateQSecond x *
            theorem_4_15_nonperiodicCandidatePhaseFirst x| := by
              rw [abs_mul]
              ring
    _ ≤ 1 * (792 / 125) :=
      mul_le_mul hcos hmono (abs_nonneg _) (by norm_num)
    _ = 792 / 125 := by ring

theorem theorem_4_15_nonperiodicCandidateQ_mul_oscillationSecond_abs_le
    {x : ℝ} (hx : 0 ≤ x) :
    |theorem_4_15_nonperiodicCandidateQ x *
        theorem_4_15_nonperiodicCandidateOscillationSecond x| ≤
      (168 : ℝ) / 25 := by
  have hsq := theorem_4_15_nonperiodicCandidateQ_mul_phaseFirst_sq_abs_le hx
  have hsecond := theorem_4_15_nonperiodicCandidateQ_mul_phaseSecond_abs_le hx
  have hsin := Real.abs_sin_le_one
    (theorem_4_15_nonperiodicCandidatePhase x)
  have hcos := Real.abs_cos_le_one
    (theorem_4_15_nonperiodicCandidatePhase x)
  rw [theorem_4_15_nonperiodicCandidateOscillationSecond, mul_add]
  calc
    |theorem_4_15_nonperiodicCandidateQ x *
          ((-Real.sin (theorem_4_15_nonperiodicCandidatePhase x) *
            theorem_4_15_nonperiodicCandidatePhaseFirst x) *
              theorem_4_15_nonperiodicCandidatePhaseFirst x) +
        theorem_4_15_nonperiodicCandidateQ x *
          (Real.cos (theorem_4_15_nonperiodicCandidatePhase x) *
            theorem_4_15_nonperiodicCandidatePhaseSecond x)| ≤
        |theorem_4_15_nonperiodicCandidateQ x *
          ((-Real.sin (theorem_4_15_nonperiodicCandidatePhase x) *
            theorem_4_15_nonperiodicCandidatePhaseFirst x) *
              theorem_4_15_nonperiodicCandidatePhaseFirst x)| +
        |theorem_4_15_nonperiodicCandidateQ x *
          (Real.cos (theorem_4_15_nonperiodicCandidatePhase x) *
            theorem_4_15_nonperiodicCandidatePhaseSecond x)| := abs_add_le _ _
    _ ≤ 1 * (144 / 25) + 1 * (24 / 25) := by
      apply add_le_add
      · calc
          |theorem_4_15_nonperiodicCandidateQ x *
            ((-Real.sin (theorem_4_15_nonperiodicCandidatePhase x) *
              theorem_4_15_nonperiodicCandidatePhaseFirst x) *
                theorem_4_15_nonperiodicCandidatePhaseFirst x)| =
              |Real.sin (theorem_4_15_nonperiodicCandidatePhase x)| *
                |theorem_4_15_nonperiodicCandidateQ x *
                  theorem_4_15_nonperiodicCandidatePhaseFirst x ^ 2| := by
                    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_neg, pow_two,
                      abs_mul]
                    ring
          _ ≤ 1 * (144 / 25) :=
            mul_le_mul hsin hsq (abs_nonneg _) (by norm_num)
      · calc
          |theorem_4_15_nonperiodicCandidateQ x *
            (Real.cos (theorem_4_15_nonperiodicCandidatePhase x) *
              theorem_4_15_nonperiodicCandidatePhaseSecond x)| =
              |Real.cos (theorem_4_15_nonperiodicCandidatePhase x)| *
                |theorem_4_15_nonperiodicCandidateQ x *
                  theorem_4_15_nonperiodicCandidatePhaseSecond x| := by
                    rw [abs_mul, abs_mul, abs_mul]
                    ring
          _ ≤ 1 * (24 / 25) :=
            mul_le_mul hcos hsecond (abs_nonneg _) (by norm_num)
    _ = 168 / 25 := by ring

theorem theorem_4_15_nonperiodicCandidateQFirst_mul_oscillationSecond_abs_le
    {x : ℝ} (hx : 0 ≤ x) :
    |theorem_4_15_nonperiodicCandidateQFirst x *
        theorem_4_15_nonperiodicCandidateOscillationSecond x| ≤
      (1008 : ℝ) / 125 := by
  have hsq := theorem_4_15_nonperiodicCandidateQFirst_mul_phaseFirst_sq_abs_le hx
  have hsecond := theorem_4_15_nonperiodicCandidateQFirst_mul_phaseSecond_abs_le hx
  have hsin := Real.abs_sin_le_one
    (theorem_4_15_nonperiodicCandidatePhase x)
  have hcos := Real.abs_cos_le_one
    (theorem_4_15_nonperiodicCandidatePhase x)
  rw [theorem_4_15_nonperiodicCandidateOscillationSecond, mul_add]
  calc
    |theorem_4_15_nonperiodicCandidateQFirst x *
          ((-Real.sin (theorem_4_15_nonperiodicCandidatePhase x) *
            theorem_4_15_nonperiodicCandidatePhaseFirst x) *
              theorem_4_15_nonperiodicCandidatePhaseFirst x) +
        theorem_4_15_nonperiodicCandidateQFirst x *
          (Real.cos (theorem_4_15_nonperiodicCandidatePhase x) *
            theorem_4_15_nonperiodicCandidatePhaseSecond x)| ≤
        |theorem_4_15_nonperiodicCandidateQFirst x *
          ((-Real.sin (theorem_4_15_nonperiodicCandidatePhase x) *
            theorem_4_15_nonperiodicCandidatePhaseFirst x) *
              theorem_4_15_nonperiodicCandidatePhaseFirst x)| +
        |theorem_4_15_nonperiodicCandidateQFirst x *
          (Real.cos (theorem_4_15_nonperiodicCandidatePhase x) *
            theorem_4_15_nonperiodicCandidatePhaseSecond x)| := abs_add_le _ _
    _ ≤ 1 * (864 / 125) + 1 * (144 / 125) := by
      apply add_le_add
      · calc
          |theorem_4_15_nonperiodicCandidateQFirst x *
            ((-Real.sin (theorem_4_15_nonperiodicCandidatePhase x) *
              theorem_4_15_nonperiodicCandidatePhaseFirst x) *
                theorem_4_15_nonperiodicCandidatePhaseFirst x)| =
              |Real.sin (theorem_4_15_nonperiodicCandidatePhase x)| *
                |theorem_4_15_nonperiodicCandidateQFirst x *
                  theorem_4_15_nonperiodicCandidatePhaseFirst x ^ 2| := by
                    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_neg, pow_two,
                      abs_mul]
                    ring
          _ ≤ 1 * (864 / 125) :=
            mul_le_mul hsin hsq (abs_nonneg _) (by norm_num)
      · calc
          |theorem_4_15_nonperiodicCandidateQFirst x *
            (Real.cos (theorem_4_15_nonperiodicCandidatePhase x) *
              theorem_4_15_nonperiodicCandidatePhaseSecond x)| =
              |Real.cos (theorem_4_15_nonperiodicCandidatePhase x)| *
                |theorem_4_15_nonperiodicCandidateQFirst x *
                  theorem_4_15_nonperiodicCandidatePhaseSecond x| := by
                    rw [abs_mul, abs_mul, abs_mul]
                    ring
          _ ≤ 1 * (144 / 125) :=
            mul_le_mul hcos hsecond (abs_nonneg _) (by norm_num)
    _ = 1008 / 125 := by ring

theorem theorem_4_15_nonperiodicCandidateQ_mul_oscillationThird_abs_le
    {x : ℝ} (hx : 0 ≤ x) :
    |theorem_4_15_nonperiodicCandidateQ x *
        theorem_4_15_nonperiodicCandidateOscillationThird x| ≤
      (2664 : ℝ) / 125 := by
  have hcube := theorem_4_15_nonperiodicCandidateQ_mul_phaseFirst_cube_abs_le hx
  have hmixed :=
    theorem_4_15_nonperiodicCandidateQ_mul_phaseFirst_mul_phaseSecond_abs_le hx
  have hthird := theorem_4_15_nonperiodicCandidateQ_mul_phaseThird_abs_le hx
  have hsin := Real.abs_sin_le_one
    (theorem_4_15_nonperiodicCandidatePhase x)
  have hcos := Real.abs_cos_le_one
    (theorem_4_15_nonperiodicCandidatePhase x)
  rw [theorem_4_15_nonperiodicCandidateOscillationThird, mul_add, mul_sub]
  calc
    |(theorem_4_15_nonperiodicCandidateQ x *
          (-Real.cos (theorem_4_15_nonperiodicCandidatePhase x) *
            theorem_4_15_nonperiodicCandidatePhaseFirst x ^ 3) -
        theorem_4_15_nonperiodicCandidateQ x *
          (3 * Real.sin (theorem_4_15_nonperiodicCandidatePhase x) *
            theorem_4_15_nonperiodicCandidatePhaseFirst x *
              theorem_4_15_nonperiodicCandidatePhaseSecond x)) +
        theorem_4_15_nonperiodicCandidateQ x *
          (Real.cos (theorem_4_15_nonperiodicCandidatePhase x) *
            theorem_4_15_nonperiodicCandidatePhaseThird x)| ≤
        (|theorem_4_15_nonperiodicCandidateQ x *
          (-Real.cos (theorem_4_15_nonperiodicCandidatePhase x) *
            theorem_4_15_nonperiodicCandidatePhaseFirst x ^ 3)| +
        |theorem_4_15_nonperiodicCandidateQ x *
          (3 * Real.sin (theorem_4_15_nonperiodicCandidatePhase x) *
            theorem_4_15_nonperiodicCandidatePhaseFirst x *
              theorem_4_15_nonperiodicCandidatePhaseSecond x)|) +
        |theorem_4_15_nonperiodicCandidateQ x *
          (Real.cos (theorem_4_15_nonperiodicCandidatePhase x) *
            theorem_4_15_nonperiodicCandidatePhaseThird x)| :=
      (abs_add_le _ _).trans (add_le_add_left (abs_sub _ _) _)
    _ ≤ (1 * (1728 / 125) + 3 * 1 * (288 / 125)) +
        1 * (72 / 125) := by
      apply add_le_add
      · apply add_le_add
        · calc
            |theorem_4_15_nonperiodicCandidateQ x *
              (-Real.cos (theorem_4_15_nonperiodicCandidatePhase x) *
                theorem_4_15_nonperiodicCandidatePhaseFirst x ^ 3)| =
                |Real.cos (theorem_4_15_nonperiodicCandidatePhase x)| *
                  |theorem_4_15_nonperiodicCandidateQ x *
                    theorem_4_15_nonperiodicCandidatePhaseFirst x ^ 3| := by
                      rw [abs_mul, abs_mul, abs_neg, abs_mul]
                      ring
            _ ≤ 1 * (1728 / 125) :=
              mul_le_mul hcos hcube (abs_nonneg _) (by norm_num)
        · calc
            |theorem_4_15_nonperiodicCandidateQ x *
              (3 * Real.sin (theorem_4_15_nonperiodicCandidatePhase x) *
                theorem_4_15_nonperiodicCandidatePhaseFirst x *
                  theorem_4_15_nonperiodicCandidatePhaseSecond x)| =
                3 * |Real.sin (theorem_4_15_nonperiodicCandidatePhase x)| *
                  |theorem_4_15_nonperiodicCandidateQ x *
                    theorem_4_15_nonperiodicCandidatePhaseFirst x *
                      theorem_4_15_nonperiodicCandidatePhaseSecond x| := by
                        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul]
                        norm_num
                        ring
            _ ≤ 3 * 1 * (288 / 125) := by
              calc
                3 * |Real.sin (theorem_4_15_nonperiodicCandidatePhase x)| *
                    |theorem_4_15_nonperiodicCandidateQ x *
                      theorem_4_15_nonperiodicCandidatePhaseFirst x *
                        theorem_4_15_nonperiodicCandidatePhaseSecond x| =
                    3 * (|Real.sin (theorem_4_15_nonperiodicCandidatePhase x)| *
                      |theorem_4_15_nonperiodicCandidateQ x *
                        theorem_4_15_nonperiodicCandidatePhaseFirst x *
                          theorem_4_15_nonperiodicCandidatePhaseSecond x|) := by ring
                _ ≤ 3 * (1 * (288 / 125)) :=
                  mul_le_mul_of_nonneg_left
                    (mul_le_mul hsin hmixed (abs_nonneg _) (by norm_num))
                    (by norm_num)
                _ = 3 * 1 * (288 / 125) := by ring
      · calc
          |theorem_4_15_nonperiodicCandidateQ x *
            (Real.cos (theorem_4_15_nonperiodicCandidatePhase x) *
              theorem_4_15_nonperiodicCandidatePhaseThird x)| =
              |Real.cos (theorem_4_15_nonperiodicCandidatePhase x)| *
                |theorem_4_15_nonperiodicCandidateQ x *
                  theorem_4_15_nonperiodicCandidatePhaseThird x| := by
                    rw [abs_mul, abs_mul, abs_mul]
                    ring
          _ ≤ 1 * (72 / 125) :=
            mul_le_mul hcos hthird (abs_nonneg _) (by norm_num)
    _ = 2664 / 125 := by ring

theorem theorem_4_15_nonperiodicCandidatePFirst_abs_le
    {x : ℝ} (hx : 0 ≤ x) :
    |theorem_4_15_nonperiodicCandidatePFirst x| ≤ (6 : ℝ) := by
  have hqFirst := theorem_4_15_nonperiodicCandidateQFirst_abs_le hx
  have hosc := theorem_4_15_nonperiodicCandidateOscillation_abs_le_three x
  have hoscFirst :=
    theorem_4_15_nonperiodicCandidateQ_mul_oscillationFirst_abs_le hx
  have hA : |theorem_4_15_nonperiodicCandidateQFirst x *
      theorem_4_15_nonperiodicCandidateOscillation x| ≤ (18 : ℝ) / 5 := by
    rw [abs_mul]
    calc
      |theorem_4_15_nonperiodicCandidateQFirst x| *
          |theorem_4_15_nonperiodicCandidateOscillation x| ≤
          (6 / 5) * 3 :=
        mul_le_mul hqFirst hosc (abs_nonneg _) (by norm_num)
      _ = 18 / 5 := by ring
  rw [theorem_4_15_nonperiodicCandidatePFirst]
  calc
    |theorem_4_15_nonperiodicCandidateQFirst x *
          theorem_4_15_nonperiodicCandidateOscillation x +
        theorem_4_15_nonperiodicCandidateQ x *
          theorem_4_15_nonperiodicCandidateOscillationFirst x| ≤
        |theorem_4_15_nonperiodicCandidateQFirst x *
          theorem_4_15_nonperiodicCandidateOscillation x| +
        |theorem_4_15_nonperiodicCandidateQ x *
          theorem_4_15_nonperiodicCandidateOscillationFirst x| := abs_add_le _ _
    _ ≤ 18 / 5 + 12 / 5 := add_le_add hA hoscFirst
    _ = 6 := by ring

theorem theorem_4_15_nonperiodicCandidatePositiveProfileFirst_abs_le
    {x : ℝ} (hx : 0 ≤ x) :
    |theorem_4_15_nonperiodicCandidatePositiveProfileFirst x| ≤ 9 := by
  have hpFirst := theorem_4_15_nonperiodicCandidatePFirst_abs_le hx
  have hq := theorem_4_15_nonperiodicCandidateQ_abs_le_one hx
  have hpPos := theorem_4_15_nonperiodicCandidateP_pos (by linarith : -1 < x)
  have hpUpper :=
    (theorem_4_15_nonperiodicCandidateP_envelope (by linarith : -1 < x)).2
  have hqNonneg : 0 ≤ theorem_4_15_nonperiodicCandidateQ x := by
    exact Real.rpow_nonneg (by linarith) _
  have hqUpper : theorem_4_15_nonperiodicCandidateQ x ≤ 1 := by
    rw [abs_of_nonneg hqNonneg] at hq
    exact hq
  have hpAbs : |theorem_4_15_nonperiodicCandidateP x| ≤ 3 := by
    rw [abs_of_pos hpPos]
    exact hpUpper.trans (by nlinarith)
  rw [theorem_4_15_nonperiodicCandidatePositiveProfileFirst]
  calc
    |-theorem_4_15_nonperiodicCandidatePFirst x -
        theorem_4_15_nonperiodicCandidateP x| ≤
        |theorem_4_15_nonperiodicCandidatePFirst x| +
          |theorem_4_15_nonperiodicCandidateP x| := by
      simpa only [abs_neg] using
        (abs_add_le (-theorem_4_15_nonperiodicCandidatePFirst x)
          (-theorem_4_15_nonperiodicCandidateP x))
    _ ≤ 6 + 3 := add_le_add hpFirst hpAbs
    _ = 9 := by norm_num

/- Exact separation of the oscillatory leading gradient from the integrable
   lower-order remainder.  This is the scalar identity needed for the
   discrete lower-density counterexample route; it is not an asymptotic or an
   arbitrary-trajectory approximation. -/
theorem theorem_4_15_nonperiodicCandidate_gradient_leading_error_eq
    {x : ℝ} (hx : 0 ≤ x) :
    theorem_4_15_nonperiodicCandidatePositiveProfileFirst x +
        theorem_4_15_nonperiodicCandidateGradientLeading x =
      -theorem_4_15_nonperiodicCandidateQFirst x *
          theorem_4_15_nonperiodicCandidateOscillation x -
        theorem_4_15_nonperiodicCandidateP x := by
  have hz : 0 < 1 + x := by linarith
  have hleading :
      theorem_4_15_nonperiodicCandidateQ x *
          theorem_4_15_nonperiodicCandidateOscillationFirst x =
        theorem_4_15_nonperiodicCandidateGradientLeading x := by
    unfold theorem_4_15_nonperiodicCandidateQ
      theorem_4_15_nonperiodicCandidateOscillationFirst
      theorem_4_15_nonperiodicCandidatePhaseFirst
      theorem_4_15_nonperiodicCandidateGradientLeading
    calc
      (1 + x) ^ (-(6 : ℝ) / 5) *
          (Real.cos (theorem_4_15_nonperiodicCandidatePhase x) *
            ((12 : ℝ) / 5 * (1 + x) ^ ((2 : ℝ) / 5))) =
          (12 / 5) *
            ((1 + x) ^ (-(6 : ℝ) / 5) *
              (1 + x) ^ ((2 : ℝ) / 5)) *
            Real.cos (theorem_4_15_nonperiodicCandidatePhase x) := by ring
      _ = (12 / 5) * (1 + x) ^ (-(4 : ℝ) / 5) *
            Real.cos (theorem_4_15_nonperiodicCandidatePhase x) := by
        rw [← Real.rpow_add hz]
        norm_num
  rw [theorem_4_15_nonperiodicCandidatePositiveProfileFirst,
    theorem_4_15_nonperiodicCandidatePFirst, ← hleading]
  ring

/- The discarded part in the preceding identity has a fixed integrable
   envelope.  The bound retains the actual phase and power law and therefore
   can be summed independently of the desired stationarity average. -/
theorem theorem_4_15_nonperiodicCandidate_gradient_leading_error_abs_le
    {x : ℝ} (hx : 0 ≤ x) :
    |theorem_4_15_nonperiodicCandidatePositiveProfileFirst x +
        theorem_4_15_nonperiodicCandidateGradientLeading x| ≤
      (33 : ℝ) / 5 * (1 + x) ^ (-(6 : ℝ) / 5) := by
  have hz : 0 < 1 + x := by linarith
  have hbase : 1 ≤ 1 + x := by linarith
  have hosc := theorem_4_15_nonperiodicCandidateOscillation_abs_le_three x
  have hqFirstNonneg :
      0 ≤ (1 + x) ^ (-(11 : ℝ) / 5) := Real.rpow_nonneg hz.le _
  have hqNonneg :
      0 ≤ (1 + x) ^ (-(6 : ℝ) / 5) := Real.rpow_nonneg hz.le _
  have hpow :
      (1 + x) ^ (-(11 : ℝ) / 5) ≤
        (1 + x) ^ (-(6 : ℝ) / 5) :=
    Real.rpow_le_rpow_of_exponent_le hbase (by norm_num)
  have hfirst :
      |theorem_4_15_nonperiodicCandidateQFirst x *
          theorem_4_15_nonperiodicCandidateOscillation x| ≤
        (18 : ℝ) / 5 * (1 + x) ^ (-(6 : ℝ) / 5) := by
    rw [abs_mul, theorem_4_15_nonperiodicCandidateQFirst, abs_mul,
      abs_of_nonneg hqFirstNonneg]
    have hcoefficient : |(-(6 : ℝ) / 5)| = 6 / 5 := by norm_num
    rw [hcoefficient]
    have hmul := mul_le_mul_of_nonneg_left hpow
      (show (0 : ℝ) ≤ 18 / 5 by norm_num)
    calc
      (6 / 5 * (1 + x) ^ (-(11 : ℝ) / 5)) *
          |theorem_4_15_nonperiodicCandidateOscillation x| ≤
          (6 / 5 * (1 + x) ^ (-(11 : ℝ) / 5)) * 3 :=
        mul_le_mul_of_nonneg_left hosc
          (mul_nonneg (by norm_num) hqFirstNonneg)
      _ = (18 / 5) * (1 + x) ^ (-(11 : ℝ) / 5) := by ring
      _ ≤ (18 / 5) * (1 + x) ^ (-(6 : ℝ) / 5) := hmul
  have hpPos := theorem_4_15_nonperiodicCandidateP_pos (by linarith : -1 < x)
  have hpUpper :=
    (theorem_4_15_nonperiodicCandidateP_envelope (by linarith : -1 < x)).2
  have hp : |theorem_4_15_nonperiodicCandidateP x| ≤
      3 * (1 + x) ^ (-(6 : ℝ) / 5) := by
    rw [abs_of_pos hpPos]
    simpa [theorem_4_15_nonperiodicCandidateQ] using hpUpper
  rw [theorem_4_15_nonperiodicCandidate_gradient_leading_error_eq hx]
  calc
    |-theorem_4_15_nonperiodicCandidateQFirst x *
          theorem_4_15_nonperiodicCandidateOscillation x -
        theorem_4_15_nonperiodicCandidateP x| ≤
        |theorem_4_15_nonperiodicCandidateQFirst x *
          theorem_4_15_nonperiodicCandidateOscillation x| +
        |theorem_4_15_nonperiodicCandidateP x| := by
      rw [sub_eq_add_neg]
      simpa only [abs_neg, neg_mul] using
        (abs_add_le
          (-theorem_4_15_nonperiodicCandidateQFirst x *
            theorem_4_15_nonperiodicCandidateOscillation x)
          (-theorem_4_15_nonperiodicCandidateP x))
    _ ≤ (18 / 5) * (1 + x) ^ (-(6 : ℝ) / 5) +
          3 * (1 + x) ^ (-(6 : ℝ) / 5) := add_le_add hfirst hp
    _ = (33 / 5) * (1 + x) ^ (-(6 : ℝ) / 5) := by ring

/- Pointwise lower bound feeding the remaining discrete-density argument.
   Unlike a triangle-inequality absorption through the generated average, its
   error is the independently summable power-law envelope above. -/
theorem theorem_4_15_nonperiodicCandidate_gradient_abs_lower
    {x : ℝ} (hx : 0 ≤ x) :
    |theorem_4_15_nonperiodicCandidateGradientLeading x| -
        (33 : ℝ) / 5 * (1 + x) ^ (-(6 : ℝ) / 5) ≤
      |theorem_4_15_nonperiodicCandidatePositiveProfileFirst x| := by
  have herr :=
    theorem_4_15_nonperiodicCandidate_gradient_leading_error_abs_le hx
  have htriangle :
      |theorem_4_15_nonperiodicCandidateGradientLeading x| ≤
        |theorem_4_15_nonperiodicCandidatePositiveProfileFirst x| +
          |theorem_4_15_nonperiodicCandidatePositiveProfileFirst x +
            theorem_4_15_nonperiodicCandidateGradientLeading x| := by
    calc
      |theorem_4_15_nonperiodicCandidateGradientLeading x| =
          |(theorem_4_15_nonperiodicCandidatePositiveProfileFirst x +
              theorem_4_15_nonperiodicCandidateGradientLeading x) +
            (-theorem_4_15_nonperiodicCandidatePositiveProfileFirst x)| := by
        congr 1
        ring
      _ ≤ |theorem_4_15_nonperiodicCandidatePositiveProfileFirst x +
              theorem_4_15_nonperiodicCandidateGradientLeading x| +
            |-theorem_4_15_nonperiodicCandidatePositiveProfileFirst x| :=
        abs_add_le _ _
      _ = |theorem_4_15_nonperiodicCandidatePositiveProfileFirst x| +
            |theorem_4_15_nonperiodicCandidatePositiveProfileFirst x +
              theorem_4_15_nonperiodicCandidateGradientLeading x| := by
        rw [abs_neg]
        ring
  linarith

/- Specialization to the exact generated grid `x_t = t * epsilon^2/sigma^2`.
   The only remaining analytic milestone is therefore a lower-density bound
   for the displayed leading cosine sum; the lower-order contribution already
   has the independent power-law envelope on this same grid. -/
theorem theorem_4_15_nonperiodicCandidate_discrete_gradient_abs_lower
    (epsilon : ℝ) (t : ℕ) :
    |theorem_4_15_nonperiodicCandidateGradientLeading
        ((t : ℝ) *
          (epsilon ^ 2 / theorem_4_15_nonperiodicCandidateSigma ^ 2))| -
      (33 : ℝ) / 5 *
        (1 + (t : ℝ) *
          (epsilon ^ 2 / theorem_4_15_nonperiodicCandidateSigma ^ 2)) ^
            (-(6 : ℝ) / 5) ≤
      |theorem_4_15_nonperiodicCandidatePositiveProfileFirst
        ((t : ℝ) *
          (epsilon ^ 2 / theorem_4_15_nonperiodicCandidateSigma ^ 2))| := by
  apply theorem_4_15_nonperiodicCandidate_gradient_abs_lower
  positivity

/- The lower-order envelope is summable uniformly on every positive mesh.
   This is the integral-test estimate needed to keep the discarded gradient
   terms separate from the oscillatory leading term.  In particular, its
   right side contains no stationarity average and no cross/Jstar quantity. -/
theorem theorem_4_15_nonperiodicCandidate_remainder_mesh_sum_le
    (h : ℝ) (N : ℕ) (hh : 0 < h) :
    h * (∑ t ∈ Finset.range (N + 1),
      (1 + (t : ℝ) * h) ^ (-(6 : ℝ) / 5)) ≤ h + 5 := by
  let g : ℝ → ℝ := fun x => (1 + x * h) ^ (-(6 : ℝ) / 5)
  have hganti : AntitoneOn g (Set.Icc 0 (0 + (N : ℝ))) := by
    intro x hx y hy hxy
    apply Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num)
    · dsimp [g]
      simp only [Set.mem_Ioi]
      nlinarith [mul_nonneg hx.1 hh.le]
    · dsimp [g]
      simp only [Set.mem_Ioi]
      nlinarith [mul_nonneg hy.1 hh.le]
    · dsimp [g]
      have hmul : x * h ≤ y * h :=
        mul_le_mul_of_nonneg_right hxy hh.le
      linarith
  have hsumInt := hganti.sum_le_integral
  have hsumInt' :
      (∑ t ∈ Finset.range N, g ((t + 1 : ℕ) : ℝ)) ≤
        ∫ x in (0 : ℝ)..(N : ℝ), g x := by
    simpa using hsumInt
  have hmulInt := mul_le_mul_of_nonneg_left hsumInt' hh.le
  have hchange :
      h * (∫ x in (0 : ℝ)..(N : ℝ), g x) =
        ∫ u in (1 : ℝ)..1 + (N : ℝ) * h,
          u ^ (-(6 : ℝ) / 5) := by
    simpa [g, add_comm, mul_comm, mul_left_comm, mul_assoc] using
      (intervalIntegral.mul_integral_comp_mul_add
        (a := (0 : ℝ)) (b := (N : ℝ))
        (f := fun u : ℝ => u ^ (-(6 : ℝ) / 5)) h 1)
  have hupperPos : 0 < 1 + (N : ℝ) * h := by positivity
  have hzeroNot : (0 : ℝ) ∉ Set.uIcc 1 (1 + (N : ℝ) * h) := by
    rw [Set.mem_uIcc]
    rintro (hcase | hcase) <;> linarith
  have hint :
      (∫ u in (1 : ℝ)..1 + (N : ℝ) * h,
        u ^ (-(6 : ℝ) / 5)) =
      5 * (1 - (1 + (N : ℝ) * h) ^ (-(1 : ℝ) / 5)) := by
    rw [integral_rpow (Or.inr ⟨by norm_num, hzeroNot⟩)]
    rw [Real.one_rpow]
    norm_num
    ring
  have hpowNonneg :
      0 ≤ (1 + (N : ℝ) * h) ^ (-(1 : ℝ) / 5) :=
    Real.rpow_nonneg hupperPos.le _
  have htail :
      h * (∑ t ∈ Finset.range N, g ((t + 1 : ℕ) : ℝ)) ≤ 5 := by
    calc
      h * (∑ t ∈ Finset.range N, g ((t + 1 : ℕ) : ℝ)) ≤
          h * (∫ x in (0 : ℝ)..(N : ℝ), g x) := hmulInt
      _ = 5 * (1 - (1 + (N : ℝ) * h) ^ (-(1 : ℝ) / 5)) := by
        rw [hchange, hint]
      _ ≤ 5 := by nlinarith
  have hsumDecomp :
      (∑ t ∈ Finset.range (N + 1),
        (1 + (t : ℝ) * h) ^ (-(6 : ℝ) / 5)) =
      (∑ t ∈ Finset.range N, g ((t + 1 : ℕ) : ℝ)) + 1 := by
    rw [Finset.sum_range_succ']
    simp [g]
  rw [hsumDecomp]
  calc
    h * ((∑ t ∈ Finset.range N, g ((t + 1 : ℕ) : ℝ)) + 1) =
        h * (∑ t ∈ Finset.range N, g ((t + 1 : ℕ) : ℝ)) + h := by ring
    _ ≤ 5 + h := by linarith
    _ = h + 5 := by ring

/- Normalizing the preceding estimate exposes the exact quantity needed at a
   finite generated horizon. -/
theorem theorem_4_15_nonperiodicCandidate_remainder_mesh_average_le
    (h : ℝ) (N : ℕ) (hh : 0 < h) (hN : 0 < N) :
    ((N : ℝ)⁻¹) * (∑ t ∈ Finset.range N,
      (1 + (t : ℝ) * h) ^ (-(6 : ℝ) / 5)) ≤
      (h + 5) / ((N : ℝ) * h) := by
  obtain ⟨K, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  have hmesh :=
    theorem_4_15_nonperiodicCandidate_remainder_mesh_sum_le h K hh
  have hdenom : 0 < ((K + 1 : ℕ) : ℝ) * h :=
    mul_pos (by positivity) hh
  apply (le_div_iff₀ hdenom).2
  have heq :
      ((↑(K + 1) : ℝ)⁻¹ *
          (∑ t ∈ Finset.range (K + 1),
            (1 + (t : ℝ) * h) ^ (-(6 : ℝ) / 5))) *
        ((K + 1 : ℕ) * h) =
      h * (∑ t ∈ Finset.range (K + 1),
        (1 + (t : ℝ) * h) ^ (-(6 : ℝ) / 5)) := by
    have hne : ((K + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    calc
      _ = (((↑(K + 1) : ℝ)⁻¹ * ((K + 1 : ℕ) : ℝ)) * h) *
          (∑ t ∈ Finset.range (K + 1),
            (1 + (t : ℝ) * h) ^ (-(6 : ℝ) / 5)) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hne, one_mul]
  rw [heq]
  exact hmesh

theorem theorem_4_15_nonperiodicCandidatePSecond_abs_le
    {x : ℝ} (hx : 0 ≤ x) :
    |theorem_4_15_nonperiodicCandidatePSecond x| ≤ (510 : ℝ) / 25 := by
  have hqSecond := theorem_4_15_nonperiodicCandidateQSecond_abs_le hx
  have hosc := theorem_4_15_nonperiodicCandidateOscillation_abs_le_three x
  have hfirst :=
    theorem_4_15_nonperiodicCandidateQFirst_mul_oscillationFirst_abs_le hx
  have hsecond :=
    theorem_4_15_nonperiodicCandidateQ_mul_oscillationSecond_abs_le hx
  have hA : |theorem_4_15_nonperiodicCandidateQSecond x *
      theorem_4_15_nonperiodicCandidateOscillation x| ≤ (198 : ℝ) / 25 := by
    rw [abs_mul]
    calc
      |theorem_4_15_nonperiodicCandidateQSecond x| *
          |theorem_4_15_nonperiodicCandidateOscillation x| ≤
          (66 / 25) * 3 :=
        mul_le_mul hqSecond hosc (abs_nonneg _) (by norm_num)
      _ = 198 / 25 := by ring
  have hB : |2 * theorem_4_15_nonperiodicCandidateQFirst x *
      theorem_4_15_nonperiodicCandidateOscillationFirst x| ≤
      (144 : ℝ) / 25 := by
    calc
      |2 * theorem_4_15_nonperiodicCandidateQFirst x *
          theorem_4_15_nonperiodicCandidateOscillationFirst x| =
          2 * |theorem_4_15_nonperiodicCandidateQFirst x *
            theorem_4_15_nonperiodicCandidateOscillationFirst x| := by
              rw [abs_mul, abs_mul]
              norm_num
              ring
      _ ≤ 2 * (72 / 25) := mul_le_mul_of_nonneg_left hfirst (by norm_num)
      _ = 144 / 25 := by ring
  rw [theorem_4_15_nonperiodicCandidatePSecond]
  calc
    |theorem_4_15_nonperiodicCandidateQSecond x *
          theorem_4_15_nonperiodicCandidateOscillation x +
        2 * theorem_4_15_nonperiodicCandidateQFirst x *
          theorem_4_15_nonperiodicCandidateOscillationFirst x +
        theorem_4_15_nonperiodicCandidateQ x *
          theorem_4_15_nonperiodicCandidateOscillationSecond x| ≤
        (|theorem_4_15_nonperiodicCandidateQSecond x *
          theorem_4_15_nonperiodicCandidateOscillation x| +
        |2 * theorem_4_15_nonperiodicCandidateQFirst x *
          theorem_4_15_nonperiodicCandidateOscillationFirst x|) +
        |theorem_4_15_nonperiodicCandidateQ x *
          theorem_4_15_nonperiodicCandidateOscillationSecond x| :=
      (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
    _ ≤ (198 / 25 + 144 / 25) + 168 / 25 :=
      add_le_add (add_le_add hA hB) hsecond
    _ = 510 / 25 := by ring

/- The derivative of `P` is uniformly bounded and Lipschitz on the complete
   generated ray.  The second estimate is the quantitative cancellation input
   for the transformed momentum `M_t + P(x_t)`; importantly, neither estimate
   refers to a trajectory or to the desired stationarity conclusion. -/
theorem theorem_4_15_nonperiodicCandidatePFirst_lipschitz
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |theorem_4_15_nonperiodicCandidatePFirst y -
        theorem_4_15_nonperiodicCandidatePFirst x| ≤
      ((510 : ℝ) / 25) * |y - x| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Set.Ici (0 : ℝ))
    (f := theorem_4_15_nonperiodicCandidatePFirst)
    (C := (510 : ℝ) / 25)
    (fun z hz =>
      (theorem_4_15_nonperiodicCandidatePFirst_hasDerivAt
        (by exact lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) hz)).differentiableAt)
    (fun z hz => by
      rw [(theorem_4_15_nonperiodicCandidatePFirst_hasDerivAt
        (by exact lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) hz)).deriv,
        Real.norm_eq_abs]
      exact theorem_4_15_nonperiodicCandidatePSecond_abs_le hz)
    (convex_Ici (0 : ℝ)) hx hy
  simpa [Real.norm_eq_abs] using h

theorem theorem_4_15_nonperiodicCandidateP_forward_remainder
    {x h : ℝ} (hx : 0 ≤ x) (hh : 0 < h) :
    |theorem_4_15_nonperiodicCandidateP (x + h) -
          theorem_4_15_nonperiodicCandidateP x -
        h * theorem_4_15_nonperiodicCandidatePFirst (x + h)| ≤
      ((510 : ℝ) / 25) * h ^ 2 := by
  have hxy : x < x + h := by linarith
  have hcont : ContinuousOn theorem_4_15_nonperiodicCandidateP
      (Set.Icc x (x + h)) := by
    intro z hz
    exact (theorem_4_15_nonperiodicCandidateP_hasDerivAt_first
      (by linarith [hx, hz.1])).continuousAt.continuousWithinAt
  have hderiv : ∀ z ∈ Set.Ioo x (x + h),
      HasDerivAt theorem_4_15_nonperiodicCandidateP
        (theorem_4_15_nonperiodicCandidatePFirst z) z := by
    intro z hz
    exact theorem_4_15_nonperiodicCandidateP_hasDerivAt_first
      (by linarith [hx, hz.1])
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope
    theorem_4_15_nonperiodicCandidateP
    theorem_4_15_nonperiodicCandidatePFirst hxy hcont hderiv
  have hdelta : theorem_4_15_nonperiodicCandidateP (x + h) -
      theorem_4_15_nonperiodicCandidateP x =
        h * theorem_4_15_nonperiodicCandidatePFirst c := by
    have hhne : h ≠ 0 := ne_of_gt hh
    rw [show x + h - x = h by ring] at hslope
    calc
      theorem_4_15_nonperiodicCandidateP (x + h) -
          theorem_4_15_nonperiodicCandidateP x =
          theorem_4_15_nonperiodicCandidatePFirst c * h :=
        ((eq_div_iff hhne).mp hslope).symm
      _ = h * theorem_4_15_nonperiodicCandidatePFirst c := by ring
  have hlip := theorem_4_15_nonperiodicCandidatePFirst_lipschitz
    (x := x + h) (y := c) (by linarith) (by linarith [hx, hc.1])
  rw [hdelta]
  have hdist : |c - (x + h)| ≤ h := by
    rw [abs_of_nonpos (by linarith [hc.2])]
    linarith [hc.1]
  calc
    |h * theorem_4_15_nonperiodicCandidatePFirst c -
        h * theorem_4_15_nonperiodicCandidatePFirst (x + h)| =
        h * |theorem_4_15_nonperiodicCandidatePFirst c -
          theorem_4_15_nonperiodicCandidatePFirst (x + h)| := by
            rw [← mul_sub, abs_mul, abs_of_pos hh]
    _ ≤ h * (((510 : ℝ) / 25) * |c - (x + h)|) :=
      mul_le_mul_of_nonneg_left hlip hh.le
    _ ≤ h * (((510 : ℝ) / 25) * h) := by
      gcongr
    _ = ((510 : ℝ) / 25) * h ^ 2 := by ring

theorem theorem_4_15_nonperiodicCandidateP_weighted_forward_remainder
    {x h beta : ℝ} (hx : 0 ≤ x) (hh : 0 < h)
    (hbeta_nonneg : 0 ≤ beta) (hbeta_le : beta ≤ 1)
    (hstep : h = 1 - beta) :
    |beta * (theorem_4_15_nonperiodicCandidateP (x + h) -
          theorem_4_15_nonperiodicCandidateP x) -
        h * theorem_4_15_nonperiodicCandidatePFirst (x + h)| ≤
      ((660 : ℝ) / 25) * h ^ 2 := by
  have hrem := theorem_4_15_nonperiodicCandidateP_forward_remainder hx hh
  have hfirst := theorem_4_15_nonperiodicCandidatePFirst_abs_le
    (show 0 ≤ x + h by linarith)
  have hbeta_abs : |beta| ≤ 1 := by
    rw [abs_of_nonneg hbeta_nonneg]
    exact hbeta_le
  calc
    |beta * (theorem_4_15_nonperiodicCandidateP (x + h) -
          theorem_4_15_nonperiodicCandidateP x) -
        h * theorem_4_15_nonperiodicCandidatePFirst (x + h)| =
      |beta * (theorem_4_15_nonperiodicCandidateP (x + h) -
            theorem_4_15_nonperiodicCandidateP x -
          h * theorem_4_15_nonperiodicCandidatePFirst (x + h)) -
        h ^ 2 * theorem_4_15_nonperiodicCandidatePFirst (x + h)| := by
          rw [hstep]
          congr 1
          ring
    _ ≤ |beta * (theorem_4_15_nonperiodicCandidateP (x + h) -
            theorem_4_15_nonperiodicCandidateP x -
          h * theorem_4_15_nonperiodicCandidatePFirst (x + h))| +
        |h ^ 2 * theorem_4_15_nonperiodicCandidatePFirst (x + h)| :=
      by
        simpa only [sub_eq_add_neg, abs_neg] using
          (abs_add_le
            (beta * (theorem_4_15_nonperiodicCandidateP (x + h) -
              theorem_4_15_nonperiodicCandidateP x -
              h * theorem_4_15_nonperiodicCandidatePFirst (x + h)))
            (-(h ^ 2 * theorem_4_15_nonperiodicCandidatePFirst (x + h))))
    _ = |beta| *
          |theorem_4_15_nonperiodicCandidateP (x + h) -
              theorem_4_15_nonperiodicCandidateP x -
            h * theorem_4_15_nonperiodicCandidatePFirst (x + h)| +
        h ^ 2 * |theorem_4_15_nonperiodicCandidatePFirst (x + h)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg h)]
    _ ≤ 1 * (((510 : ℝ) / 25) * h ^ 2) + h ^ 2 * 6 := by
      exact add_le_add
        (mul_le_mul hbeta_abs hrem (abs_nonneg _) (by positivity))
        (mul_le_mul_of_nonneg_left hfirst (sq_nonneg h))
    _ = ((660 : ℝ) / 25) * h ^ 2 := by ring

theorem theorem_4_15_nonperiodicCandidatePThird_abs_le
    {x : ℝ} (hx : 0 ≤ x) :
    |theorem_4_15_nonperiodicCandidatePThird x| ≤ (11232 : ℝ) / 125 := by
  have hqThird := theorem_4_15_nonperiodicCandidateQThird_abs_le hx
  have hosc := theorem_4_15_nonperiodicCandidateOscillation_abs_le_three x
  have hfirst :=
    theorem_4_15_nonperiodicCandidateQSecond_mul_oscillationFirst_abs_le hx
  have hsecond :=
    theorem_4_15_nonperiodicCandidateQFirst_mul_oscillationSecond_abs_le hx
  have hthird := theorem_4_15_nonperiodicCandidateQ_mul_oscillationThird_abs_le hx
  have hA : |theorem_4_15_nonperiodicCandidateQThird x *
      theorem_4_15_nonperiodicCandidateOscillation x| ≤ (3168 : ℝ) / 125 := by
    rw [abs_mul]
    calc
      |theorem_4_15_nonperiodicCandidateQThird x| *
          |theorem_4_15_nonperiodicCandidateOscillation x| ≤
          (1056 / 125) * 3 :=
        mul_le_mul hqThird hosc (abs_nonneg _) (by norm_num)
      _ = 3168 / 125 := by ring
  have hB : |3 * theorem_4_15_nonperiodicCandidateQSecond x *
      theorem_4_15_nonperiodicCandidateOscillationFirst x| ≤
      (2376 : ℝ) / 125 := by
    calc
      |3 * theorem_4_15_nonperiodicCandidateQSecond x *
          theorem_4_15_nonperiodicCandidateOscillationFirst x| =
          3 * |theorem_4_15_nonperiodicCandidateQSecond x *
            theorem_4_15_nonperiodicCandidateOscillationFirst x| := by
              rw [abs_mul, abs_mul]
              norm_num
              ring
      _ ≤ 3 * (792 / 125) := mul_le_mul_of_nonneg_left hfirst (by norm_num)
      _ = 2376 / 125 := by ring
  have hC : |3 * theorem_4_15_nonperiodicCandidateQFirst x *
      theorem_4_15_nonperiodicCandidateOscillationSecond x| ≤
      (3024 : ℝ) / 125 := by
    calc
      |3 * theorem_4_15_nonperiodicCandidateQFirst x *
          theorem_4_15_nonperiodicCandidateOscillationSecond x| =
          3 * |theorem_4_15_nonperiodicCandidateQFirst x *
            theorem_4_15_nonperiodicCandidateOscillationSecond x| := by
              rw [abs_mul, abs_mul]
              norm_num
              ring
      _ ≤ 3 * (1008 / 125) := mul_le_mul_of_nonneg_left hsecond (by norm_num)
      _ = 3024 / 125 := by ring
  rw [theorem_4_15_nonperiodicCandidatePThird]
  calc
    |theorem_4_15_nonperiodicCandidateQThird x *
          theorem_4_15_nonperiodicCandidateOscillation x +
        3 * theorem_4_15_nonperiodicCandidateQSecond x *
          theorem_4_15_nonperiodicCandidateOscillationFirst x +
        3 * theorem_4_15_nonperiodicCandidateQFirst x *
          theorem_4_15_nonperiodicCandidateOscillationSecond x +
        theorem_4_15_nonperiodicCandidateQ x *
          theorem_4_15_nonperiodicCandidateOscillationThird x| ≤
        ((|theorem_4_15_nonperiodicCandidateQThird x *
          theorem_4_15_nonperiodicCandidateOscillation x| +
        |3 * theorem_4_15_nonperiodicCandidateQSecond x *
          theorem_4_15_nonperiodicCandidateOscillationFirst x|) +
        |3 * theorem_4_15_nonperiodicCandidateQFirst x *
          theorem_4_15_nonperiodicCandidateOscillationSecond x|) +
        |theorem_4_15_nonperiodicCandidateQ x *
          theorem_4_15_nonperiodicCandidateOscillationThird x| :=
      (abs_add_le _ _).trans (add_le_add_left
        ((abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)) _)
    _ ≤ ((3168 / 125 + 2376 / 125) + 3024 / 125) + 2664 / 125 :=
      add_le_add (add_le_add (add_le_add hA hB) hC) hthird
    _ = 11232 / 125 := by ring

/- This is the explicit positive-tail estimate requested by the counterexample
   route.  In particular it contains no trajectory, descent, cross-curvature,
   or stationarity premise. -/
theorem theorem_4_15_nonperiodicCandidatePositiveProfileThird_abs_le
    {x : ℝ} (hx : 0 ≤ x) :
    |theorem_4_15_nonperiodicCandidatePositiveProfileThird x| ≤ 111 := by
  have hthird := theorem_4_15_nonperiodicCandidatePThird_abs_le hx
  have hsecond := theorem_4_15_nonperiodicCandidatePSecond_abs_le hx
  rw [theorem_4_15_nonperiodicCandidatePositiveProfileThird]
  calc
    |-theorem_4_15_nonperiodicCandidatePThird x -
        theorem_4_15_nonperiodicCandidatePSecond x| ≤
        |theorem_4_15_nonperiodicCandidatePThird x| +
          |theorem_4_15_nonperiodicCandidatePSecond x| := by
      simpa only [abs_neg] using
        (abs_sub (-theorem_4_15_nonperiodicCandidatePThird x)
          (theorem_4_15_nonperiodicCandidatePSecond x))
    _ ≤ 11232 / 125 + 510 / 25 := add_le_add hthird hsecond
    _ ≤ 111 := by norm_num

theorem theorem_4_15_nonperiodicCandidatePositiveProfile_iteratedDeriv_three_abs_le
    {x : ℝ} (hx : 0 ≤ x) :
    |iteratedDeriv 3 theorem_4_15_nonperiodicCandidatePositiveProfile x| ≤ 111 := by
  rw [theorem_4_15_nonperiodicCandidatePositiveProfile_iteratedDeriv_three
    (by linarith)]
  exact theorem_4_15_nonperiodicCandidatePositiveProfileThird_abs_le hx

theorem theorem_4_15_nonperiodicCandidateGlobalProfile_iteratedDeriv_three_eq
    {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 3 theorem_4_15_nonperiodicCandidateGlobalProfile x =
      iteratedDeriv 3 theorem_4_15_nonperiodicCandidatePositiveProfile x := by
  apply Filter.EventuallyEq.iteratedDeriv_eq
  filter_upwards [eventually_gt_nhds hx] with y hy
  exact theorem_4_15_nonperiodicCandidateGlobalProfile_eq hy.le

theorem theorem_4_15_nonperiodicCandidateGlobalProfile_iteratedDeriv_three_abs_le_tail
    {x : ℝ} (hx : 1 ≤ x) :
    |iteratedDeriv 3 theorem_4_15_nonperiodicCandidateGlobalProfile x| ≤ 111 := by
  rw [theorem_4_15_nonperiodicCandidateGlobalProfile_iteratedDeriv_three_eq
    (lt_of_lt_of_le zero_lt_one hx)]
  exact theorem_4_15_nonperiodicCandidatePositiveProfile_iteratedDeriv_three_abs_le
    (zero_le_one.trans hx)

theorem theorem_4_15_nonperiodicCandidateGlobalProfile_third_compact_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Set.Icc (-(1 : ℝ)) 1,
      |iteratedDeriv 3 theorem_4_15_nonperiodicCandidateGlobalProfile x| ≤ C := by
  have hcont : Continuous
      (iteratedDeriv 3 theorem_4_15_nonperiodicCandidateGlobalProfile) :=
    ContDiff.continuous_iteratedDeriv' 3
      theorem_4_15_nonperiodicCandidateGlobalProfile_contDiff_three
  obtain ⟨C, hC, hbound⟩ :=
    exists_nonneg_norm_bound_of_isCompact_of_continuousOn
      (iteratedDeriv 3 theorem_4_15_nonperiodicCandidateGlobalProfile)
      isCompact_Icc hcont.continuousOn
  refine ⟨C, hC, ?_⟩
  intro x hx
  simpa [Real.norm_eq_abs] using hbound x hx

theorem theorem_4_15_nonperiodicCandidateGlobalP_eq_two
    {x : ℝ} (hx : x < -1) :
    theorem_4_15_nonperiodicCandidateGlobalP x = 2 := by
  rw [theorem_4_15_nonperiodicCandidateGlobalP,
    theorem_4_15_nonperiodicCandidateGlobalQ,
    theorem_4_15_nonperiodicCandidateGlobalPhase,
    theorem_4_15_nonperiodicCandidateGlobalZ,
    Real.smoothTransition.zero_of_nonpos (by linarith)]
  norm_num

theorem theorem_4_15_nonperiodicCandidateGlobalProfile_hasDerivAt (x : ℝ) :
    HasDerivAt theorem_4_15_nonperiodicCandidateGlobalProfile
      (-deriv theorem_4_15_nonperiodicCandidateGlobalP x -
        theorem_4_15_nonperiodicCandidateGlobalP x) x := by
  have hp : HasDerivAt theorem_4_15_nonperiodicCandidateGlobalP
      (deriv theorem_4_15_nonperiodicCandidateGlobalP x) x :=
    (theorem_4_15_nonperiodicCandidateGlobalP_contDiff_three.differentiable
      (by norm_num)).differentiableAt.hasDerivAt
  have hi := theorem_4_15_nonperiodicCandidateGlobalIntegral_hasDerivAt x
  convert ((hasDerivAt_const (x := x) (2 : ℝ)).sub hp).sub hi using 1 <;>
    simp [theorem_4_15_nonperiodicCandidateGlobalProfile] <;> ring

theorem theorem_4_15_nonperiodicCandidateGlobalProfile_iteratedDeriv_three_eq_zero
    {x : ℝ} (hx : x < -1) :
    iteratedDeriv 3 theorem_4_15_nonperiodicCandidateGlobalProfile x = 0 := by
  have hsecondLocal :
      deriv (deriv theorem_4_15_nonperiodicCandidateGlobalProfile) =ᶠ[nhds x]
        (fun _ : ℝ => 0) := by
    filter_upwards [eventually_lt_nhds hx] with y hy
    have hderivAtY :
        deriv theorem_4_15_nonperiodicCandidateGlobalProfile =ᶠ[nhds y]
          (fun _ : ℝ => -2) := by
      filter_upwards [eventually_lt_nhds hy] with z hz
      have hpLocal : theorem_4_15_nonperiodicCandidateGlobalP =ᶠ[nhds z]
          (fun _ : ℝ => 2) := by
        filter_upwards [eventually_lt_nhds hz] with u hu
        exact theorem_4_15_nonperiodicCandidateGlobalP_eq_two hu
      rw [(theorem_4_15_nonperiodicCandidateGlobalProfile_hasDerivAt z).deriv,
        hpLocal.deriv_eq, theorem_4_15_nonperiodicCandidateGlobalP_eq_two hz]
      norm_num
    simpa using hderivAtY.deriv_eq
  rw [show 3 = 2 + 1 by norm_num, iteratedDeriv_succ,
    show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  calc
    deriv (deriv (deriv theorem_4_15_nonperiodicCandidateGlobalProfile)) x =
        deriv (fun _ : ℝ => 0) x := hsecondLocal.deriv_eq
    _ = 0 := by simp

theorem theorem_4_15_nonperiodicCandidateGlobalProfile_third_bounded :
    ∃ s : ℝ, 0 ≤ s ∧ ∀ x : ℝ,
      |iteratedDeriv 3 theorem_4_15_nonperiodicCandidateGlobalProfile x| ≤ s := by
  obtain ⟨C, hC, hcompact⟩ :=
    theorem_4_15_nonperiodicCandidateGlobalProfile_third_compact_bound
  refine ⟨max C 111, hC.trans (le_max_left _ _), ?_⟩
  intro x
  rcases lt_or_ge x (-1) with hxneg | hxneg
  · rw [theorem_4_15_nonperiodicCandidateGlobalProfile_iteratedDeriv_three_eq_zero hxneg,
      abs_zero]
    exact le_trans (by norm_num) (le_max_right _ _)
  · rcases le_or_gt x 1 with hxone | hxone
    · exact (hcompact x ⟨hxneg, hxone⟩).trans (le_max_left _ _)
    · exact
        (theorem_4_15_nonperiodicCandidateGlobalProfile_iteratedDeriv_three_abs_le_tail
          hxone.le).trans (le_max_right _ _)

theorem theorem_4_15_nonperiodicCandidateObjective_thirdDerivativeBounded :
    ∃ s : ℝ, ThirdDerivativeBounded
      theorem_4_15_nonperiodicCandidateObjective s := by
  obtain ⟨s, _hs, hscalar⟩ :=
    theorem_4_15_nonperiodicCandidateGlobalProfile_third_bounded
  refine ⟨s, theorem_4_15_nonperiodicCandidateObjective_contDiff_three, ?_⟩
  intro W
  change ‖iteratedFDeriv ℝ 3
    (theorem_4_15_nonperiodicCandidateGlobalProfile ∘
      theorem_4_5_counterexampleEntry) W‖ ≤ s
  rw [theorem_4_5_counterexampleEntry.iteratedFDeriv_comp_right
    theorem_4_15_nonperiodicCandidateGlobalProfile_contDiff_three W (by norm_num)]
  have hentry : ‖theorem_4_5_counterexampleEntry‖ ≤ (1 : ℝ) := by
    refine theorem_4_5_counterexampleEntry.opNorm_le_bound (by norm_num) ?_
    intro X
    rw [one_mul]
    change ‖X 0 0‖ ≤ ‖X‖
    exact le_of_eq (by
      rw [Matrix.frobenius_norm_def]
      simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
        Real.norm_eq_abs, Real.rpow_two]
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs,
        abs_of_nonneg (abs_nonneg _)])
  have hprod : ∏ _i : Fin 3, ‖theorem_4_5_counterexampleEntry‖ ≤ (1 : ℝ) := by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) hentry
  calc
    ‖(iteratedFDeriv ℝ 3 theorem_4_15_nonperiodicCandidateGlobalProfile
        (theorem_4_5_counterexampleEntry W)).compContinuousLinearMap
          (fun _ => theorem_4_5_counterexampleEntry)‖ ≤
        ‖iteratedFDeriv ℝ 3 theorem_4_15_nonperiodicCandidateGlobalProfile
          (theorem_4_5_counterexampleEntry W)‖ *
          ∏ _i : Fin 3, ‖theorem_4_5_counterexampleEntry‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ 3 theorem_4_15_nonperiodicCandidateGlobalProfile
          (theorem_4_5_counterexampleEntry W)‖ * 1 :=
      mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = |iteratedDeriv 3 theorem_4_15_nonperiodicCandidateGlobalProfile
          (theorem_4_5_counterexampleEntry W)| := by
      rw [mul_one, norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    _ ≤ s := hscalar _

/- This is the gradient formula used in the oscillatory lower bound.  Its
   leading term decays like `(1+x)^(-4/5)`; the remaining term contains only
   `q` and `q'`, and is integrable on the positive ray. -/
theorem theorem_4_15_nonperiodicCandidatePositiveProfile_gradient_formula
    {x : ℝ} (hx : -1 < x) :
    HasDerivAt theorem_4_15_nonperiodicCandidatePositiveProfile
      (-((12 : ℝ) / 5) * (1 + x) ^ (-(4 : ℝ) / 5) *
          Real.cos (theorem_4_15_nonperiodicCandidatePhase x) -
        (theorem_4_15_nonperiodicCandidateQ x +
            (-(6 : ℝ) / 5) * (1 + x) ^ (-(11 : ℝ) / 5)) *
          (2 + Real.sin (theorem_4_15_nonperiodicCandidatePhase x))) x := by
  convert theorem_4_15_nonperiodicCandidatePositiveProfile_hasDerivAt hx using 1
  have hz : 0 < 1 + x := by linarith
  have hpow :
      (1 + x) ^ (-(6 : ℝ) / 5) * (1 + x) ^ ((2 : ℝ) / 5) =
        (1 + x) ^ (-(4 : ℝ) / 5) := by
    rw [← Real.rpow_add hz]
    norm_num
  have hlead :
      (1 + x) ^ (-(6 : ℝ) / 5) *
          (Real.cos (theorem_4_15_nonperiodicCandidatePhase x) *
            ((12 : ℝ) / 5 * (1 + x) ^ ((2 : ℝ) / 5))) =
        (12 : ℝ) / 5 * (1 + x) ^ (-(4 : ℝ) / 5) *
          Real.cos (theorem_4_15_nonperiodicCandidatePhase x) := by
    rw [← hpow]
    ring
  rw [theorem_4_15_nonperiodicCandidateP,
    theorem_4_15_nonperiodicCandidateQ, hlead]
  ring

theorem theorem_4_15_nonperiodicCandidate_initial_values :
    theorem_4_15_nonperiodicCandidateQ 0 = 1 ∧
      theorem_4_15_nonperiodicCandidatePhase 0 = 0 ∧
      theorem_4_15_nonperiodicCandidateP 0 = 2 := by
  norm_num [theorem_4_15_nonperiodicCandidateQ,
    theorem_4_15_nonperiodicCandidatePhase,
    theorem_4_15_nonperiodicCandidateP]

theorem theorem_4_15_nonperiodicCandidatePositiveProfile_zero :
    theorem_4_15_nonperiodicCandidatePositiveProfile 0 = 0 := by
  simp [theorem_4_15_nonperiodicCandidatePositiveProfile,
    theorem_4_15_nonperiodicCandidate_initial_values]

/- The coefficient `12 / 7` in the phase is not cosmetic: it makes the
   derivative of `p` vanish at the initial point.  This is the normalization
   used by the exact momentum-error recurrence in the documented candidate. -/
theorem theorem_4_15_nonperiodicCandidateP_hasDerivAt_zero :
    HasDerivAt theorem_4_15_nonperiodicCandidateP 0 0 := by
  have hz : HasDerivAt (fun x : ℝ => 1 + x) 1 0 := by
    simpa using (hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).add
      (hasDerivAt_id (x := (0 : ℝ)))
  have hq : HasDerivAt theorem_4_15_nonperiodicCandidateQ (-(6 : ℝ) / 5) 0 := by
    convert hz.rpow_const (p := (-(6 : ℝ) / 5)) (Or.inl (by norm_num)) using 1 <;>
      norm_num [theorem_4_15_nonperiodicCandidateQ]
  have hpow : HasDerivAt (fun x : ℝ => (1 + x) ^ ((7 : ℝ) / 5))
      ((7 : ℝ) / 5) 0 := by
    convert hz.rpow_const (p := ((7 : ℝ) / 5)) (Or.inl (by norm_num)) using 1 <;>
      norm_num
  have hphase : HasDerivAt theorem_4_15_nonperiodicCandidatePhase
      ((12 : ℝ) / 5) 0 := by
    convert (hpow.sub_const 1).const_mul ((12 : ℝ) / 7) using 1 <;>
      norm_num [theorem_4_15_nonperiodicCandidatePhase] <;> ring
  have hosc : HasDerivAt
      (fun x : ℝ => 2 + Real.sin (theorem_4_15_nonperiodicCandidatePhase x))
      ((12 : ℝ) / 5) 0 := by
    convert (hasDerivAt_const (x := (0 : ℝ)) (2 : ℝ)).add hphase.sin using 1 <;>
      norm_num [theorem_4_15_nonperiodicCandidate_initial_values]
  convert hq.mul hosc using 1 <;>
    norm_num [theorem_4_15_nonperiodicCandidateP,
      theorem_4_15_nonperiodicCandidate_initial_values] <;> ring

theorem theorem_4_15_nonperiodicCandidatePositiveProfile_hasDerivAt_zero :
    HasDerivAt theorem_4_15_nonperiodicCandidatePositiveProfile (-2) 0 := by
  have hp := theorem_4_15_nonperiodicCandidateP_hasDerivAt_zero
  have hcont : ContinuousAt theorem_4_15_nonperiodicCandidateP 0 :=
    hp.continuousAt
  have hcontOn : ContinuousOn theorem_4_15_nonperiodicCandidateP
      (Set.Ioi (-1 : ℝ)) := by
    intro x hx
    exact (theorem_4_15_nonperiodicCandidateP_hasDerivAt
      (Set.mem_Ioi.mp hx)).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable theorem_4_15_nonperiodicCandidateP volume 0 0 := by
    simp
  have hmeas : StronglyMeasurableAtFilter theorem_4_15_nonperiodicCandidateP
      (nhds (0 : ℝ)) volume :=
    hcontOn.stronglyMeasurableAtFilter isOpen_Ioi 0 (by norm_num)
  have hi : HasDerivAt
      (fun x : ℝ => ∫ u in 0..x, theorem_4_15_nonperiodicCandidateP u)
      (theorem_4_15_nonperiodicCandidateP 0) 0 :=
    intervalIntegral.integral_hasDerivAt_right hint hmeas hcont
  convert ((hasDerivAt_const (x := (0 : ℝ)) (2 : ℝ)).sub hp).sub hi using 1 <;>
    norm_num [theorem_4_15_nonperiodicCandidatePositiveProfile,
      theorem_4_15_nonperiodicCandidate_initial_values]

/- The candidate's initial source gap is genuinely positive.  This does not
   identify the infimum: the negative value needed below follows locally from
   the checked derivative `F'(0) = -2`, while the previously proved global
   lower bound supplies the finite-infimum side of the source definition. -/
theorem theorem_4_15_nonperiodicCandidatePositiveProfile_exists_negative :
    ∃ x : ℝ, 0 < x ∧
      theorem_4_15_nonperiodicCandidatePositiveProfile x < 0 := by
  have hslope : Tendsto
      (fun t : ℝ => t⁻¹ •
        (theorem_4_15_nonperiodicCandidatePositiveProfile (0 + t) -
          theorem_4_15_nonperiodicCandidatePositiveProfile 0))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (-2 : ℝ)) :=
    HasDerivAt.tendsto_slope_zero_right
      theorem_4_15_nonperiodicCandidatePositiveProfile_hasDerivAt_zero
  have hslope_lt : Filter.Eventually
      (fun x : ℝ => x⁻¹ •
        (theorem_4_15_nonperiodicCandidatePositiveProfile (0 + x) -
          theorem_4_15_nonperiodicCandidatePositiveProfile 0) < -1)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) :=
    hslope.eventually (eventually_lt_nhds (by norm_num))
  have hinterval : Filter.Eventually (fun x : ℝ => x ∈ Set.Ioo 0 1)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) :=
    Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)
  have hboth := Filter.Eventually.and hinterval hslope_lt
  obtain ⟨x, hx01, hxslope⟩ := hboth.exists
  refine ⟨x, hx01.1, ?_⟩
  simp only [zero_add,
    theorem_4_15_nonperiodicCandidatePositiveProfile_zero, sub_zero,
    smul_eq_mul] at hxslope
  have hxpos : 0 < x := hx01.1
  field_simp at hxslope
  nlinarith

theorem theorem_4_15_nonperiodicCandidateObjective_fStar_lt_zero :
    theorem_4_15_nonperiodicCandidateObjective.fStar < 0 := by
  obtain ⟨x, hx, hxneg⟩ :=
    theorem_4_15_nonperiodicCandidatePositiveProfile_exists_negative
  let W : Mat 1 1 := fun _ _ => x
  have hentry : theorem_4_5_counterexampleEntry W = x := by
    rw [theorem_4_5_counterexampleEntry_apply]
  have hvalue : theorem_4_15_nonperiodicCandidateObjective.f W =
      theorem_4_15_nonperiodicCandidatePositiveProfile x := by
    simpa [hentry] using
      (theorem_4_15_nonperiodicCandidateObjective_eq_positiveProfile
        (W := W) (by simpa [hentry] using hx.le))
  have hinf_le : theorem_4_15_nonperiodicCandidateObjective.fStar ≤
      theorem_4_15_nonperiodicCandidateObjective.f W := by
    simpa [Objective.fStar] using
      (csInf_le theorem_4_15_nonperiodicCandidateObjective_hasFiniteInfimum
        (show theorem_4_15_nonperiodicCandidateObjective.f W ∈
          Set.range theorem_4_15_nonperiodicCandidateObjective.f from ⟨W, rfl⟩))
  rw [hvalue] at hinf_le
  exact lt_of_le_of_lt hinf_le hxneg

theorem theorem_4_15_nonperiodicCandidateObjective_sourceInitialGap_pos :
    0 < sourceObjectiveInitialGap theorem_4_15_nonperiodicCandidateObjective 0
      theorem_4_15_nonperiodicCandidateObjective_hasFiniteInfimum := by
  rw [sourceObjectiveInitialGap_eq_objectiveInitialGap]
  unfold objectiveInitialGap
  have hzero : theorem_4_15_nonperiodicCandidateObjective.f 0 = 0 := by
    change theorem_4_15_nonperiodicCandidateGlobalProfile 0 = 0
    rw [theorem_4_15_nonperiodicCandidateGlobalProfile_eq (by norm_num)]
    exact theorem_4_15_nonperiodicCandidatePositiveProfile_zero
  rw [hzero]
  linarith [theorem_4_15_nonperiodicCandidateObjective_fStar_lt_zero]

/- The counterexample program must use the literal stochastic source objects,
   even though its oracle is deterministic.  This singleton problem is the
   exact Algorithm 1 realization of the fixed nonperiodic objective; no
   trajectory, curvature estimate, or stationarity conclusion is included in
   its data. -/
noncomputable def theorem_4_15_nonperiodicCandidateProblem :
    StochasticProblem Unit 1 1 :=
  deterministicOracleProblem theorem_4_15_nonperiodicCandidateObjective

theorem theorem_4_15_nonperiodicCandidateProblem_objective :
    theorem_4_15_nonperiodicCandidateProblem.objective =
      theorem_4_15_nonperiodicCandidateObjective := by
  exact deterministicOracleProblem_objective _

/- Appendix B.4 requires a positive advertised noise scale even for a
   zero-variance oracle.  Fix it to the objective's actual initial source gap,
   rather than introducing an unrelated free constant. -/
noncomputable def theorem_4_15_nonperiodicCandidateSigma : ℝ :=
  sourceObjectiveInitialGap theorem_4_15_nonperiodicCandidateObjective 0
    theorem_4_15_nonperiodicCandidateObjective_hasFiniteInfimum

theorem theorem_4_15_nonperiodicCandidateSigma_pos :
    0 < theorem_4_15_nonperiodicCandidateSigma := by
  exact theorem_4_15_nonperiodicCandidateObjective_sourceInitialGap_pos

noncomputable def theorem_4_15_nonperiodicCandidateThirdDerivativeScale : ℝ :=
  Classical.choose
    theorem_4_15_nonperiodicCandidateObjective_thirdDerivativeBounded

theorem theorem_4_15_nonperiodicCandidateProblem_thirdDerivativeBounded :
    ThirdDerivativeBounded
      theorem_4_15_nonperiodicCandidateProblem.objective
      theorem_4_15_nonperiodicCandidateThirdDerivativeScale := by
  rw [theorem_4_15_nonperiodicCandidateProblem_objective]
  exact Classical.choose_spec
    theorem_4_15_nonperiodicCandidateObjective_thirdDerivativeBounded

theorem theorem_4_15_nonperiodicCandidateProblem_hasFiniteInfimum :
    theorem_4_15_nonperiodicCandidateProblem.objective.HasFiniteInfimum := by
  rw [theorem_4_15_nonperiodicCandidateProblem_objective]
  exact theorem_4_15_nonperiodicCandidateObjective_hasFiniteInfimum

theorem theorem_4_15_nonperiodicCandidateProblem_sourceInitialGap :
    sourceObjectiveInitialGap theorem_4_15_nonperiodicCandidateProblem.objective 0
        theorem_4_15_nonperiodicCandidateProblem_hasFiniteInfimum =
      theorem_4_15_nonperiodicCandidateSigma := by
  rw [sourceObjectiveInitialGap_eq_objectiveInitialGap]
  unfold theorem_4_15_nonperiodicCandidateSigma
  rw [sourceObjectiveInitialGap_eq_objectiveInitialGap,
    theorem_4_15_nonperiodicCandidateProblem_objective]

theorem theorem_4_15_nonperiodicCandidateProblem_boundedVariance :
    BoundedVariance theorem_4_15_nonperiodicCandidateProblem
      theorem_4_15_nonperiodicCandidateSigma := by
  exact deterministicOracleProblem_boundedVariance_of_nonneg
    theorem_4_15_nonperiodicCandidateObjective
    theorem_4_15_nonperiodicCandidateSigma_pos.le

/- These are the integrability witnesses required by the realized average,
   objective-drop, and directional/cross Hessian source quantities on every
   exact generated Algorithm 1 run of the singleton problem.  The proof uses
   only Assumptions 4.13 and 3.3 established above. -/
theorem theorem_4_15_nonperiodicCandidateProblem_expectationsWellDefined
    (cfg : DeterministicMomentumMuonConfig 1 1) (T : ℕ) :
    stochasticMuonExpectationsWellDefined
      theorem_4_15_nonperiodicCandidateProblem
      (deterministicOracleConfig cfg) T := by
  have hregularity : StochasticObjectiveRegularity
      theorem_4_15_nonperiodicCandidateProblem.objective :=
    Or.inr (Or.inr
      ⟨theorem_4_15_nonperiodicCandidateThirdDerivativeScale,
        theorem_4_15_nonperiodicCandidateProblem_thirdDerivativeBounded⟩)
  exact ⟨
    stochasticAverageNuclearGradient_wellDefined_of_source_assumptions
      theorem_4_15_nonperiodicCandidateProblem (deterministicOracleConfig cfg) T
      theorem_4_15_nonperiodicCandidateSigma hregularity
      theorem_4_15_nonperiodicCandidateProblem_boundedVariance,
    stochasticExpectedObjectiveDrop_wellDefined_of_source_assumptions
      theorem_4_15_nonperiodicCandidateProblem (deterministicOracleConfig cfg) T
      theorem_4_15_nonperiodicCandidateSigma hregularity
      theorem_4_15_nonperiodicCandidateProblem_boundedVariance,
    stochasticHessianJstar_wellDefined_of_source_assumptions
      theorem_4_15_nonperiodicCandidateProblem (deterministicOracleConfig cfg) T
      theorem_4_15_nonperiodicCandidateThirdDerivativeScale
      theorem_4_15_nonperiodicCandidateSigma
      theorem_4_15_nonperiodicCandidateProblem_thirdDerivativeBounded
      theorem_4_15_nonperiodicCandidateProblem_boundedVariance⟩

/- A fixed smooth periodic objective is the natural remaining candidate for
   testing the source-small-`J` branch: unlike a positive quadratic, it can
   cancel signed directional curvature while retaining a nonzero gradient,
   and unlike an accuracy-dependent construction it is one objective for the
   whole asymptotic family.  The declarations below establish only the
   source-object facts that are already justified.  They do not assert that
   the generated momentum orbit has the required cancellation. -/
/- Counterexample construction: `Algorithms/Unverified/Muon.lean` documents a
   fixed nonperiodic objective, a generated monotone momentum trajectory, and
   directional-J/rate estimates for the literal Appendix B.4 claim. Those
   estimates remain to be formalized; the periodic lemmas below are separate. -/
def theorem_4_15_periodicCandidateObjective : Objective 1 1 :=
  ⟨fun W => Real.sin (theorem_4_5_counterexampleEntry W)⟩

theorem theorem_4_15_periodicCandidateObjective_hasFiniteInfimum :
    theorem_4_15_periodicCandidateObjective.HasFiniteInfimum := by
  refine ⟨-1, ?_⟩
  rintro y ⟨W, rfl⟩
  exact Real.neg_one_le_sin _

theorem theorem_4_15_periodicCandidateObjective_fStar :
    theorem_4_15_periodicCandidateObjective.fStar = -1 := by
  apply le_antisymm
  · apply csInf_le theorem_4_15_periodicCandidateObjective_hasFiniteInfimum
    refine ⟨fun _ _ => -(Real.pi / 2), ?_⟩
    change Real.sin (-(Real.pi / 2)) = -1
    rw [Real.sin_neg, Real.sin_pi_div_two]
  · apply le_csInf
    · exact Set.range_nonempty _
    · rintro y ⟨W, rfl⟩
      exact Real.neg_one_le_sin _

theorem theorem_4_15_periodicCandidateObjective_sourceInitialGap_zero :
    sourceObjectiveInitialGap theorem_4_15_periodicCandidateObjective 0
        theorem_4_15_periodicCandidateObjective_hasFiniteInfimum = 1 := by
  rw [sourceObjectiveInitialGap_eq_objectiveInitialGap]
  unfold objectiveInitialGap
  rw [theorem_4_15_periodicCandidateObjective_fStar]
  norm_num [theorem_4_15_periodicCandidateObjective,
    theorem_4_5_counterexampleEntry]

theorem theorem_4_15_periodicCandidateObjective_contDiff_three :
    ContDiff ℝ 3
      (vectorizedObjective theorem_4_15_periodicCandidateObjective) := by
  simpa [vectorizedObjective, theorem_4_15_periodicCandidateObjective] using
    theorem_4_5_counterexampleEntry.contDiff.sin

theorem theorem_4_15_periodicCandidateObjective_thirdDerivativeBounded :
    ThirdDerivativeBounded theorem_4_15_periodicCandidateObjective 6 := by
  constructor
  · exact theorem_4_15_periodicCandidateObjective_contDiff_three
  · intro W
    change ‖iteratedFDeriv ℝ 3
      ((fun x : ℝ => Real.sin x) ∘ theorem_4_5_counterexampleEntry) W‖ ≤ 6
    apply (norm_iteratedFDeriv_comp_le
      (n := 3) (N := 3) Real.contDiff_sin
      theorem_4_5_counterexampleEntry.contDiff (by norm_num) W
      (C := 1) (D := 1) (by
        intro i _hi
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
        exact Real.abs_iteratedDeriv_sin_le_one i _) (by
        intro i hi1 hi3
        have hnorm : ‖theorem_4_5_counterexampleEntry‖ ≤ (1 : ℝ) := by
          refine theorem_4_5_counterexampleEntry.opNorm_le_bound (by norm_num) ?_
          intro X
          rw [one_mul]
          change ‖X 0 0‖ ≤ ‖X‖
          exact le_of_eq (by
            rw [Matrix.frobenius_norm_def]
            simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
              Real.norm_eq_abs, Real.rpow_two]
            rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs,
              abs_of_nonneg (abs_nonneg _)])
        have hfderiv : fderiv ℝ (⇑theorem_4_5_counterexampleEntry) =
            fun _ => theorem_4_5_counterexampleEntry := by
          funext X
          exact ContinuousLinearMap.fderiv _
        interval_cases i
        · rw [← norm_iteratedFDeriv_fderiv (n := 0), hfderiv]
          simpa using hnorm
        · rw [show 2 = 1 + 1 by norm_num, iteratedFDeriv_succ_eq_comp_right]
          simp only [hfderiv, iteratedFDeriv_succ_const, Function.comp_apply,
            one_pow, Pi.zero_apply]
          change ‖(0 : ContinuousMultilinearMap ℝ
            (fun _ : Fin 2 => Mat 1 1) ℝ)‖ ≤ 1
          rw [norm_zero]
          norm_num
        · rw [show 3 = 2 + 1 by norm_num, iteratedFDeriv_succ_eq_comp_right]
          simp only [hfderiv, iteratedFDeriv_succ_const, Function.comp_apply,
            one_pow, Pi.zero_apply]
          change ‖(0 : ContinuousMultilinearMap ℝ
            (fun _ : Fin 3 => Mat 1 1) ℝ)‖ ≤ 1
          rw [norm_zero]
          norm_num)).trans_eq (by norm_num)

theorem theorem_4_15_periodicCandidate_coordinateDirection :
    orthogonalizedDirection (coordinateMatrix (m := 1) (n := 1) 0 0) =
      coordinateMatrix 0 0 := by
  let A : Mat 1 1 := coordinateMatrix 0 0
  have hentryNorm : ∀ W : Mat 1 1, ‖W 0 0‖ = ‖W‖ := by
    intro W
    rw [Matrix.frobenius_norm_def]
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
      Real.norm_eq_abs, Real.rpow_two]
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (abs_nonneg _)]
  have hfrob : frobeniusNorm A = 1 := by
    unfold frobeniusNorm
    rw [← hentryNorm]
    simp [A, coordinateMatrix]
  have hnuc : nuclearNorm A = 1 := by
    apply le_antisymm
    · have h := nuclearNorm_le_sqrt_rankBound_mul_frobeniusNorm A
      norm_num [matrixRankBound, hfrob] at h ⊢
      exact h
    · simpa [hfrob] using frobeniusNorm_le_nuclearNorm A
  have hpair := orthogonalizedDirection_frobeniusInner_eq_nuclearNorm A
  rw [hnuc] at hpair
  ext i j
  fin_cases i
  fin_cases j
  unfold frobeniusInner at hpair
  simp [A, coordinateMatrix] at hpair ⊢
  exact hpair

theorem theorem_4_15_periodicCandidateObjective_grad (W : Mat 1 1) :
    theorem_4_15_periodicCandidateObjective.grad W =
      fun _ _ => Real.cos (theorem_4_5_counterexampleEntry W) := by
  ext i j
  fin_cases i
  fin_cases j
  have hderiv : HasFDerivAt
      (fun W : Mat 1 1 => Real.sin (theorem_4_5_counterexampleEntry W))
      (Real.cos (theorem_4_5_counterexampleEntry W) •
        theorem_4_5_counterexampleEntry) W :=
    theorem_4_5_counterexampleEntry.hasFDerivAt.sin
  rw [Objective.grad_eq_coordinate_fderiv]
  change fderiv ℝ
      (fun W : Mat 1 1 => Real.sin (theorem_4_5_counterexampleEntry W)) W
        (coordinateMatrix 0 0) =
    Real.cos (theorem_4_5_counterexampleEntry W)
  rw [hderiv.fderiv]
  simp [coordinateMatrix]

def theorem_4_15_periodicCandidateGradDerivative (W : Mat 1 1) :
    Mat 1 1 →L[ℝ] Mat 1 1 :=
  ((-Real.sin (theorem_4_5_counterexampleEntry W)) •
      theorem_4_5_counterexampleEntry).smulRight (coordinateMatrix 0 0)

theorem theorem_4_15_periodicCandidateObjective_hasFDerivAt_grad
    (W : Mat 1 1) :
    HasFDerivAt theorem_4_15_periodicCandidateObjective.grad
      (theorem_4_15_periodicCandidateGradDerivative W) W := by
  have hpointwise : HasFDerivAt
      (fun X : Mat 1 1 =>
        Real.cos (theorem_4_5_counterexampleEntry X) • coordinateMatrix 0 0)
      (theorem_4_15_periodicCandidateGradDerivative W) W := by
    exact theorem_4_5_counterexampleEntry.hasFDerivAt.cos.smul_const
      (coordinateMatrix 0 0)
  have hfun : theorem_4_15_periodicCandidateObjective.grad =
      (fun X : Mat 1 1 =>
        Real.cos (theorem_4_5_counterexampleEntry X) • coordinateMatrix 0 0) := by
    funext X
    rw [theorem_4_15_periodicCandidateObjective_grad]
    ext i j
    fin_cases i
    fin_cases j
    simp [coordinateMatrix]
  rwa [hfun]

theorem theorem_4_15_periodicCandidateObjective_hessianBilinear
    (W A B : Mat 1 1) :
    hessianBilinear theorem_4_15_periodicCandidateObjective W A B =
      -Real.sin (theorem_4_5_counterexampleEntry W) * A 0 0 * B 0 0 := by
  unfold hessianBilinear
  rw [(theorem_4_15_periodicCandidateObjective_hasFDerivAt_grad W).fderiv]
  simp only [frobeniusInner, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton]
  simp [theorem_4_15_periodicCandidateGradDerivative, coordinateMatrix]
  ring

theorem theorem_4_15_periodicCandidate_directionalTerm
    (cfg : DeterministicMomentumMuonConfig 1 1) (t : ℕ) :
    deterministicMomentumHessianDirectionalTerm
        theorem_4_15_periodicCandidateObjective cfg t =
      -Real.sin (theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg t).W) *
        (orthogonalizedDirection
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg t).M 0 0) ^ 2 := by
  unfold deterministicMomentumHessianDirectionalTerm
  rw [theorem_4_15_periodicCandidateObjective_hessianBilinear]
  ring

theorem theorem_4_15_periodicCandidateObjective_grad_zero :
    theorem_4_15_periodicCandidateObjective.grad 0 = coordinateMatrix 0 0 := by
  rw [theorem_4_15_periodicCandidateObjective_grad]
  ext i j
  fin_cases i
  fin_cases j
  simp [theorem_4_5_counterexampleEntry, coordinateMatrix]

theorem theorem_4_15_periodicCandidateObjective_grad_zero_ne :
    theorem_4_15_periodicCandidateObjective.grad 0 ≠ 0 := by
  rw [theorem_4_15_periodicCandidateObjective_grad_zero]
  intro hzero
  have hentry := congrArg (fun M : Mat 1 1 => M 0 0) hzero
  norm_num [coordinateMatrix] at hentry

theorem theorem_4_15_periodicCandidateObjective_hessianBilinear_zero
    (A B : Mat 1 1) :
    hessianBilinear theorem_4_15_periodicCandidateObjective 0 A B = 0 := by
  rw [theorem_4_15_periodicCandidateObjective_hessianBilinear]
  simp [theorem_4_5_counterexampleEntry]

theorem theorem_4_15_periodicCandidate_directionalTerm_zero_of_periodic_phase
    (cfg : DeterministicMomentumMuonConfig 1 1) (t : ℕ) (q : ℤ)
    (hphase : theorem_4_5_counterexampleEntry
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg t).W =
      (q : ℝ) * (2 * Real.pi)) :
    deterministicMomentumHessianDirectionalTerm
        theorem_4_15_periodicCandidateObjective cfg t = 0 := by
  have hsin : Real.sin ((q : ℝ) * (2 * Real.pi)) = 0 := by
    simpa using Real.sin_add_int_mul_two_pi 0 q
  rw [theorem_4_15_periodicCandidate_directionalTerm, hphase, hsin]
  ring

theorem theorem_4_15_periodicCandidateObjective_value_periodic
    (W : Mat 1 1) (q : ℤ) :
    theorem_4_15_periodicCandidateObjective.f
        (W + (q * (2 * Real.pi)) • coordinateMatrix 0 0) =
      theorem_4_15_periodicCandidateObjective.f W := by
  change Real.sin
      (theorem_4_5_counterexampleEntry
        (W + (q * (2 * Real.pi)) • coordinateMatrix 0 0)) =
    Real.sin (theorem_4_5_counterexampleEntry W)
  rw [show theorem_4_5_counterexampleEntry
      (W + (q * (2 * Real.pi)) • coordinateMatrix 0 0) =
        theorem_4_5_counterexampleEntry W + (q : ℝ) * (2 * Real.pi) by
    simp [coordinateMatrix]]
  exact Real.sin_add_int_mul_two_pi _ q

theorem theorem_4_15_periodicCandidateObjective_grad_periodic
    (W : Mat 1 1) (q : ℤ) :
    theorem_4_15_periodicCandidateObjective.grad
        (W + (q * (2 * Real.pi)) • coordinateMatrix 0 0) =
      theorem_4_15_periodicCandidateObjective.grad W := by
  rw [theorem_4_15_periodicCandidateObjective_grad,
    theorem_4_15_periodicCandidateObjective_grad]
  funext i j
  fin_cases i
  fin_cases j
  rw [show theorem_4_5_counterexampleEntry
      (W + (q * (2 * Real.pi)) • coordinateMatrix 0 0) =
        theorem_4_5_counterexampleEntry W + (q : ℝ) * (2 * Real.pi) by
    simp [coordinateMatrix]]
  exact Real.cos_add_int_mul_two_pi _ q

def theorem_4_15_periodicCandidateConfig :
    DeterministicMomentumMuonConfig 1 1 where
  W0 := 0
  eta := fun _ => 2 * Real.pi
  beta := 0
  beta_mem := by norm_num

theorem theorem_4_15_periodicCandidate_generatedState (t : ℕ) :
    deterministicMomentumMuonState theorem_4_15_periodicCandidateObjective
        theorem_4_15_periodicCandidateConfig t =
      { W := -((t : ℝ) * (2 * Real.pi)) • coordinateMatrix 0 0
        M := coordinateMatrix 0 0 } := by
  induction t with
  | zero =>
      simp [deterministicMomentumMuonState, deterministicMomentumMuonBaseState,
        deterministicGradient, theorem_4_15_periodicCandidateConfig,
        theorem_4_15_periodicCandidateObjective_grad_zero]
  | succ t ih =>
      change deterministicMomentumMuonStep theorem_4_15_periodicCandidateObjective
          theorem_4_15_periodicCandidateConfig t
          (deterministicMomentumMuonState theorem_4_15_periodicCandidateObjective
            theorem_4_15_periodicCandidateConfig t) = _
      rw [ih]
      unfold deterministicMomentumMuonStep muonUpdate deterministicGradient
      simp only [theorem_4_15_periodicCandidateConfig,
        theorem_4_15_periodicCandidate_coordinateDirection, zero_smul, zero_add,
        one_smul, MuonState.mk.injEq]
      constructor
      · ext i j
        fin_cases i
        fin_cases j
        simp only [Matrix.sub_apply, Matrix.smul_apply, coordinateMatrix,
          Matrix.single_apply, if_pos, smul_eq_mul, one_mul]
        push_cast
        ring
      · rw [theorem_4_15_periodicCandidateObjective_grad]
        ext i j
        fin_cases i
        fin_cases j
        simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
          theorem_4_5_counterexampleEntry_apply]
        simp [coordinateMatrix, Matrix.single_apply]

theorem theorem_4_15_periodicCandidate_generatedPhase (t : ℕ) :
    theorem_4_5_counterexampleEntry
        (deterministicMomentumMuonState theorem_4_15_periodicCandidateObjective
          theorem_4_15_periodicCandidateConfig t).W =
      ((-(Int.ofNat t) : ℤ) : ℝ) * (2 * Real.pi) := by
  rw [theorem_4_15_periodicCandidate_generatedState]
  simp only [Matrix.smul_apply, smul_eq_mul,
    theorem_4_5_counterexampleEntry_apply]
  simp [coordinateMatrix]

theorem theorem_4_15_periodicCandidate_generatedDirectionalTerm_zero (t : ℕ) :
    deterministicMomentumHessianDirectionalTerm
        theorem_4_15_periodicCandidateObjective
        theorem_4_15_periodicCandidateConfig t = 0 := by
  apply theorem_4_15_periodicCandidate_directionalTerm_zero_of_periodic_phase
    theorem_4_15_periodicCandidateConfig t (-(Int.ofNat t))
  exact theorem_4_15_periodicCandidate_generatedPhase t

theorem theorem_4_15_periodicCandidate_generatedDirectionalAverage_zero (T : ℕ) :
    deterministicMomentumHessianDirectionalAverage
        theorem_4_15_periodicCandidateObjective
        theorem_4_15_periodicCandidateConfig T = 0 := by
  unfold deterministicMomentumHessianDirectionalAverage
  simp [theorem_4_15_periodicCandidate_generatedDirectionalTerm_zero]

theorem theorem_4_15_periodicCandidate_generatedGradient (t : ℕ) :
    theorem_4_15_periodicCandidateObjective.grad
        (deterministicMomentumMuonState theorem_4_15_periodicCandidateObjective
          theorem_4_15_periodicCandidateConfig t).W =
      coordinateMatrix 0 0 := by
  rw [theorem_4_15_periodicCandidate_generatedState,
    theorem_4_15_periodicCandidateObjective_grad]
  ext i j
  fin_cases i
  fin_cases j
  simp only [Matrix.smul_apply, smul_eq_mul,
    theorem_4_5_counterexampleEntry_apply]
  simp only [coordinateMatrix, Matrix.single_apply, if_pos, one_mul]
  rw [show -((t : ℝ) * (2 * Real.pi)) =
      ((-(Int.ofNat t) : ℤ) : ℝ) * (2 * Real.pi) by
    push_cast
    norm_num]
  simpa using Real.cos_add_int_mul_two_pi 0 (-(Int.ofNat t))

theorem theorem_4_15_periodicCandidate_coordinateNuclearNorm :
    nuclearNorm (coordinateMatrix (m := 1) (n := 1) 0 0) = 1 := by
  have hentryNorm : ∀ W : Mat 1 1, ‖W 0 0‖ = ‖W‖ := by
    intro W
    rw [Matrix.frobenius_norm_def]
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
      Real.norm_eq_abs, Real.rpow_two]
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (abs_nonneg _)]
  have hfrob : frobeniusNorm
      (coordinateMatrix (m := 1) (n := 1) 0 0) = 1 := by
    unfold frobeniusNorm
    rw [← hentryNorm]
    simp [coordinateMatrix]
  apply le_antisymm
  · have h := nuclearNorm_le_sqrt_rankBound_mul_frobeniusNorm
      (coordinateMatrix (m := 1) (n := 1) 0 0)
    norm_num [matrixRankBound, hfrob] at h ⊢
    exact h
  · simpa [hfrob] using frobeniusNorm_le_nuclearNorm
      (coordinateMatrix (m := 1) (n := 1) 0 0)

/- In the one-dimensional periodic candidate, the nuclear norm of a scalar
   coordinate matrix is exactly the scalar absolute value.  This lets the
   full generated-gradient average be reduced to the actual orbit phases,
   without replacing the generated process by an arbitrary scalar sequence. -/
theorem theorem_4_15_periodicCandidate_scalarCoordinateNuclearNorm (c : ℝ) :
    nuclearNorm (c • coordinateMatrix (m := 1) (n := 1) 0 0) = |c| := by
  let E : Mat 1 1 := coordinateMatrix 0 0
  have hE : E ≠ 0 := by
    intro hzero
    have hentry := congrArg (fun M : Mat 1 1 => M 0 0) hzero
    norm_num [E, coordinateMatrix] at hentry
  have hpositive : ∀ d : ℝ, 0 < d → nuclearNorm (d • E) = d := by
    intro d hd
    have hupper := nuclearNorm_smul_le_of_nonneg d E hd.le
    rw [theorem_4_15_periodicCandidate_coordinateNuclearNorm] at hupper
    have hback := nuclearNorm_smul_le_of_nonneg d⁻¹ (d • E) (by positivity)
    have hscaleBack : d⁻¹ • (d • E) = E := by
      ext i j
      simp [ne_of_gt hd]
    rw [hscaleBack, theorem_4_15_periodicCandidate_coordinateNuclearNorm] at hback
    apply le_antisymm
    · simpa [E] using hupper
    · have hmul := mul_le_mul_of_nonneg_left hback hd.le
      field_simp [ne_of_gt hd] at hmul
      simpa [E] using hmul
  by_cases hc : c = 0
  · subst c
    apply le_antisymm
    · have hzero := nuclearNorm_smul_le_of_nonneg (0 : ℝ) E le_rfl
      simpa [E] using hzero
    · simpa using nuclearNorm_nonneg_early (0 : Mat 1 1)
  by_cases hcp : 0 < c
  · simpa [abs_of_pos hcp, E] using hpositive c hcp
  · have hcn : c < 0 := lt_of_le_of_ne (le_of_not_gt hcp) hc
    have hmatrix : c • E = -((-c) • E) := by module
    rw [show c • coordinateMatrix (m := 1) (n := 1) 0 0 = c • E by rfl,
      hmatrix, nuclearNorm_neg_eq, hpositive (-c) (neg_pos.mpr hcn),
      abs_of_neg hcn]

/- Exact full-orbit gradient quantity for the candidate.  Unlike the earlier
   fixed `2*pi` orbit calculation, this holds for every generated momentum
   configuration, including the shrinking-step schedules relevant to the
   source-small-`J` branch. -/
theorem theorem_4_15_periodicCandidate_generatedNuclearGradient_eq_abs_cos
    (cfg : DeterministicMomentumMuonConfig 1 1) (t : ℕ) :
    nuclearNorm (theorem_4_15_periodicCandidateObjective.grad
      (deterministicMomentumMuonState theorem_4_15_periodicCandidateObjective
        cfg t).W) =
      |Real.cos (theorem_4_5_counterexampleEntry
        (deterministicMomentumMuonState theorem_4_15_periodicCandidateObjective
          cfg t).W)| := by
  rw [theorem_4_15_periodicCandidateObjective_grad]
  have hmatrix :
      (fun _ _ => Real.cos (theorem_4_5_counterexampleEntry
        (deterministicMomentumMuonState theorem_4_15_periodicCandidateObjective
          cfg t).W)) =
        Real.cos (theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState theorem_4_15_periodicCandidateObjective
            cfg t).W) • coordinateMatrix (m := 1) (n := 1) 0 0 := by
    ext i j
    fin_cases i
    fin_cases j
    simp [coordinateMatrix]
  rw [hmatrix, theorem_4_15_periodicCandidate_scalarCoordinateNuclearNorm]

theorem theorem_4_15_periodicCandidate_generatedNuclearGradient (t : ℕ) :
    nuclearNorm (theorem_4_15_periodicCandidateObjective.grad
      (deterministicMomentumMuonState theorem_4_15_periodicCandidateObjective
        theorem_4_15_periodicCandidateConfig t).W) = 1 := by
  rw [theorem_4_15_periodicCandidate_generatedGradient,
    theorem_4_15_periodicCandidate_coordinateNuclearNorm]

theorem theorem_4_15_periodicCandidate_generatedAverage_one
    (T : ℕ) (hT : horizonDomain T) :
    deterministicMomentumAverageNuclearGradient
        theorem_4_15_periodicCandidateObjective
        theorem_4_15_periodicCandidateConfig T = 1 := by
  unfold deterministicMomentumAverageNuclearGradient
  simp_rw [theorem_4_15_periodicCandidate_generatedNuclearGradient]
  rw [Finset.sum_const, Finset.card_range]
  simp only [nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (by exact_mod_cast (ne_of_gt hT))

/- The fixed periodic orbit has `beta = 0`, hence its actual `1 - beta` is
   one.  The printed otherwise schedule can contain this configuration only
   when the upper theta constant compensates for the shrinking
   `epsilon^2 / sigma^2` target.  Clearing the positive noise denominator
   gives the exact necessary inequality below.  This identifies the schedule
   hypothesis that fails for all sufficiently small accuracies; it is not a
   counterexample to the source theorem. -/
theorem theorem_4_15_periodicCandidate_schedule_forces_accuracy_floor
    (T : ℕ) (sigma Delta epsilon : ℝ)
    (betaLower betaUpper etaLower etaUpper : ℝ)
    (hsigma : 0 < sigma)
    (hschedule : theorem_4_15_otherwiseBranchSchedule
      (deterministicOracleConfig theorem_4_15_periodicCandidateConfig)
      T sigma Delta epsilon betaLower betaUpper etaLower etaUpper) :
    sigma ^ 2 ≤ betaUpper * epsilon ^ 2 ∧
      (2 * Real.pi) * sigma ^ 3 ≤ etaUpper * Delta * epsilon ^ 2 := by
  rcases hschedule with
    ⟨_hdomain, _hbatch, hbeta, heta, _hconstant⟩
  constructor
  · have hupper := hbeta.2.2.2
    dsimp [deterministicOracleConfig, theorem_4_15_periodicCandidateConfig,
      theorem_4_15_otherwiseOneMinusBetaScale, matrixRankBound, sourceQuot] at hupper
    norm_num at hupper
    have hscaled := mul_le_mul_of_nonneg_right hupper (sq_nonneg sigma)
    calc
      sigma ^ 2 = 1 * sigma ^ 2 := by ring
      _ ≤ (betaUpper * (epsilon ^ 2 / sigma ^ 2)) * sigma ^ 2 := hscaled
      _ = betaUpper * epsilon ^ 2 := by
        field_simp [ne_of_gt hsigma]
  · have hupper := heta.2.2.2
    dsimp [deterministicOracleConfig, theorem_4_15_periodicCandidateConfig,
      theorem_4_15_otherwiseEtaRate, matrixRankBound, sourceQuot] at hupper
    norm_num at hupper
    have hscaled := mul_le_mul_of_nonneg_right hupper
      (show 0 ≤ sigma ^ 3 by positivity)
    calc
      (2 * Real.pi) * sigma ^ 3 ≤
          (etaUpper * (Delta * epsilon ^ 2 / sigma ^ 3)) * sigma ^ 3 := hscaled
      _ = etaUpper * Delta * epsilon ^ 2 := by
        field_simp [ne_of_gt hsigma]

/- Consequently the concrete fixed-step periodic orbit from this section is
   incompatible with the source schedule whenever accuracy is below the
   displayed noise-dependent floor.  The obstruction already occurs in the
   beta scale, before curvature, horizon, or output-transfer conditions are
   considered. -/
theorem theorem_4_15_periodicCandidate_schedule_incompatible_of_small_accuracy
    (T : ℕ) (sigma Delta epsilon : ℝ)
    (betaLower betaUpper etaLower etaUpper : ℝ)
    (hsigma : 0 < sigma)
    (hsmall : betaUpper * epsilon ^ 2 < sigma ^ 2) :
    ¬ theorem_4_15_otherwiseBranchSchedule
      (deterministicOracleConfig theorem_4_15_periodicCandidateConfig)
      T sigma Delta epsilon betaLower betaUpper etaLower etaUpper := by
  intro hschedule
  exact (not_le_of_gt hsmall)
    (theorem_4_15_periodicCandidate_schedule_forces_accuracy_floor
      T sigma Delta epsilon betaLower betaUpper etaLower etaUpper
      hsigma hschedule).1

theorem theorem_4_15_periodicCandidate_eta_schedule_incompatible_of_small_accuracy
    (T : ℕ) (sigma Delta epsilon : ℝ)
    (betaLower betaUpper etaLower etaUpper : ℝ)
    (hsigma : 0 < sigma)
    (hsmall : etaUpper * Delta * epsilon ^ 2 <
      (2 * Real.pi) * sigma ^ 3) :
    ¬ theorem_4_15_otherwiseBranchSchedule
      (deterministicOracleConfig theorem_4_15_periodicCandidateConfig)
      T sigma Delta epsilon betaLower betaUpper etaLower etaUpper := by
  intro hschedule
  exact (not_le_of_gt hsmall)
    (theorem_4_15_periodicCandidate_schedule_forces_accuracy_floor
      T sigma Delta epsilon betaLower betaUpper etaLower etaUpper
      hsigma hschedule).2

theorem theorem_4_15_periodicCandidate_not_source_small_j_run_of_small_accuracy
    (T : ℕ) (sigma Delta epsilon C s : ℝ)
    (betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ)
    (hsigma : 0 < sigma)
    (hsmall : betaUpper * epsilon ^ 2 < sigma ^ 2) :
    ¬ theorem_4_15_otherwiseSourceSmallJGeneratedRunForAccuracyHorizon
      (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
      (fun _epsilon _N =>
        deterministicOracleConfig theorem_4_15_periodicCandidateConfig)
      0 sigma Delta epsilon C s betaLower betaUpper etaLower etaUpper
      horizonLower horizonUpper T := by
  intro hrun
  rcases hrun with
    ⟨_horizon, _hfinite, _hDelta, _hthird, _hvariance, _hwd, _hW0,
      hschedule, _hsource, _hhorizonScale, _hregDomain, _hregime⟩
  exact
    (theorem_4_15_periodicCandidate_schedule_incompatible_of_small_accuracy
      T sigma Delta epsilon betaLower betaUpper etaLower etaUpper
      hsigma hsmall) hschedule

/- A concrete accuracy-indexed configuration for the shrinking-schedule
   counterexample program.  In one dimension the printed scales reduce
   exactly to `1 - beta = epsilon^2 / sigma^2` and
   `eta = Delta * epsilon^2 / sigma^3`.  Unlike the earlier resonant config,
   this is one of the actual Algorithm 1 schedules permitted by Appendix B.4
   at every positive accuracy below the noise scale. -/
def theorem_4_15_periodicCandidateShrinkingConfig
    (sigma Delta epsilon : ℝ)
    (hsigma : 0 < sigma) (hepsilon : 0 < epsilon)
    (hepsilon_le_sigma : epsilon ≤ sigma) :
    DeterministicMomentumMuonConfig 1 1 where
  W0 := 0
  eta := fun _ =>
    theorem_4_15_otherwiseEtaRate 1 1 sigma Delta epsilon 0
  beta := 1 - theorem_4_15_otherwiseOneMinusBetaScale 1 1 sigma epsilon
  beta_mem := by
    have hsigma_sq : 0 < sigma ^ 2 := sq_pos_of_pos hsigma
    have hepsilon_sq : 0 < epsilon ^ 2 := sq_pos_of_pos hepsilon
    have hsquares : epsilon ^ 2 ≤ sigma ^ 2 := by
      nlinarith
    have hratio_pos : 0 < epsilon ^ 2 / sigma ^ 2 :=
      div_pos hepsilon_sq hsigma_sq
    have hratio_le : epsilon ^ 2 / sigma ^ 2 ≤ 1 :=
      (div_le_one hsigma_sq).2 hsquares
    simpa [theorem_4_15_otherwiseOneMinusBetaScale, sourceQuot,
      matrixRankBound] using
      (And.intro (sub_nonneg.mpr hratio_le) (sub_lt_self 1 hratio_pos))

/- The concrete configuration discharges the complete printed constant-step
   schedule with theta constants equal to one.  This removes schedule
   existence from the remaining sine-orbit investigation; what is still open
   is the full-horizon directional-curvature cancellation and gradient-average
   separation, not compatibility with the Appendix B.4 scales. -/
theorem theorem_4_15_periodicCandidate_shrinkingConfig_schedule
    (T : ℕ) (sigma Delta epsilon : ℝ)
    (hT : horizonDomain T)
    (hsigma : 0 < sigma) (hepsilon : 0 < epsilon)
    (hepsilon_le_sigma : epsilon ≤ sigma) :
    theorem_4_15_otherwiseBranchSchedule
      (deterministicOracleConfig
        (theorem_4_15_periodicCandidateShrinkingConfig
          sigma Delta epsilon hsigma hepsilon hepsilon_le_sigma))
      T sigma Delta epsilon 1 1 1 1 := by
  have hsigma_ne : sigma ≠ 0 := ne_of_gt hsigma
  refine ⟨?_, rfl, ?_, ?_, ?_⟩
  · refine ⟨hT, ?_, ?_, ?_⟩
    · simp [sourceQuotDomain, matrixRankBound, hsigma_ne]
    · simp [sourceSqrtDomain, matrixRankBound]
    · exact pow_ne_zero 3 hsigma_ne
  · unfold theorem_4_15_uniformThetaAt
    refine ⟨by norm_num, le_rfl, ?_, ?_⟩
    · simp [deterministicOracleConfig,
        theorem_4_15_periodicCandidateShrinkingConfig]
    · simp [deterministicOracleConfig,
        theorem_4_15_periodicCandidateShrinkingConfig]
  · unfold theorem_4_15_uniformThetaAt
    refine ⟨by norm_num, le_rfl, ?_, ?_⟩
    · simp [deterministicOracleConfig,
        theorem_4_15_periodicCandidateShrinkingConfig,
        theorem_4_15_otherwiseEtaRate]
    · simp [deterministicOracleConfig,
        theorem_4_15_periodicCandidateShrinkingConfig,
        theorem_4_15_otherwiseEtaRate]
  · intro t _ht
    rfl

/- Positivity of the source step is also automatic for the same concrete
   schedule once the source initial-gap parameter is positive.  This is the
   remaining schedule-side definedness field used by the source-small-`J`
   generated-run predicate. -/
theorem theorem_4_15_periodicCandidate_shrinkingConfig_sourceDomain
    (T : ℕ) (sigma Delta epsilon : ℝ)
    (hT : horizonDomain T)
    (hsigma : 0 < sigma) (hDelta : 0 < Delta)
    (hepsilon : 0 < epsilon)
    (hepsilon_le_sigma : epsilon ≤ sigma) :
    theorem_4_15_sourceDomain T
      ((deterministicOracleConfig
        (theorem_4_15_periodicCandidateShrinkingConfig
          sigma Delta epsilon hsigma hepsilon hepsilon_le_sigma)).eta 0) := by
  have heta : 0 < theorem_4_15_otherwiseEtaRate
      1 1 sigma Delta epsilon 0 := by
    unfold theorem_4_15_otherwiseEtaRate sourceQuot matrixRankBound
    norm_num
    positivity
  refine ⟨⟨hT, ?_⟩, ?_⟩
  · unfold sourceQuotDomain
    exact mul_ne_zero (by exact_mod_cast (Nat.ne_of_gt hT)) (ne_of_gt heta)
  · simpa [deterministicOracleConfig,
      theorem_4_15_periodicCandidateShrinkingConfig] using heta

/- Select the nearest integral horizon above the exact one-dimensional
   Appendix B.4 complexity scale.  Keeping this choice independent of the
   objective and orbit makes explicit that the remaining counterexample work
   is genuinely dynamical rather than another schedule-existence issue. -/
def theorem_4_15_periodicCandidateShrinkingHorizon
    (sigma epsilon : ℝ) : ℕ :=
  Nat.ceil (theorem_4_15_otherwiseComplexityRate 1 1 sigma epsilon)

/- For positive accuracy below the noise scale, the selected horizon is
   positive and is uniformly between one and two times the printed
   `sigma^3 * r^(3/2) * epsilon^(-3)` rate.  Thus constants one and two supply
   exactly the horizon field of the source-small-`J` generated-run predicate. -/
theorem theorem_4_15_periodicCandidate_shrinkingHorizon_scale
    (sigma epsilon : ℝ)
    (hsigma : 0 < sigma) (hepsilon : 0 < epsilon)
    (hepsilon_le_sigma : epsilon ≤ sigma) :
    let N := theorem_4_15_periodicCandidateShrinkingHorizon sigma epsilon
    horizonDomain N ∧
      theorem_4_15_uniformThetaAt 1 2
        (theorem_4_15_otherwiseComplexityRate 1 1 sigma epsilon) (N : ℝ) := by
  let rate := theorem_4_15_otherwiseComplexityRate 1 1 sigma epsilon
  have hrate_eq : rate = (sigma / epsilon) ^ 3 := by
    dsimp [rate, theorem_4_15_otherwiseComplexityRate, matrixRankBound]
    norm_num
    field_simp [ne_of_gt hepsilon]
  have hratio : 1 ≤ sigma / epsilon := by
    exact (le_div_iff₀ hepsilon).2 (by simpa using hepsilon_le_sigma)
  have hrate_one : 1 ≤ rate := by
    rw [hrate_eq]
    exact one_le_pow₀ hratio
  have hrate_nonneg : 0 ≤ rate := le_trans (by norm_num) hrate_one
  let N := theorem_4_15_periodicCandidateShrinkingHorizon sigma epsilon
  have hNlower : rate ≤ (N : ℝ) := by
    simpa [N, theorem_4_15_periodicCandidateShrinkingHorizon, rate] using
      Nat.le_ceil rate
  have hNpos : horizonDomain N := by
    dsimp [horizonDomain]
    have honeN : (1 : ℝ) ≤ (N : ℝ) := le_trans hrate_one hNlower
    exact_mod_cast (show (1 : ℕ) ≤ N by exact_mod_cast honeN)
  have hNupper : (N : ℝ) ≤ 2 * rate := by
    have hceil := Nat.ceil_lt_add_one hrate_nonneg
    have hadd : rate + 1 ≤ 2 * rate := by linarith
    exact le_trans hceil.le hadd
  dsimp [theorem_4_15_periodicCandidateShrinkingHorizon]
  refine ⟨hNpos, ?_⟩
  exact ⟨by norm_num, by norm_num, by simpa [one_mul, N, rate] using hNlower,
    by simpa [N, rate] using hNupper⟩

/- Specialize the objective-independent shrinking schedule to the fixed
   nonperiodic problem.  Its advertised noise scale and source gap are the
   same positive number, so both printed one-dimensional step parameters are
   exactly `epsilon^2 / sigma^2`. -/
def theorem_4_15_nonperiodicCandidateConfig
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_le_sigma :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma) :
    DeterministicMomentumMuonConfig 1 1 :=
  theorem_4_15_periodicCandidateShrinkingConfig
    theorem_4_15_nonperiodicCandidateSigma
    theorem_4_15_nonperiodicCandidateSigma epsilon
    theorem_4_15_nonperiodicCandidateSigma_pos hepsilon hepsilon_le_sigma

def theorem_4_15_nonperiodicCandidateHorizon (epsilon : ℝ) : ℕ :=
  theorem_4_15_periodicCandidateShrinkingHorizon
    theorem_4_15_nonperiodicCandidateSigma epsilon

/- One proof-irrelevant family for the complete accuracy-indexed
   counterexample.  On the source neighbourhood it selects the printed
   shrinking Algorithm 1 configuration at the requested accuracy; outside
   that neighbourhood it uses a fixed valid fallback configuration.  The
   horizon argument is intentionally irrelevant because the printed schedule
   is constant-step and its parameters depend on accuracy, not on which
   admissible selected horizon is supplied. -/
noncomputable def theorem_4_15_nonperiodicCandidateConfigForAccuracyHorizon
    (epsilon : ℝ) (_N : ℕ) : StochasticMuonConfig 1 1 :=
  if h : 0 < epsilon ∧ epsilon ≤ theorem_4_15_nonperiodicCandidateSigma then
    deterministicOracleConfig
      (theorem_4_15_nonperiodicCandidateConfig epsilon h.1 h.2)
  else
    deterministicOracleConfig
      (theorem_4_15_nonperiodicCandidateConfig
        theorem_4_15_nonperiodicCandidateSigma
        theorem_4_15_nonperiodicCandidateSigma_pos le_rfl)

theorem theorem_4_15_nonperiodicCandidateConfigForAccuracyHorizon_eq
    (epsilon : ℝ) (N : ℕ) (hepsilon : 0 < epsilon)
    (hepsilon_le_sigma :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma) :
    theorem_4_15_nonperiodicCandidateConfigForAccuracyHorizon epsilon N =
      deterministicOracleConfig
        (theorem_4_15_nonperiodicCandidateConfig epsilon hepsilon
          hepsilon_le_sigma) := by
  rw [theorem_4_15_nonperiodicCandidateConfigForAccuracyHorizon,
    dif_pos (And.intro hepsilon hepsilon_le_sigma)]

theorem theorem_4_15_nonperiodicCandidateConfig_exact_parameters
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_le_sigma :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma) :
    let cfg := theorem_4_15_nonperiodicCandidateConfig epsilon hepsilon
      hepsilon_le_sigma
    1 - cfg.beta =
        epsilon ^ 2 / theorem_4_15_nonperiodicCandidateSigma ^ 2 ∧
      cfg.eta 0 =
        epsilon ^ 2 / theorem_4_15_nonperiodicCandidateSigma ^ 2 := by
  dsimp [theorem_4_15_nonperiodicCandidateConfig,
    theorem_4_15_periodicCandidateShrinkingConfig,
    theorem_4_15_otherwiseOneMinusBetaScale,
    theorem_4_15_otherwiseEtaRate, sourceQuot, matrixRankBound]
  constructor
  · norm_num [matrixRankBound]
  · norm_num [matrixRankBound]
    field_simp [ne_of_gt theorem_4_15_nonperiodicCandidateSigma_pos]

theorem theorem_4_15_nonperiodicCandidateConfig_schedule
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_le_sigma :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma) :
    theorem_4_15_otherwiseBranchSchedule
      (deterministicOracleConfig
        (theorem_4_15_nonperiodicCandidateConfig epsilon hepsilon
          hepsilon_le_sigma))
      (theorem_4_15_nonperiodicCandidateHorizon epsilon)
      theorem_4_15_nonperiodicCandidateSigma
      theorem_4_15_nonperiodicCandidateSigma epsilon 1 1 1 1 := by
  exact theorem_4_15_periodicCandidate_shrinkingConfig_schedule
    (theorem_4_15_nonperiodicCandidateHorizon epsilon)
    theorem_4_15_nonperiodicCandidateSigma
    theorem_4_15_nonperiodicCandidateSigma epsilon
    (theorem_4_15_periodicCandidate_shrinkingHorizon_scale
      theorem_4_15_nonperiodicCandidateSigma epsilon
      theorem_4_15_nonperiodicCandidateSigma_pos hepsilon
      hepsilon_le_sigma).1
    theorem_4_15_nonperiodicCandidateSigma_pos hepsilon hepsilon_le_sigma

theorem theorem_4_15_nonperiodicCandidateConfig_sourceDomain
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_le_sigma :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma) :
    theorem_4_15_sourceDomain
      (theorem_4_15_nonperiodicCandidateHorizon epsilon)
      ((deterministicOracleConfig
        (theorem_4_15_nonperiodicCandidateConfig epsilon hepsilon
          hepsilon_le_sigma)).eta 0) := by
  exact theorem_4_15_periodicCandidate_shrinkingConfig_sourceDomain
    (theorem_4_15_nonperiodicCandidateHorizon epsilon)
    theorem_4_15_nonperiodicCandidateSigma
    theorem_4_15_nonperiodicCandidateSigma epsilon
    (theorem_4_15_periodicCandidate_shrinkingHorizon_scale
      theorem_4_15_nonperiodicCandidateSigma epsilon
      theorem_4_15_nonperiodicCandidateSigma_pos hepsilon
      hepsilon_le_sigma).1
    theorem_4_15_nonperiodicCandidateSigma_pos
    theorem_4_15_nonperiodicCandidateSigma_pos hepsilon hepsilon_le_sigma

theorem theorem_4_15_nonperiodicCandidateHorizon_scale
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_le_sigma :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma) :
    horizonDomain (theorem_4_15_nonperiodicCandidateHorizon epsilon) ∧
      theorem_4_15_uniformThetaAt 1 2
        (theorem_4_15_otherwiseComplexityRate 1 1
          theorem_4_15_nonperiodicCandidateSigma epsilon)
        (theorem_4_15_nonperiodicCandidateHorizon epsilon : ℝ) := by
  exact theorem_4_15_periodicCandidate_shrinkingHorizon_scale
    theorem_4_15_nonperiodicCandidateSigma epsilon
    theorem_4_15_nonperiodicCandidateSigma_pos hepsilon hepsilon_le_sigma

/- At the selected Appendix B.4 horizon, the normalized lower-order power
   envelope is O(epsilon) with an explicit constant.  This completes the
   remainder half of the counterexample's finite-sum estimate independently
   of the still-open weighted-cosine lower-density half. -/
theorem theorem_4_15_nonperiodicCandidate_selected_remainder_average_le
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_le_sigma :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma) :
    let sigma := theorem_4_15_nonperiodicCandidateSigma
    let h := epsilon ^ 2 / sigma ^ 2
    let N := theorem_4_15_nonperiodicCandidateHorizon epsilon
    ((N : ℝ)⁻¹) * (∑ t ∈ Finset.range N,
      (1 + (t : ℝ) * h) ^ (-(6 : ℝ) / 5)) ≤
      6 * epsilon / sigma := by
  let sigma := theorem_4_15_nonperiodicCandidateSigma
  let h := epsilon ^ 2 / sigma ^ 2
  let N := theorem_4_15_nonperiodicCandidateHorizon epsilon
  have hsigma : 0 < sigma := by
    simpa [sigma] using theorem_4_15_nonperiodicCandidateSigma_pos
  have hh : 0 < h := by
    dsimp [h]
    positivity
  have hscale := theorem_4_15_nonperiodicCandidateHorizon_scale
    epsilon hepsilon hepsilon_le_sigma
  have hN : 0 < N := by simpa [N] using hscale.1
  have havg :=
    theorem_4_15_nonperiodicCandidate_remainder_mesh_average_le h N hh hN
  have hsquares : epsilon ^ 2 ≤ sigma ^ 2 := by
    dsimp [sigma]
    nlinarith [theorem_4_15_nonperiodicCandidateSigma_pos]
  have hh_le_one : h ≤ 1 := by
    dsimp [h]
    exact (div_le_one (sq_pos_of_pos hsigma)).2 hsquares
  have hrate :
      theorem_4_15_otherwiseComplexityRate 1 1 sigma epsilon =
        (sigma / epsilon) ^ 3 := by
    dsimp [theorem_4_15_otherwiseComplexityRate, matrixRankBound]
    norm_num
    field_simp [ne_of_gt hepsilon]
  have hNlower : (sigma / epsilon) ^ 3 ≤ (N : ℝ) := by
    have hraw := hscale.2.2.2.1
    rw [show theorem_4_15_otherwiseComplexityRate 1 1
        theorem_4_15_nonperiodicCandidateSigma epsilon =
          (sigma / epsilon) ^ 3 by simpa [sigma] using hrate] at hraw
    simpa [N] using hraw
  have hNhLower : sigma / epsilon ≤ (N : ℝ) * h := by
    have hmul := mul_le_mul_of_nonneg_right hNlower hh.le
    calc
      sigma / epsilon = (sigma / epsilon) ^ 3 * h := by
        dsimp [h]
        field_simp [ne_of_gt hepsilon, ne_of_gt hsigma]
      _ ≤ (N : ℝ) * h := hmul
  have hdenomPos : 0 < (N : ℝ) * h := mul_pos (by positivity) hh
  have hratio :
      (h + 5) / ((N : ℝ) * h) ≤ 6 * epsilon / sigma := by
    apply (div_le_iff₀ hdenomPos).2
    have hepsSig : 0 < epsilon / sigma := div_pos hepsilon hsigma
    have hprodRaw := mul_le_mul_of_nonneg_left hNhLower hepsSig.le
    have hcancel : (epsilon / sigma) * (sigma / epsilon) = 1 := by
      field_simp [ne_of_gt hepsilon, ne_of_gt hsigma]
    rw [hcancel] at hprodRaw
    have hprod : 1 ≤ (epsilon / sigma) * ((N : ℝ) * h) := hprodRaw
    have hlarge : 6 ≤ 6 * epsilon / sigma * ((N : ℝ) * h) := by
      calc
        6 = 6 * 1 := by ring
        _ ≤ 6 * ((epsilon / sigma) * ((N : ℝ) * h)) :=
          mul_le_mul_of_nonneg_left hprod (by norm_num)
        _ = 6 * epsilon / sigma * ((N : ℝ) * h) := by ring
    nlinarith
  exact havg.trans hratio

theorem theorem_4_15_nonperiodicCandidate_selected_remainder_envelope_le
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_le_sigma :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma) :
    let sigma := theorem_4_15_nonperiodicCandidateSigma
    let h := epsilon ^ 2 / sigma ^ 2
    let N := theorem_4_15_nonperiodicCandidateHorizon epsilon
    ((N : ℝ)⁻¹) * (∑ t ∈ Finset.range N,
      (33 : ℝ) / 5 *
        (1 + (t : ℝ) * h) ^ (-(6 : ℝ) / 5)) ≤
      (198 : ℝ) / 5 * epsilon / sigma := by
  let sigma := theorem_4_15_nonperiodicCandidateSigma
  let h := epsilon ^ 2 / sigma ^ 2
  let N := theorem_4_15_nonperiodicCandidateHorizon epsilon
  have havg :=
    theorem_4_15_nonperiodicCandidate_selected_remainder_average_le
      epsilon hepsilon hepsilon_le_sigma
  have hmul := mul_le_mul_of_nonneg_left havg
    (show (0 : ℝ) ≤ 33 / 5 by norm_num)
  calc
    (N : ℝ)⁻¹ * (∑ t ∈ Finset.range N,
        (33 : ℝ) / 5 *
          (1 + (t : ℝ) * h) ^ (-(6 : ℝ) / 5)) =
        (33 / 5) * ((N : ℝ)⁻¹ * (∑ t ∈ Finset.range N,
          (1 + (t : ℝ) * h) ^ (-(6 : ℝ) / 5))) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ (33 / 5) * (6 * epsilon / sigma) := hmul
    _ = (198 / 5) * epsilon / sigma := by ring

/- Summing the checked pointwise gradient decomposition now loses only the
   explicit O(epsilon) remainder.  Thus the remaining counterexample gap is
   exactly the lower-density estimate for the displayed leading cosine sum. -/
theorem theorem_4_15_nonperiodicCandidate_selected_gradient_average_reduction
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_le_sigma :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma) :
    let sigma := theorem_4_15_nonperiodicCandidateSigma
    let h := epsilon ^ 2 / sigma ^ 2
    let N := theorem_4_15_nonperiodicCandidateHorizon epsilon
    ((N : ℝ)⁻¹) * (∑ t ∈ Finset.range N,
        |theorem_4_15_nonperiodicCandidateGradientLeading ((t : ℝ) * h)|) -
      (198 : ℝ) / 5 * epsilon / sigma ≤
    ((N : ℝ)⁻¹) * (∑ t ∈ Finset.range N,
      |theorem_4_15_nonperiodicCandidatePositiveProfileFirst
        ((t : ℝ) * h)|) := by
  let sigma := theorem_4_15_nonperiodicCandidateSigma
  let h := epsilon ^ 2 / sigma ^ 2
  let N := theorem_4_15_nonperiodicCandidateHorizon epsilon
  have hN : 0 < N := by
    simpa [N] using
      (theorem_4_15_nonperiodicCandidateHorizon_scale
        epsilon hepsilon hepsilon_le_sigma).1
  have hpoint :
      (∑ t ∈ Finset.range N,
        (|theorem_4_15_nonperiodicCandidateGradientLeading ((t : ℝ) * h)| -
          (33 : ℝ) / 5 *
            (1 + (t : ℝ) * h) ^ (-(6 : ℝ) / 5))) ≤
      ∑ t ∈ Finset.range N,
        |theorem_4_15_nonperiodicCandidatePositiveProfileFirst
          ((t : ℝ) * h)| := by
    apply Finset.sum_le_sum
    intro t ht
    exact theorem_4_15_nonperiodicCandidate_discrete_gradient_abs_lower
      epsilon t
  have hinv : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  have hscaled := mul_le_mul_of_nonneg_left hpoint hinv
  have hsplit :
      ((N : ℝ)⁻¹) * (∑ t ∈ Finset.range N,
          |theorem_4_15_nonperiodicCandidateGradientLeading ((t : ℝ) * h)|) -
        ((N : ℝ)⁻¹) * (∑ t ∈ Finset.range N,
          (33 : ℝ) / 5 *
            (1 + (t : ℝ) * h) ^ (-(6 : ℝ) / 5)) ≤
      ((N : ℝ)⁻¹) * (∑ t ∈ Finset.range N,
        |theorem_4_15_nonperiodicCandidatePositiveProfileFirst
          ((t : ℝ) * h)|) := by
    calc
      _ = (N : ℝ)⁻¹ * (∑ t ∈ Finset.range N,
          (|theorem_4_15_nonperiodicCandidateGradientLeading ((t : ℝ) * h)| -
            (33 : ℝ) / 5 *
              (1 + (t : ℝ) * h) ^ (-(6 : ℝ) / 5))) := by
        rw [Finset.sum_sub_distrib]
        ring
      _ ≤ _ := hscaled
  have henv :=
    theorem_4_15_nonperiodicCandidate_selected_remainder_envelope_le
      epsilon hepsilon hepsilon_le_sigma
  linarith

/- Squaring the cosine gives a smooth lower minorant of its absolute value.
   This is useful for the density argument because `cos^2` has an exact
   constant-plus-oscillation decomposition, while retaining the same
   power-law amplitude as the leading gradient term. -/
theorem theorem_4_15_nonperiodicCandidate_leading_cos_sq_lower
    {x : ℝ} (hx : 0 ≤ x) :
    (12 : ℝ) / 5 * (1 + x) ^ (-(4 : ℝ) / 5) *
        Real.cos (theorem_4_15_nonperiodicCandidatePhase x) ^ 2 ≤
      |theorem_4_15_nonperiodicCandidateGradientLeading x| := by
  have hbase : 0 ≤ (1 + x) ^ (-(4 : ℝ) / 5) := by positivity
  have hcosAbs :
      |Real.cos (theorem_4_15_nonperiodicCandidatePhase x)| ≤ 1 :=
    Real.abs_cos_le_one _
  have hcosSq :
      Real.cos (theorem_4_15_nonperiodicCandidatePhase x) ^ 2 ≤
        |Real.cos (theorem_4_15_nonperiodicCandidatePhase x)| := by
    rw [← sq_abs]
    nlinarith [abs_nonneg
      (Real.cos (theorem_4_15_nonperiodicCandidatePhase x))]
  rw [theorem_4_15_nonperiodicCandidateGradientLeading,
    abs_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 12 / 5 by norm_num),
    abs_of_nonneg hbase]
  exact mul_le_mul_of_nonneg_left hcosSq
    (mul_nonneg (by norm_num) hbase)

/- The squared-cosine lower minorant separates exactly into its positive
   power-law mass and one signed oscillatory correction.  No stationarity,
   cross-curvature, or `Jstar` quantity occurs in this identity. -/
theorem theorem_4_15_nonperiodicCandidate_weighted_cos_sq_decomposition
    (h : ℝ) (N : ℕ) :
    (∑ t ∈ Finset.range N,
        (1 + (t : ℝ) * h) ^ (-(4 : ℝ) / 5) *
          Real.cos (theorem_4_15_nonperiodicCandidatePhase
            ((t : ℝ) * h)) ^ 2) =
      (1 : ℝ) / 2 *
        ((∑ t ∈ Finset.range N,
            (1 + (t : ℝ) * h) ^ (-(4 : ℝ) / 5)) +
          ∑ t ∈ Finset.range N,
            (1 + (t : ℝ) * h) ^ (-(4 : ℝ) / 5) *
              Real.cos (2 * theorem_4_15_nonperiodicCandidatePhase
                ((t : ℝ) * h))) := by
  calc
    (∑ t ∈ Finset.range N,
        (1 + (t : ℝ) * h) ^ (-(4 : ℝ) / 5) *
          Real.cos (theorem_4_15_nonperiodicCandidatePhase
            ((t : ℝ) * h)) ^ 2) =
        ∑ t ∈ Finset.range N, (1 : ℝ) / 2 *
          ((1 + (t : ℝ) * h) ^ (-(4 : ℝ) / 5) +
            (1 + (t : ℝ) * h) ^ (-(4 : ℝ) / 5) *
              Real.cos (2 * theorem_4_15_nonperiodicCandidatePhase
                ((t : ℝ) * h))) := by
      apply Finset.sum_congr rfl
      intro t _ht
      rw [Real.cos_two_mul]
      ring
    _ = _ := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/- The nonoscillatory mass is bounded below by its terminal weight.  This
   elementary monotonicity estimate keeps the main growing scale explicit;
   only the signed oscillatory correction from the preceding identity still
   needs cancellation control. -/
theorem theorem_4_15_nonperiodicCandidate_power_mass_average_lower
    (h : ℝ) (N : ℕ) (hh : 0 ≤ h) (hN : 0 < N) :
    (1 + (N : ℝ) * h) ^ (-(4 : ℝ) / 5) ≤
      ((N : ℝ)⁻¹) * (∑ t ∈ Finset.range N,
        (1 + (t : ℝ) * h) ^ (-(4 : ℝ) / 5)) := by
  have hpoint :
      (∑ _t ∈ Finset.range N,
          (1 + (N : ℝ) * h) ^ (-(4 : ℝ) / 5)) ≤
        ∑ t ∈ Finset.range N,
          (1 + (t : ℝ) * h) ^ (-(4 : ℝ) / 5) := by
    apply Finset.sum_le_sum
    intro t ht
    have htN : t ≤ N := (Finset.mem_range.mp ht).le
    have htNReal : (t : ℝ) ≤ (N : ℝ) := by exact_mod_cast htN
    have hbase : 1 + (t : ℝ) * h ≤ 1 + (N : ℝ) * h := by
      simpa [add_comm] using
        (add_le_add_left (mul_le_mul_of_nonneg_right htNReal hh) 1)
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by norm_num)
  have hinv : 0 ≤ (N : ℝ)⁻¹ := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hpoint hinv
  have hNne : (N : ℝ) ≠ 0 := by positivity
  calc
    (1 + (N : ℝ) * h) ^ (-(4 : ℝ) / 5) =
        (N : ℝ)⁻¹ * (∑ _t ∈ Finset.range N,
          (1 + (N : ℝ) * h) ^ (-(4 : ℝ) / 5)) := by
      simp [hNne]
    _ ≤ _ := hscaled

/- At the printed selected horizon the terminal mesh location is at most
   `2 * sigma / epsilon`.  Hence the positive part of the squared-cosine
   decomposition already has the required larger-than-linear power scale;
   the remaining task is to show that the signed oscillation cannot cancel a
   fixed fraction of this mass. -/
theorem theorem_4_15_nonperiodicCandidate_selected_power_mass_lower
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_le_sigma :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma) :
    let sigma := theorem_4_15_nonperiodicCandidateSigma
    let h := epsilon ^ 2 / sigma ^ 2
    let N := theorem_4_15_nonperiodicCandidateHorizon epsilon
    (1 + 2 * sigma / epsilon) ^ (-(4 : ℝ) / 5) ≤
      ((N : ℝ)⁻¹) * (∑ t ∈ Finset.range N,
        (1 + (t : ℝ) * h) ^ (-(4 : ℝ) / 5)) := by
  let sigma := theorem_4_15_nonperiodicCandidateSigma
  let h := epsilon ^ 2 / sigma ^ 2
  let N := theorem_4_15_nonperiodicCandidateHorizon epsilon
  have hsigma : 0 < sigma := by
    simpa [sigma] using theorem_4_15_nonperiodicCandidateSigma_pos
  have hh : 0 < h := by
    dsimp [h]
    positivity
  have hscale := theorem_4_15_nonperiodicCandidateHorizon_scale
    epsilon hepsilon hepsilon_le_sigma
  have hN : 0 < N := by simpa [N] using hscale.1
  have hrate :
      theorem_4_15_otherwiseComplexityRate 1 1 sigma epsilon =
        (sigma / epsilon) ^ 3 := by
    dsimp [theorem_4_15_otherwiseComplexityRate, matrixRankBound]
    norm_num
    field_simp [ne_of_gt hepsilon]
  have hNupper : (N : ℝ) ≤ 2 * (sigma / epsilon) ^ 3 := by
    have hraw := hscale.2.2.2.2
    rw [show theorem_4_15_otherwiseComplexityRate 1 1
        theorem_4_15_nonperiodicCandidateSigma epsilon =
          (sigma / epsilon) ^ 3 by simpa [sigma] using hrate] at hraw
    simpa [N] using hraw
  have hNhUpper : (N : ℝ) * h ≤ 2 * sigma / epsilon := by
    have hmul := mul_le_mul_of_nonneg_right hNupper hh.le
    calc
      (N : ℝ) * h ≤ 2 * (sigma / epsilon) ^ 3 * h := hmul
      _ = 2 * sigma / epsilon := by
        dsimp [h]
        field_simp [ne_of_gt hepsilon, ne_of_gt hsigma]
  have hterminal :=
    theorem_4_15_nonperiodicCandidate_power_mass_average_lower h N hh.le hN
  have hbase : 1 + (N : ℝ) * h ≤ 1 + 2 * sigma / epsilon :=
    by simpa [add_comm] using add_le_add_left hNhUpper 1
  have hrpow :
      (1 + 2 * sigma / epsilon) ^ (-(4 : ℝ) / 5) ≤
        (1 + (N : ℝ) * h) ^ (-(4 : ℝ) / 5) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by norm_num)
  exact hrpow.trans hterminal

/- Combining the pointwise minorant and the exact `cos^2` identity reduces
   the full leading sum to a positive mass plus one signed oscillatory sum.
   This is the finite-sum cancellation milestone to be consumed next. -/
theorem theorem_4_15_nonperiodicCandidate_leading_sum_lower_by_signed_mass
    (h : ℝ) (N : ℕ) (hh : 0 ≤ h) :
    (6 : ℝ) / 5 *
        ((∑ t ∈ Finset.range N,
            (1 + (t : ℝ) * h) ^ (-(4 : ℝ) / 5)) +
          ∑ t ∈ Finset.range N,
            (1 + (t : ℝ) * h) ^ (-(4 : ℝ) / 5) *
              Real.cos (2 * theorem_4_15_nonperiodicCandidatePhase
                ((t : ℝ) * h))) ≤
      ∑ t ∈ Finset.range N,
        |theorem_4_15_nonperiodicCandidateGradientLeading
          ((t : ℝ) * h)| := by
  have hpoint :
      (∑ t ∈ Finset.range N,
        (12 : ℝ) / 5 * (1 + (t : ℝ) * h) ^ (-(4 : ℝ) / 5) *
          Real.cos (theorem_4_15_nonperiodicCandidatePhase
            ((t : ℝ) * h)) ^ 2) ≤
      ∑ t ∈ Finset.range N,
        |theorem_4_15_nonperiodicCandidateGradientLeading
          ((t : ℝ) * h)| := by
    apply Finset.sum_le_sum
    intro t _ht
    apply theorem_4_15_nonperiodicCandidate_leading_cos_sq_lower
    exact mul_nonneg (by positivity) hh
  have hdecomp :=
    theorem_4_15_nonperiodicCandidate_weighted_cos_sq_decomposition h N
  calc
    (6 : ℝ) / 5 *
          ((∑ t ∈ Finset.range N,
              (1 + (t : ℝ) * h) ^ (-(4 : ℝ) / 5)) +
            ∑ t ∈ Finset.range N,
              (1 + (t : ℝ) * h) ^ (-(4 : ℝ) / 5) *
                Real.cos (2 * theorem_4_15_nonperiodicCandidatePhase
                  ((t : ℝ) * h))) =
        ∑ t ∈ Finset.range N,
          (12 : ℝ) / 5 * (1 + (t : ℝ) * h) ^ (-(4 : ℝ) / 5) *
            Real.cos (theorem_4_15_nonperiodicCandidatePhase
              ((t : ℝ) * h)) ^ 2 := by
      calc
        (6 : ℝ) / 5 *
              ((∑ t ∈ Finset.range N,
                  (1 + (t : ℝ) * h) ^ (-(4 : ℝ) / 5)) +
                ∑ t ∈ Finset.range N,
                  (1 + (t : ℝ) * h) ^ (-(4 : ℝ) / 5) *
                    Real.cos (2 * theorem_4_15_nonperiodicCandidatePhase
                      ((t : ℝ) * h))) =
            (12 : ℝ) / 5 * ((1 : ℝ) / 2 *
              ((∑ t ∈ Finset.range N,
                  (1 + (t : ℝ) * h) ^ (-(4 : ℝ) / 5)) +
                ∑ t ∈ Finset.range N,
                  (1 + (t : ℝ) * h) ^ (-(4 : ℝ) / 5) *
                    Real.cos (2 * theorem_4_15_nonperiodicCandidatePhase
                      ((t : ℝ) * h)))) := by ring
        _ = (12 : ℝ) / 5 *
            (∑ t ∈ Finset.range N,
              (1 + (t : ℝ) * h) ^ (-(4 : ℝ) / 5) *
                Real.cos (theorem_4_15_nonperiodicCandidatePhase
                  ((t : ℝ) * h)) ^ 2) := by rw [← hdecomp]
        _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t _ht
          ring
    _ ≤ _ := hpoint

/- The signed correction has a bounded continuous primitive up to an
   integrable power-law remainder.  This is the exact integration-by-parts
   identity behind the discrete cancellation estimate: the phase derivative
   converts the weight `(1+x)^(-4/5)` into the derivative of the sine, while
   differentiating the auxiliary weight contributes only
   `(1+x)^(-11/5)`. -/
theorem theorem_4_15_nonperiodicCandidate_signed_boundary_hasDerivAt
    {x : ℝ} (hx : -1 < x) :
    HasDerivAt
      (fun y : ℝ => (5 : ℝ) / 24 * (1 + y) ^ (-(6 : ℝ) / 5) *
        Real.sin (2 * theorem_4_15_nonperiodicCandidatePhase y))
      ((1 + x) ^ (-(4 : ℝ) / 5) *
          Real.cos (2 * theorem_4_15_nonperiodicCandidatePhase x) -
        (1 : ℝ) / 4 * (1 + x) ^ (-(11 : ℝ) / 5) *
          Real.sin (2 * theorem_4_15_nonperiodicCandidatePhase x)) x := by
  have hq := theorem_4_15_nonperiodicCandidate_rpow_hasDerivAt
    (-(6 : ℝ) / 5) hx
  have hphase := theorem_4_15_nonperiodicCandidatePhase_hasDerivAt hx
  have hsin := (hphase.const_mul 2).sin
  have hprod := (hq.mul hsin).const_mul ((5 : ℝ) / 24)
  convert hprod using 1
  · funext y
    simp only [Pi.mul_apply]
    ring
  · have hz : 0 < 1 + x := by linarith
    have hexp : (-(6 : ℝ) / 5) - 1 = -(11 : ℝ) / 5 := by norm_num
    have hpow :
        (1 + x) ^ (-(6 : ℝ) / 5) * (1 + x) ^ ((2 : ℝ) / 5) =
          (1 + x) ^ (-(4 : ℝ) / 5) := by
      rw [← Real.rpow_add hz]
      norm_num
    rw [hexp]
    rw [show
      (1 + x) ^ (-(6 : ℝ) / 5) *
          (Real.cos (2 * theorem_4_15_nonperiodicCandidatePhase x) *
            (2 * ((12 : ℝ) / 5 * (1 + x) ^ ((2 : ℝ) / 5)))) =
        (24 : ℝ) / 5 * (1 + x) ^ (-(4 : ℝ) / 5) *
          Real.cos (2 * theorem_4_15_nonperiodicCandidatePhase x) by
      rw [← hpow]
      ring]
    ring

/- Integrating the preceding derivative gives an exact decomposition of the
   continuous oscillatory correction into a boundary term and an absolutely
   summable tail.  The later mesh estimate only has to compare the displayed
   finite sum with this continuous integral. -/
theorem theorem_4_15_nonperiodicCandidate_signed_integral_decomposition
    (X : ℝ) (hX : 0 ≤ X) :
    (∫ x in 0..X,
        (1 + x) ^ (-(4 : ℝ) / 5) *
          Real.cos (2 * theorem_4_15_nonperiodicCandidatePhase x)) =
      (5 : ℝ) / 24 * (1 + X) ^ (-(6 : ℝ) / 5) *
          Real.sin (2 * theorem_4_15_nonperiodicCandidatePhase X) +
        (1 : ℝ) / 4 *
          (∫ x in 0..X,
            (1 + x) ^ (-(11 : ℝ) / 5) *
              Real.sin (2 * theorem_4_15_nonperiodicCandidatePhase x)) := by
  let lead : ℝ → ℝ := fun x =>
    (1 + x) ^ (-(4 : ℝ) / 5) *
      Real.cos (2 * theorem_4_15_nonperiodicCandidatePhase x)
  let tail : ℝ → ℝ := fun x =>
    (1 : ℝ) / 4 * (1 + x) ^ (-(11 : ℝ) / 5) *
      Real.sin (2 * theorem_4_15_nonperiodicCandidatePhase x)
  let boundary : ℝ → ℝ := fun x =>
    (5 : ℝ) / 24 * (1 + x) ^ (-(6 : ℝ) / 5) *
      Real.sin (2 * theorem_4_15_nonperiodicCandidatePhase x)
  have hx_nonneg {x : ℝ} (hx : x ∈ Set.uIcc (0 : ℝ) X) : 0 ≤ x := by
    rw [Set.uIcc_of_le hX] at hx
    exact hx.1
  have hboundary : ∀ x ∈ Set.uIcc (0 : ℝ) X,
      HasDerivAt boundary (lead x - tail x) x := by
    intro x hx
    simpa [boundary, lead, tail] using
      theorem_4_15_nonperiodicCandidate_signed_boundary_hasDerivAt
        (show -1 < x by linarith [hx_nonneg hx])
  have hlead_cont : ContinuousOn lead (Set.uIcc (0 : ℝ) X) := by
    intro x hx
    have hx' : -1 < x := by linarith [hx_nonneg hx]
    have hpow :=
      (theorem_4_15_nonperiodicCandidate_rpow_hasDerivAt
        (-(4 : ℝ) / 5) hx').continuousAt
    have hphase :=
      (theorem_4_15_nonperiodicCandidatePhase_hasDerivAt hx').continuousAt
    have htwophase : ContinuousAt
        (fun y : ℝ => 2 * theorem_4_15_nonperiodicCandidatePhase y) x :=
      continuousAt_const.mul hphase
    exact (hpow.mul
      (Real.continuous_cos.continuousAt.comp htwophase)).continuousWithinAt
  have htail_cont : ContinuousOn tail (Set.uIcc (0 : ℝ) X) := by
    intro x hx
    have hx' : -1 < x := by linarith [hx_nonneg hx]
    have hpow :=
      (theorem_4_15_nonperiodicCandidate_rpow_hasDerivAt
        (-(11 : ℝ) / 5) hx').continuousAt
    have hphase :=
      (theorem_4_15_nonperiodicCandidatePhase_hasDerivAt hx').continuousAt
    have htwophase : ContinuousAt
        (fun y : ℝ => 2 * theorem_4_15_nonperiodicCandidatePhase y) x :=
      continuousAt_const.mul hphase
    exact (((continuousAt_const.mul hpow).mul
      (Real.continuous_sin.continuousAt.comp htwophase))).continuousWithinAt
  have hlead_int : IntervalIntegrable lead volume 0 X :=
    hlead_cont.intervalIntegrable
  have htail_int : IntervalIntegrable tail volume 0 X :=
    htail_cont.intervalIntegrable
  have hftc :
      (∫ x in 0..X, lead x - tail x) = boundary X - boundary 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hboundary
      (hlead_int.sub htail_int)
  have hboundary_zero : boundary 0 = 0 := by
    simp [boundary, theorem_4_15_nonperiodicCandidatePhase]
  rw [intervalIntegral.integral_sub hlead_int htail_int,
    hboundary_zero, sub_zero] at hftc
  have htail_factor :
      (∫ x in 0..X, tail x) =
        (1 : ℝ) / 4 *
          (∫ x in 0..X,
            (1 + x) ^ (-(11 : ℝ) / 5) *
              Real.sin (2 * theorem_4_15_nonperiodicCandidatePhase x)) := by
    simp_rw [tail, mul_assoc]
    rw [intervalIntegral.integral_const_mul]
  dsimp [lead, boundary] at hftc ⊢
  rw [htail_factor] at hftc
  linarith

/- The continuous signed correction is uniformly bounded, independently of
   the endpoint.  This is the quantitative cancellation fact needed before
   passing back to the shrinking generated mesh. -/
theorem theorem_4_15_nonperiodicCandidate_signed_integral_abs_le
    (X : ℝ) (hX : 0 ≤ X) :
    |(∫ x in 0..X,
        (1 + x) ^ (-(4 : ℝ) / 5) *
          Real.cos (2 * theorem_4_15_nonperiodicCandidatePhase x))| ≤
      (5 : ℝ) / 12 := by
  let tail0 : ℝ → ℝ := fun x =>
    (1 + x) ^ (-(11 : ℝ) / 5) *
      Real.sin (2 * theorem_4_15_nonperiodicCandidatePhase x)
  let power : ℝ → ℝ := fun x => (1 + x) ^ (-(11 : ℝ) / 5)
  have hx_nonneg {x : ℝ} (hx : x ∈ Set.uIcc (0 : ℝ) X) : 0 ≤ x := by
    rw [Set.uIcc_of_le hX] at hx
    exact hx.1
  have hpower_cont : ContinuousOn power (Set.uIcc (0 : ℝ) X) := by
    intro x hx
    exact (theorem_4_15_nonperiodicCandidate_rpow_hasDerivAt
      (-(11 : ℝ) / 5) (show -1 < x by linarith [hx_nonneg hx])).continuousAt.continuousWithinAt
  have htail_cont : ContinuousOn tail0 (Set.uIcc (0 : ℝ) X) := by
    intro x hx
    have hx' : -1 < x := by linarith [hx_nonneg hx]
    have hpow :=
      (theorem_4_15_nonperiodicCandidate_rpow_hasDerivAt
        (-(11 : ℝ) / 5) hx').continuousAt
    have hphase :=
      (theorem_4_15_nonperiodicCandidatePhase_hasDerivAt hx').continuousAt
    have htwophase : ContinuousAt
        (fun y : ℝ => 2 * theorem_4_15_nonperiodicCandidatePhase y) x :=
      continuousAt_const.mul hphase
    exact (hpow.mul
      (Real.continuous_sin.continuousAt.comp htwophase)).continuousWithinAt
  have hpower_int : IntervalIntegrable power volume 0 X :=
    hpower_cont.intervalIntegrable
  have htail_int : IntervalIntegrable tail0 volume 0 X :=
    htail_cont.intervalIntegrable
  have hpoint : ∀ x ∈ Set.Icc (0 : ℝ) X, |tail0 x| ≤ power x := by
    intro x hx
    have hpow_nonneg : 0 ≤ power x := by
      dsimp [power]
      exact Real.rpow_nonneg (by linarith [hx.1]) _
    rw [show |tail0 x| = power x *
        |Real.sin (2 * theorem_4_15_nonperiodicCandidatePhase x)| by
      simp [tail0, power, abs_mul, abs_of_nonneg hpow_nonneg]]
    exact mul_le_of_le_one_right hpow_nonneg (Real.abs_sin_le_one _)
  have htail_mono :
      (∫ x in 0..X, |tail0 x|) ≤ ∫ x in 0..X, power x := by
    exact intervalIntegral.integral_mono_on hX htail_int.abs hpower_int hpoint
  have hzeroNot : (0 : ℝ) ∉ Set.uIcc 1 (1 + X) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro hz
    linarith [hz.1]
  have hpower_eval :
      (∫ x in 0..X, power x) =
        (5 : ℝ) / 6 * (1 - (1 + X) ^ (-(6 : ℝ) / 5)) := by
    have hchange :
        (∫ x in 0..X, power x) =
          ∫ u in 1..1 + X, u ^ (-(11 : ℝ) / 5) := by
      simpa [power, add_comm] using
        (intervalIntegral.integral_comp_add_left
          (f := fun u : ℝ => u ^ (-(11 : ℝ) / 5))
          (a := (0 : ℝ)) (b := X) 1)
    rw [hchange, integral_rpow (Or.inr ⟨by norm_num, hzeroNot⟩)]
    rw [Real.one_rpow]
    norm_num
    ring
  have htail_abs : |(∫ x in 0..X, tail0 x)| ≤ (5 : ℝ) / 6 := by
    calc
      |(∫ x in 0..X, tail0 x)| ≤ ∫ x in 0..X, |tail0 x| :=
        intervalIntegral.abs_integral_le_integral_abs hX
      _ ≤ ∫ x in 0..X, power x := htail_mono
      _ = (5 : ℝ) / 6 * (1 - (1 + X) ^ (-(6 : ℝ) / 5)) :=
        hpower_eval
      _ ≤ (5 : ℝ) / 6 := by
        have hp : 0 ≤ (1 + X) ^ (-(6 : ℝ) / 5) := by positivity
        nlinarith
  have hboundary_abs :
      |(5 : ℝ) / 24 * (1 + X) ^ (-(6 : ℝ) / 5) *
          Real.sin (2 * theorem_4_15_nonperiodicCandidatePhase X)| ≤
        (5 : ℝ) / 24 := by
    have hpow_nonneg : 0 ≤ (1 + X) ^ (-(6 : ℝ) / 5) := by positivity
    have hpow_le : (1 + X) ^ (-(6 : ℝ) / 5) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    rw [abs_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 5 / 24 by norm_num),
      abs_of_nonneg hpow_nonneg]
    have hmul :
        (1 + X) ^ (-(6 : ℝ) / 5) *
            |Real.sin (2 * theorem_4_15_nonperiodicCandidatePhase X)| ≤ 1 := by
      calc
        _ ≤ (1 : ℝ) * 1 := mul_le_mul hpow_le
          (Real.abs_sin_le_one _) (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    nlinarith
  have hdecomp :=
    theorem_4_15_nonperiodicCandidate_signed_integral_decomposition X hX
  rw [hdecomp]
  have hquarter_tail :
      |(1 : ℝ) / 4 * (∫ x in 0..X,
          (1 + x) ^ (-(11 : ℝ) / 5) *
            Real.sin (2 * theorem_4_15_nonperiodicCandidatePhase x))| ≤
        (5 : ℝ) / 24 := by
    rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 1 / 4 by norm_num)]
    have htail_abs' :
        |(∫ x in 0..X,
          (1 + x) ^ (-(11 : ℝ) / 5) *
            Real.sin (2 * theorem_4_15_nonperiodicCandidatePhase x))| ≤
          (5 : ℝ) / 6 := by
      simpa only [tail0] using htail_abs
    nlinarith
  exact (abs_add_le _ _).trans (by linarith)

/- The derivative controlling the left-mesh error has one integrable term
   and one explicitly growing-variation term.  Both remain independent of the
   generated stationarity average and of every cross/Jstar quantity. -/
theorem theorem_4_15_nonperiodicCandidate_signed_integrand_hasDerivAt
    {x : ℝ} (hx : -1 < x) :
    HasDerivAt
      (fun y : ℝ => (1 + y) ^ (-(4 : ℝ) / 5) *
        Real.cos (2 * theorem_4_15_nonperiodicCandidatePhase y))
      ((-(4 : ℝ) / 5) * (1 + x) ^ (-(9 : ℝ) / 5) *
          Real.cos (2 * theorem_4_15_nonperiodicCandidatePhase x) -
        (24 : ℝ) / 5 * (1 + x) ^ (-(2 : ℝ) / 5) *
          Real.sin (2 * theorem_4_15_nonperiodicCandidatePhase x)) x := by
  have hweight := theorem_4_15_nonperiodicCandidate_rpow_hasDerivAt
    (-(4 : ℝ) / 5) hx
  have hphase := theorem_4_15_nonperiodicCandidatePhase_hasDerivAt hx
  have hcos := (hphase.const_mul 2).cos
  have hprod := hweight.mul hcos
  convert hprod using 1
  have hz : 0 < 1 + x := by linarith
  have hexp : (-(4 : ℝ) / 5) - 1 = -(9 : ℝ) / 5 := by norm_num
  have hpow :
      (1 + x) ^ (-(4 : ℝ) / 5) * (1 + x) ^ ((2 : ℝ) / 5) =
        (1 + x) ^ (-(2 : ℝ) / 5) := by
    rw [← Real.rpow_add hz]
    norm_num
  rw [hexp]
  rw [← hpow]
  ring

theorem theorem_4_15_nonperiodicCandidate_signed_integrand_deriv_abs_le
    {x : ℝ} (hx : 0 ≤ x) :
    |(-(4 : ℝ) / 5) * (1 + x) ^ (-(9 : ℝ) / 5) *
          Real.cos (2 * theorem_4_15_nonperiodicCandidatePhase x) -
        (24 : ℝ) / 5 * (1 + x) ^ (-(2 : ℝ) / 5) *
          Real.sin (2 * theorem_4_15_nonperiodicCandidatePhase x)| ≤
      (4 : ℝ) / 5 * (1 + x) ^ (-(9 : ℝ) / 5) +
        (24 : ℝ) / 5 * (1 + x) ^ (-(2 : ℝ) / 5) := by
  have hpow9 : 0 ≤ (1 + x) ^ (-(9 : ℝ) / 5) := by positivity
  have hpow2 : 0 ≤ (1 + x) ^ (-(2 : ℝ) / 5) := by positivity
  have hfirst :
      |(-(4 : ℝ) / 5) * (1 + x) ^ (-(9 : ℝ) / 5) *
        Real.cos (2 * theorem_4_15_nonperiodicCandidatePhase x)| ≤
        (4 : ℝ) / 5 * (1 + x) ^ (-(9 : ℝ) / 5) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hpow9]
    norm_num
    have hcoef :
        0 ≤ (4 : ℝ) / 5 * (1 + x) ^ (-(9 : ℝ) / 5) :=
      mul_nonneg (by norm_num) hpow9
    convert (mul_le_mul_of_nonneg_left
      (Real.abs_cos_le_one
        (2 * theorem_4_15_nonperiodicCandidatePhase x)) hcoef) using 1 <;>
      norm_num
  have hsecond :
      |(24 : ℝ) / 5 * (1 + x) ^ (-(2 : ℝ) / 5) *
        Real.sin (2 * theorem_4_15_nonperiodicCandidatePhase x)| ≤
        (24 : ℝ) / 5 * (1 + x) ^ (-(2 : ℝ) / 5) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hpow2]
    norm_num
    have hcoef :
        0 ≤ (24 : ℝ) / 5 * (1 + x) ^ (-(2 : ℝ) / 5) :=
      mul_nonneg (by norm_num) hpow2
    convert (mul_le_mul_of_nonneg_left
      (Real.abs_sin_le_one
        (2 * theorem_4_15_nonperiodicCandidatePhase x)) hcoef) using 1 <;>
      norm_num
  calc
    |(-(4 : ℝ) / 5) * (1 + x) ^ (-(9 : ℝ) / 5) *
          Real.cos (2 * theorem_4_15_nonperiodicCandidatePhase x) -
        (24 : ℝ) / 5 * (1 + x) ^ (-(2 : ℝ) / 5) *
          Real.sin (2 * theorem_4_15_nonperiodicCandidatePhase x)| ≤
        |(-(4 : ℝ) / 5) * (1 + x) ^ (-(9 : ℝ) / 5) *
          Real.cos (2 * theorem_4_15_nonperiodicCandidatePhase x)| +
        |(24 : ℝ) / 5 * (1 + x) ^ (-(2 : ℝ) / 5) *
          Real.sin (2 * theorem_4_15_nonperiodicCandidatePhase x)| :=
      abs_sub _ _
    _ ≤ (4 : ℝ) / 5 * (1 + x) ^ (-(9 : ℝ) / 5) +
        (24 : ℝ) / 5 * (1 + x) ^ (-(2 : ℝ) / 5) := by
      exact add_le_add hfirst hsecond

/- On the nonnegative half-line the derivative envelope is uniformly bounded.
   The sharper power envelope above remains available, but this coarse bound is
   enough for the shrinking-mesh comparison because `N * h^2 = O(epsilon)` on
   the selected schedule. -/
theorem theorem_4_15_nonperiodicCandidate_signed_integrand_deriv_abs_le_uniform
    {x : ℝ} (hx : 0 ≤ x) :
    |(-(4 : ℝ) / 5) * (1 + x) ^ (-(9 : ℝ) / 5) *
          Real.cos (2 * theorem_4_15_nonperiodicCandidatePhase x) -
        (24 : ℝ) / 5 * (1 + x) ^ (-(2 : ℝ) / 5) *
          Real.sin (2 * theorem_4_15_nonperiodicCandidatePhase x)| ≤
      (28 : ℝ) / 5 := by
  have h9 : (1 + x) ^ (-(9 : ℝ) / 5) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have h2 : (1 + x) ^ (-(2 : ℝ) / 5) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have henv :=
    theorem_4_15_nonperiodicCandidate_signed_integrand_deriv_abs_le hx
  nlinarith [Real.rpow_nonneg (show 0 ≤ 1 + x by linarith) (-(9 : ℝ) / 5),
    Real.rpow_nonneg (show 0 ≤ 1 + x by linarith) (-(2 : ℝ) / 5)]

/- The signed correction is globally Lipschitz on the nonnegative half-line.
   This is stated directly in the scalar form used on each generated mesh
   cell, keeping the later Riemann estimate independent of algorithmic
   quantities. -/
theorem theorem_4_15_nonperiodicCandidate_signed_integrand_lipschitz
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |(1 + y) ^ (-(4 : ℝ) / 5) *
          Real.cos (2 * theorem_4_15_nonperiodicCandidatePhase y) -
        (1 + x) ^ (-(4 : ℝ) / 5) *
          Real.cos (2 * theorem_4_15_nonperiodicCandidatePhase x)| ≤
      (28 : ℝ) / 5 * |y - x| := by
  let f : ℝ → ℝ := fun z =>
    (1 + z) ^ (-(4 : ℝ) / 5) *
      Real.cos (2 * theorem_4_15_nonperiodicCandidatePhase z)
  let f' : ℝ → ℝ := fun z =>
    (-(4 : ℝ) / 5) * (1 + z) ^ (-(9 : ℝ) / 5) *
        Real.cos (2 * theorem_4_15_nonperiodicCandidatePhase z) -
      (24 : ℝ) / 5 * (1 + z) ^ (-(2 : ℝ) / 5) *
        Real.sin (2 * theorem_4_15_nonperiodicCandidatePhase z)
  have hderiv : ∀ z ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt f (f' z) (Set.Ici (0 : ℝ)) z := by
    intro z hz
    have hz0 : 0 ≤ z := hz
    exact (theorem_4_15_nonperiodicCandidate_signed_integrand_hasDerivAt
      (show -1 < z by linarith)).hasDerivWithinAt
  have hbound : ∀ z ∈ Set.Ici (0 : ℝ), ‖f' z‖ ≤ (28 : ℝ) / 5 := by
    intro z hz
    rw [Real.norm_eq_abs]
    exact theorem_4_15_nonperiodicCandidate_signed_integrand_deriv_abs_le_uniform hz
  have hlip := (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound hx hy
  simpa [f, Real.norm_eq_abs] using hlip

/- A quantitative left-mesh comparison for the exact signed correction.  The
   error is `O(N*h^2)` and therefore `O(epsilon)` at the printed selected
   horizon.  The estimate is deliberately one-sided, which is all the later
   lower-bound argument needs. -/
theorem theorem_4_15_nonperiodicCandidate_signed_left_mesh_lower
    (h : ℝ) (N : ℕ) (hh : 0 ≤ h) :
    (-(28 : ℝ) / 5) * (N : ℝ) * h ^ 2 +
        (∫ x in 0..(N : ℝ) * h,
          (1 + x) ^ (-(4 : ℝ) / 5) *
            Real.cos (2 * theorem_4_15_nonperiodicCandidatePhase x)) ≤
      h * (∑ t ∈ Finset.range N,
        (1 + (t : ℝ) * h) ^ (-(4 : ℝ) / 5) *
          Real.cos (2 * theorem_4_15_nonperiodicCandidatePhase
            ((t : ℝ) * h))) := by
  let f : ℝ → ℝ := fun x =>
    (1 + x) ^ (-(4 : ℝ) / 5) *
      Real.cos (2 * theorem_4_15_nonperiodicCandidatePhase x)
  let a : ℕ → ℝ := fun t => (t : ℝ) * h
  have hfint : ∀ t < N, IntervalIntegrable f volume (a t) (a (t + 1)) := by
    intro t _ht
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hat : 0 ≤ a t := by
      dsimp [a]
      positivity
    have hx0 : 0 ≤ x := by
      rw [Set.uIcc_of_le] at hx
      · exact hat.trans hx.1
      · dsimp [a]
        exact mul_le_mul_of_nonneg_right (by
          exact_mod_cast Nat.le_succ t) hh
    exact (theorem_4_15_nonperiodicCandidate_signed_integrand_hasDerivAt
      (show -1 < x by linarith)).continuousAt.continuousWithinAt
  have hcell : ∀ t < N,
      (∫ x in a t..a (t + 1), f x) ≤
        h * f (a t) + (28 : ℝ) / 5 * h ^ 2 := by
    intro t ht
    have hab : a t ≤ a (t + 1) := by
      dsimp [a]
      exact mul_le_mul_of_nonneg_right (by
        exact_mod_cast Nat.le_succ t) hh
    have hconst : IntervalIntegrable
        (fun _x : ℝ => f (a t) + (28 : ℝ) / 5 * h) volume
        (a t) (a (t + 1)) := intervalIntegrable_const
    have hpoint : ∀ x ∈ Set.Icc (a t) (a (t + 1)),
        f x ≤ f (a t) + (28 : ℝ) / 5 * h := by
      intro x hx
      have hat : 0 ≤ a t := by
        dsimp [a]
        positivity
      have hx0 : 0 ≤ x := hat.trans hx.1
      have hlip := theorem_4_15_nonperiodicCandidate_signed_integrand_lipschitz
        hat hx0
      have hdist : |x - a t| ≤ h := by
        rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
        have hwidth : a (t + 1) - a t = h := by
          dsimp [a]
          push_cast
          ring
        linarith [hx.2]
      have hscaled := mul_le_mul_of_nonneg_left hdist
        (show (0 : ℝ) ≤ 28 / 5 by norm_num)
      have hdiff : f x - f (a t) ≤ (28 : ℝ) / 5 * |x - a t| :=
        (le_abs_self (f x - f (a t))).trans (by simpa [f] using hlip)
      linarith
    have hmono := intervalIntegral.integral_mono_on hab (hfint t ht) hconst hpoint
    calc
      (∫ x in a t..a (t + 1), f x) ≤
          ∫ _x in a t..a (t + 1),
            (f (a t) + (28 : ℝ) / 5 * h) := hmono
      _ = h * f (a t) + (28 : ℝ) / 5 * h ^ 2 := by
        have hwidth : a (t + 1) - a t = h := by
          dsimp [a]
          push_cast
          ring
        simp [hwidth]
        ring
  have hsum := Finset.sum_le_sum fun t ht =>
    hcell t (Finset.mem_range.mp ht)
  have hjoin := intervalIntegral.sum_integral_adjacent_intervals
    (f := f) (a := a) hfint
  rw [hjoin] at hsum
  have ha0 : a 0 = 0 := by simp [a]
  have haN : a N = (N : ℝ) * h := by rfl
  rw [ha0, haN] at hsum
  have hsum_rhs :
      (∑ t ∈ Finset.range N,
          (h * f (a t) + (28 : ℝ) / 5 * h ^ 2)) =
        h * (∑ t ∈ Finset.range N, f (a t)) +
          (28 : ℝ) / 5 * (N : ℝ) * h ^ 2 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
    ring
  rw [hsum_rhs] at hsum
  dsimp [f, a] at hsum ⊢
  linarith

/- At the printed mesh and selected horizon, the preceding discretization
   error is linear in `epsilon/sigma`.  Together with the uniform continuous
   cancellation bound this gives the first direct lower bound on the exact
   finite signed sum used by the generated-gradient reduction. -/
theorem theorem_4_15_nonperiodicCandidate_selected_signed_mesh_lower
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_le_sigma :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma) :
    let sigma := theorem_4_15_nonperiodicCandidateSigma
    let h := epsilon ^ 2 / sigma ^ 2
    let N := theorem_4_15_nonperiodicCandidateHorizon epsilon
    (-(5 : ℝ) / 12 - (56 : ℝ) / 5 * epsilon / sigma) ≤
      h * (∑ t ∈ Finset.range N,
        (1 + (t : ℝ) * h) ^ (-(4 : ℝ) / 5) *
          Real.cos (2 * theorem_4_15_nonperiodicCandidatePhase
            ((t : ℝ) * h))) := by
  let sigma := theorem_4_15_nonperiodicCandidateSigma
  let h := epsilon ^ 2 / sigma ^ 2
  let N := theorem_4_15_nonperiodicCandidateHorizon epsilon
  have hsigma : 0 < sigma := by
    simpa [sigma] using theorem_4_15_nonperiodicCandidateSigma_pos
  have hh : 0 < h := by
    dsimp [h]
    positivity
  have hscale := theorem_4_15_nonperiodicCandidateHorizon_scale
    epsilon hepsilon hepsilon_le_sigma
  have hrate :
      theorem_4_15_otherwiseComplexityRate 1 1 sigma epsilon =
        (sigma / epsilon) ^ 3 := by
    dsimp [theorem_4_15_otherwiseComplexityRate, matrixRankBound]
    norm_num
    field_simp [ne_of_gt hepsilon]
  have hNupper : (N : ℝ) ≤ 2 * (sigma / epsilon) ^ 3 := by
    have hraw := hscale.2.2.2.2
    rw [show theorem_4_15_otherwiseComplexityRate 1 1
        theorem_4_15_nonperiodicCandidateSigma epsilon =
          (sigma / epsilon) ^ 3 by simpa [sigma] using hrate] at hraw
    simpa [N] using hraw
  have herr :
      (28 : ℝ) / 5 * (N : ℝ) * h ^ 2 ≤
        (56 : ℝ) / 5 * epsilon / sigma := by
    have hmul := mul_le_mul_of_nonneg_right hNupper
      (show 0 ≤ (28 : ℝ) / 5 * h ^ 2 by positivity)
    calc
      (28 : ℝ) / 5 * (N : ℝ) * h ^ 2 =
          (N : ℝ) * ((28 : ℝ) / 5 * h ^ 2) := by ring
      _ ≤ 2 * (sigma / epsilon) ^ 3 *
          ((28 : ℝ) / 5 * h ^ 2) := hmul
      _ = (56 : ℝ) / 5 * epsilon / sigma := by
        dsimp [h]
        field_simp [ne_of_gt hepsilon, ne_of_gt hsigma]
        <;> ring
  have hmesh := theorem_4_15_nonperiodicCandidate_signed_left_mesh_lower
    h N hh.le
  have hintAbs :=
    theorem_4_15_nonperiodicCandidate_signed_integral_abs_le
      ((N : ℝ) * h) (mul_nonneg (by positivity) hh.le)
  have hintLower :
      -(5 : ℝ) / 12 ≤
        ∫ x in 0..(N : ℝ) * h,
          (1 + x) ^ (-(4 : ℝ) / 5) *
            Real.cos (2 * theorem_4_15_nonperiodicCandidatePhase x) := by
    have hneg := neg_abs_le
      (∫ x in 0..(N : ℝ) * h,
        (1 + x) ^ (-(4 : ℝ) / 5) *
          Real.cos (2 * theorem_4_15_nonperiodicCandidatePhase x))
    linarith
  dsimp [sigma, h, N] at hmesh hintLower herr ⊢
  linarith

/- The mesh cancellation and the nonoscillatory mass estimate now combine on
   the exact selected grid.  This lower bound is the finite-sum milestone: its
   positive term has scale `(sigma/epsilon)^(1/5)`, whereas both displayed
   losses are bounded or vanish as `epsilon` decreases. -/
theorem theorem_4_15_nonperiodicCandidate_selected_leading_scaled_lower
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_le_sigma :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma) :
    let sigma := theorem_4_15_nonperiodicCandidateSigma
    let h := epsilon ^ 2 / sigma ^ 2
    let N := theorem_4_15_nonperiodicCandidateHorizon epsilon
    (6 : ℝ) / 5 *
        ((sigma / epsilon) *
            (1 + 2 * sigma / epsilon) ^ (-(4 : ℝ) / 5) -
          (5 : ℝ) / 12 - (56 : ℝ) / 5 * epsilon / sigma) ≤
      h * (∑ t ∈ Finset.range N,
        |theorem_4_15_nonperiodicCandidateGradientLeading
          ((t : ℝ) * h)|) := by
  let sigma := theorem_4_15_nonperiodicCandidateSigma
  let h := epsilon ^ 2 / sigma ^ 2
  let N := theorem_4_15_nonperiodicCandidateHorizon epsilon
  let p : ℝ := (1 + 2 * sigma / epsilon) ^ (-(4 : ℝ) / 5)
  let mass : ℝ := ∑ t ∈ Finset.range N,
    (1 + (t : ℝ) * h) ^ (-(4 : ℝ) / 5)
  let signed : ℝ := ∑ t ∈ Finset.range N,
    (1 + (t : ℝ) * h) ^ (-(4 : ℝ) / 5) *
      Real.cos (2 * theorem_4_15_nonperiodicCandidatePhase ((t : ℝ) * h))
  let leading : ℝ := ∑ t ∈ Finset.range N,
    |theorem_4_15_nonperiodicCandidateGradientLeading ((t : ℝ) * h)|
  have hsigma : 0 < sigma := by
    simpa [sigma] using theorem_4_15_nonperiodicCandidateSigma_pos
  have hh : 0 < h := by
    dsimp [h]
    positivity
  have hscale := theorem_4_15_nonperiodicCandidateHorizon_scale
    epsilon hepsilon hepsilon_le_sigma
  have hN : 0 < N := by simpa [N] using hscale.1
  have hrate :
      theorem_4_15_otherwiseComplexityRate 1 1 sigma epsilon =
        (sigma / epsilon) ^ 3 := by
    dsimp [theorem_4_15_otherwiseComplexityRate, matrixRankBound]
    norm_num
    field_simp [ne_of_gt hepsilon]
  have hNlower : (sigma / epsilon) ^ 3 ≤ (N : ℝ) := by
    have hraw := hscale.2.2.2.1
    rw [show theorem_4_15_otherwiseComplexityRate 1 1
        theorem_4_15_nonperiodicCandidateSigma epsilon =
          (sigma / epsilon) ^ 3 by simpa [sigma] using hrate] at hraw
    simpa [N] using hraw
  have hNhLower : sigma / epsilon ≤ (N : ℝ) * h := by
    have hmul := mul_le_mul_of_nonneg_right hNlower hh.le
    calc
      sigma / epsilon = (sigma / epsilon) ^ 3 * h := by
        dsimp [h]
        field_simp [ne_of_gt hepsilon, ne_of_gt hsigma]
      _ ≤ (N : ℝ) * h := hmul
  have hp : 0 ≤ p := by
    dsimp [p]
    positivity
  have hmassAvg := theorem_4_15_nonperiodicCandidate_selected_power_mass_lower
    epsilon hepsilon hepsilon_le_sigma
  have hmassN : (N : ℝ) * p ≤ mass := by
    have hmul := mul_le_mul_of_nonneg_left hmassAvg (show 0 ≤ (N : ℝ) by positivity)
    have hNne : (N : ℝ) ≠ 0 := by positivity
    simpa [sigma, h, N, p, mass, hNne, mul_assoc] using hmul
  have hmass : (sigma / epsilon) * p ≤ h * mass := by
    calc
      (sigma / epsilon) * p ≤ ((N : ℝ) * h) * p :=
        mul_le_mul_of_nonneg_right hNhLower hp
      _ = h * ((N : ℝ) * p) := by ring
      _ ≤ h * mass := mul_le_mul_of_nonneg_left hmassN hh.le
  have hsigned := theorem_4_15_nonperiodicCandidate_selected_signed_mesh_lower
    epsilon hepsilon hepsilon_le_sigma
  have hleading := theorem_4_15_nonperiodicCandidate_leading_sum_lower_by_signed_mass
    h N hh.le
  have hleadingScaled := mul_le_mul_of_nonneg_left hleading hh.le
  dsimp [sigma, h, N, p, mass, signed, leading] at hmass hsigned hleadingScaled
  dsimp [sigma, h, N, p, mass, signed, leading]
  nlinarith

/- The existing pointwise gradient reduction loses only a bounded amount
   after multiplying by the selected mesh width.  Thus the actual positive
   profile derivative, not merely its leading oscillatory term, inherits the
   growing finite-sum lower bound. -/
theorem theorem_4_15_nonperiodicCandidate_selected_gradient_scaled_lower
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_le_sigma :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma) :
    let sigma := theorem_4_15_nonperiodicCandidateSigma
    let h := epsilon ^ 2 / sigma ^ 2
    let N := theorem_4_15_nonperiodicCandidateHorizon epsilon
    (6 : ℝ) / 5 *
        ((sigma / epsilon) *
            (1 + 2 * sigma / epsilon) ^ (-(4 : ℝ) / 5) -
          (5 : ℝ) / 12 - (56 : ℝ) / 5 * epsilon / sigma) -
        (396 : ℝ) / 5 ≤
      h * (∑ t ∈ Finset.range N,
        |theorem_4_15_nonperiodicCandidatePositiveProfileFirst
          ((t : ℝ) * h)|) := by
  let sigma := theorem_4_15_nonperiodicCandidateSigma
  let h := epsilon ^ 2 / sigma ^ 2
  let N := theorem_4_15_nonperiodicCandidateHorizon epsilon
  let leading : ℝ := ∑ t ∈ Finset.range N,
    |theorem_4_15_nonperiodicCandidateGradientLeading ((t : ℝ) * h)|
  let gradient : ℝ := ∑ t ∈ Finset.range N,
    |theorem_4_15_nonperiodicCandidatePositiveProfileFirst ((t : ℝ) * h)|
  have hsigma : 0 < sigma := by
    simpa [sigma] using theorem_4_15_nonperiodicCandidateSigma_pos
  have hh : 0 < h := by
    dsimp [h]
    positivity
  have hscale := theorem_4_15_nonperiodicCandidateHorizon_scale
    epsilon hepsilon hepsilon_le_sigma
  have hN : 0 < N := by simpa [N] using hscale.1
  have hrate :
      theorem_4_15_otherwiseComplexityRate 1 1 sigma epsilon =
        (sigma / epsilon) ^ 3 := by
    dsimp [theorem_4_15_otherwiseComplexityRate, matrixRankBound]
    norm_num
    field_simp [ne_of_gt hepsilon]
  have hNupper : (N : ℝ) ≤ 2 * (sigma / epsilon) ^ 3 := by
    have hraw := hscale.2.2.2.2
    rw [show theorem_4_15_otherwiseComplexityRate 1 1
        theorem_4_15_nonperiodicCandidateSigma epsilon =
          (sigma / epsilon) ^ 3 by simpa [sigma] using hrate] at hraw
    simpa [N] using hraw
  have hNhUpper : (N : ℝ) * h ≤ 2 * sigma / epsilon := by
    have hmul := mul_le_mul_of_nonneg_right hNupper hh.le
    calc
      (N : ℝ) * h ≤ 2 * (sigma / epsilon) ^ 3 * h := hmul
      _ = 2 * sigma / epsilon := by
        dsimp [h]
        field_simp [ne_of_gt hepsilon, ne_of_gt hsigma]
  have hremainder :
      ((N : ℝ) * h) * ((198 : ℝ) / 5 * epsilon / sigma) ≤
        (396 : ℝ) / 5 := by
    have hmul := mul_le_mul_of_nonneg_right hNhUpper
      (show 0 ≤ (198 : ℝ) / 5 * epsilon / sigma by positivity)
    calc
      ((N : ℝ) * h) * ((198 : ℝ) / 5 * epsilon / sigma) ≤
          (2 * sigma / epsilon) * ((198 : ℝ) / 5 * epsilon / sigma) := hmul
      _ = (396 : ℝ) / 5 := by
        field_simp [ne_of_gt hepsilon, ne_of_gt hsigma]
        <;> ring
  have hreduction :=
    theorem_4_15_nonperiodicCandidate_selected_gradient_average_reduction
      epsilon hepsilon hepsilon_le_sigma
  have hreductionScaled := mul_le_mul_of_nonneg_left hreduction
    (show 0 ≤ (N : ℝ) * h by positivity)
  have hNne : (N : ℝ) ≠ 0 := by positivity
  have hscaled :
      h * leading - ((N : ℝ) * h) *
          ((198 : ℝ) / 5 * epsilon / sigma) ≤ h * gradient := by
    calc
      h * leading - ((N : ℝ) * h) *
            ((198 : ℝ) / 5 * epsilon / sigma) =
          ((N : ℝ) * h) *
            ((N : ℝ)⁻¹ * leading -
              (198 : ℝ) / 5 * epsilon / sigma) := by
        field_simp [hNne]
        <;> ring
      _ ≤ ((N : ℝ) * h) *
          ((N : ℝ)⁻¹ * gradient) := by
        simpa [sigma, h, N, leading, gradient] using hreductionScaled
      _ = h * gradient := by
        field_simp [hNne]
        <;> ring
  have hleading :=
    theorem_4_15_nonperiodicCandidate_selected_leading_scaled_lower
      epsilon hepsilon hepsilon_le_sigma
  dsimp [sigma, h, N, leading, gradient] at hscaled hleading hremainder
  dsimp [sigma, h, N, leading, gradient]
  linarith

/- Consequently every field of the original generated source-small-J run is
   checked for this fixed problem and printed schedule except the actual
   directional-curvature inequality.  The remaining premise below is exactly
   that source object after singleton-oracle transfer. -/
theorem theorem_4_15_nonperiodicCandidate_selected_source_run_of_directional_bound
    (epsilon C : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_le_sigma :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma)
    (hC : 0 < C)
    (hdirectional :
      deterministicMomentumHessianDirectionalAverage
          theorem_4_15_nonperiodicCandidateObjective
          (theorem_4_15_nonperiodicCandidateConfig epsilon hepsilon
            hepsilon_le_sigma)
          (theorem_4_15_nonperiodicCandidateHorizon epsilon) ≤
        C * epsilon) :
    theorem_4_15_otherwiseSourceSmallJGeneratedRunForAccuracyHorizon
      theorem_4_15_nonperiodicCandidateProblem
      (fun _accuracy _horizon => deterministicOracleConfig
        (theorem_4_15_nonperiodicCandidateConfig epsilon hepsilon
          hepsilon_le_sigma))
      0 theorem_4_15_nonperiodicCandidateSigma
      theorem_4_15_nonperiodicCandidateSigma epsilon C
      theorem_4_15_nonperiodicCandidateThirdDerivativeScale
      1 1 1 1 1 2
      (theorem_4_15_nonperiodicCandidateHorizon epsilon) := by
  let cfg := theorem_4_15_nonperiodicCandidateConfig epsilon hepsilon
    hepsilon_le_sigma
  let scfg := deterministicOracleConfig cfg
  let N := theorem_4_15_nonperiodicCandidateHorizon epsilon
  let hwd := theorem_4_15_nonperiodicCandidateProblem_expectationsWellDefined cfg N
  have hregDom : theorem_4_15_branchRegimeThresholdDomain 1 1
      theorem_4_15_nonperiodicCandidateSigma
      theorem_4_15_nonperiodicCandidateSigma := by
    simp [theorem_4_15_branchRegimeThresholdDomain, sourceInvDomain,
      ne_of_gt theorem_4_15_nonperiodicCandidateSigma_pos]
  have hscale := theorem_4_15_nonperiodicCandidateHorizon_scale
    epsilon hepsilon hepsilon_le_sigma
  refine ⟨hscale.1,
    theorem_4_15_nonperiodicCandidateProblem_hasFiniteInfimum,
    theorem_4_15_nonperiodicCandidateProblem_sourceInitialGap,
    theorem_4_15_nonperiodicCandidateProblem_thirdDerivativeBounded,
    theorem_4_15_nonperiodicCandidateProblem_boundedVariance, hwd, ?_, ?_, ?_,
    hscale.2, hregDom, ?_⟩
  · rfl
  · simpa [scfg, cfg, N] using
      theorem_4_15_nonperiodicCandidateConfig_schedule epsilon hepsilon
        hepsilon_le_sigma
  · simpa [scfg, cfg, N] using
      theorem_4_15_nonperiodicCandidateConfig_sourceDomain epsilon hepsilon
        hepsilon_le_sigma
  · refine ⟨hepsilon, hC, ?_⟩
    change stochasticHessianDirectionalAverageRealized
        (deterministicOracleProblem theorem_4_15_nonperiodicCandidateObjective)
        (deterministicOracleConfig cfg) N _ ≤ _
    rw [deterministicOracle_hessianDirectionalAverageRealized_eq]
    simpa [cfg, N,
      theorem_4_15_branchRegimeThreshold, matrixRankBound,
      realizedSourceSqrt, sourceSqrt, realizedSourceInv, sourceInv,
      ne_of_gt theorem_4_15_nonperiodicCandidateSigma_pos] using
      hdirectional

/- The selected shrinking run has two exact dynamical scales that are hidden by
   the source's separate `beta`, `eta`, and horizon displays.  The distance
   travelled during one momentum-memory time is `1 / sigma`, while the full
   selected horizon covers between `1 / epsilon` and `2 / epsilon` units of
   scalar step length.  Thus the remaining directional-curvature question is
   a genuinely many-window cancellation problem as accuracy tends to zero;
   it cannot be settled by the already proved first-leg prefix estimate. -/
theorem theorem_4_15_periodicCandidate_shrinking_selected_dynamical_scales
    (sigma epsilon : ℝ)
    (hsigma : 0 < sigma) (hepsilon : 0 < epsilon)
    (hepsilon_le_sigma : epsilon ≤ sigma) :
    let cfg := theorem_4_15_periodicCandidateShrinkingConfig
      sigma 1 epsilon hsigma hepsilon hepsilon_le_sigma
    let N := theorem_4_15_periodicCandidateShrinkingHorizon sigma epsilon
    cfg.eta 0 / (1 - cfg.beta) = sigma⁻¹ ∧
      epsilon⁻¹ ≤ (N : ℝ) * cfg.eta 0 ∧
      (N : ℝ) * cfg.eta 0 ≤ 2 * epsilon⁻¹ := by
  let cfg := theorem_4_15_periodicCandidateShrinkingConfig
    sigma 1 epsilon hsigma hepsilon hepsilon_le_sigma
  let N := theorem_4_15_periodicCandidateShrinkingHorizon sigma epsilon
  let rate := theorem_4_15_otherwiseComplexityRate 1 1 sigma epsilon
  have hscale := theorem_4_15_periodicCandidate_shrinkingHorizon_scale
    sigma epsilon hsigma hepsilon hepsilon_le_sigma
  have heta : 0 < cfg.eta 0 := by
    dsimp [cfg, theorem_4_15_periodicCandidateShrinkingConfig,
      theorem_4_15_otherwiseEtaRate, sourceQuot, matrixRankBound]
    positivity
  have hproduct : rate * cfg.eta 0 = epsilon⁻¹ := by
    have h := theorem_4_15_otherwise_horizon_eta_product
      1 1 sigma 1 epsilon 0 (ne_of_gt hsigma) (ne_of_gt hepsilon)
    simpa [rate, cfg, theorem_4_15_periodicCandidateShrinkingConfig,
      matrixRankBound] using h
  have hNlower : rate ≤ (N : ℝ) := by
    simpa [rate, N] using hscale.2.2.2.1
  have hNupper : (N : ℝ) ≤ 2 * rate := by
    simpa [rate, N] using hscale.2.2.2.2
  dsimp [cfg, N]
  constructor
  · dsimp [theorem_4_15_periodicCandidateShrinkingConfig,
      theorem_4_15_otherwiseEtaRate,
      theorem_4_15_otherwiseOneMinusBetaScale, sourceQuot, matrixRankBound]
    field_simp [ne_of_gt hsigma, ne_of_gt hepsilon]
    norm_num [matrixRankBound]
  · constructor
    · have hmul := mul_le_mul_of_nonneg_right hNlower heta.le
      simpa [hproduct] using hmul
    · have hmul := mul_le_mul_of_nonneg_right hNupper heta.le
      calc
        ((theorem_4_15_periodicCandidateShrinkingHorizon sigma epsilon : ℝ) *
              (theorem_4_15_periodicCandidateShrinkingConfig
                sigma 1 epsilon hsigma hepsilon hepsilon_le_sigma).eta 0)
            ≤ (2 * rate) * cfg.eta 0 := by
              simpa [N, cfg] using hmul
        _ = 2 * epsilon⁻¹ := by rw [mul_assoc, hproduct]

/- The same selected horizon contains a diverging number of momentum-memory
   windows.  More precisely, after measuring time in units of `1 - beta`, the
   horizon lies between `sigma / epsilon` and twice that quantity.  Together
   with the preceding constant displacement per memory window, this isolates
   the remaining counterexample question as a long-time cancellation problem
   for the exact shrinking-schedule dynamics, rather than a one-window or
   fixed-step resonance. -/
theorem theorem_4_15_periodicCandidate_shrinking_selected_memory_windows
    (sigma epsilon : ℝ)
    (hsigma : 0 < sigma) (hepsilon : 0 < epsilon)
    (hepsilon_le_sigma : epsilon ≤ sigma) :
    let cfg := theorem_4_15_periodicCandidateShrinkingConfig
      sigma 1 epsilon hsigma hepsilon hepsilon_le_sigma
    let N := theorem_4_15_periodicCandidateShrinkingHorizon sigma epsilon
    sigma / epsilon ≤ (N : ℝ) * (1 - cfg.beta) ∧
      (N : ℝ) * (1 - cfg.beta) ≤ 2 * (sigma / epsilon) := by
  let cfg := theorem_4_15_periodicCandidateShrinkingConfig
    sigma 1 epsilon hsigma hepsilon hepsilon_le_sigma
  let N := theorem_4_15_periodicCandidateShrinkingHorizon sigma epsilon
  let rate := theorem_4_15_otherwiseComplexityRate 1 1 sigma epsilon
  have hrank : (matrixRankBound 1 1 : ℝ) = 1 := by
    norm_num [matrixRankBound]
  have hscale := theorem_4_15_periodicCandidate_shrinkingHorizon_scale
    sigma epsilon hsigma hepsilon hepsilon_le_sigma
  have hrate_eq : rate = (sigma / epsilon) ^ 3 := by
    dsimp [rate, theorem_4_15_otherwiseComplexityRate]
    rw [hrank]
    norm_num
    field_simp [ne_of_gt hepsilon]
  have hNlower : rate ≤ (N : ℝ) := by
    simpa [rate, N] using hscale.2.2.2.1
  have hNupper : (N : ℝ) ≤ 2 * rate := by
    simpa [rate, N] using hscale.2.2.2.2
  have honeMinusNonneg : 0 ≤ 1 - cfg.beta := by
    exact sub_nonneg.mpr cfg.beta_mem.2.le
  have hproduct : rate * (1 - cfg.beta) = sigma / epsilon := by
    rw [hrate_eq]
    dsimp [cfg, theorem_4_15_periodicCandidateShrinkingConfig,
      theorem_4_15_otherwiseOneMinusBetaScale, sourceQuot]
    rw [hrank]
    field_simp [ne_of_gt hsigma, ne_of_gt hepsilon]
    ring
  dsimp [cfg, N]
  constructor
  · have hmul := mul_le_mul_of_nonneg_right hNlower honeMinusNonneg
    simpa [hproduct] using hmul
  · have hmul := mul_le_mul_of_nonneg_right hNupper honeMinusNonneg
    calc
      ((theorem_4_15_periodicCandidateShrinkingHorizon sigma epsilon : ℝ) *
          (1 - (theorem_4_15_periodicCandidateShrinkingConfig
            sigma 1 epsilon hsigma hepsilon hepsilon_le_sigma).beta)) ≤
          (2 * rate) * (1 - cfg.beta) := by
            simpa [N, cfg] using hmul
      _ = 2 * (sigma / epsilon) := by rw [mul_assoc, hproduct]

/- A generated candidate with a fixed positive lower floor on the realized
   directional curvature cannot remain in the printed small-`J` regime as
   accuracy tends to zero.  The conclusion is the exact source threshold
   with its inverse-gap denominator cleared.  In particular, this rules out
   positive-curvature quadratic candidates for an asymptotic counterexample;
   a viable candidate must instead make the directional average vanish or use
   signed curvature cancellation.  This is only a candidate-screening fact,
   not a proof of the missing generated-average implication. -/
theorem theorem_4_15_otherwise_source_small_j_directional_floor_forces_accuracy_floor
    {xi : Type*} [MeasurableSpace xi] {m n : ℕ}
    (P : StochasticProblem xi m n)
    (cfgForAccuracyHorizon : ℝ → ℕ → StochasticMuonConfig m n)
    (W0 : Mat m n) (sigma Delta epsilon C s Jfloor : ℝ)
    (betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ)
    (N : ℕ)
    (hN : theorem_4_15_otherwiseSourceSmallJGeneratedRunForAccuracyHorizon P
      cfgForAccuracyHorizon W0 sigma Delta epsilon C s
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N)
    (hwdDir : stochasticHessianDirectionalAverageWellDefined P
      (cfgForAccuracyHorizon epsilon N) N)
    (hfloor : Jfloor ≤ stochasticHessianDirectionalAverageRealized P
      (cfgForAccuracyHorizon epsilon N) N hwdDir) :
    (Jfloor * Delta) /
        (C * Real.sqrt (matrixRankBound m n : ℝ) * sigma) ≤ epsilon := by
  rcases hN with
    ⟨_horizon, hfinite, hDelta, _hthird, hvariance, hwd, _hW0, hschedule,
      _hsource, _hHorizon, hregDom, hregime⟩
  rcases hschedule with
    ⟨hscheduleDom, _hbatch, _hbeta, _heta, _hconstEta⟩
  rcases hscheduleDom with
    ⟨_horizon', hnoiseDom, _hrankDom, _hetaDom⟩
  have hnoise_ne :
      (matrixRankBound m n : ℝ) * sigma ^ 2 ≠ 0 := by
    simpa [sourceQuotDomain] using hnoiseDom
  have hrank_ne : (matrixRankBound m n : ℝ) ≠ 0 := by
    intro hrank
    apply hnoise_ne
    simp [hrank]
  have hsigma_ne : sigma ≠ 0 := by
    intro hsigma
    apply hnoise_ne
    simp [hsigma]
  have hrank_pos : 0 < (matrixRankBound m n : ℝ) :=
    lt_of_le_of_ne (by positivity) (Ne.symm hrank_ne)
  have hsigma_pos : 0 < sigma :=
    lt_of_le_of_ne hvariance.nonneg (Ne.symm hsigma_ne)
  have hdenominator_pos :
      0 < C * Real.sqrt (matrixRankBound m n : ℝ) * sigma := by
    exact mul_pos (mul_pos hregime.2.1 (Real.sqrt_pos.2 hrank_pos)) hsigma_pos
  have hDelta_nonneg : 0 ≤ Delta := by
    rw [← hDelta]
    unfold sourceObjectiveInitialGap Objective.sourceFStar
    linarith [objective_value_ge_fStar_early P.objective hfinite W0]
  have hDelta_ne : Delta ≠ 0 := by
    simpa [theorem_4_15_branchRegimeThresholdDomain, sourceInvDomain] using hregDom
  have hbound :
      Jfloor ≤ C * theorem_4_15_branchRegimeThreshold
        m n sigma Delta epsilon hregDom := by
    have hfloor' :
        Jfloor ≤ stochasticHessianDirectionalAverageRealized P
          (cfgForAccuracyHorizon epsilon N) N hwd.2.2.1 := by
      simpa only using hfloor
    exact hfloor'.trans hregime.2.2
  dsimp [theorem_4_15_branchRegimeThreshold, realizedSourceSqrt,
    realizedSourceInv, sourceSqrt, sourceInv] at hbound
  have hscaled := mul_le_mul_of_nonneg_right hbound hDelta_nonneg
  have hproduct :
    Jfloor * Delta ≤
      C * Real.sqrt (matrixRankBound m n : ℝ) * sigma * epsilon := by
    calc
      Jfloor * Delta ≤
          (C * (Real.sqrt (matrixRankBound m n : ℝ) * sigma * Delta⁻¹ * epsilon)) *
            Delta := hscaled
      _ = C * Real.sqrt (matrixRankBound m n : ℝ) * sigma * epsilon := by
        field_simp [hDelta_ne]
  apply (div_le_iff₀ hdenominator_pos).2
  calc
    Jfloor * Delta ≤
        C * Real.sqrt (matrixRankBound m n : ℝ) * sigma * epsilon := hproduct
    _ = epsilon * (C * Real.sqrt (matrixRankBound m n : ℝ) * sigma) := by ring

/- A fixed-period one-dimensional candidate would need a step size bounded
   below by a positive fraction of that period in order to revisit the same
   nonstationary phase.  The printed Appendix B.4 eta schedule rules out that
   mechanism asymptotically: after clearing the (nonzero) `sigma ^ 3`
   denominator, every source-small-`J` generated run satisfies the square
   accuracy constraint below.  Unlike the preceding curvature-floor lemma,
   this uses no property of either Hessian average, so it also applies to
   signed-cancellation candidates.  It is a candidate-screening fact only,
   not the missing average-gradient implication. -/
theorem theorem_4_15_otherwise_source_small_j_fixed_step_forces_square_accuracy_floor
    {xi : Type*} [MeasurableSpace xi] {m n : ℕ}
    (P : StochasticProblem xi m n)
    (cfgForAccuracyHorizon : ℝ → ℕ → StochasticMuonConfig m n)
    (W0 : Mat m n) (sigma Delta epsilon C s etaFloor : ℝ)
    (betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ)
    (N : ℕ)
    (hN : theorem_4_15_otherwiseSourceSmallJGeneratedRunForAccuracyHorizon P
      cfgForAccuracyHorizon W0 sigma Delta epsilon C s
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N)
    (hfloor : etaFloor ≤ (cfgForAccuracyHorizon epsilon N).eta 0) :
    etaFloor * sigma ^ 3 ≤
      etaUpper * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) *
        Delta * epsilon ^ 2 := by
  rcases hN with
    ⟨_horizon, _hfinite, _hDelta, _hthird, hvariance, _hwd, _hW0, hschedule,
      _hsource, _hHorizon, _hregDom, _hregime⟩
  rcases hschedule with
    ⟨hscheduleDom, _hbatch, _hbeta, heta, _hconstEta⟩
  rcases hscheduleDom with ⟨_horizon', _hbetaDom, _hrankDom, hetaDom⟩
  rcases heta with
    ⟨_hetaLowerPos, _hetaOrder, _hetaLowerBound, hetaUpperBound⟩
  have hsigma_ne : sigma ≠ 0 := by
    simpa [sourceQuotDomain] using hetaDom
  have hsigma_pos : 0 < sigma :=
    lt_of_le_of_ne hvariance.nonneg (Ne.symm hsigma_ne)
  have hstep :
      etaFloor ≤ etaUpper * theorem_4_15_otherwiseEtaRate
        m n sigma Delta epsilon N :=
    hfloor.trans hetaUpperBound
  have hscaled := mul_le_mul_of_nonneg_right hstep (show 0 ≤ sigma ^ 3 by positivity)
  calc
    etaFloor * sigma ^ 3 ≤
        (etaUpper * theorem_4_15_otherwiseEtaRate
          m n sigma Delta epsilon N) * sigma ^ 3 := hscaled
    _ = etaUpper * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) *
          Delta * epsilon ^ 2 := by
      unfold theorem_4_15_otherwiseEtaRate sourceQuot
      field_simp [hsigma_ne]

/- The printed shrinking schedule does not make the displacement accumulated
   over one momentum-memory scale vanish.  Indeed, `eta` and `1 - beta` both
   carry the same `epsilon ^ 2` factor, and their ratio is uniformly comparable
   to the accuracy-independent scale
   `r * sqrt (r ^ 3) * Delta / sigma`.  The cross-multiplied inequalities below
   avoid introducing a new quotient by `1 - beta`; all positivity and
   definedness facts are extracted from the same source-small-`J` generated
   run.  This is schedule geometry for the shrinking-step counterexample
   program, not a stationarity or curvature conclusion. -/
theorem theorem_4_15_otherwise_source_small_j_memory_displacement_scale
    {xi : Type*} [MeasurableSpace xi] {m n : ℕ}
    (P : StochasticProblem xi m n)
    (cfgForAccuracyHorizon : ℝ → ℕ → StochasticMuonConfig m n)
    (W0 : Mat m n) (sigma Delta epsilon C s : ℝ)
    (betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ)
    (N : ℕ)
    (hN : theorem_4_15_otherwiseSourceSmallJGeneratedRunForAccuracyHorizon P
      cfgForAccuracyHorizon W0 sigma Delta epsilon C s
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N) :
    let cfgN := cfgForAccuracyHorizon epsilon N
    let memoryDisplacementScale := sourceQuot
      ((matrixRankBound m n : ℝ) *
        Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Delta) sigma
    etaLower * memoryDisplacementScale * (1 - cfgN.beta) ≤
        betaUpper * cfgN.eta 0 ∧
      betaLower * cfgN.eta 0 ≤
        etaUpper * memoryDisplacementScale * (1 - cfgN.beta) := by
  dsimp only
  rcases hN with
    ⟨_horizon, hfinite, hDelta, _hthird, hvariance, _hwd, _hW0, hschedule,
      _hsource, _hHorizon, hregDom, _hregime⟩
  rcases hschedule with
    ⟨hscheduleDom, _hbatch, hbeta, heta, _hconstantEta⟩
  rcases hscheduleDom with
    ⟨_horizon', hbetaDom, _hrankDom, hetaDom⟩
  have hsigma_ne : sigma ≠ 0 := by
    simpa [sourceQuotDomain] using hetaDom
  have hsigma_pos : 0 < sigma :=
    lt_of_le_of_ne hvariance.nonneg (Ne.symm hsigma_ne)
  have hrank_ne : (matrixRankBound m n : ℝ) ≠ 0 := by
    have hdenom : (matrixRankBound m n : ℝ) * sigma ^ 2 ≠ 0 := by
      simpa [sourceQuotDomain] using hbetaDom
    intro hrank
    apply hdenom
    simp [hrank]
  have hrank_pos : 0 < (matrixRankBound m n : ℝ) :=
    lt_of_le_of_ne (by positivity) (Ne.symm hrank_ne)
  have hDelta_nonneg : 0 ≤ Delta := by
    rw [← hDelta]
    unfold sourceObjectiveInitialGap Objective.sourceFStar
    linarith [objective_value_ge_fStar_early P.objective hfinite W0]
  have hDelta_ne : Delta ≠ 0 := by
    simpa [theorem_4_15_branchRegimeThresholdDomain, sourceInvDomain] using hregDom
  have hDelta_pos : 0 < Delta :=
    lt_of_le_of_ne hDelta_nonneg (Ne.symm hDelta_ne)
  let scale := sourceQuot
    ((matrixRankBound m n : ℝ) *
      Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Delta) sigma
  have hscale_pos : 0 < scale := by
    dsimp [scale, sourceQuot]
    positivity
  have hscale_identity :
      theorem_4_15_otherwiseEtaRate m n sigma Delta epsilon N =
        theorem_4_15_otherwiseOneMinusBetaScale m n sigma epsilon * scale := by
    dsimp [theorem_4_15_otherwiseEtaRate,
      theorem_4_15_otherwiseOneMinusBetaScale, scale, sourceQuot]
    field_simp [hsigma_ne, hrank_ne]
  have hbetaLowerPos : 0 < betaLower := hbeta.1
  have hbetaUpperPos : 0 < betaUpper := lt_of_lt_of_le hbeta.1 hbeta.2.1
  have hetaLowerPos : 0 < etaLower := heta.1
  have hetaUpperPos : 0 < etaUpper := lt_of_lt_of_le heta.1 heta.2.1
  have hbetaLower := hbeta.2.2.1
  have hbetaUpper := hbeta.2.2.2
  have hetaLowerBound := heta.2.2.1
  have hetaUpperBound := heta.2.2.2
  rw [hscale_identity] at hetaLowerBound hetaUpperBound
  change
    etaLower * scale *
        (1 - (cfgForAccuracyHorizon epsilon N).beta) ≤
          betaUpper * (cfgForAccuracyHorizon epsilon N).eta 0 ∧
      betaLower * (cfgForAccuracyHorizon epsilon N).eta 0 ≤
        etaUpper * scale *
          (1 - (cfgForAccuracyHorizon epsilon N).beta)
  constructor
  · have hscaledBeta := mul_le_mul_of_nonneg_left hbetaUpper
      (mul_nonneg hetaLowerPos.le hscale_pos.le)
    have hscaledEta := mul_le_mul_of_nonneg_left hetaLowerBound
      hbetaUpperPos.le
    calc
      etaLower * scale * (1 - (cfgForAccuracyHorizon epsilon N).beta) ≤
          etaLower * scale *
            (betaUpper * theorem_4_15_otherwiseOneMinusBetaScale
              m n sigma epsilon) := hscaledBeta
      _ = betaUpper *
          (etaLower *
            (theorem_4_15_otherwiseOneMinusBetaScale m n sigma epsilon *
              scale)) := by ring
      _ ≤ betaUpper * (cfgForAccuracyHorizon epsilon N).eta 0 := hscaledEta
  · have hscaledEta := mul_le_mul_of_nonneg_left hetaUpperBound
      hbetaLowerPos.le
    have hscaledBeta := mul_le_mul_of_nonneg_left hbetaLower
      (mul_nonneg hetaUpperPos.le hscale_pos.le)
    calc
      betaLower * (cfgForAccuracyHorizon epsilon N).eta 0 ≤
          betaLower *
            (etaUpper *
              (theorem_4_15_otherwiseOneMinusBetaScale m n sigma epsilon *
                scale)) := hscaledEta
      _ = etaUpper * scale *
          (betaLower * theorem_4_15_otherwiseOneMinusBetaScale
            m n sigma epsilon) := by ring
      _ ≤ etaUpper * scale *
          (1 - (cfgForAccuracyHorizon epsilon N).beta) := hscaledBeta

/- The preceding comparison is realized on an actual integer momentum window.
   Once the printed upper beta scale is below one quarter, choose
   `q = ceil (1 / (4 * (1 - beta)))`.  Then `q * (1 - beta)` lies between one
   quarter and one half, so the exact reversal recurrence still has positive
   momentum throughout that window.  Moreover, the generated displacement
   `q * eta` has a positive lower bound at the accuracy-independent scale from
   the preceding theorem.  This is still schedule geometry only: it does not
   assume that the reversed-gradient pattern is realized by an admissible
   objective and therefore does not claim a source counterexample. -/
theorem theorem_4_15_otherwise_source_small_j_natural_memory_window
    {xi : Type*} [MeasurableSpace xi] {m n : ℕ}
    (P : StochasticProblem xi m n)
    (cfgForAccuracyHorizon : ℝ → ℕ → StochasticMuonConfig m n)
    (W0 : Mat m n) (sigma Delta epsilon C s : ℝ)
    (betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ)
    (N : ℕ)
    (hN : theorem_4_15_otherwiseSourceSmallJGeneratedRunForAccuracyHorizon P
      cfgForAccuracyHorizon W0 sigma Delta epsilon C s
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N)
    (hsmall : betaUpper *
        theorem_4_15_otherwiseOneMinusBetaScale m n sigma epsilon < 1 / 4) :
    let cfgN := cfgForAccuracyHorizon epsilon N
    let delta := 1 - cfgN.beta
    let q := Nat.ceil (1 / (4 * delta))
    let memoryDisplacementScale := sourceQuot
      ((matrixRankBound m n : ℝ) *
        Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Delta) sigma
    1 / 4 ≤ (q : ℝ) * delta ∧
      (q : ℝ) * delta < 1 / 2 ∧
      1 / 2 < cfgN.beta ^ q ∧
      etaLower * memoryDisplacementScale / 4 ≤
        betaUpper * ((q : ℝ) * cfgN.eta 0) := by
  dsimp only
  let cfgN := cfgForAccuracyHorizon epsilon N
  let delta := 1 - cfgN.beta
  let scale := sourceQuot
    ((matrixRankBound m n : ℝ) *
      Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Delta) sigma
  let q := Nat.ceil (1 / (4 * delta))
  have hscale :=
    theorem_4_15_otherwise_source_small_j_memory_displacement_scale
      P cfgForAccuracyHorizon W0 sigma Delta epsilon C s
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N hN
  dsimp only at hscale
  have hfields := hN
  rcases hfields with
    ⟨_horizon, hfinite, hDelta, _hthird, hvariance, _hwd, _hW0,
      hschedule, _hsource, _hHorizon, _hregDom, _hregime⟩
  rcases hschedule with
    ⟨_hscheduleDom, _hbatch, hbeta, heta, _hconstantEta⟩
  have hdelta_pos : 0 < delta := by
    dsimp [delta, cfgN]
    exact sub_pos.mpr (cfgForAccuracyHorizon epsilon N).beta_mem.2
  have hdelta_upper : delta ≤ betaUpper *
      theorem_4_15_otherwiseOneMinusBetaScale m n sigma epsilon := by
    simpa [delta, cfgN] using hbeta.2.2.2
  have hdelta_small : delta < 1 / 4 := hdelta_upper.trans_lt hsmall
  have hceil_nonneg : 0 ≤ 1 / (4 * delta) := by positivity
  have hq_lower : 1 / (4 * delta) ≤ (q : ℝ) := by
    simpa [q] using Nat.le_ceil (1 / (4 * delta))
  have hq_upper : (q : ℝ) < 1 / (4 * delta) + 1 := by
    simpa [q] using Nat.ceil_lt_add_one hceil_nonneg
  have hwindow_lower : 1 / 4 ≤ (q : ℝ) * delta := by
    have hmul := mul_le_mul_of_nonneg_right hq_lower hdelta_pos.le
    calc
      1 / 4 = (1 / (4 * delta)) * delta := by
        field_simp [ne_of_gt hdelta_pos]
      _ ≤ (q : ℝ) * delta := hmul
  have hwindow_upper : (q : ℝ) * delta < 1 / 2 := by
    have hmul := mul_lt_mul_of_pos_right hq_upper hdelta_pos
    have hid : (1 / (4 * delta) + 1) * delta = 1 / 4 + delta := by
      field_simp [ne_of_gt hdelta_pos]
      <;> ring
    rw [hid] at hmul
    linarith
  have hpower : 1 / 2 < cfgN.beta ^ q := by
    have hbernoulli := one_add_mul_le_pow
      (a := cfgN.beta - 1) (n := q) (by linarith [cfgN.beta_mem.1])
    have hlower : (1 / 2 : ℝ) <
        1 + (q : ℝ) * (cfgN.beta - 1) := by
      dsimp [delta] at hwindow_upper
      linarith
    exact lt_of_lt_of_le hlower (by simpa using hbernoulli)
  have hetaLower_nonneg : 0 ≤ etaLower := heta.1.le
  have hDelta_nonneg : 0 ≤ Delta := by
    rw [← hDelta]
    unfold sourceObjectiveInitialGap Objective.sourceFStar
    linarith [objective_value_ge_fStar_early P.objective hfinite W0]
  have hscale_nonneg : 0 ≤ scale := by
    dsimp [scale, sourceQuot]
    exact div_nonneg (mul_nonneg
      (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) hDelta_nonneg)
      hvariance.nonneg
  have hlower_scaled := mul_le_mul_of_nonneg_left hwindow_lower
    (mul_nonneg hetaLower_nonneg hscale_nonneg)
  have hschedule_scaled := mul_le_mul_of_nonneg_left hscale.1
    (show 0 ≤ (q : ℝ) by positivity)
  refine ⟨hwindow_lower, hwindow_upper, hpower, ?_⟩
  calc
    etaLower * scale / 4 =
        etaLower * scale * (1 / 4) := by ring
    _ ≤ etaLower * scale * ((q : ℝ) * delta) := hlower_scaled
    _ = (q : ℝ) *
        (etaLower * scale *
          (1 - (cfgForAccuracyHorizon epsilon N).beta)) := by
      simp only [delta, cfgN]
      ring
    _ ≤ (q : ℝ) *
        (betaUpper * (cfgForAccuracyHorizon epsilon N).eta 0) :=
      hschedule_scaled
    _ = betaUpper *
        ((q : ℝ) * (cfgForAccuracyHorizon epsilon N).eta 0) := by ring

/- Exact generated-state calculation for the periodic-candidate route.  If the
   initial mini-batch gradient is `A` and every subsequent generated iterate
   sees the reversed gradient `-A`, Algorithm 1's momentum does not reverse
   immediately: at time `t` it is `(2 * beta ^ t - 1) A`.  Thus the direction
   keeps its initial sign until the geometric memory has decayed past one half.
   This lemma changes no source assumption and does not claim that such a
   gradient pattern is realizable by a source-admissible objective; that is the
   remaining counterexample obligation. -/
theorem theorem_4_15_generated_momentum_under_constant_gradient_reversal
    {xi : Type*} [MeasurableSpace xi] {m n : ℕ}
    (P : StochasticProblem xi m n) (cfg : StochasticMuonConfig m n)
    (omega : SamplePath xi cfg.batchSize) (A : Mat m n)
    (hinitial : stochasticBatchGradient P cfg.batchSize cfg.W0 (omega 0) = A)
    (hreversed : ∀ t : ℕ,
      stochasticBatchGradient P cfg.batchSize
        (stochasticMuonState P cfg omega (t + 1)).W (omega (t + 1)) = -A) :
    ∀ t : ℕ,
      (stochasticMuonState P cfg omega t).M =
        (2 * cfg.beta ^ t - 1) • A := by
  intro t
  induction t with
  | zero =>
      rw [stochasticMuon_M_zero_eq_G_zero, hinitial]
      norm_num
  | succ t ih =>
      rw [stochasticMuon_M_succ_eq_source_update, hreversed t, ih]
      module

/- The preceding exact recurrence locates the momentum switch without any
   asymptotic approximation: its scalar coefficient is positive before
   `beta ^ t` reaches one half and negative afterwards.  This remains a
   candidate-analysis fact; in particular, it does not assert that the
   reversed-gradient hypotheses are realized by a source-admissible
   objective. -/
theorem theorem_4_15_generated_momentum_reversal_switch
    {xi : Type*} [MeasurableSpace xi] {m n : ℕ}
    (P : StochasticProblem xi m n) (cfg : StochasticMuonConfig m n)
    (omega : SamplePath xi cfg.batchSize) (A : Mat m n)
    (hinitial : stochasticBatchGradient P cfg.batchSize cfg.W0 (omega 0) = A)
    (hreversed : ∀ t : ℕ,
      stochasticBatchGradient P cfg.batchSize
        (stochasticMuonState P cfg omega (t + 1)).W (omega (t + 1)) = -A)
    (t : ℕ) :
    ((1 / 2 : ℝ) < cfg.beta ^ t →
        ∃ c : ℝ, 0 < c ∧
          (stochasticMuonState P cfg omega t).M = c • A) ∧
      (cfg.beta ^ t < (1 / 2 : ℝ) →
        ∃ c : ℝ, c < 0 ∧
          (stochasticMuonState P cfg omega t).M = c • A) := by
  have hmomentum := theorem_4_15_generated_momentum_under_constant_gradient_reversal
    P cfg omega A hinitial hreversed t
  constructor
  · intro hbefore
    refine ⟨2 * cfg.beta ^ t - 1, ?_, hmomentum⟩
    linarith
  · intro hafter
    refine ⟨2 * cfg.beta ^ t - 1, ?_, hmomentum⟩
    linarith

/- Bernoulli's inequality turns the qualitative switch criterion above into
   an exact memory window.  Since Algorithm 1 has `0 <= beta < 1`, its
   momentum coefficient cannot cross zero in fewer than a constant multiple
   of `1 / (1 - beta)` steps.  This is a recurrence fact, independent of any
   curvature premise or desired convergence conclusion. -/
theorem theorem_4_15_momentum_power_above_half_during_memory_window
    (beta : ℝ) (hbeta_nonneg : 0 ≤ beta) (q : ℕ)
    (hwindow : (q : ℝ) * (1 - beta) < 1 / 2) :
    (1 / 2 : ℝ) < beta ^ q := by
  have hbernoulli := one_add_mul_le_pow (a := beta - 1) (n := q) (by linarith)
  have hlower : (1 / 2 : ℝ) < 1 + (q : ℝ) * (beta - 1) := by
    push_cast at hbernoulli
    linarith
  exact lt_of_lt_of_le hlower (by simpa using hbernoulli)

/- In one dimension the exact polar direction is unchanged by a positive
   rescaling of a nonzero matrix.  This is proved from the certified polar
   pairing rather than from a choice of singular vectors: positive homogeneity
   of the nuclear norm makes both directions have the same pairing with the
   unique nonzero entry of `A`, which forces the entries themselves to agree. -/
theorem orthogonalizedDirection_pos_smul_eq_one_dimensional
    (A : Mat 1 1) (c : ℝ) (hA : A ≠ 0) (hc : 0 < c) :
    orthogonalizedDirection (c • A) = orthogonalizedDirection A := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hscaleBack : c⁻¹ • (c • A) = A := by
    ext i j
    simp [hc0]
  have hnormUpper : nuclearNorm (c • A) ≤ c * nuclearNorm A :=
    nuclearNorm_smul_le_of_nonneg c A hc.le
  have hnormBack := nuclearNorm_smul_le_of_nonneg c⁻¹ (c • A) (by positivity)
  rw [hscaleBack] at hnormBack
  have hnormLower : c * nuclearNorm A ≤ nuclearNorm (c • A) := by
    have hdiv : nuclearNorm A ≤ nuclearNorm (c • A) / c := by
      simpa [div_eq_inv_mul, mul_comm] using hnormBack
    have hmul := (le_div_iff₀ hc).1 hdiv
    simpa [mul_comm] using hmul
  have hnorm : nuclearNorm (c • A) = c * nuclearNorm A :=
    le_antisymm hnormUpper hnormLower
  have hpairScaled :
      frobeniusInner (c • A) (orthogonalizedDirection (c • A)) =
        nuclearNorm (c • A) :=
    orthogonalizedDirection_frobeniusInner_eq_nuclearNorm (c • A)
  have hpairLinear :
      frobeniusInner (c • A) (orthogonalizedDirection (c • A)) =
        c * frobeniusInner A (orthogonalizedDirection (c • A)) := by
    unfold frobeniusInner
    simp only [Matrix.smul_apply, smul_eq_mul, mul_assoc]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.mul_sum]
  have hpairScaledOnA :
      frobeniusInner A (orthogonalizedDirection (c • A)) = nuclearNorm A := by
    rw [hpairLinear, hnorm] at hpairScaled
    exact mul_left_cancel₀ hc0 hpairScaled
  have hpairA :
      frobeniusInner A (orthogonalizedDirection A) = nuclearNorm A :=
    orthogonalizedDirection_frobeniusInner_eq_nuclearNorm A
  have hpairEq :
      frobeniusInner A (orthogonalizedDirection (c • A)) =
        frobeniusInner A (orthogonalizedDirection A) :=
    hpairScaledOnA.trans hpairA.symm
  have hentry : A 0 0 ≠ 0 := by
    intro hzero
    apply hA
    ext i j
    fin_cases i
    fin_cases j
    simpa using hzero
  ext i j
  fin_cases i
  fin_cases j
  unfold frobeniusInner at hpairEq
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton] at hpairEq
  exact mul_left_cancel₀ hentry hpairEq

/- In one dimension the exact polar also changes sign under negation.  As in
   the positive-rescaling lemma, this is derived from the certified polar
   pairing and therefore does not rely on a particular choice of singular
   vectors.  This supplies the direction used by the return leg of the
   proposed momentum-delayed periodic orbit. -/
theorem orthogonalizedDirection_neg_eq_neg_one_dimensional
    (A : Mat 1 1) (hA : A ≠ 0) :
    orthogonalizedDirection (-A) = -orthogonalizedDirection A := by
  have hpairNeg :
      frobeniusInner (-A) (orthogonalizedDirection (-A)) = nuclearNorm A := by
    rw [orthogonalizedDirection_frobeniusInner_eq_nuclearNorm,
      nuclearNorm_neg_eq]
  have hpairA :
      frobeniusInner A (orthogonalizedDirection A) = nuclearNorm A :=
    orthogonalizedDirection_frobeniusInner_eq_nuclearNorm A
  have hentry : A 0 0 ≠ 0 := by
    intro hzero
    apply hA
    ext i j
    fin_cases i
    fin_cases j
    simpa using hzero
  ext i j
  fin_cases i
  fin_cases j
  unfold frobeniusInner at hpairNeg hpairA
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
    Matrix.neg_apply] at hpairNeg hpairA
  apply mul_left_cancel₀ hentry
  change A 0 0 * orthogonalizedDirection (-A) 0 0 =
    A 0 0 * (-orthogonalizedDirection A 0 0)
  rw [mul_neg]
  linarith

/- Every nonzero one-dimensional exact polar has entry of absolute value one.
   This is a consequence of the already-certified positive homogeneity and
   negation laws, rather than an additional choice of an SVD sign.  It lets the
   periodic-candidate investigation compare the actual generated cross and
   directional Hessian objects without replacing either by an arbitrary
   scalar. -/
theorem orthogonalizedDirection_abs_entry_eq_one_one_dimensional
    (A : Mat 1 1) (hA : A ≠ 0) :
    |orthogonalizedDirection A 0 0| = 1 := by
  let E : Mat 1 1 := coordinateMatrix 0 0
  have hE : E ≠ 0 := by
    intro hzero
    have hentry := congrArg (fun M : Mat 1 1 => M 0 0) hzero
    norm_num [E, coordinateMatrix] at hentry
  have hentry : A 0 0 ≠ 0 := by
    intro hzero
    apply hA
    ext i j
    fin_cases i
    fin_cases j
    simpa using hzero
  by_cases hpos : 0 < A 0 0
  · have hAeq : A = (A 0 0) • E := by
      ext i j
      fin_cases i
      fin_cases j
      simp [E, coordinateMatrix]
    rw [hAeq,
      orthogonalizedDirection_pos_smul_eq_one_dimensional E (A 0 0) hE hpos,
      theorem_4_15_periodicCandidate_coordinateDirection]
    simp [E, coordinateMatrix]
  · have hneg : A 0 0 < 0 := by
      have hnonpos : A 0 0 ≤ 0 := le_of_not_gt hpos
      exact lt_of_le_of_ne hnonpos hentry
    have hAeq : A = (-A 0 0) • (-E) := by
      ext i j
      fin_cases i
      fin_cases j
      simp [E, coordinateMatrix]
    rw [hAeq,
      orthogonalizedDirection_pos_smul_eq_one_dimensional (-E) (-A 0 0)
        (neg_ne_zero.mpr hE) (neg_pos.mpr hneg),
      orthogonalizedDirection_neg_eq_neg_one_dimensional E hE,
      theorem_4_15_periodicCandidate_coordinateDirection]
    simp [E, coordinateMatrix]

/- Whenever the actual generated momentum is nonzero, the one-dimensional
   exact polar has squared entry one.  Thus the candidate's source
   directional Hessian term is precisely `-sin(W_t)`, rather than merely
   having the same absolute value as a scalar surrogate. -/
theorem theorem_4_15_periodicCandidate_generatedDirectionalTerm_eq_neg_sin
    (cfg : DeterministicMomentumMuonConfig 1 1) (t : ℕ)
    (hM : (deterministicMomentumMuonState
      theorem_4_15_periodicCandidateObjective cfg t).M ≠ 0) :
    deterministicMomentumHessianDirectionalTerm
        theorem_4_15_periodicCandidateObjective cfg t =
      -Real.sin (theorem_4_5_counterexampleEntry
        (deterministicMomentumMuonState theorem_4_15_periodicCandidateObjective
          cfg t).W) := by
  rw [theorem_4_15_periodicCandidate_directionalTerm]
  have habs := orthogonalizedDirection_abs_entry_eq_one_one_dimensional
    (deterministicMomentumMuonState
      theorem_4_15_periodicCandidateObjective cfg t).M hM
  have hsquare :
      (orthogonalizedDirection
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg t).M 0 0) ^ 2 = 1 := by
    nlinarith [sq_abs (orthogonalizedDirection
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg t).M 0 0)]
  rw [hsquare, mul_one]

/- Horizon-level reduction of both substantive quantities in the proposed
   counterexample.  The only extra hypothesis is the concrete nonvanishing
   condition needed to identify each exact polar; no source conclusion,
   cross control, or stationarity estimate is assumed. -/
theorem theorem_4_15_periodicCandidate_fullHorizon_scalar_reduction
    (cfg : DeterministicMomentumMuonConfig 1 1) (T : ℕ)
    (hM : ∀ t ∈ Finset.range T,
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg t).M ≠ 0) :
    deterministicMomentumHessianDirectionalAverage
        theorem_4_15_periodicCandidateObjective cfg T =
        ((T : ℝ)⁻¹) * Finset.sum (Finset.range T) (fun t =>
          -Real.sin (theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg t).W)) ∧
      deterministicMomentumAverageNuclearGradient
        theorem_4_15_periodicCandidateObjective cfg T =
        ((T : ℝ)⁻¹) * Finset.sum (Finset.range T) (fun t =>
          |Real.cos (theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg t).W)|) := by
  constructor
  · unfold deterministicMomentumHessianDirectionalAverage
    congr 1
    apply Finset.sum_congr rfl
    intro t ht
    exact theorem_4_15_periodicCandidate_generatedDirectionalTerm_eq_neg_sin
      cfg t (hM t ht)
  · unfold deterministicMomentumAverageNuclearGradient
    congr 1
    apply Finset.sum_congr rfl
    intro t _ht
    exact theorem_4_15_periodicCandidate_generatedNuclearGradient_eq_abs_cos cfg t

/- On the actual one-dimensional deterministic-momentum process for the
   bounded-below periodic objective, the cross and directional Hessian terms
   have the same magnitude whenever their two polar inputs are nonzero.  Thus
   a prospective source counterexample cannot obtain a large cross term from
   a larger Hessian magnitude than the source `J` sees; it must realize a sign
   pattern in which the directional terms cancel while the generated gradient
   differences align the cross terms.  This is candidate-screening evidence,
   not cross control and not a source-theorem counterexample. -/
theorem theorem_4_15_periodicCandidate_cross_abs_eq_directional_abs_of_nonzero
    (cfg : DeterministicMomentumMuonConfig 1 1) (t : ℕ)
    (hM : (deterministicMomentumMuonState
      theorem_4_15_periodicCandidateObjective cfg t).M ≠ 0)
    (hgradDiff :
      theorem_4_15_periodicCandidateObjective.grad
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg t).W -
        theorem_4_15_periodicCandidateObjective.grad
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg (t + 1)).W ≠ 0) :
    |deterministicMomentumHessianCrossTerm
        theorem_4_15_periodicCandidateObjective cfg t| =
      |deterministicMomentumHessianDirectionalTerm
        theorem_4_15_periodicCandidateObjective cfg t| := by
  let state := deterministicMomentumMuonState
    theorem_4_15_periodicCandidateObjective cfg t
  let nextState := deterministicMomentumMuonState
    theorem_4_15_periodicCandidateObjective cfg (t + 1)
  let Dg := orthogonalizedDirection
    (theorem_4_15_periodicCandidateObjective.grad state.W -
      theorem_4_15_periodicCandidateObjective.grad nextState.W)
  let D := orthogonalizedDirection state.M
  have hDg : |Dg 0 0| = 1 := by
    apply orthogonalizedDirection_abs_entry_eq_one_one_dimensional
    simpa [state, nextState] using hgradDiff
  have hD : |D 0 0| = 1 := by
    apply orthogonalizedDirection_abs_entry_eq_one_one_dimensional
    simpa [state] using hM
  unfold deterministicMomentumHessianCrossTerm
    deterministicMomentumHessianDirectionalTerm
  dsimp only
  rw [theorem_4_15_periodicCandidateObjective_hessianBilinear,
    theorem_4_15_periodicCandidateObjective_hessianBilinear]
  change
    |(-Real.sin (theorem_4_5_counterexampleEntry state.W)) * Dg 0 0 * D 0 0| =
      |(-Real.sin (theorem_4_5_counterexampleEntry state.W)) * D 0 0 * D 0 0|
  simp only [abs_mul, hDg, hD, mul_one]

/- A concrete generated one-step sign test for the same bounded-below periodic
   objective.  Starting at `pi / 4` and taking the exact Algorithm 1 step
   `pi / 8`, the momentum polar points to the right while the true-gradient
   difference polar points to the left.  Consequently the signed directional
   Hessian term is negative and the cross term is equally positive.  This is
   an original generated-process obstruction to any *pointwise* inference
   from signed directional curvature to cross curvature; it is not by itself
   a counterexample to the horizon-averaged source theorem. -/
def theorem_4_15_periodicCandidateLocalSeparationConfig
    (beta : ℝ) (hbeta : beta ∈ Set.Ico (0 : ℝ) 1) :
    DeterministicMomentumMuonConfig 1 1 where
  W0 := (Real.pi / 4) • coordinateMatrix 0 0
  eta := fun _ => Real.pi / 8
  beta := beta
  beta_mem := hbeta

theorem theorem_4_15_periodicCandidate_local_initial_direction
    (beta : ℝ) (hbeta : beta ∈ Set.Ico (0 : ℝ) 1) :
    orthogonalizedDirection
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective
          (theorem_4_15_periodicCandidateLocalSeparationConfig beta hbeta) 0).M =
      coordinateMatrix 0 0 := by
  let E : Mat 1 1 := coordinateMatrix 0 0
  have hE : E ≠ 0 := by
    intro hzero
    have hentry := congrArg (fun M : Mat 1 1 => M 0 0) hzero
    norm_num [E, coordinateMatrix] at hentry
  have hcoefficient : 0 < Real.sqrt 2 / 2 := by positivity
  have hmomentum :
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective
        (theorem_4_15_periodicCandidateLocalSeparationConfig beta hbeta) 0).M =
        (Real.sqrt 2 / 2) • E := by
    rw [deterministicMomentumMuon_M_zero_eq_gradient]
    unfold deterministicGradient
    rw [theorem_4_15_periodicCandidateObjective_grad]
    ext i j
    fin_cases i
    fin_cases j
    simp only [theorem_4_5_counterexampleEntry_apply, Matrix.smul_apply,
      smul_eq_mul]
    simp [theorem_4_15_periodicCandidateLocalSeparationConfig, E,
      coordinateMatrix, Real.cos_pi_div_four]
  rw [hmomentum,
    orthogonalizedDirection_pos_smul_eq_one_dimensional E
      (Real.sqrt 2 / 2) hE hcoefficient,
    theorem_4_15_periodicCandidate_coordinateDirection]

theorem theorem_4_15_periodicCandidate_local_first_state
    (beta : ℝ) (hbeta : beta ∈ Set.Ico (0 : ℝ) 1) :
    (deterministicMomentumMuonState
      theorem_4_15_periodicCandidateObjective
      (theorem_4_15_periodicCandidateLocalSeparationConfig beta hbeta) 1).W =
        (Real.pi / 8) • coordinateMatrix 0 0 := by
  calc
    (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective
        (theorem_4_15_periodicCandidateLocalSeparationConfig beta hbeta) 1).W =
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective
          (theorem_4_15_periodicCandidateLocalSeparationConfig beta hbeta) 0).W -
          (theorem_4_15_periodicCandidateLocalSeparationConfig beta hbeta).eta 0 •
            orthogonalizedDirection
              (deterministicMomentumMuonState
                theorem_4_15_periodicCandidateObjective
                (theorem_4_15_periodicCandidateLocalSeparationConfig beta hbeta) 0).M :=
      deterministicMomentumMuon_W_succ_eq_source_update
        theorem_4_15_periodicCandidateObjective
        (theorem_4_15_periodicCandidateLocalSeparationConfig beta hbeta) 0
    _ = (Real.pi / 8) • coordinateMatrix 0 0 := by
      rw [theorem_4_15_periodicCandidate_local_initial_direction]
      change
        (Real.pi / 4) • coordinateMatrix 0 0 -
            (Real.pi / 8) • coordinateMatrix 0 0 =
          (Real.pi / 8) • coordinateMatrix 0 0
      module

theorem theorem_4_15_periodicCandidate_local_gradient_difference_direction
    (beta : ℝ) (hbeta : beta ∈ Set.Ico (0 : ℝ) 1) :
    orthogonalizedDirection
        (theorem_4_15_periodicCandidateObjective.grad
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective
              (theorem_4_15_periodicCandidateLocalSeparationConfig beta hbeta) 0).W -
          theorem_4_15_periodicCandidateObjective.grad
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective
              (theorem_4_15_periodicCandidateLocalSeparationConfig beta hbeta) 1).W) =
      -(coordinateMatrix 0 0) := by
  let E : Mat 1 1 := coordinateMatrix 0 0
  let c : ℝ := Real.cos (Real.pi / 8) - Real.cos (Real.pi / 4)
  have hE : E ≠ 0 := by
    intro hzero
    have hentry := congrArg (fun M : Mat 1 1 => M 0 0) hzero
    norm_num [E, coordinateMatrix] at hentry
  have hc : 0 < c := by
    dsimp [c]
    have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi
      (x := Real.pi / 8) (y := Real.pi / 4)
      (by positivity) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    linarith
  have hdiff :
      theorem_4_15_periodicCandidateObjective.grad
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective
            (theorem_4_15_periodicCandidateLocalSeparationConfig beta hbeta) 0).W -
        theorem_4_15_periodicCandidateObjective.grad
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective
            (theorem_4_15_periodicCandidateLocalSeparationConfig beta hbeta) 1).W =
        c • (-E) := by
    change theorem_4_15_periodicCandidateObjective.grad
        ((Real.pi / 4) • E) -
      theorem_4_15_periodicCandidateObjective.grad
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective
          (theorem_4_15_periodicCandidateLocalSeparationConfig beta hbeta) 1).W =
      c • (-E)
    rw [theorem_4_15_periodicCandidateObjective_grad,
      theorem_4_15_periodicCandidateObjective_grad,
      theorem_4_15_periodicCandidate_local_first_state]
    ext i j
    fin_cases i
    fin_cases j
    simp only [theorem_4_5_counterexampleEntry_apply, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.neg_apply, Pi.neg_apply, smul_eq_mul]
    simp only [E, coordinateMatrix, Matrix.single_apply, if_pos, one_mul,
      mul_neg, mul_one, neg_mul]
    dsimp [c]
    ring
  rw [hdiff,
    orthogonalizedDirection_pos_smul_eq_one_dimensional (-E) c
      (neg_ne_zero.mpr hE) hc,
    orthogonalizedDirection_neg_eq_neg_one_dimensional E hE,
    theorem_4_15_periodicCandidate_coordinateDirection]

theorem theorem_4_15_periodicCandidate_local_signed_cross_separation
    (beta : ℝ) (hbeta : beta ∈ Set.Ico (0 : ℝ) 1) :
    deterministicMomentumHessianDirectionalTerm
        theorem_4_15_periodicCandidateObjective
        (theorem_4_15_periodicCandidateLocalSeparationConfig beta hbeta) 0 =
        -(Real.sqrt 2 / 2) ∧
      deterministicMomentumHessianCrossTerm
        theorem_4_15_periodicCandidateObjective
        (theorem_4_15_periodicCandidateLocalSeparationConfig beta hbeta) 0 =
        Real.sqrt 2 / 2 := by
  constructor
  · unfold deterministicMomentumHessianDirectionalTerm
    dsimp only
    rw [theorem_4_15_periodicCandidateObjective_hessianBilinear,
      theorem_4_15_periodicCandidate_local_initial_direction]
    change
      -Real.sin (theorem_4_5_counterexampleEntry
          ((Real.pi / 4) • coordinateMatrix 0 0)) *
          coordinateMatrix 0 0 0 0 * coordinateMatrix 0 0 0 0 =
        -(Real.sqrt 2 / 2)
    simp only [theorem_4_5_counterexampleEntry_apply, Matrix.smul_apply,
      smul_eq_mul, coordinateMatrix, Matrix.single_apply, if_pos, one_mul]
    simp only [true_and, if_true, mul_one]
    rw [Real.sin_pi_div_four]
  · unfold deterministicMomentumHessianCrossTerm
    dsimp only
    rw [theorem_4_15_periodicCandidateObjective_hessianBilinear,
      theorem_4_15_periodicCandidate_local_gradient_difference_direction,
      theorem_4_15_periodicCandidate_local_initial_direction]
    change
      -Real.sin (theorem_4_5_counterexampleEntry
          ((Real.pi / 4) • coordinateMatrix 0 0)) *
          (-coordinateMatrix 0 0) 0 0 * coordinateMatrix 0 0 0 0 =
        Real.sqrt 2 / 2
    simp only [theorem_4_5_counterexampleEntry_apply, Matrix.smul_apply,
      Matrix.neg_apply, smul_eq_mul, coordinateMatrix, Matrix.single_apply,
      if_pos, one_mul]
    simp only [true_and, if_true, mul_one]
    rw [Real.sin_pi_div_four]
    ring

/- The preceding witness is not an artefact of the fixed `pi / 8` step.
   At the same initial point, every positive first step smaller than `pi / 4`
   makes the true gradient increase, so its difference polar is opposite to
   the momentum polar.  This is the form relevant to the shrinking
   Appendix B.4 schedule. -/
theorem theorem_4_15_periodicCandidate_initial_direction_of_W0
    (cfg : DeterministicMomentumMuonConfig 1 1)
    (hW0 : cfg.W0 = (Real.pi / 4) • coordinateMatrix 0 0) :
    orthogonalizedDirection
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg 0).M =
      coordinateMatrix 0 0 := by
  let E : Mat 1 1 := coordinateMatrix 0 0
  have hE : E ≠ 0 := by
    intro hzero
    have hentry := congrArg (fun M : Mat 1 1 => M 0 0) hzero
    norm_num [E, coordinateMatrix] at hentry
  have hcoefficient : 0 < Real.sqrt 2 / 2 := by positivity
  have hmomentum :
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg 0).M =
        (Real.sqrt 2 / 2) • E := by
    rw [deterministicMomentumMuon_M_zero_eq_gradient]
    unfold deterministicGradient
    rw [hW0, theorem_4_15_periodicCandidateObjective_grad]
    ext i j
    fin_cases i
    fin_cases j
    simp only [theorem_4_5_counterexampleEntry_apply, Matrix.smul_apply,
      smul_eq_mul]
    simp [E, coordinateMatrix, Real.cos_pi_div_four]
  rw [hmomentum,
    orthogonalizedDirection_pos_smul_eq_one_dimensional E
      (Real.sqrt 2 / 2) hE hcoefficient,
    theorem_4_15_periodicCandidate_coordinateDirection]

theorem theorem_4_15_periodicCandidate_first_state_of_small_step
    (cfg : DeterministicMomentumMuonConfig 1 1)
    (hW0 : cfg.W0 = (Real.pi / 4) • coordinateMatrix 0 0) :
    (deterministicMomentumMuonState
      theorem_4_15_periodicCandidateObjective cfg 1).W =
        (Real.pi / 4 - cfg.eta 0) • coordinateMatrix 0 0 := by
  calc
    (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg 1).W =
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg 0).W -
          cfg.eta 0 • orthogonalizedDirection
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg 0).M := by
      simpa using deterministicMomentumMuon_W_succ_eq_source_update
        theorem_4_15_periodicCandidateObjective cfg 0
    _ = (Real.pi / 4 - cfg.eta 0) • coordinateMatrix 0 0 := by
      rw [theorem_4_15_periodicCandidate_initial_direction_of_W0 cfg hW0]
      change cfg.W0 - cfg.eta 0 • coordinateMatrix 0 0 = _
      rw [hW0]
      module

theorem theorem_4_15_periodicCandidate_gradient_difference_direction_of_small_step
    (cfg : DeterministicMomentumMuonConfig 1 1)
    (hW0 : cfg.W0 = (Real.pi / 4) • coordinateMatrix 0 0)
    (hetaPos : 0 < cfg.eta 0) (hetaLt : cfg.eta 0 < Real.pi / 4) :
    orthogonalizedDirection
        (theorem_4_15_periodicCandidateObjective.grad
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg 0).W -
          theorem_4_15_periodicCandidateObjective.grad
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg 1).W) =
      -(coordinateMatrix 0 0) := by
  let E : Mat 1 1 := coordinateMatrix 0 0
  let c : ℝ := Real.cos (Real.pi / 4 - cfg.eta 0) -
    Real.cos (Real.pi / 4)
  have hE : E ≠ 0 := by
    intro hzero
    have hentry := congrArg (fun M : Mat 1 1 => M 0 0) hzero
    norm_num [E, coordinateMatrix] at hentry
  have hleftNonneg : 0 ≤ Real.pi / 4 - cfg.eta 0 := by
    linarith
  have hrightLePi : Real.pi / 4 ≤ Real.pi := by
    linarith [Real.pi_pos]
  have hc : 0 < c := by
    dsimp [c]
    have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi
      hleftNonneg hrightLePi (by linarith)
    linarith
  have hdiff :
      theorem_4_15_periodicCandidateObjective.grad
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg 0).W -
        theorem_4_15_periodicCandidateObjective.grad
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg 1).W =
        c • (-E) := by
    change theorem_4_15_periodicCandidateObjective.grad cfg.W0 -
      theorem_4_15_periodicCandidateObjective.grad
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg 1).W = c • (-E)
    rw [hW0, theorem_4_15_periodicCandidateObjective_grad,
      theorem_4_15_periodicCandidateObjective_grad,
      theorem_4_15_periodicCandidate_first_state_of_small_step cfg hW0]
    ext i j
    fin_cases i
    fin_cases j
    simp only [theorem_4_5_counterexampleEntry_apply, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.neg_apply, Pi.neg_apply, smul_eq_mul]
    simp only [E, coordinateMatrix, Matrix.single_apply, if_pos, one_mul,
      mul_neg, mul_one, neg_mul]
    dsimp [c]
    ring
  rw [hdiff,
    orthogonalizedDirection_pos_smul_eq_one_dimensional (-E) c
      (neg_ne_zero.mpr hE) hc,
    orthogonalizedDirection_neg_eq_neg_one_dimensional E hE,
    theorem_4_15_periodicCandidate_coordinateDirection]

theorem theorem_4_15_periodicCandidate_signed_cross_separation_of_small_step
    (cfg : DeterministicMomentumMuonConfig 1 1)
    (hW0 : cfg.W0 = (Real.pi / 4) • coordinateMatrix 0 0)
    (hetaPos : 0 < cfg.eta 0) (hetaLt : cfg.eta 0 < Real.pi / 4) :
    deterministicMomentumHessianDirectionalTerm
        theorem_4_15_periodicCandidateObjective cfg 0 =
        -(Real.sqrt 2 / 2) ∧
      deterministicMomentumHessianCrossTerm
        theorem_4_15_periodicCandidateObjective cfg 0 =
        Real.sqrt 2 / 2 := by
  constructor
  · unfold deterministicMomentumHessianDirectionalTerm
    dsimp only
    rw [theorem_4_15_periodicCandidateObjective_hessianBilinear,
      theorem_4_15_periodicCandidate_initial_direction_of_W0 cfg hW0]
    change
      -Real.sin (theorem_4_5_counterexampleEntry cfg.W0) *
          coordinateMatrix 0 0 0 0 * coordinateMatrix 0 0 0 0 =
        -(Real.sqrt 2 / 2)
    rw [hW0]
    simp only [theorem_4_5_counterexampleEntry_apply, Matrix.smul_apply,
      smul_eq_mul, coordinateMatrix, Matrix.single_apply, if_pos, one_mul]
    simp only [true_and, if_true, mul_one]
    rw [Real.sin_pi_div_four]
  · unfold deterministicMomentumHessianCrossTerm
    dsimp only
    rw [theorem_4_15_periodicCandidateObjective_hessianBilinear,
      theorem_4_15_periodicCandidate_gradient_difference_direction_of_small_step
        cfg hW0 hetaPos hetaLt,
      theorem_4_15_periodicCandidate_initial_direction_of_W0 cfg hW0]
    change
      -Real.sin (theorem_4_5_counterexampleEntry cfg.W0) *
          (-coordinateMatrix 0 0) 0 0 * coordinateMatrix 0 0 0 0 =
        Real.sqrt 2 / 2
    rw [hW0]
    simp only [theorem_4_5_counterexampleEntry_apply, Matrix.smul_apply,
      Matrix.neg_apply, smul_eq_mul, coordinateMatrix, Matrix.single_apply,
      if_pos, one_mul]
    simp only [true_and, if_true, mul_one]
    rw [Real.sin_pi_div_four]
    ring

/- This corollary puts the variable-step sign separation inside the exact
   source-small-`J` generated-run boundary.  It is deliberately conditional
   on membership in that boundary: it proves compatibility of the local
   phenomenon with every source assumption and printed schedule field, but
   does not claim that the first-step obstruction accumulates over the whole
   selected horizon. -/
theorem theorem_4_15_periodicCandidate_source_run_local_signed_cross_separation
    (cfgForAccuracyHorizon :
      ℝ → ℕ → DeterministicMomentumMuonConfig 1 1)
    (W0 : Mat 1 1) (sigma Delta epsilon C s : ℝ)
    (betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ)
    (N : ℕ)
    (hN : theorem_4_15_otherwiseSourceSmallJGeneratedRunForAccuracyHorizon
      (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
      (fun eps T => deterministicOracleConfig (cfgForAccuracyHorizon eps T))
      W0 sigma Delta epsilon C s
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N)
    (hW0 : W0 = (Real.pi / 4) • coordinateMatrix 0 0)
    (hsmall : etaUpper *
        theorem_4_15_otherwiseEtaRate 1 1 sigma Delta epsilon N <
      Real.pi / 4) :
    deterministicMomentumHessianDirectionalTerm
        theorem_4_15_periodicCandidateObjective
        (cfgForAccuracyHorizon epsilon N) 0 = -(Real.sqrt 2 / 2) ∧
      deterministicMomentumHessianCrossTerm
        theorem_4_15_periodicCandidateObjective
        (cfgForAccuracyHorizon epsilon N) 0 = Real.sqrt 2 / 2 := by
  rcases hN with
    ⟨_horizon, _hfinite, _hDelta, _hthird, _hvariance, _hwd, hcfgW0,
      hschedule, hsource, _hHorizon, _hregDom, _hregime⟩
  rcases hschedule with
    ⟨_hscheduleDomain, _hbatch, _hbeta, heta, _hconstantEta⟩
  have hetaLt :
      (cfgForAccuracyHorizon epsilon N).eta 0 < Real.pi / 4 :=
    lt_of_le_of_lt (by
      simpa [deterministicOracleConfig] using heta.2.2.2) hsmall
  apply theorem_4_15_periodicCandidate_signed_cross_separation_of_small_step
  · simpa [deterministicOracleConfig, hW0] using hcfgW0
  · simpa [deterministicOracleConfig] using hsource.2
  · exact hetaLt

/- Exact displacement during any constant-direction block of the proposed
   periodic candidate.  The direction premise is deliberately local and
   explicit: a future one-dimensional construction must discharge it from
   the positive coefficient supplied by the switch lemma and the exact polar,
   rather than importing it into a source-facing theorem. -/
theorem theorem_4_15_generated_displacement_under_constant_gradient_reversal
    {xi : Type*} [MeasurableSpace xi] {m n : ℕ}
    (P : StochasticProblem xi m n) (cfg : StochasticMuonConfig m n)
    (omega : SamplePath xi cfg.batchSize) (A D : Mat m n) (η : ℝ)
    (hinitial : stochasticBatchGradient P cfg.batchSize cfg.W0 (omega 0) = A)
    (hreversed : ∀ t : ℕ,
      stochasticBatchGradient P cfg.batchSize
        (stochasticMuonState P cfg omega (t + 1)).W (omega (t + 1)) = -A) :
    ∀ t : ℕ,
      (∀ k < t, cfg.eta k = η) →
      (∀ k < t,
        orthogonalizedDirection ((2 * cfg.beta ^ k - 1) • A) = D) →
      (stochasticMuonState P cfg omega t).W =
        cfg.W0 - ((t : ℝ) * η) • D := by
  intro t
  induction t with
  | zero =>
      intro _hη _hdirection
      simp [stochasticMuonState, stochasticMuonBaseState]
  | succ t ih =>
      intro hη hdirection
      have hηt : cfg.eta t = η := hη t (Nat.lt_succ_self t)
      have hdirectiont :
          orthogonalizedDirection ((2 * cfg.beta ^ t - 1) • A) = D :=
        hdirection t (Nat.lt_succ_self t)
      have ih' := ih
        (fun k hk => hη k (Nat.lt_trans hk (Nat.lt_succ_self t)))
        (fun k hk => hdirection k (Nat.lt_trans hk (Nat.lt_succ_self t)))
      have hmomentum :=
        theorem_4_15_generated_momentum_under_constant_gradient_reversal
          P cfg omega A hinitial hreversed t
      rw [stochasticMuon_W_succ_eq_source_update, hmomentum, hdirectiont, hηt, ih']
      push_cast
      module

/- The one-dimensional specialization now discharges the preceding lemma's
   polar-direction premise from the exact momentum coefficient itself.  Before
   `beta ^ k` reaches one half, every coefficient is positive, so all generated
   updates use the initial nonzero matrix's exact polar direction.  The only
   remaining conditional hypothesis is the gradient-reversal pattern that a
   source-admissible objective and sample law would have to realize. -/
theorem theorem_4_15_generated_displacement_before_momentum_switch_one_dimensional
    {xi : Type*} [MeasurableSpace xi]
    (P : StochasticProblem xi 1 1) (cfg : StochasticMuonConfig 1 1)
    (omega : SamplePath xi cfg.batchSize) (A : Mat 1 1) (η : ℝ)
    (hinitial : stochasticBatchGradient P cfg.batchSize cfg.W0 (omega 0) = A)
    (hreversed : ∀ k : ℕ,
      stochasticBatchGradient P cfg.batchSize
        (stochasticMuonState P cfg omega (k + 1)).W (omega (k + 1)) = -A)
    (hA : A ≠ 0) (t : ℕ)
    (hη : ∀ k < t, cfg.eta k = η)
    (hbefore : ∀ k < t, (1 / 2 : ℝ) < cfg.beta ^ k) :
    (stochasticMuonState P cfg omega t).W =
      cfg.W0 - ((t : ℝ) * η) • orthogonalizedDirection A := by
  apply theorem_4_15_generated_displacement_under_constant_gradient_reversal
    P cfg omega A (orthogonalizedDirection A) η hinitial hreversed t hη
  intro k hk
  apply orthogonalizedDirection_pos_smul_eq_one_dimensional A
  · exact hA
  · linarith [hbefore k hk]

/- The source schedule need not separately guess the switch index.  On every
   prefix shorter than half a momentum-memory time, Bernoulli's inequality
   supplies all of the positive-coefficient hypotheses required by the exact
   generated displacement theorem.  In particular, even if every post-zero
   batch gradient is already reversed, the generated Algorithm 1 state keeps
   moving in its initial polar direction throughout this whole window. -/
theorem theorem_4_15_generated_displacement_during_memory_window_one_dimensional
    {xi : Type*} [MeasurableSpace xi]
    (P : StochasticProblem xi 1 1) (cfg : StochasticMuonConfig 1 1)
    (omega : SamplePath xi cfg.batchSize) (A : Mat 1 1) (eta : ℝ)
    (hinitial : stochasticBatchGradient P cfg.batchSize cfg.W0 (omega 0) = A)
    (hreversed : ∀ k : ℕ,
      stochasticBatchGradient P cfg.batchSize
        (stochasticMuonState P cfg omega (k + 1)).W (omega (k + 1)) = -A)
    (hA : A ≠ 0) (t : ℕ)
    (heta : ∀ k < t, cfg.eta k = eta)
    (hwindow : (t : ℝ) * (1 - cfg.beta) < 1 / 2) :
    (stochasticMuonState P cfg omega t).W =
      cfg.W0 - ((t : ℝ) * eta) • orthogonalizedDirection A := by
  apply theorem_4_15_generated_displacement_before_momentum_switch_one_dimensional
    P cfg omega A eta hinitial hreversed hA t heta
  intro k hk
  apply theorem_4_15_momentum_power_above_half_during_memory_window
    cfg.beta cfg.beta_mem.1 k
  have hk_cast : (k : ℝ) ≤ (t : ℝ) := by
    exact_mod_cast (Nat.le_of_lt hk)
  have hone_sub_beta_nonneg : 0 ≤ 1 - cfg.beta := by
    linarith [cfg.beta_mem.2]
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right hk_cast hone_sub_beta_nonneg) hwindow

/- The preceding recurrence can be tied directly to the printed otherwise
   schedule.  For a source-small-`J` generated run, the upper theta bound on
   `1 - beta` guarantees that every prefix shorter than the displayed
   accuracy-dependent memory window still moves in the initial polar
   direction under the exact reversed-gradient test pattern.  This is a
   generated Algorithm 1 fact on the same configuration selected by the
   source predicate; it adds no cross/Jstar, curvature, descent, or average
   premise. -/
theorem theorem_4_15_otherwise_source_small_j_generated_reversal_prefix
    {xi : Type*} [MeasurableSpace xi]
    (P : StochasticProblem xi 1 1)
    (cfgForAccuracyHorizon : ℝ → ℕ → StochasticMuonConfig 1 1)
    (W0 : Mat 1 1) (sigma Delta epsilon C s : ℝ)
    (betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ)
    (N : ℕ)
    (hN : theorem_4_15_otherwiseSourceSmallJGeneratedRunForAccuracyHorizon P
      cfgForAccuracyHorizon W0 sigma Delta epsilon C s
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N)
    (omega : SamplePath xi (cfgForAccuracyHorizon epsilon N).batchSize)
    (A : Mat 1 1)
    (hinitial : stochasticBatchGradient P
      (cfgForAccuracyHorizon epsilon N).batchSize
      (cfgForAccuracyHorizon epsilon N).W0 (omega 0) = A)
    (hreversed : ∀ k : ℕ,
      stochasticBatchGradient P (cfgForAccuracyHorizon epsilon N).batchSize
        (stochasticMuonState P (cfgForAccuracyHorizon epsilon N) omega (k + 1)).W
        (omega (k + 1)) = -A)
    (hA : A ≠ 0) (t : ℕ) (htN : t ≤ N)
    (hwindow : (t : ℝ) *
        (betaUpper * theorem_4_15_otherwiseOneMinusBetaScale
          1 1 sigma epsilon) < 1 / 2) :
    (stochasticMuonState P (cfgForAccuracyHorizon epsilon N) omega t).W =
      (cfgForAccuracyHorizon epsilon N).W0 -
        ((t : ℝ) * (cfgForAccuracyHorizon epsilon N).eta 0) •
          orthogonalizedDirection A := by
  rcases hN with
    ⟨_horizon, _hfinite, _hDelta, _hthird, _hvariance, _hwd, _hW0,
      hschedule, _hsource, _hhorizonScale, _hregDomain, _hregime⟩
  rcases hschedule with
    ⟨_hscheduleDomain, _hbatch, hbeta, _heta, hconstantEta⟩
  rcases hbeta with
    ⟨_hbetaLowerPos, _hbetaOrder, _hbetaLowerBound, hbetaUpperBound⟩
  apply theorem_4_15_generated_displacement_during_memory_window_one_dimensional
    P (cfgForAccuracyHorizon epsilon N) omega A
      ((cfgForAccuracyHorizon epsilon N).eta 0) hinitial hreversed hA t
  · intro k hk
    exact hconstantEta k (Finset.mem_range.mpr (lt_of_lt_of_le hk htN))
  · have hnonneg : 0 ≤ (t : ℝ) := by positivity
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left hbetaUpperBound hnonneg) hwindow

/- Once the same exact reversed-gradient pattern has driven the momentum past
   zero, the one-dimensional polar direction reverses and Algorithm 1 retraces
   its earlier displacement.  The formula is stated for a finite post-switch
   block: this is exactly the finite-horizon object needed by a counterexample,
   and it avoids assuming that the pattern can persist after the orbit returns
   to its initial point. -/
theorem theorem_4_15_generated_displacement_after_momentum_switch_one_dimensional
    {xi : Type*} [MeasurableSpace xi]
    (P : StochasticProblem xi 1 1) (cfg : StochasticMuonConfig 1 1)
    (omega : SamplePath xi cfg.batchSize) (A : Mat 1 1) (η : ℝ)
    (hinitial : stochasticBatchGradient P cfg.batchSize cfg.W0 (omega 0) = A)
    (hreversed : ∀ k : ℕ,
      stochasticBatchGradient P cfg.batchSize
        (stochasticMuonState P cfg omega (k + 1)).W (omega (k + 1)) = -A)
    (hA : A ≠ 0) (q d : ℕ)
    (hη : ∀ k < q + d, cfg.eta k = η)
    (hbefore : ∀ k < q, (1 / 2 : ℝ) < cfg.beta ^ k)
    (hafter : ∀ j < d, cfg.beta ^ (q + j) < (1 / 2 : ℝ)) :
    (stochasticMuonState P cfg omega (q + d)).W =
      cfg.W0 - ((q : ℝ) * η) • orthogonalizedDirection A +
        ((d : ℝ) * η) • orthogonalizedDirection A := by
  revert hη hafter
  induction d with
  | zero =>
      intro hη _hafter
      simpa using
        (theorem_4_15_generated_displacement_before_momentum_switch_one_dimensional
          P cfg omega A η hinitial hreversed hA q
          (fun k hk => hη k (by simpa using hk)) hbefore)
  | succ d ih =>
      intro hη hafter
      have hηprefix : ∀ k < q + d, cfg.eta k = η := by
        intro k hk
        exact hη k (lt_trans hk (by omega))
      have hafterPrefix : ∀ j < d, cfg.beta ^ (q + j) < (1 / 2 : ℝ) := by
        intro j hj
        exact hafter j (lt_trans hj (Nat.lt_succ_self d))
      have ih' := ih hηprefix hafterPrefix
      have hmomentum :=
        theorem_4_15_generated_momentum_under_constant_gradient_reversal
          P cfg omega A hinitial hreversed (q + d)
      have hcoeffNeg : 2 * cfg.beta ^ (q + d) - 1 < 0 := by
        linarith [hafter d (Nat.lt_succ_self d)]
      have hcoeffPos : 0 < -(2 * cfg.beta ^ (q + d) - 1) := neg_pos.mpr hcoeffNeg
      have hscaledNeg :
          (2 * cfg.beta ^ (q + d) - 1) • A =
            (-(2 * cfg.beta ^ (q + d) - 1)) • (-A) := by
        module
      have hdirection :
          orthogonalizedDirection ((2 * cfg.beta ^ (q + d) - 1) • A) =
            -orthogonalizedDirection A := by
        rw [hscaledNeg,
          orthogonalizedDirection_pos_smul_eq_one_dimensional (-A)
            (-(2 * cfg.beta ^ (q + d) - 1)) (neg_ne_zero.mpr hA) hcoeffPos,
          orthogonalizedDirection_neg_eq_neg_one_dimensional A hA]
      have hηcurrent : cfg.eta (q + d) = η :=
        hη (q + d) (by omega)
      rw [show q + (d + 1) = (q + d) + 1 by omega,
        stochasticMuon_W_succ_eq_source_update, hmomentum, hdirection,
        hηcurrent, ih']
      push_cast
      module

/- The exact constant-reversal toy pattern cannot itself be realized by a
   deterministic (or merely repeated-batch) oracle for a complete out-and-back
   block.  After equally many pre- and post-switch steps the preceding formula
   returns to `W0`; querying the same batch there must reproduce the initial
   gradient, contradicting the stipulated reversed gradient.  Hence a genuine
   periodic counterexample must analyze the varying objective gradient (or
   genuinely varying samples), rather than reuse the constant `-A` shortcut. -/
theorem theorem_4_15_constant_gradient_reversal_cannot_close_with_same_batch
    {xi : Type*} [MeasurableSpace xi]
    (P : StochasticProblem xi 1 1) (cfg : StochasticMuonConfig 1 1)
    (omega : SamplePath xi cfg.batchSize) (A : Mat 1 1) (η : ℝ)
    (hinitial : stochasticBatchGradient P cfg.batchSize cfg.W0 (omega 0) = A)
    (hreversed : ∀ k : ℕ,
      stochasticBatchGradient P cfg.batchSize
        (stochasticMuonState P cfg omega (k + 1)).W (omega (k + 1)) = -A)
    (hA : A ≠ 0) (q : ℕ) (hq : 0 < q)
    (hη : ∀ k < q + q, cfg.eta k = η)
    (hbefore : ∀ k < q, (1 / 2 : ℝ) < cfg.beta ^ k)
    (hafter : ∀ j < q, cfg.beta ^ (q + j) < (1 / 2 : ℝ))
    (hsameBatch : omega (q + q) = omega 0) : False := by
  have horbit :=
    theorem_4_15_generated_displacement_after_momentum_switch_one_dimensional
      P cfg omega A η hinitial hreversed hA q q hη hbefore hafter
  have hreturn : (stochasticMuonState P cfg omega (q + q)).W = cfg.W0 := by
    rw [horbit]
    module
  have hpositive : 1 ≤ q + q := by omega
  have hrev := hreversed (q + q - 1)
  rw [Nat.sub_add_cancel hpositive, hreturn, hsameBatch] at hrev
  have hneg : -A = A := hrev.symm.trans hinitial
  apply hA
  ext i j
  have hij := congrArg (fun M : Mat 1 1 => M i j) hneg
  simp only [Matrix.neg_apply] at hij
  simp only [Matrix.zero_apply]
  linarith

/- The exact first Algorithm 1 step exposes the continuity invariant forced by
   Assumption 4.13 when the printed otherwise-branch stepsize tends to zero.
   This formulation deliberately records both generated objects: the first
   state converges to the fixed initial state, and its objective gradient
   converges to the fixed initial gradient.  It uses no curvature-average or
   stationarity conclusion and is therefore reusable when screening proposed
   shrinking-step counterexamples. -/
theorem theorem_4_15_deterministic_first_step_and_gradient_tendsto
    {m n : ℕ} (P : Objective m n) (s : ℝ)
    (hthird : ThirdDerivativeBounded P s)
    (cfgForIndex : ℕ → DeterministicMomentumMuonConfig m n)
    (W0 A : Mat m n)
    (hW0 : ∀ k : ℕ, (cfgForIndex k).W0 = W0)
    (hinitial : P.grad W0 = A)
    (heta : Filter.Tendsto (fun k : ℕ => (cfgForIndex k).eta 0)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
        (fun k : ℕ => (deterministicMomentumMuonState P (cfgForIndex k) 1).W)
        Filter.atTop (nhds W0) ∧
      Filter.Tendsto
        (fun k : ℕ => P.grad
          ((deterministicMomentumMuonState P (cfgForIndex k) 1).W))
        Filter.atTop (nhds (P.grad W0)) := by
  have hfirstStep : ∀ k : ℕ,
      (deterministicMomentumMuonState P (cfgForIndex k) 1).W =
        W0 - (cfgForIndex k).eta 0 • orthogonalizedDirection A := by
    intro k
    rw [show 1 = 0 + 1 by omega,
      deterministicMomentumMuon_W_succ_eq_source_update]
    change (cfgForIndex k).W0 -
        (cfgForIndex k).eta 0 •
          orthogonalizedDirection (deterministicGradient P (cfgForIndex k).W0) = _
    rw [hW0 k]
    simpa [deterministicGradient, hinitial]
  have hstates : Filter.Tendsto
      (fun k : ℕ => (deterministicMomentumMuonState P (cfgForIndex k) 1).W)
      Filter.atTop (nhds W0) := by
    rw [show (fun k : ℕ =>
        (deterministicMomentumMuonState P (cfgForIndex k) 1).W) =
      (fun k : ℕ => W0 -
        (cfgForIndex k).eta 0 • orthogonalizedDirection A) by
          funext k
          exact hfirstStep k]
    simpa using tendsto_const_nhds.sub (heta.smul_const (orthogonalizedDirection A))
  exact ⟨hstates,
    hthird.gradient_continuous.continuousAt.tendsto.comp hstates⟩

/- Assumption 4.13 rules out the constant-reversal shortcut even before a
   complete out-and-back block when it is required uniformly along shrinking
   first steps.  The preceding generated-object invariant forces first-step
   gradients to converge to the initial gradient, so they cannot all equal
   its negative unless that gradient is zero.  This is the exact failed
   hypothesis of the reversal candidate, not a claim about the source-small-J
   branch itself. -/
theorem theorem_4_15_deterministic_reversal_at_shrinking_first_step_forces_zero
    {m n : ℕ} (P : Objective m n) (s : ℝ)
    (hthird : ThirdDerivativeBounded P s)
    (cfgForIndex : ℕ → DeterministicMomentumMuonConfig m n)
    (W0 A : Mat m n)
    (hW0 : ∀ k : ℕ, (cfgForIndex k).W0 = W0)
    (hinitial : P.grad W0 = A)
    (heta : Filter.Tendsto (fun k : ℕ => (cfgForIndex k).eta 0)
      Filter.atTop (nhds 0))
    (hreversed : ∀ k : ℕ,
      P.grad ((deterministicMomentumMuonState P (cfgForIndex k) 1).W) = -A) :
    A = 0 := by
  have hgrad :=
    (theorem_4_15_deterministic_first_step_and_gradient_tendsto
      P s hthird cfgForIndex W0 A hW0 hinitial heta).2
  have hconstant : Filter.Tendsto (fun _ : ℕ => -A)
      Filter.atTop (nhds (-A)) := tendsto_const_nhds
  have hnegative : -A = P.grad W0 := by
    apply tendsto_nhds_unique hconstant
    simpa only [hreversed] using hgrad
  rw [hinitial] at hnegative
  ext i j
  have hij := congrArg (fun M : Mat m n => M i j) hnegative
  simp only [Matrix.neg_apply, Matrix.zero_apply] at hij ⊢
  linarith

/- The source-faithful generated-run predicate supplies the shrinking-step
   hypothesis needed by the preceding continuity lemma.  Along every accuracy
   sequence tending to zero, its upper theta bound squeezes the selected first
   steps to zero.  Thus the first state and first objective gradient of the
   exact deterministic-oracle Algorithm 1 specialization converge to the same
   fixed initial objects.  This is a positive Track-A invariant of the printed
   schedule, independent of cross/Jstar control. -/
theorem theorem_4_15_otherwise_source_small_j_deterministic_first_step_tendsto
    {m n : ℕ} (P : Objective m n)
    (cfgForAccuracyHorizon : ℝ → ℕ → DeterministicMomentumMuonConfig m n)
    (W0 : Mat m n) (sigma Delta C s : ℝ)
    (betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ)
    (epsilonSeq : ℕ → ℝ) (horizonSeq : ℕ → ℕ)
    (hthird : ThirdDerivativeBounded P s)
    (hepsilon : Filter.Tendsto epsilonSeq Filter.atTop (nhds 0))
    (hruns : ∀ k : ℕ,
      theorem_4_15_otherwiseSourceSmallJGeneratedRunForAccuracyHorizon
        (deterministicOracleProblem P)
        (fun epsilon N =>
          deterministicOracleConfig (cfgForAccuracyHorizon epsilon N))
        W0 sigma Delta (epsilonSeq k) C s
        betaLower betaUpper etaLower etaUpper horizonLower horizonUpper
        (horizonSeq k)) :
    Filter.Tendsto
        (fun k : ℕ => (deterministicMomentumMuonState P
          (cfgForAccuracyHorizon (epsilonSeq k) (horizonSeq k)) 1).W)
        Filter.atTop (nhds W0) ∧
      Filter.Tendsto
        (fun k : ℕ => P.grad ((deterministicMomentumMuonState P
          (cfgForAccuracyHorizon (epsilonSeq k) (horizonSeq k)) 1).W))
        Filter.atTop (nhds (P.grad W0)) := by
  let cfgForIndex : ℕ → DeterministicMomentumMuonConfig m n :=
    fun k => cfgForAccuracyHorizon (epsilonSeq k) (horizonSeq k)
  have hW0 : ∀ k : ℕ, (cfgForIndex k).W0 = W0 := by
    intro k
    rcases hruns k with
      ⟨_horizon, _hfinite, _hDelta, _hthird, _hvariance, _hwd, hW0,
        _hschedule, _hsource, _hHorizon, _hregDom, _hregime⟩
    simpa [cfgForIndex, deterministicOracleConfig] using hW0
  let upperScale : ℝ :=
    etaUpper * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Delta / sigma ^ 3
  have hupperTendsto : Filter.Tendsto
      (fun k : ℕ => upperScale * epsilonSeq k ^ 2)
      Filter.atTop (nhds 0) := by
    simpa [upperScale] using (hepsilon.pow 2).const_mul upperScale
  have hetaNonneg : ∀ k : ℕ, 0 ≤ (cfgForIndex k).eta 0 := by
    intro k
    rcases hruns k with
      ⟨_horizon, _hfinite, _hDelta, _hthird, _hvariance, _hwd, _hW0,
        _hschedule, hsource, _hHorizon, _hregDom, _hregime⟩
    exact (by simpa [cfgForIndex, deterministicOracleConfig] using hsource.2.le)
  have hetaUpper : ∀ k : ℕ,
      (cfgForIndex k).eta 0 ≤ upperScale * epsilonSeq k ^ 2 := by
    intro k
    rcases hruns k with
      ⟨_horizon, _hfinite, _hDelta, _hthird, _hvariance, _hwd, _hW0,
        hschedule, _hsource, _hHorizon, _hregDom, _hregime⟩
    rcases hschedule with ⟨_hdomain, _hbatch, _hbeta, heta, _hconstant⟩
    have hbound := heta.2.2.2
    change (cfgForIndex k).eta 0 ≤ _
    change (cfgForAccuracyHorizon (epsilonSeq k) (horizonSeq k)).eta 0 ≤ _
    calc
      (cfgForAccuracyHorizon (epsilonSeq k) (horizonSeq k)).eta 0 ≤
          etaUpper * theorem_4_15_otherwiseEtaRate m n sigma Delta
            (epsilonSeq k) (horizonSeq k) := by
        simpa [deterministicOracleConfig] using hbound
      _ = upperScale * epsilonSeq k ^ 2 := by
        dsimp [upperScale, theorem_4_15_otherwiseEtaRate, sourceQuot]
        ring
  have heta : Filter.Tendsto (fun k : ℕ => (cfgForIndex k).eta 0)
      Filter.atTop (nhds 0) :=
    squeeze_zero hetaNonneg hetaUpper hupperTendsto
  simpa [cfgForIndex] using
    (theorem_4_15_deterministic_first_step_and_gradient_tendsto
      P s hthird cfgForIndex W0 (P.grad W0) hW0 rfl heta)

/- The printed otherwise schedule supplies the shrinking-step premise in the
   preceding invariant.  Along any accuracy sequence tending to zero, the
   upper theta bound on `eta` squeezes every selected first step to zero.
   Therefore an exact deterministic reversal at the first generated iterate,
   with one fixed nonzero initial gradient across the family, is incompatible
   with the original generated source-small-J run predicate.  This closes the
   constant-reversal candidate route at the precise Assumption 4.13
   continuity hypothesis; it neither proves the desired average nor changes
   the public source boundary. -/
theorem theorem_4_15_otherwise_source_small_j_deterministic_first_reversal_forces_zero
    (P : Objective 1 1)
    (cfgForAccuracyHorizon : ℝ → ℕ → DeterministicMomentumMuonConfig 1 1)
    (W0 : Mat 1 1) (sigma Delta C s : ℝ)
    (betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ)
    (epsilonSeq : ℕ → ℝ) (horizonSeq : ℕ → ℕ)
    (hthird : ThirdDerivativeBounded P s)
    (hepsilon : Filter.Tendsto epsilonSeq Filter.atTop (nhds 0))
    (hruns : ∀ k : ℕ,
      theorem_4_15_otherwiseSourceSmallJGeneratedRunForAccuracyHorizon
        (deterministicOracleProblem P)
        (fun epsilon N =>
          deterministicOracleConfig (cfgForAccuracyHorizon epsilon N))
        W0 sigma Delta (epsilonSeq k) C s
        betaLower betaUpper etaLower etaUpper horizonLower horizonUpper
        (horizonSeq k))
    (A : Mat 1 1) (hinitial : P.grad W0 = A)
    (hreversed : ∀ k : ℕ,
      P.grad ((deterministicMomentumMuonState P
        (cfgForAccuracyHorizon (epsilonSeq k) (horizonSeq k)) 1).W) = -A) :
    A = 0 := by
  have hgrad :=
    (theorem_4_15_otherwise_source_small_j_deterministic_first_step_tendsto
      P cfgForAccuracyHorizon W0 sigma Delta C s
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper
      epsilonSeq horizonSeq hthird hepsilon hruns).2
  have hconstant : Filter.Tendsto (fun _ : ℕ => -A)
      Filter.atTop (nhds (-A)) := tendsto_const_nhds
  have hnegative : -A = P.grad W0 := by
    apply tendsto_nhds_unique hconstant
    simpa only [hreversed] using hgrad
  rw [hinitial] at hnegative
  ext i j
  have hij := congrArg (fun M : Mat 1 1 => M i j) hnegative
  simp only [Matrix.neg_apply, Matrix.zero_apply] at hij ⊢
  linarith

/- The step itself shrinks in the printed otherwise schedule, but the relevant
   momentum-memory displacement does not: `eta / (1 - beta)` is trapped between
   accuracy-independent multiples of the exact scale below.  Thus the preceding
   fixed-step obstruction does not rule out a shrinking-step periodic candidate
   whose momentum delay spans a fixed spatial distance.  This is derived only
   from the source schedule of the same generated run and adds no curvature or
   stationarity premise. -/
theorem theorem_4_15_otherwise_source_small_j_momentum_memory_scale
    {xi : Type*} [MeasurableSpace xi] {m n : ℕ}
    (P : StochasticProblem xi m n)
    (cfgForAccuracyHorizon : ℝ → ℕ → StochasticMuonConfig m n)
    (W0 : Mat m n) (sigma Delta epsilon C s : ℝ)
    (betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ)
    (N : ℕ)
    (hN : theorem_4_15_otherwiseSourceSmallJGeneratedRunForAccuracyHorizon P
      cfgForAccuracyHorizon W0 sigma Delta epsilon C s
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N) :
    let memoryScale :=
      Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) *
        (matrixRankBound m n : ℝ) * Delta / sigma
    (etaLower / betaUpper) * memoryScale ≤
        (cfgForAccuracyHorizon epsilon N).eta 0 /
          (1 - (cfgForAccuracyHorizon epsilon N).beta) ∧
      (cfgForAccuracyHorizon epsilon N).eta 0 /
          (1 - (cfgForAccuracyHorizon epsilon N).beta) ≤
        (etaUpper / betaLower) * memoryScale := by
  dsimp only
  rcases hN with
    ⟨_horizon, hfinite, hDelta, _hthird, hvariance, _hwd, _hW0, hschedule,
      _hsource, _hHorizon, _hregDom, _hregime⟩
  rcases hschedule with
    ⟨hscheduleDom, _hbatch, hbeta, heta, _hconstEta⟩
  rcases hscheduleDom with ⟨_horizon', hbetaDom, _hrankDom, hetaDom⟩
  rcases hbeta with
    ⟨hbetaLowerPos, hbetaOrder, hbetaLowerBound, hbetaUpperBound⟩
  rcases heta with
    ⟨hetaLowerPos, hetaOrder, hetaLowerBound, hetaUpperBound⟩
  let cfgN := cfgForAccuracyHorizon epsilon N
  let betaRate := theorem_4_15_otherwiseOneMinusBetaScale m n sigma epsilon
  let etaRate := theorem_4_15_otherwiseEtaRate m n sigma Delta epsilon N
  let memoryScale :=
    Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) *
      (matrixRankBound m n : ℝ) * Delta / sigma
  have hsigma_ne : sigma ≠ 0 := by
    simpa [sourceQuotDomain] using hetaDom
  have hsigma_pos : 0 < sigma :=
    lt_of_le_of_ne hvariance.nonneg (Ne.symm hsigma_ne)
  have hepsilon_ne : epsilon ≠ 0 := ne_of_gt _hregime.1
  have hnoise_ne : (matrixRankBound m n : ℝ) * sigma ^ 2 ≠ 0 := by
    simpa [sourceQuotDomain] using hbetaDom
  have hrank_ne : (matrixRankBound m n : ℝ) ≠ 0 := by
    intro hrank
    apply hnoise_ne
    simp [hrank]
  have hDelta_nonneg : 0 ≤ Delta := by
    rw [← hDelta]
    unfold sourceObjectiveInitialGap Objective.sourceFStar
    exact sub_nonneg.mpr
      (objective_value_ge_fStar_early P.objective hfinite W0)
  have hbetaRate_nonneg : 0 ≤ betaRate := by
    dsimp [betaRate, theorem_4_15_otherwiseOneMinusBetaScale, sourceQuot]
    positivity
  have hetaRate_nonneg : 0 ≤ etaRate := by
    dsimp [etaRate, theorem_4_15_otherwiseEtaRate, sourceQuot]
    positivity
  have hmemory_nonneg : 0 ≤ memoryScale := by
    dsimp [memoryScale]
    positivity
  have hbetaUpperPos : 0 < betaUpper := lt_of_lt_of_le hbetaLowerPos hbetaOrder
  have hetaUpperPos : 0 < etaUpper := lt_of_lt_of_le hetaLowerPos hetaOrder
  have honeSubBetaPos : 0 < 1 - cfgN.beta := sub_pos.mpr cfgN.beta_mem.2
  have hlowerCoeffNonneg :
      0 ≤ (etaLower / betaUpper) * memoryScale :=
    mul_nonneg (div_nonneg hetaLowerPos.le hbetaUpperPos.le) hmemory_nonneg
  have hupperCoeffNonneg :
      0 ≤ (etaUpper / betaLower) * memoryScale :=
    mul_nonneg (div_nonneg hetaUpperPos.le hbetaLowerPos.le) hmemory_nonneg
  have hlowerIdentity :
      ((etaLower / betaUpper) * memoryScale) * (betaUpper * betaRate) =
        etaLower * etaRate := by
    dsimp [memoryScale, betaRate, etaRate,
      theorem_4_15_otherwiseOneMinusBetaScale,
      theorem_4_15_otherwiseEtaRate, sourceQuot]
    field_simp [hsigma_ne, hepsilon_ne, hrank_ne, ne_of_gt hbetaUpperPos]
  have hupperIdentity :
      ((etaUpper / betaLower) * memoryScale) * (betaLower * betaRate) =
        etaUpper * etaRate := by
    dsimp [memoryScale, betaRate, etaRate,
      theorem_4_15_otherwiseOneMinusBetaScale,
      theorem_4_15_otherwiseEtaRate, sourceQuot]
    field_simp [hsigma_ne, hepsilon_ne, hrank_ne, ne_of_gt hbetaLowerPos]
  constructor
  · apply (le_div_iff₀ honeSubBetaPos).2
    calc
      (etaLower / betaUpper) * memoryScale * (1 - cfgN.beta) ≤
          (etaLower / betaUpper) * memoryScale * (betaUpper * betaRate) :=
        mul_le_mul_of_nonneg_left (by simpa [cfgN, betaRate] using hbetaUpperBound)
          hlowerCoeffNonneg
      _ = etaLower * etaRate := hlowerIdentity
      _ ≤ cfgN.eta 0 := by simpa [cfgN, etaRate] using hetaLowerBound
  · apply (div_le_iff₀ honeSubBetaPos).2
    calc
      cfgN.eta 0 ≤ etaUpper * etaRate := by
        simpa [cfgN, etaRate] using hetaUpperBound
      _ = (etaUpper / betaLower) * memoryScale * (betaLower * betaRate) :=
        hupperIdentity.symm
      _ ≤ (etaUpper / betaLower) * memoryScale * (1 - cfgN.beta) :=
        mul_le_mul_of_nonneg_left (by simpa [cfgN, betaRate] using hbetaLowerBound)
          hupperCoeffNonneg

/- The selected Appendix B.4 horizon is much longer than one momentum-memory
   window.  Multiplying the lower theta bounds for `N` and `1 - beta` gives a
   same-run lower bound on the exact dimensionless memory count
   `N * (1 - beta)`.  This is the scale that a periodic candidate must analyze:
   the nonshrinking displacement of one window alone does not control the
   diverging number of windows in the complete source-selected horizon. -/
theorem theorem_4_15_otherwise_source_small_j_horizon_memory_count
    {xi : Type*} [MeasurableSpace xi] {m n : ℕ}
    (P : StochasticProblem xi m n)
    (cfgForAccuracyHorizon : ℝ → ℕ → StochasticMuonConfig m n)
    (W0 : Mat m n) (sigma Delta epsilon C s : ℝ)
    (betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ)
    (N : ℕ)
    (hN : theorem_4_15_otherwiseSourceSmallJGeneratedRunForAccuracyHorizon P
      cfgForAccuracyHorizon W0 sigma Delta epsilon C s
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N) :
    (horizonLower * theorem_4_15_otherwiseComplexityRate m n sigma epsilon) *
        (betaLower *
          theorem_4_15_otherwiseOneMinusBetaScale m n sigma epsilon) ≤
      (N : ℝ) * (1 - (cfgForAccuracyHorizon epsilon N).beta) := by
  rcases hN with
    ⟨_horizon, _hfinite, _hDelta, _hthird, _hvariance, _hwd, _hW0,
      hschedule, _hsource, hHorizon, _hregDom, _hregime⟩
  rcases hschedule with
    ⟨_hscheduleDom, _hbatch, hbeta, _heta, _hconstantEta⟩
  have hbetaRate_nonneg :
      0 ≤ theorem_4_15_otherwiseOneMinusBetaScale m n sigma epsilon := by
    unfold theorem_4_15_otherwiseOneMinusBetaScale sourceQuot
    positivity
  have hHorizonLower :
      horizonLower * theorem_4_15_otherwiseComplexityRate m n sigma epsilon ≤
        (N : ℝ) := hHorizon.2.2.1
  have hbetaLower :
      betaLower *
          theorem_4_15_otherwiseOneMinusBetaScale m n sigma epsilon ≤
        1 - (cfgForAccuracyHorizon epsilon N).beta := hbeta.2.2.1
  have hbetaScale_nonneg :
      0 ≤ betaLower *
        theorem_4_15_otherwiseOneMinusBetaScale m n sigma epsilon :=
    mul_nonneg hbeta.1.le hbetaRate_nonneg
  calc
    (horizonLower * theorem_4_15_otherwiseComplexityRate m n sigma epsilon) *
          (betaLower *
            theorem_4_15_otherwiseOneMinusBetaScale m n sigma epsilon) ≤
        (N : ℝ) *
          (betaLower *
            theorem_4_15_otherwiseOneMinusBetaScale m n sigma epsilon) :=
      mul_le_mul_of_nonneg_right hHorizonLower hbetaScale_nonneg
    _ ≤ (N : ℝ) * (1 - (cfgForAccuracyHorizon epsilon N).beta) :=
      mul_le_mul_of_nonneg_left hbetaLower (by positivity)

/- In the one-dimensional periodic-candidate setting, the product of the
   printed horizon and memory rates is exactly `sigma / epsilon`.  Hence the
   number of memory windows diverges at least at that rate for every source
   run, rather than remaining on the constant spatial scale of one window. -/
theorem theorem_4_15_otherwise_source_small_j_horizon_memory_count_one_dimensional
    {xi : Type*} [MeasurableSpace xi]
    (P : StochasticProblem xi 1 1)
    (cfgForAccuracyHorizon : ℝ → ℕ → StochasticMuonConfig 1 1)
    (W0 : Mat 1 1) (sigma Delta epsilon C s : ℝ)
    (betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ)
    (N : ℕ)
    (hN : theorem_4_15_otherwiseSourceSmallJGeneratedRunForAccuracyHorizon P
      cfgForAccuracyHorizon W0 sigma Delta epsilon C s
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N) :
    (betaLower * horizonLower) * (sigma / epsilon) ≤
      (N : ℝ) * (1 - (cfgForAccuracyHorizon epsilon N).beta) := by
  have hcount :=
    theorem_4_15_otherwise_source_small_j_horizon_memory_count
      P cfgForAccuracyHorizon W0 sigma Delta epsilon C s
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N hN
  have hsigma_ne : sigma ≠ 0 := by
    rcases hN with
      ⟨_horizon, _hfinite, _hDelta, _hthird, _hvariance, _hwd, _hW0,
        hschedule, _hsource, _hHorizon, _hregDom, _hregime⟩
    intro hsigma
    apply hschedule.1.2.1
    simp [hsigma]
  have hepsilon_ne : epsilon ≠ 0 := by
    rcases hN with
      ⟨_horizon, _hfinite, _hDelta, _hthird, _hvariance, _hwd, _hW0,
        _hschedule, _hsource, _hHorizon, _hregDom, hregime⟩
    exact ne_of_gt hregime.1
  have hrates :
      theorem_4_15_otherwiseComplexityRate 1 1 sigma epsilon *
          theorem_4_15_otherwiseOneMinusBetaScale 1 1 sigma epsilon =
        sigma / epsilon := by
    unfold theorem_4_15_otherwiseComplexityRate
      theorem_4_15_otherwiseOneMinusBetaScale sourceQuot matrixRankBound
    norm_num
    field_simp [hsigma_ne, hepsilon_ne]
  calc
    (betaLower * horizonLower) * (sigma / epsilon) =
        (horizonLower * theorem_4_15_otherwiseComplexityRate 1 1 sigma epsilon) *
          (betaLower *
            theorem_4_15_otherwiseOneMinusBetaScale 1 1 sigma epsilon) := by
      rw [← hrates]
      ring
    _ ≤ (N : ℝ) * (1 - (cfgForAccuracyHorizon epsilon N).beta) := hcount

/- The natural integer memory window selected from the actual momentum of a
   one-dimensional source-small-`J` run lies inside the printed horizon once
   the explicit horizon-memory lower scale has reached one half.  Unlike the
   discarded reversal-orbit helper, this is a schedule-only fact: it assumes
   no gradient pattern, auxiliary trajectory, cross/Jstar control, or desired
   stationarity conclusion.  It isolates the exact finite prefix that any
   future fixed-objective counterexample (or recurrence proof) may inspect. -/
theorem theorem_4_15_otherwise_source_small_j_natural_memory_window_le_horizon
    {xi : Type*} [MeasurableSpace xi]
    (P : StochasticProblem xi 1 1)
    (cfgForAccuracyHorizon : ℝ → ℕ → StochasticMuonConfig 1 1)
    (W0 : Mat 1 1) (sigma Delta epsilon C s : ℝ)
    (betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ)
    (N : ℕ)
    (hN : theorem_4_15_otherwiseSourceSmallJGeneratedRunForAccuracyHorizon P
      cfgForAccuracyHorizon W0 sigma Delta epsilon C s
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N)
    (hsmall : betaUpper *
        theorem_4_15_otherwiseOneMinusBetaScale 1 1 sigma epsilon < 1 / 4)
    (hlong : (1 / 2 : ℝ) ≤
      (betaLower * horizonLower) * (sigma / epsilon)) :
    Nat.ceil
        (1 / (4 * (1 - (cfgForAccuracyHorizon epsilon N).beta))) ≤ N := by
  let cfgN := cfgForAccuracyHorizon epsilon N
  let delta := 1 - cfgN.beta
  let q := Nat.ceil (1 / (4 * delta))
  have hwindow :=
    theorem_4_15_otherwise_source_small_j_natural_memory_window
      P cfgForAccuracyHorizon W0 sigma Delta epsilon C s
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N hN hsmall
  dsimp only at hwindow
  have hcount :=
    theorem_4_15_otherwise_source_small_j_horizon_memory_count_one_dimensional
      P cfgForAccuracyHorizon W0 sigma Delta epsilon C s
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N hN
  have hdelta_pos : 0 < delta := by
    dsimp [delta, cfgN]
    exact sub_pos.mpr (cfgForAccuracyHorizon epsilon N).beta_mem.2
  have hNwindow : (1 / 2 : ℝ) ≤ (N : ℝ) * delta := by
    exact hlong.trans (by simpa [delta, cfgN] using hcount)
  have hproduct : (q : ℝ) * delta < (N : ℝ) * delta :=
    hwindow.2.1.trans_le hNwindow
  have hq_lt_N_real : (q : ℝ) < (N : ℝ) := by
    nlinarith
  have hqN : q ≤ N := Nat.le_of_lt (by exact_mod_cast hq_lt_N_real)
  simpa [q, delta, cfgN] using hqN

/- The same selected run also fixes the total phase-travel scale available to
   a generated counterexample.  Multiplying the horizon and step-size theta
   bounds traps `N * eta` between the corresponding products.  Unlike a
   one-window displacement estimate, this controls the complete printed
   horizon and uses the actual constant step of that run. -/
theorem theorem_4_15_otherwise_source_small_j_horizon_travel_scale
    {xi : Type*} [MeasurableSpace xi] {m n : ℕ}
    (P : StochasticProblem xi m n)
    (cfgForAccuracyHorizon : ℝ → ℕ → StochasticMuonConfig m n)
    (W0 : Mat m n) (sigma Delta epsilon C s : ℝ)
    (betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ)
    (N : ℕ)
    (hN : theorem_4_15_otherwiseSourceSmallJGeneratedRunForAccuracyHorizon P
      cfgForAccuracyHorizon W0 sigma Delta epsilon C s
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N) :
    (horizonLower * theorem_4_15_otherwiseComplexityRate m n sigma epsilon) *
        (etaLower * theorem_4_15_otherwiseEtaRate m n sigma Delta epsilon N) ≤
      (N : ℝ) * (cfgForAccuracyHorizon epsilon N).eta 0 ∧
    (N : ℝ) * (cfgForAccuracyHorizon epsilon N).eta 0 ≤
      (horizonUpper * theorem_4_15_otherwiseComplexityRate m n sigma epsilon) *
        (etaUpper * theorem_4_15_otherwiseEtaRate m n sigma Delta epsilon N) := by
  rcases hN with
    ⟨_horizon, hfinite, hDelta, _hthird, hvariance, _hwd, _hW0,
      hschedule, hsource, hHorizon, _hregDom, hregime⟩
  rcases hschedule with
    ⟨_hscheduleDom, _hbatch, _hbeta, heta, _hconstantEta⟩
  have hsigma_nonneg : 0 ≤ sigma := hvariance.nonneg
  have hepsilon_pos : 0 < epsilon := hregime.1
  have hDelta_nonneg : 0 ≤ Delta := by
    rw [← hDelta]
    unfold sourceObjectiveInitialGap Objective.sourceFStar
    exact sub_nonneg.mpr
      (objective_value_ge_fStar_early P.objective hfinite W0)
  have hcomplexityRate_nonneg :
      0 ≤ theorem_4_15_otherwiseComplexityRate m n sigma epsilon := by
    unfold theorem_4_15_otherwiseComplexityRate
    positivity
  have hetaRate_nonneg :
      0 ≤ theorem_4_15_otherwiseEtaRate m n sigma Delta epsilon N := by
    unfold theorem_4_15_otherwiseEtaRate sourceQuot
    positivity
  have hHorizonLower := hHorizon.2.2.1
  have hHorizonUpper := hHorizon.2.2.2
  have hetaLowerBound := heta.2.2.1
  have hetaUpperBound := heta.2.2.2
  have hscaledEtaLower_nonneg :
      0 ≤ etaLower * theorem_4_15_otherwiseEtaRate m n sigma Delta epsilon N :=
    mul_nonneg heta.1.le hetaRate_nonneg
  have hscaledHorizonUpper_nonneg :
      0 ≤ horizonUpper *
        theorem_4_15_otherwiseComplexityRate m n sigma epsilon :=
    mul_nonneg (le_trans hHorizon.1.le hHorizon.2.1) hcomplexityRate_nonneg
  constructor
  · calc
      (horizonLower * theorem_4_15_otherwiseComplexityRate m n sigma epsilon) *
            (etaLower * theorem_4_15_otherwiseEtaRate m n sigma Delta epsilon N) ≤
          (N : ℝ) *
            (etaLower * theorem_4_15_otherwiseEtaRate m n sigma Delta epsilon N) :=
        mul_le_mul_of_nonneg_right hHorizonLower hscaledEtaLower_nonneg
      _ ≤ (N : ℝ) * (cfgForAccuracyHorizon epsilon N).eta 0 :=
        mul_le_mul_of_nonneg_left hetaLowerBound (by positivity)
  · calc
      (N : ℝ) * (cfgForAccuracyHorizon epsilon N).eta 0 ≤
          (horizonUpper * theorem_4_15_otherwiseComplexityRate m n sigma epsilon) *
            (cfgForAccuracyHorizon epsilon N).eta 0 :=
        mul_le_mul_of_nonneg_right hHorizonUpper hsource.2.le
      _ ≤ (horizonUpper *
            theorem_4_15_otherwiseComplexityRate m n sigma epsilon) *
          (etaUpper * theorem_4_15_otherwiseEtaRate m n sigma Delta epsilon N) :=
        mul_le_mul_of_nonneg_left hetaUpperBound hscaledHorizonUpper_nonneg

/- In one dimension the product of the printed horizon and step rates is
   exactly `Delta / epsilon`.  Thus a shrinking individual step still leaves
   an order-`Delta / epsilon` total travel budget over the full source-selected
   horizon.  Any periodic witness must therefore control many spatial cycles,
   not just many momentum-memory windows. -/
theorem theorem_4_15_otherwise_source_small_j_horizon_travel_scale_one_dimensional
    {xi : Type*} [MeasurableSpace xi]
    (P : StochasticProblem xi 1 1)
    (cfgForAccuracyHorizon : ℝ → ℕ → StochasticMuonConfig 1 1)
    (W0 : Mat 1 1) (sigma Delta epsilon C s : ℝ)
    (betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ)
    (N : ℕ)
    (hN : theorem_4_15_otherwiseSourceSmallJGeneratedRunForAccuracyHorizon P
      cfgForAccuracyHorizon W0 sigma Delta epsilon C s
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N) :
    (horizonLower * etaLower) * (Delta / epsilon) ≤
        (N : ℝ) * (cfgForAccuracyHorizon epsilon N).eta 0 ∧
      (N : ℝ) * (cfgForAccuracyHorizon epsilon N).eta 0 ≤
        (horizonUpper * etaUpper) * (Delta / epsilon) := by
  have htravel := theorem_4_15_otherwise_source_small_j_horizon_travel_scale
    P cfgForAccuracyHorizon W0 sigma Delta epsilon C s
    betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N hN
  have hsigma_ne : sigma ≠ 0 := by
    rcases hN with
      ⟨_horizon, _hfinite, _hDelta, _hthird, _hvariance, _hwd, _hW0,
        hschedule, _hsource, _hHorizon, _hregDom, _hregime⟩
    intro hsigma
    apply hschedule.1.2.1
    simp [hsigma]
  have hepsilon_ne : epsilon ≠ 0 := by
    rcases hN with
      ⟨_horizon, _hfinite, _hDelta, _hthird, _hvariance, _hwd, _hW0,
        _hschedule, _hsource, _hHorizon, _hregDom, hregime⟩
    exact ne_of_gt hregime.1
  have hrates := theorem_4_15_otherwise_horizon_eta_product
    1 1 sigma Delta epsilon N hsigma_ne hepsilon_ne
  norm_num [matrixRankBound] at hrates
  constructor
  · calc
      (horizonLower * etaLower) * (Delta / epsilon) =
          (horizonLower * etaLower) *
            (theorem_4_15_otherwiseComplexityRate 1 1 sigma epsilon *
              theorem_4_15_otherwiseEtaRate 1 1 sigma Delta epsilon N) := by
        rw [hrates]
      _ = (horizonLower * theorem_4_15_otherwiseComplexityRate 1 1 sigma epsilon) *
            (etaLower * theorem_4_15_otherwiseEtaRate 1 1 sigma Delta epsilon N) := by
        ring
      _ ≤ (N : ℝ) * (cfgForAccuracyHorizon epsilon N).eta 0 := htravel.1
  · calc
      (N : ℝ) * (cfgForAccuracyHorizon epsilon N).eta 0 ≤
          (horizonUpper * theorem_4_15_otherwiseComplexityRate 1 1 sigma epsilon) *
            (etaUpper * theorem_4_15_otherwiseEtaRate 1 1 sigma Delta epsilon N) :=
        htravel.2
      _ = (horizonUpper * etaUpper) *
          (theorem_4_15_otherwiseComplexityRate 1 1 sigma epsilon *
            theorem_4_15_otherwiseEtaRate 1 1 sigma Delta epsilon N) := by
        ring
      _ = (horizonUpper * etaUpper) * (Delta / epsilon) := by
        rw [hrates]

/- The mixed Hessian quantity occurring in the momentum-lag term is not an
   unrelated curvature scalar.  On the exact generated update it agrees,
   after multiplication by the constant step, with the nuclear norm of the
   successive objective-gradient increment, up to the third-order Taylor
   remainder.  The earlier one-sided bound was sufficient for the corrected
   `Jstar` route; the symmetric form below isolates the precise variation
   estimate that a source-small-`J` Track-A argument still has to control. -/
theorem theorem_4_15_gradient_increment_cross_approximation
    {xi : Type*} [MeasurableSpace xi] {m n : ℕ}
    (P : StochasticProblem xi m n) (cfg : StochasticMuonConfig m n)
    (omega : SamplePath xi cfg.batchSize) {T t : ℕ} {s eta : ℝ}
    (ht : t ∈ Finset.range T)
    (hthird : ThirdDerivativeBounded P.objective s)
    (heta : ∀ k ∈ Finset.range T, cfg.eta k = eta)
    (heta_nonneg : 0 ≤ eta) :
    |nuclearNorm
          (P.objective.grad (stochasticMuonState P cfg omega t).W -
            P.objective.grad (stochasticMuonState P cfg omega (t + 1)).W) -
        eta * stochasticHessianCrossTerm P cfg omega t| ≤
      s * eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2 := by
  classical
  let Wt := (stochasticMuonState P cfg omega t).W
  let Wnext := (stochasticMuonState P cfg omega (t + 1)).W
  let Dt := stochasticMuonDirection P cfg omega t
  let Dg := stochasticGradientDifferenceDirection P cfg omega t
  let d := Wnext - Wt
  have hupdate : Wnext = Wt - eta • Dt := by
    simpa [Wnext, Wt, Dt, stochasticMuonDirection, heta t ht] using
      stochasticMuon_W_succ_eq_source_update P cfg omega t
  have hd : d = (-eta) • Dt := by
    change Wnext - Wt = (-eta) • Dt
    rw [hupdate]
    ext i j
    simp
  have hDg :
      Dg = orthogonalizedDirection
        (P.objective.grad Wt - P.objective.grad Wnext) := by
    rfl
  have hpair :
      frobeniusInner
          (P.objective.grad Wt - P.objective.grad Wnext) Dg =
        nuclearNorm (P.objective.grad Wt - P.objective.grad Wnext) := by
    rw [hDg]
    exact orthogonalizedDirection_frobeniusInner_eq_nuclearNorm _
  have hDg_norm :
      ‖Dg‖ ≤ Real.sqrt (matrixRankBound m n : ℝ) := by
    simpa [Dg, stochasticGradientDifferenceDirection, Wt, Wnext,
      frobeniusNorm] using
      orthogonalizedDirection_frobeniusNorm_le_sqrt_rankBound
        (P.objective.grad Wt - P.objective.grad Wnext)
  have hDt_norm :
      ‖Dt‖ ≤ Real.sqrt (matrixRankBound m n : ℝ) := by
    simpa [Dt, stochasticMuonDirection, frobeniusNorm] using
      orthogonalizedDirection_frobeniusNorm_le_sqrt_rankBound
        (stochasticMuonState P cfg omega t).M
  have htaylor :=
    gradient_pairing_first_order_taylor_remainder_bound
      P.objective hthird Wt Dg d
  have hcross :
      stochasticHessianCrossTerm P cfg omega t =
        hessianBilinear P.objective Wt Dg Dt := by
    rfl
  have hHd :
      hessianBilinear P.objective Wt Dg d =
        -eta * hessianBilinear P.objective Wt Dg Dt := by
    rw [hd]
    unfold hessianBilinear frobeniusInner
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [Matrix.smul_apply]
    simp only [smul_eq_mul]
    ring
  have hr : 0 ≤ (matrixRankBound m n : ℝ) := by positivity
  have hd_norm : ‖d‖ ≤ eta * Real.sqrt (matrixRankBound m n : ℝ) := by
    rw [hd, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg heta_nonneg]
    exact mul_le_mul_of_nonneg_left hDt_norm heta_nonneg
  have hrank_product :
      ‖Dg‖ * ‖d‖ ^ 2 ≤
        eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) := by
    calc
      ‖Dg‖ * ‖d‖ ^ 2 ≤
          Real.sqrt (matrixRankBound m n : ℝ) *
            (eta * Real.sqrt (matrixRankBound m n : ℝ)) ^ 2 := by
        gcongr
      _ = eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) := by
        have hsqrtcube :
            (Real.sqrt (matrixRankBound m n : ℝ)) ^ 3 =
              Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) := by
          have hs2 : (Real.sqrt (matrixRankBound m n : ℝ)) ^ 2 =
              (matrixRankBound m n : ℝ) := Real.sq_sqrt hr
          have hleft :
              ((Real.sqrt (matrixRankBound m n : ℝ)) ^ 3) ^ 2 =
                (matrixRankBound m n : ℝ) ^ 3 := by
            rw [show ((Real.sqrt (matrixRankBound m n : ℝ)) ^ 3) ^ 2 =
              ((Real.sqrt (matrixRankBound m n : ℝ)) ^ 2) ^ 3 by ring, hs2]
          have hright :
              (Real.sqrt ((matrixRankBound m n : ℝ) ^ 3)) ^ 2 =
                (matrixRankBound m n : ℝ) ^ 3 :=
            Real.sq_sqrt (by positivity)
          have hsq := hleft.trans hright.symm
          rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with h | h
          · exact h
          · have hleft_nonneg :
                0 ≤ (Real.sqrt (matrixRankBound m n : ℝ)) ^ 3 := by positivity
            have hright_nonneg :
                0 ≤ Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) :=
              Real.sqrt_nonneg _
            nlinarith
        rw [← hsqrtcube]
        ring
  have hs : 0 ≤ s :=
    le_trans (norm_nonneg _) (hthird.bound Wt)
  have hremainder :
      s * ‖Dg‖ * ‖d‖ ^ 2 / 2 ≤
        s * eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hrank_product hs
    nlinarith
  let e : ℝ :=
    frobeniusInner (P.objective.grad (Wt + d)) Dg -
      frobeniusInner (P.objective.grad Wt) Dg -
        hessianBilinear P.objective Wt Dg d
  have he_abs : |e| ≤
      s * eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2 := by
    exact (show |e| ≤ s * ‖Dg‖ * ‖d‖ ^ 2 / 2 by
      simpa [e] using htaylor).trans hremainder
  have hWt_d : Wt + d = Wnext := by
    change Wt + (Wnext - Wt) = Wnext
    abel
  have hinner_sub :
      frobeniusInner
          (P.objective.grad Wt - P.objective.grad Wnext) Dg =
        frobeniusInner (P.objective.grad Wt) Dg -
          frobeniusInner (P.objective.grad Wnext) Dg := by
    unfold frobeniusInner
    change
      (∑ i, ∑ j,
        (P.objective.grad Wt i j - P.objective.grad Wnext i j) * Dg i j) =
      (∑ i, ∑ j, P.objective.grad Wt i j * Dg i j) -
        ∑ i, ∑ j, P.objective.grad Wnext i j * Dg i j
    simp_rw [sub_mul, Finset.sum_sub_distrib]
  have hsplit :
      frobeniusInner
          (P.objective.grad Wt - P.objective.grad Wnext) Dg =
        eta * hessianBilinear P.objective Wt Dg Dt - e := by
    rw [hinner_sub]
    dsimp [e]
    rw [hWt_d, hHd]
    ring
  calc
    |nuclearNorm
          (P.objective.grad (stochasticMuonState P cfg omega t).W -
            P.objective.grad (stochasticMuonState P cfg omega (t + 1)).W) -
        eta * stochasticHessianCrossTerm P cfg omega t| = |e| := by
      change |nuclearNorm (P.objective.grad Wt - P.objective.grad Wnext) -
        eta * stochasticHessianCrossTerm P cfg omega t| = |e|
      rw [← hpair, hsplit, hcross]
      convert abs_neg e using 1 <;> ring
    _ ≤ s * eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2 := he_abs

/- The source directional Hessian term has its own signed Taylor formula on
   the exact generated update.  Unlike the mixed-term formula above, this
   pairs the gradient increment with the update direction itself and keeps
   its sign.  It is the local identity needed by a monotone one-dimensional
   counterexample: when the generated direction is fixed, these pairings
   telescope to a boundary gradient difference. -/
theorem theorem_4_15_gradient_pairing_directional_approximation
    {xi : Type*} [MeasurableSpace xi] {m n : ℕ}
    (P : StochasticProblem xi m n) (cfg : StochasticMuonConfig m n)
    (omega : SamplePath xi cfg.batchSize) {T t : ℕ} {s eta : ℝ}
    (ht : t ∈ Finset.range T)
    (hthird : ThirdDerivativeBounded P.objective s)
    (heta : ∀ k ∈ Finset.range T, cfg.eta k = eta)
    (heta_nonneg : 0 ≤ eta) :
    |frobeniusInner
          (P.objective.grad (stochasticMuonState P cfg omega t).W -
            P.objective.grad (stochasticMuonState P cfg omega (t + 1)).W)
          (stochasticMuonDirection P cfg omega t) -
        eta * stochasticHessianDirectionalTerm P cfg omega t| ≤
      s * eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2 := by
  classical
  let Wt := (stochasticMuonState P cfg omega t).W
  let Wnext := (stochasticMuonState P cfg omega (t + 1)).W
  let Dt := stochasticMuonDirection P cfg omega t
  let d := Wnext - Wt
  have hupdate : Wnext = Wt - eta • Dt := by
    simpa [Wnext, Wt, Dt, stochasticMuonDirection, heta t ht] using
      stochasticMuon_W_succ_eq_source_update P cfg omega t
  have hd : d = (-eta) • Dt := by
    change Wnext - Wt = (-eta) • Dt
    rw [hupdate]
    ext i j
    simp
  have hDt_norm :
      ‖Dt‖ ≤ Real.sqrt (matrixRankBound m n : ℝ) := by
    simpa [Dt, stochasticMuonDirection, frobeniusNorm] using
      orthogonalizedDirection_frobeniusNorm_le_sqrt_rankBound
        (stochasticMuonState P cfg omega t).M
  have htaylor :=
    gradient_pairing_first_order_taylor_remainder_bound
      P.objective hthird Wt Dt d
  have hdirectional :
      stochasticHessianDirectionalTerm P cfg omega t =
        hessianBilinear P.objective Wt Dt Dt := by
    rfl
  have hHd :
      hessianBilinear P.objective Wt Dt d =
        -eta * hessianBilinear P.objective Wt Dt Dt := by
    rw [hd]
    unfold hessianBilinear frobeniusInner
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [Matrix.smul_apply]
    simp only [smul_eq_mul]
    ring
  have hr : 0 ≤ (matrixRankBound m n : ℝ) := by positivity
  have hd_norm : ‖d‖ ≤ eta * Real.sqrt (matrixRankBound m n : ℝ) := by
    rw [hd, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg heta_nonneg]
    exact mul_le_mul_of_nonneg_left hDt_norm heta_nonneg
  have hrank_product :
      ‖Dt‖ * ‖d‖ ^ 2 ≤
        eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) := by
    calc
      ‖Dt‖ * ‖d‖ ^ 2 ≤
          Real.sqrt (matrixRankBound m n : ℝ) *
            (eta * Real.sqrt (matrixRankBound m n : ℝ)) ^ 2 := by
        gcongr
      _ = eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) := by
        have hsqrtcube :
            (Real.sqrt (matrixRankBound m n : ℝ)) ^ 3 =
              Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) := by
          have hs2 : (Real.sqrt (matrixRankBound m n : ℝ)) ^ 2 =
              (matrixRankBound m n : ℝ) := Real.sq_sqrt hr
          have hleft :
              ((Real.sqrt (matrixRankBound m n : ℝ)) ^ 3) ^ 2 =
                (matrixRankBound m n : ℝ) ^ 3 := by
            rw [show ((Real.sqrt (matrixRankBound m n : ℝ)) ^ 3) ^ 2 =
              ((Real.sqrt (matrixRankBound m n : ℝ)) ^ 2) ^ 3 by ring, hs2]
          have hright :
              (Real.sqrt ((matrixRankBound m n : ℝ) ^ 3)) ^ 2 =
                (matrixRankBound m n : ℝ) ^ 3 :=
            Real.sq_sqrt (by positivity)
          have hsq := hleft.trans hright.symm
          rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with h | h
          · exact h
          · have hleft_nonneg :
                0 ≤ (Real.sqrt (matrixRankBound m n : ℝ)) ^ 3 := by positivity
            have hright_nonneg :
                0 ≤ Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) :=
              Real.sqrt_nonneg _
            nlinarith
        rw [← hsqrtcube]
        ring
  have hs : 0 ≤ s :=
    le_trans (norm_nonneg _) (hthird.bound Wt)
  have hremainder :
      s * ‖Dt‖ * ‖d‖ ^ 2 / 2 ≤
        s * eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hrank_product hs
    nlinarith
  let e : ℝ :=
    frobeniusInner (P.objective.grad (Wt + d)) Dt -
      frobeniusInner (P.objective.grad Wt) Dt -
        hessianBilinear P.objective Wt Dt d
  have he_abs : |e| ≤
      s * eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2 := by
    exact (show |e| ≤ s * ‖Dt‖ * ‖d‖ ^ 2 / 2 by
      simpa [e] using htaylor).trans hremainder
  have hWt_d : Wt + d = Wnext := by
    change Wt + (Wnext - Wt) = Wnext
    abel
  have hinner_sub :
      frobeniusInner (P.objective.grad Wt - P.objective.grad Wnext) Dt =
        frobeniusInner (P.objective.grad Wt) Dt -
          frobeniusInner (P.objective.grad Wnext) Dt := by
    unfold frobeniusInner
    change
      (∑ i, ∑ j,
        (P.objective.grad Wt i j - P.objective.grad Wnext i j) * Dt i j) =
      (∑ i, ∑ j, P.objective.grad Wt i j * Dt i j) -
        ∑ i, ∑ j, P.objective.grad Wnext i j * Dt i j
    simp_rw [sub_mul, Finset.sum_sub_distrib]
  have hsplit :
      frobeniusInner (P.objective.grad Wt - P.objective.grad Wnext) Dt =
        eta * hessianBilinear P.objective Wt Dt Dt - e := by
    rw [hinner_sub]
    dsimp [e]
    rw [hWt_d, hHd]
    ring
  change |frobeniusInner (P.objective.grad Wt - P.objective.grad Wnext) Dt -
      eta * stochasticHessianDirectionalTerm P cfg omega t| ≤ _
  rw [hsplit, hdirectional]
  simpa only [sub_sub_cancel_left, abs_neg] using he_abs

/- When the exact generated Algorithm 1 direction is constant, the signed
   directional Hessian sum is controlled only by a boundary gradient pairing
   and the accumulated third-order remainder.  This is the horizon-level
   cancellation used by the fixed monotone counterexample program; the
   hypothesis identifies a property of the generated directions and does not
   assume a curvature, descent, or stationarity conclusion. -/
theorem theorem_4_15_fixed_generated_direction_directional_sum_telescope
    {xi : Type*} [MeasurableSpace xi] {m n : ℕ}
    (P : StochasticProblem xi m n) (cfg : StochasticMuonConfig m n)
    (omega : SamplePath xi cfg.batchSize) (T : ℕ) (D : Mat m n)
    {s eta : ℝ}
    (hthird : ThirdDerivativeBounded P.objective s)
    (heta : ∀ k ∈ Finset.range T, cfg.eta k = eta)
    (heta_nonneg : 0 ≤ eta)
    (hdirection : ∀ t ∈ Finset.range T,
      stochasticMuonDirection P cfg omega t = D) :
    |frobeniusInner
          (P.objective.grad (stochasticMuonState P cfg omega 0).W -
            P.objective.grad (stochasticMuonState P cfg omega T).W) D -
        eta * ∑ t ∈ Finset.range T,
          stochasticHessianDirectionalTerm P cfg omega t| ≤
      (T : ℝ) *
        (s * eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2) := by
  let g : ℕ → ℝ := fun t =>
    frobeniusInner
      (P.objective.grad (stochasticMuonState P cfg omega t).W) D
  let j : ℕ → ℝ := fun t =>
    stochasticHessianDirectionalTerm P cfg omega t
  let K : ℝ :=
    s * eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2
  have hpoint : ∀ t ∈ Finset.range T,
      |(g t - g (t + 1)) - eta * j t| ≤ K := by
    intro t ht
    have happ := theorem_4_15_gradient_pairing_directional_approximation
      P cfg omega ht hthird heta heta_nonneg
    rw [hdirection t ht] at happ
    have hinner :
        frobeniusInner
            (P.objective.grad (stochasticMuonState P cfg omega t).W -
              P.objective.grad
                (stochasticMuonState P cfg omega (t + 1)).W) D =
          g t - g (t + 1) := by
      dsimp [g]
      unfold frobeniusInner
      change
        (∑ i, ∑ j,
          (P.objective.grad (stochasticMuonState P cfg omega t).W i j -
            P.objective.grad
              (stochasticMuonState P cfg omega (t + 1)).W i j) * D i j) =
        (∑ i, ∑ j,
          P.objective.grad (stochasticMuonState P cfg omega t).W i j * D i j) -
          ∑ i, ∑ j,
            P.objective.grad
              (stochasticMuonState P cfg omega (t + 1)).W i j * D i j
      simp_rw [sub_mul, Finset.sum_sub_distrib]
    simpa [hinner, j, K] using happ
  have habsSum :
      |∑ t ∈ Finset.range T, ((g t - g (t + 1)) - eta * j t)| ≤
        ∑ _t ∈ Finset.range T, K := by
    calc
      |∑ t ∈ Finset.range T, ((g t - g (t + 1)) - eta * j t)| ≤
          ∑ t ∈ Finset.range T, |(g t - g (t + 1)) - eta * j t| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t ∈ Finset.range T, K := by
        exact Finset.sum_le_sum hpoint
  have htelescope :
      ∑ t ∈ Finset.range T, (g t - g (t + 1)) = g 0 - g T := by
    simpa using Finset.sum_range_sub' g T
  have hrearrange :
      (∑ t ∈ Finset.range T, ((g t - g (t + 1)) - eta * j t)) =
        (g 0 - g T) - eta * ∑ t ∈ Finset.range T, j t := by
    rw [Finset.sum_sub_distrib, htelescope, Finset.mul_sum]
  rw [hrearrange] at habsSum
  have hboundary :
      frobeniusInner
          (P.objective.grad (stochasticMuonState P cfg omega 0).W -
            P.objective.grad (stochasticMuonState P cfg omega T).W) D =
        g 0 - g T := by
    dsimp [g]
    unfold frobeniusInner
    change
      (∑ i, ∑ j,
        (P.objective.grad (stochasticMuonState P cfg omega 0).W i j -
          P.objective.grad (stochasticMuonState P cfg omega T).W i j) * D i j) =
      (∑ i, ∑ j,
        P.objective.grad (stochasticMuonState P cfg omega 0).W i j * D i j) -
        ∑ i, ∑ j,
          P.objective.grad (stochasticMuonState P cfg omega T).W i j * D i j
    simp_rw [sub_mul, Finset.sum_sub_distrib]
  rw [hboundary]
  simpa [j, K] using habsSum

/- Summing the symmetric Taylor estimate gives a genuine upper bound on the
   generated mixed-curvature contribution.  It reduces the unresolved source
   bridge to total nuclear variation of consecutive objective gradients; no
   directional, cross, `Jstar`, descent, or stationarity conclusion is used
   as a premise. -/
theorem theorem_4_15_cross_sum_upper_bound_by_gradient_variation
    {xi : Type*} [MeasurableSpace xi] {m n : ℕ}
    (P : StochasticProblem xi m n) (cfg : StochasticMuonConfig m n)
    (omega : SamplePath xi cfg.batchSize) (T : ℕ) {s eta : ℝ}
    (hthird : ThirdDerivativeBounded P.objective s)
    (heta : ∀ k ∈ Finset.range T, cfg.eta k = eta)
    (heta_nonneg : 0 ≤ eta) :
    eta * ∑ t ∈ Finset.range (T - 1),
        stochasticHessianCrossTerm P cfg omega t ≤
      ∑ t ∈ Finset.range (T - 1),
          nuclearNorm
            (P.objective.grad (stochasticMuonState P cfg omega t).W -
              P.objective.grad
                (stochasticMuonState P cfg omega (t + 1)).W) +
        ((T - 1 : ℕ) : ℝ) *
          (s * eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2) := by
  rw [Finset.mul_sum]
  calc
    ∑ t ∈ Finset.range (T - 1),
        eta * stochasticHessianCrossTerm P cfg omega t ≤
      ∑ t ∈ Finset.range (T - 1),
        (nuclearNorm
            (P.objective.grad (stochasticMuonState P cfg omega t).W -
              P.objective.grad
                (stochasticMuonState P cfg omega (t + 1)).W) +
          s * eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2) := by
      apply Finset.sum_le_sum
      intro t ht
      have htT : t ∈ Finset.range T := Finset.mem_range.mpr (by
        have htt : t < T - 1 := Finset.mem_range.mp ht
        omega)
      have happ := theorem_4_15_gradient_increment_cross_approximation
        P cfg omega htT hthird heta heta_nonneg
      have hneg := neg_le_abs
        (nuclearNorm
            (P.objective.grad (stochasticMuonState P cfg omega t).W -
              P.objective.grad
                (stochasticMuonState P cfg omega (t + 1)).W) -
          eta * stochasticHessianCrossTerm P cfg omega t)
      nlinarith
    _ = ∑ t ∈ Finset.range (T - 1),
          nuclearNorm
            (P.objective.grad (stochasticMuonState P cfg omega t).W -
              P.objective.grad
                (stochasticMuonState P cfg omega (t + 1)).W) +
        ((T - 1 : ℕ) : ℝ) *
          (s * eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2) := by
      rw [Finset.sum_add_distrib]
      simp [Finset.card_range, nsmul_eq_mul]

/- Keeping both sides of the per-step Taylor estimate shows that the generated
   mixed-curvature sum is not merely bounded by total objective-gradient
   variation: after multiplication by the actual step size, the two quantities
   agree up to exactly the accumulated third-order remainder.  This is still a
   pathwise statement about the generated Algorithm 1 recurrence and assumes
   neither cross/Jstar control nor the desired average-gradient conclusion. -/
theorem theorem_4_15_gradient_variation_cross_sum_abs_bound
    {xi : Type*} [MeasurableSpace xi] {m n : ℕ}
    (P : StochasticProblem xi m n) (cfg : StochasticMuonConfig m n)
    (omega : SamplePath xi cfg.batchSize) (T : ℕ) {s eta : ℝ}
    (hthird : ThirdDerivativeBounded P.objective s)
    (heta : ∀ k ∈ Finset.range T, cfg.eta k = eta)
    (heta_nonneg : 0 ≤ eta) :
    |(∑ t ∈ Finset.range (T - 1),
        nuclearNorm
          (P.objective.grad (stochasticMuonState P cfg omega t).W -
            P.objective.grad
              (stochasticMuonState P cfg omega (t + 1)).W)) -
        eta * ∑ t ∈ Finset.range (T - 1),
          stochasticHessianCrossTerm P cfg omega t| ≤
      ((T - 1 : ℕ) : ℝ) *
        (s * eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    |∑ t ∈ Finset.range (T - 1),
        (nuclearNorm
            (P.objective.grad (stochasticMuonState P cfg omega t).W -
              P.objective.grad
                (stochasticMuonState P cfg omega (t + 1)).W) -
          eta * stochasticHessianCrossTerm P cfg omega t)| ≤
        ∑ t ∈ Finset.range (T - 1),
          |nuclearNorm
              (P.objective.grad (stochasticMuonState P cfg omega t).W -
                P.objective.grad
                  (stochasticMuonState P cfg omega (t + 1)).W) -
            eta * stochasticHessianCrossTerm P cfg omega t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ Finset.range (T - 1),
        (s * eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2) := by
      apply Finset.sum_le_sum
      intro t ht
      have htT : t ∈ Finset.range T := Finset.mem_range.mpr (by
        have htt : t < T - 1 := Finset.mem_range.mp ht
        omega)
      exact theorem_4_15_gradient_increment_cross_approximation
        P cfg omega htT hthird heta heta_nonneg
    _ = ((T - 1 : ℕ) : ℝ) *
        (s * eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2) := by
      simp [Finset.card_range, nsmul_eq_mul]

/- The total nuclear variation of consecutive objective gradients is the
   exact random quantity exposed by the preceding generated-path estimate.
   Its integrability is not a new source assumption: it follows from the
   already required well-defined expected gradient sum, since each difference
   is bounded by the two adjacent nuclear gradient norms. -/
def stochasticGradientVariationAverageWellDefined
    {xi : Type*} [MeasurableSpace xi] {m n : ℕ}
    (P : StochasticProblem xi m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) : Prop :=
  SOptLib.expectationWellDefined (samplePathLaw P cfg.batchSize)
    (fun omega => ∑ t ∈ Finset.range (T - 1),
      nuclearNorm
        (P.objective.grad (stochasticMuonState P cfg omega t).W -
          P.objective.grad (stochasticMuonState P cfg omega (t + 1)).W))

noncomputable def stochasticGradientVariationAverageRealized
    {xi : Type*} [MeasurableSpace xi] {m n : ℕ}
    (P : StochasticProblem xi m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (hwd : stochasticGradientVariationAverageWellDefined P cfg T) : ℝ :=
  ((T : ℝ)⁻¹) *
    realizedExpectation (samplePathLaw P cfg.batchSize)
      (fun omega => ∑ t ∈ Finset.range (T - 1),
        nuclearNorm
          (P.objective.grad (stochasticMuonState P cfg omega t).W -
            P.objective.grad (stochasticMuonState P cfg omega (t + 1)).W)) hwd

theorem stochasticGradientVariationAverage_wellDefined_of_gradientAverage
    {xi : Type*} [MeasurableSpace xi] {m n : ℕ}
    (P : StochasticProblem xi m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (hwd : stochasticAverageNuclearGradientWellDefined P cfg T) :
    stochasticGradientVariationAverageWellDefined P cfg T := by
  let mu := samplePathLaw P cfg.batchSize
  have hsum : Integrable
      (fun omega => ∑ t ∈ Finset.range T,
        nuclearNorm
          (P.objective.grad (stochasticMuonState P cfg omega t).W)) mu := by
    simpa [mu, stochasticAverageNuclearGradientWellDefined,
      SOptLib.expectationWellDefined] using hwd
  have hterm (t : ℕ) (ht : t ∈ Finset.range T) : Integrable
      (fun omega =>
        nuclearNorm
          (P.objective.grad (stochasticMuonState P cfg omega t).W)) mu := by
    have hmeas : Measurable
        (fun omega : SamplePath xi cfg.batchSize =>
          nuclearNorm
            (P.objective.grad (stochasticMuonState P cfg omega t).W)) := by
      exact nuclearNorm_measurable.comp
        ((objectiveGradient_measurable P.objective.f).comp
          (stochasticMuon_W_measurable P cfg t))
    apply hsum.mono' hmeas.aestronglyMeasurable
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (nuclearNorm_nonneg _)]
    exact Finset.single_le_sum
      (fun k _hk => nuclearNorm_nonneg
        (P.objective.grad (stochasticMuonState P cfg omega k).W)) ht
  have hvariationTerm (t : ℕ) (ht : t ∈ Finset.range (T - 1)) : Integrable
      (fun omega =>
        nuclearNorm
          (P.objective.grad (stochasticMuonState P cfg omega t).W -
            P.objective.grad (stochasticMuonState P cfg omega (t + 1)).W)) mu := by
    have htT : t ∈ Finset.range T := Finset.mem_range.mpr (by
      have htt : t < T - 1 := Finset.mem_range.mp ht
      omega)
    have hsuccT : t + 1 ∈ Finset.range T := Finset.mem_range.mpr (by
      have htt : t < T - 1 := Finset.mem_range.mp ht
      omega)
    have hmajorant := (hterm t htT).add (hterm (t + 1) hsuccT)
    have hmeas : Measurable
        (fun omega : SamplePath xi cfg.batchSize =>
          nuclearNorm
            (P.objective.grad (stochasticMuonState P cfg omega t).W -
              P.objective.grad
                (stochasticMuonState P cfg omega (t + 1)).W)) := by
      exact nuclearNorm_measurable.comp
        (((objectiveGradient_measurable P.objective.f).comp
            (stochasticMuon_W_measurable P cfg t)).sub
          ((objectiveGradient_measurable P.objective.f).comp
            (stochasticMuon_W_measurable P cfg (t + 1))))
    apply hmajorant.mono' hmeas.aestronglyMeasurable
    filter_upwards with omega
    rw [Real.norm_eq_abs,
      abs_of_nonneg (nuclearNorm_nonneg _)]
    exact nuclearNorm_sub_le _ _
  unfold stochasticGradientVariationAverageWellDefined
    SOptLib.expectationWellDefined
  exact MeasureTheory.integrable_finset_sum (Finset.range (T - 1)) hvariationTerm

/- Averaging the pathwise estimate gives the promised exact realized cross
   statement.  Both random variables use the same Algorithm 1 path law and
   the proof consumes only the existing expectation witness, third-derivative
   bound, constant generated step, and nonnegative step size. -/
theorem theorem_4_15_cross_average_realized_upper_bound_by_gradient_variation
    {xi : Type*} [MeasurableSpace xi] {m n : ℕ}
    (P : StochasticProblem xi m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) {s eta : ℝ}
    (hwd : stochasticMuonExpectationsWellDefined P cfg T)
    (hthird : ThirdDerivativeBounded P.objective s)
    (heta : ∀ k ∈ Finset.range T, cfg.eta k = eta)
    (heta_nonneg : 0 ≤ eta) :
    let hvariation :=
      stochasticGradientVariationAverage_wellDefined_of_gradientAverage
        P cfg T hwd.1
    eta * stochasticHessianCrossAverageRealized P cfg T hwd.2.2.2 ≤
      stochasticGradientVariationAverageRealized P cfg T hvariation +
        ((T : ℝ)⁻¹) * ((T - 1 : ℕ) : ℝ) *
          (s * eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2) := by
  let mu := samplePathLaw P cfg.batchSize
  letI : IsProbabilityMeasure P.sampleLaw := P.isProbability_sampleLaw
  letI : IsProbabilityMeasure mu := by
    dsimp [mu, samplePathLaw]
    infer_instance
  let variation := fun omega : SamplePath xi cfg.batchSize =>
    ∑ t ∈ Finset.range (T - 1),
      nuclearNorm
        (P.objective.grad (stochasticMuonState P cfg omega t).W -
          P.objective.grad (stochasticMuonState P cfg omega (t + 1)).W)
  let cross := fun omega : SamplePath xi cfg.batchSize =>
    ∑ t ∈ Finset.range (T - 1),
      stochasticHessianCrossTerm P cfg omega t
  let remainder : ℝ :=
    ((T - 1 : ℕ) : ℝ) *
      (s * eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2)
  let hvariation :=
    stochasticGradientVariationAverage_wellDefined_of_gradientAverage
      P cfg T hwd.1
  have hvariation_int : Integrable variation mu := by
    simpa [variation, mu, stochasticGradientVariationAverageWellDefined,
      SOptLib.expectationWellDefined] using hvariation
  have hcross_int : Integrable cross mu := by
    simpa [cross, mu, stochasticHessianCrossAverageWellDefined,
      SOptLib.expectationWellDefined] using hwd.2.2.2
  have hpoint (omega : SamplePath xi cfg.batchSize) :
      eta * cross omega ≤ variation omega + remainder := by
    simpa [cross, variation, remainder] using
      theorem_4_15_cross_sum_upper_bound_by_gradient_variation
        P cfg omega T hthird heta heta_nonneg
  have hintegral :
      (∫ omega, eta * cross omega ∂mu) ≤
        ∫ omega, variation omega + remainder ∂mu := by
    apply integral_mono (hcross_int.const_mul eta)
      (hvariation_int.add (integrable_const remainder))
    exact hpoint
  have hintegral' :
      eta * (∫ omega, cross omega ∂mu) ≤
        (∫ omega, variation omega ∂mu) + remainder := by
    rw [integral_const_mul,
      integral_add hvariation_int (integrable_const remainder),
      integral_const, measureReal_univ_eq_one] at hintegral
    simpa using hintegral
  have hinv_nonneg : 0 ≤ ((T : ℝ)⁻¹) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hintegral' hinv_nonneg
  dsimp [hvariation, stochasticHessianCrossAverageRealized,
    stochasticGradientVariationAverageRealized, realizedExpectation]
  change eta * ((T : ℝ)⁻¹ * ∫ omega, cross omega ∂mu) ≤
    (T : ℝ)⁻¹ * ∫ omega, variation omega ∂mu +
      (T : ℝ)⁻¹ * ((T - 1 : ℕ) : ℝ) *
        (s * eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2)
  calc
    eta * ((T : ℝ)⁻¹ * ∫ omega, cross omega ∂mu) =
        (T : ℝ)⁻¹ * (eta * ∫ omega, cross omega ∂mu) := by ring
    _ ≤ (T : ℝ)⁻¹ *
        ((∫ omega, variation omega ∂mu) + remainder) := hscaled
    _ = (T : ℝ)⁻¹ * ∫ omega, variation omega ∂mu +
        (T : ℝ)⁻¹ * ((T - 1 : ℕ) : ℝ) *
          (s * eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2) := by
      dsimp [remainder]
      ring

/- The preceding pathwise absolute estimate also survives integration.  Thus
   on the exact generated path law, realized total gradient variation is
   within the normalized third-order remainder of `eta` times the realized
   mixed Hessian average.  This identifies the unresolved Track-A object in
   both directions without importing it as an assumption. -/
theorem theorem_4_15_gradient_variation_cross_average_realized_abs_bound
    {xi : Type*} [MeasurableSpace xi] {m n : ℕ}
    (P : StochasticProblem xi m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) {s eta : ℝ}
    (hwd : stochasticMuonExpectationsWellDefined P cfg T)
    (hthird : ThirdDerivativeBounded P.objective s)
    (heta : ∀ k ∈ Finset.range T, cfg.eta k = eta)
    (heta_nonneg : 0 ≤ eta) :
    let hvariation :=
      stochasticGradientVariationAverage_wellDefined_of_gradientAverage
        P cfg T hwd.1
    |stochasticGradientVariationAverageRealized P cfg T hvariation -
        eta * stochasticHessianCrossAverageRealized P cfg T hwd.2.2.2| ≤
      ((T : ℝ)⁻¹) * ((T - 1 : ℕ) : ℝ) *
        (s * eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2) := by
  let mu := samplePathLaw P cfg.batchSize
  letI : IsProbabilityMeasure P.sampleLaw := P.isProbability_sampleLaw
  letI : IsProbabilityMeasure mu := by
    dsimp [mu, samplePathLaw]
    infer_instance
  let variation := fun omega : SamplePath xi cfg.batchSize =>
    ∑ t ∈ Finset.range (T - 1),
      nuclearNorm
        (P.objective.grad (stochasticMuonState P cfg omega t).W -
          P.objective.grad (stochasticMuonState P cfg omega (t + 1)).W)
  let cross := fun omega : SamplePath xi cfg.batchSize =>
    ∑ t ∈ Finset.range (T - 1),
      stochasticHessianCrossTerm P cfg omega t
  let remainder : ℝ :=
    ((T - 1 : ℕ) : ℝ) *
      (s * eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2)
  let hvariation :=
    stochasticGradientVariationAverage_wellDefined_of_gradientAverage
      P cfg T hwd.1
  have hvariation_int : Integrable variation mu := by
    simpa [variation, mu, stochasticGradientVariationAverageWellDefined,
      SOptLib.expectationWellDefined] using hvariation
  have hcross_int : Integrable cross mu := by
    simpa [cross, mu, stochasticHessianCrossAverageWellDefined,
      SOptLib.expectationWellDefined] using hwd.2.2.2
  have hgap_int : Integrable (fun omega => variation omega - eta * cross omega) mu :=
    hvariation_int.sub (hcross_int.const_mul eta)
  have hpoint (omega : SamplePath xi cfg.batchSize) :
      |variation omega - eta * cross omega| ≤ remainder := by
    simpa [variation, cross, remainder] using
      theorem_4_15_gradient_variation_cross_sum_abs_bound
        P cfg omega T hthird heta heta_nonneg
  have hmean :
      |∫ omega, variation omega - eta * cross omega ∂mu| ≤ remainder := by
    calc
      |∫ omega, variation omega - eta * cross omega ∂mu| ≤
          ∫ omega, |variation omega - eta * cross omega| ∂mu :=
        abs_integral_le_integral_abs
      _ ≤ ∫ _omega, remainder ∂mu := by
        apply integral_mono hgap_int.abs (integrable_const remainder)
        exact hpoint
      _ = remainder := by
        rw [integral_const, measureReal_univ_eq_one, one_smul]
  have hinv_nonneg : 0 ≤ ((T : ℝ)⁻¹) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hmean hinv_nonneg
  dsimp [hvariation, stochasticGradientVariationAverageRealized,
    stochasticHessianCrossAverageRealized, realizedExpectation]
  change
    |(T : ℝ)⁻¹ * ∫ omega, variation omega ∂mu -
        eta * ((T : ℝ)⁻¹ * ∫ omega, cross omega ∂mu)| ≤
      (T : ℝ)⁻¹ * ((T - 1 : ℕ) : ℝ) *
        (s * eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2)
  have hrewrite :
      |(T : ℝ)⁻¹ * ∫ omega, variation omega ∂mu -
          eta * ((T : ℝ)⁻¹ * ∫ omega, cross omega ∂mu)| =
        (T : ℝ)⁻¹ *
          |∫ omega, variation omega - eta * cross omega ∂mu| := by
    rw [integral_sub hvariation_int (hcross_int.const_mul eta),
      integral_const_mul]
    rw [show
      (T : ℝ)⁻¹ * (∫ omega, variation omega ∂mu) -
          eta * ((T : ℝ)⁻¹ * ∫ omega, cross omega ∂mu) =
        (T : ℝ)⁻¹ *
          ((∫ omega, variation omega ∂mu) -
            eta * ∫ omega, cross omega ∂mu) by ring,
      abs_mul, abs_of_nonneg hinv_nonneg]
  rw [hrewrite]
  simpa [remainder, mul_assoc] using hscaled

/- Total variation of consecutive generated objective gradients is controlled
   by the two adjacent copies of the generated-gradient sum.  This is a
   premise-free pathwise fact; after integration it identifies the strongest
   direct estimate available from the stationarity quantity itself, without
   importing directional, cross, or `Jstar` control. -/
theorem stochasticGradientVariationAverageRealized_le_two_gradientAverage
    {xi : Type*} [MeasurableSpace xi] {m n : ℕ}
    (P : StochasticProblem xi m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (hT : horizonDomain T)
    (hwd : stochasticAverageNuclearGradientWellDefined P cfg T) :
    let hvariation :=
      stochasticGradientVariationAverage_wellDefined_of_gradientAverage
        P cfg T hwd
    stochasticGradientVariationAverageRealized P cfg T hvariation ≤
      2 * stochasticAverageNuclearGradientRealized P cfg T hwd := by
  let mu := samplePathLaw P cfg.batchSize
  let gradientSum := fun omega : SamplePath xi cfg.batchSize =>
    ∑ t ∈ Finset.range T,
      nuclearNorm (P.objective.grad (stochasticMuonState P cfg omega t).W)
  let variation := fun omega : SamplePath xi cfg.batchSize =>
    ∑ t ∈ Finset.range (T - 1),
      nuclearNorm
        (P.objective.grad (stochasticMuonState P cfg omega t).W -
          P.objective.grad (stochasticMuonState P cfg omega (t + 1)).W)
  let hvariation :=
    stochasticGradientVariationAverage_wellDefined_of_gradientAverage
      P cfg T hwd
  have hgradient_int : Integrable gradientSum mu := by
    simpa [gradientSum, mu, stochasticAverageNuclearGradientWellDefined,
      SOptLib.expectationWellDefined] using hwd
  have hvariation_int : Integrable variation mu := by
    simpa [variation, mu, stochasticGradientVariationAverageWellDefined,
      SOptLib.expectationWellDefined] using hvariation
  have hTsplit : T = (T - 1) + 1 := by
    unfold horizonDomain at hT
    omega
  have hpoint (omega : SamplePath xi cfg.batchSize) :
      variation omega ≤ 2 * gradientSum omega := by
    let g : ℕ → ℝ := fun t =>
      nuclearNorm (P.objective.grad (stochasticMuonState P cfg omega t).W)
    have htriangle :
        variation omega ≤
          (∑ t ∈ Finset.range (T - 1), g t) +
            ∑ t ∈ Finset.range (T - 1), g (t + 1) := by
      dsimp [variation]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro t _ht
      exact nuclearNorm_sub_le _ _
    have hfirst :
        (∑ t ∈ Finset.range (T - 1), g t) ≤ gradientSum omega := by
      dsimp [gradientSum]
      rw [hTsplit, Finset.sum_range_succ]
      exact le_add_of_nonneg_right (nuclearNorm_nonneg _)
    have hsecond :
        (∑ t ∈ Finset.range (T - 1), g (t + 1)) ≤ gradientSum omega := by
      dsimp [gradientSum]
      rw [hTsplit, Finset.sum_range_succ']
      exact le_add_of_nonneg_right (nuclearNorm_nonneg _)
    calc
      variation omega ≤
          (∑ t ∈ Finset.range (T - 1), g t) +
            ∑ t ∈ Finset.range (T - 1), g (t + 1) := htriangle
      _ ≤ gradientSum omega + gradientSum omega := add_le_add hfirst hsecond
      _ = 2 * gradientSum omega := by ring
  have hintegral :
      (∫ omega, variation omega ∂mu) ≤
        ∫ omega, 2 * gradientSum omega ∂mu := by
    exact integral_mono hvariation_int (hgradient_int.const_mul 2) hpoint
  rw [integral_const_mul] at hintegral
  have hinv_nonneg : 0 ≤ ((T : ℝ)⁻¹) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hintegral hinv_nonneg
  dsimp [hvariation, stochasticGradientVariationAverageRealized,
    stochasticAverageNuclearGradientRealized, realizedExpectation]
  change (T : ℝ)⁻¹ * ∫ omega, variation omega ∂mu ≤
    2 * ((T : ℝ)⁻¹ * ∫ omega, gradientSum omega ∂mu)
  calc
    (T : ℝ)⁻¹ * ∫ omega, variation omega ∂mu ≤
        (T : ℝ)⁻¹ * (2 * ∫ omega, gradientSum omega ∂mu) := hscaled
    _ = 2 * ((T : ℝ)⁻¹ * ∫ omega, gradientSum omega ∂mu) := by ring

/- Combining the preceding estimate with the generated Taylor bridge bounds
   the mixed-Hessian contribution by the desired stationarity average itself
   plus the cubic remainder.  This is useful diagnostic progress, but it is
   deliberately not used as a source proof: the printed momentum coefficient
   multiplies the right-hand average by a non-absorbable factor near one
   momentum, as quantified immediately below. -/
theorem theorem_4_15_cross_average_realized_upper_bound_by_gradient_average
    {xi : Type*} [MeasurableSpace xi] {m n : ℕ}
    (P : StochasticProblem xi m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (hT : horizonDomain T) {s eta : ℝ}
    (hwd : stochasticMuonExpectationsWellDefined P cfg T)
    (hthird : ThirdDerivativeBounded P.objective s)
    (heta : ∀ k ∈ Finset.range T, cfg.eta k = eta)
    (heta_nonneg : 0 ≤ eta) :
    eta * stochasticHessianCrossAverageRealized P cfg T hwd.2.2.2 ≤
      2 * stochasticAverageNuclearGradientRealized P cfg T hwd.1 +
        ((T : ℝ)⁻¹) * ((T - 1 : ℕ) : ℝ) *
          (s * eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2) := by
  let hvariation :=
    stochasticGradientVariationAverage_wellDefined_of_gradientAverage
      P cfg T hwd.1
  have hcross := theorem_4_15_cross_average_realized_upper_bound_by_gradient_variation
    P cfg T hwd hthird heta heta_nonneg
  have hvariationBound :=
    stochasticGradientVariationAverageRealized_le_two_gradientAverage
      P cfg T hT hwd.1
  dsimp only at hcross hvariationBound
  linarith

/- The complete signed geometric history has an exact terminal-memory
   correction.  This keeps the mixed terms in the form in which they occur in
   the momentum recurrence: replacing the left side by a multiple of the
   unweighted sum discards the final (signed) history shown on the right. -/
theorem geometric_history_sum_exact_terminal_correction
    (beta : ℝ) (a : ℕ → ℝ) (T : ℕ) :
    (1 - beta) *
        (∑ t ∈ Finset.range (T + 1), ∑ i ∈ Finset.range t,
          beta ^ (t - i) * a i) =
      beta * (∑ i ∈ Finset.range T, a i) -
        beta * (∑ i ∈ Finset.range T, beta ^ (T - i) * a i) := by
  induction T with
  | zero => simp
  | succ T ih =>
      have hhistory :
          (∑ i ∈ Finset.range (T + 1), beta ^ (T + 1 - i) * a i) =
            beta *
              (a T + ∑ i ∈ Finset.range T, beta ^ (T - i) * a i) := by
        rw [Finset.sum_range_succ]
        have hprefix :
            (∑ i ∈ Finset.range T, beta ^ (T + 1 - i) * a i) =
              beta * (∑ i ∈ Finset.range T,
                beta ^ (T - i) * a i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          have hiT : i < T := Finset.mem_range.mp hi
          have hsub : T + 1 - i = (T - i) + 1 := by omega
          rw [hsub, pow_succ]
          ring
        rw [hprefix]
        simp
        ring
      have houter :
          (∑ t ∈ Finset.range ((T + 1) + 1), ∑ i ∈ Finset.range t,
              beta ^ (t - i) * a i) =
            (∑ t ∈ Finset.range (T + 1), ∑ i ∈ Finset.range t,
              beta ^ (t - i) * a i) +
              ∑ i ∈ Finset.range (T + 1), beta ^ (T + 1 - i) * a i := by
        rw [Finset.sum_range_succ]
      have ha :
          (∑ i ∈ Finset.range (T + 1), a i) =
            (∑ i ∈ Finset.range T, a i) + a T := by
        rw [Finset.sum_range_succ]
      rw [houter, ha, hhistory]
      linear_combination ih

/- If each signed input is approximated after multiplication by the step
   size, the exact terminal correction transfers that approximation to the
   complete geometric history without replacing it by an unweighted sum.
   The surviving coefficient `1 - beta^(T-i)` is precisely the cancellation
   contributed by terminal momentum memory. -/
theorem geometric_history_sum_le_of_abs_approximation
    (beta eta K : ℝ) (a v : ℕ → ℝ) (T : ℕ)
    (hbeta_nonneg : 0 ≤ beta) (hbeta_le_one : beta ≤ 1)
    (happrox : ∀ i ∈ Finset.range T, |v i - eta * a i| ≤ K) :
    eta * (1 - beta) *
        (∑ t ∈ Finset.range (T + 1), ∑ i ∈ Finset.range t,
          beta ^ (t - i) * a i) ≤
      beta * ∑ i ∈ Finset.range T,
        (1 - beta ^ (T - i)) * (v i + K) := by
  have hexact := geometric_history_sum_exact_terminal_correction beta a T
  have hrewrite :
      eta * (1 - beta) *
          (∑ t ∈ Finset.range (T + 1), ∑ i ∈ Finset.range t,
            beta ^ (t - i) * a i) =
        beta * ∑ i ∈ Finset.range T,
          (1 - beta ^ (T - i)) * (eta * a i) := by
    calc
      eta * (1 - beta) *
          (∑ t ∈ Finset.range (T + 1), ∑ i ∈ Finset.range t,
            beta ^ (t - i) * a i) =
          eta * ((1 - beta) *
            (∑ t ∈ Finset.range (T + 1), ∑ i ∈ Finset.range t,
              beta ^ (t - i) * a i)) := by ring
      _ = eta * (beta * (∑ i ∈ Finset.range T, a i) -
          beta * (∑ i ∈ Finset.range T, beta ^ (T - i) * a i)) := by
        rw [hexact]
      _ = beta * ∑ i ∈ Finset.range T,
          (1 - beta ^ (T - i)) * (eta * a i) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
  rw [hrewrite]
  apply mul_le_mul_of_nonneg_left _ hbeta_nonneg
  apply Finset.sum_le_sum
  intro i hi
  have hpow_le : beta ^ (T - i) ≤ 1 := by
    exact pow_le_one₀ hbeta_nonneg hbeta_le_one
  have hcoeff_nonneg : 0 ≤ 1 - beta ^ (T - i) := sub_nonneg.mpr hpow_le
  have hterm : eta * a i ≤ v i + K := by
    have hneg := neg_le_abs (v i - eta * a i)
    linarith [happrox i hi]
  exact mul_le_mul_of_nonneg_left hterm hcoeff_nonneg

/- Specialization of the exact correction to the generated Algorithm 1 mixed
   Hessian terms appearing in `theorem_4_15_finite_sum_descent_with_history`.
   No directional, cross/Jstar, descent, or stationarity bound is assumed. -/
theorem theorem_4_15_weighted_cross_history_exact_terminal_correction
    {xi : Type*} [MeasurableSpace xi] {m n : ℕ}
    (P : StochasticProblem xi m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (hT : 0 < T) :
    (1 - cfg.beta) *
        (∑ t ∈ Finset.range T, ∑ i ∈ Finset.range t,
          cfg.beta ^ (t - i) *
            (∫ omega, stochasticHessianCrossTerm P cfg omega i
              ∂(samplePathLaw P cfg.batchSize))) =
      cfg.beta *
          (∑ i ∈ Finset.range (T - 1),
            (∫ omega, stochasticHessianCrossTerm P cfg omega i
              ∂(samplePathLaw P cfg.batchSize))) -
        cfg.beta *
          (∑ i ∈ Finset.range (T - 1), cfg.beta ^ (T - 1 - i) *
            (∫ omega, stochasticHessianCrossTerm P cfg omega i
              ∂(samplePathLaw P cfg.batchSize))) := by
  have hTsplit : T = (T - 1) + 1 := by omega
  rw [hTsplit]
  simpa using
    (geometric_history_sum_exact_terminal_correction cfg.beta
      (fun i =>
        ∫ omega, stochasticHessianCrossTerm P cfg omega i
          ∂(samplePathLaw P cfg.batchSize)) (T - 1))

/- On each exact Algorithm 1 path, the complete mixed-Hessian history can be
   made cross-free while retaining the terminal-memory weights.  Unlike the
   exhausted total-variation substitution, this statement does not replace
   `1 - beta^(T-1-i)` by one and therefore records the full cancellation
   available from the momentum recurrence. -/
theorem theorem_4_15_weighted_cross_history_pathwise_upper_bound
    {xi : Type*} [MeasurableSpace xi] {m n : ℕ}
    (P : StochasticProblem xi m n) (cfg : StochasticMuonConfig m n)
    (omega : SamplePath xi cfg.batchSize) (T : ℕ) (hT : 0 < T)
    {s eta : ℝ}
    (hthird : ThirdDerivativeBounded P.objective s)
    (heta : ∀ k ∈ Finset.range T, cfg.eta k = eta)
    (heta_nonneg : 0 ≤ eta) :
    eta * (1 - cfg.beta) *
        (∑ t ∈ Finset.range T, ∑ i ∈ Finset.range t,
          cfg.beta ^ (t - i) * stochasticHessianCrossTerm P cfg omega i) ≤
      cfg.beta * ∑ i ∈ Finset.range (T - 1),
        (1 - cfg.beta ^ (T - 1 - i)) *
          (nuclearNorm
              (P.objective.grad (stochasticMuonState P cfg omega i).W -
                P.objective.grad
                  (stochasticMuonState P cfg omega (i + 1)).W) +
            s * eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2) := by
  have hTsplit : T = (T - 1) + 1 := by omega
  rw [hTsplit]
  apply geometric_history_sum_le_of_abs_approximation
    cfg.beta eta
      (s * eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2)
    (fun i => stochasticHessianCrossTerm P cfg omega i)
    (fun i => nuclearNorm
      (P.objective.grad (stochasticMuonState P cfg omega i).W -
        P.objective.grad (stochasticMuonState P cfg omega (i + 1)).W))
    (T - 1) cfg.beta_mem.1 cfg.beta_mem.2.le
  intro i hi
  have hiT : i ∈ Finset.range T := Finset.mem_range.mpr (by
    have hii : i < T - 1 := Finset.mem_range.mp hi
    omega)
  exact theorem_4_15_gradient_increment_cross_approximation
    P cfg omega hiT hthird heta heta_nonneg

/- The same per-step Taylor approximation holds after expectation on the
   generated path law.  Integrability is discharged from the existing
   generated expectation witness and source regularity, rather than added as
   an independent premise. -/
theorem theorem_4_15_gradient_increment_cross_expectation_approximation
    {xi : Type*} [MeasurableSpace xi] {m n : ℕ}
    (P : StochasticProblem xi m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) {i : ℕ} (hi : i ∈ Finset.range (T - 1)) {s eta : ℝ}
    (hwd : stochasticMuonExpectationsWellDefined P cfg T)
    (hthird : ThirdDerivativeBounded P.objective s)
    (heta : ∀ k ∈ Finset.range T, cfg.eta k = eta)
    (heta_nonneg : 0 ≤ eta) :
    |(∫ omega,
        nuclearNorm
          (P.objective.grad (stochasticMuonState P cfg omega i).W -
            P.objective.grad
              (stochasticMuonState P cfg omega (i + 1)).W)
          ∂(samplePathLaw P cfg.batchSize)) -
        eta * (∫ omega, stochasticHessianCrossTerm P cfg omega i
          ∂(samplePathLaw P cfg.batchSize))| ≤
      s * eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2 := by
  let mu := samplePathLaw P cfg.batchSize
  let variation : SamplePath xi cfg.batchSize → ℝ := fun omega =>
    nuclearNorm
      (P.objective.grad (stochasticMuonState P cfg omega i).W -
        P.objective.grad (stochasticMuonState P cfg omega (i + 1)).W)
  let cross : SamplePath xi cfg.batchSize → ℝ := fun omega =>
    stochasticHessianCrossTerm P cfg omega i
  let K : ℝ :=
    s * eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2
  letI : IsProbabilityMeasure P.sampleLaw := P.isProbability_sampleLaw
  letI : IsProbabilityMeasure mu := by
    dsimp [mu, samplePathLaw]
    infer_instance
  have hiT : i ∈ Finset.range T := Finset.mem_range.mpr (by
    have hii : i < T - 1 := Finset.mem_range.mp hi
    omega)
  have hvariation_all :=
    stochasticGradientVariationAverage_wellDefined_of_gradientAverage
      P cfg T hwd.1
  have hvariation_sum : Integrable
      (fun omega : SamplePath xi cfg.batchSize =>
        ∑ t ∈ Finset.range (T - 1),
          nuclearNorm
            (P.objective.grad (stochasticMuonState P cfg omega t).W -
              P.objective.grad
                (stochasticMuonState P cfg omega (t + 1)).W)) mu := by
    simpa [mu, stochasticGradientVariationAverageWellDefined,
      SOptLib.expectationWellDefined] using hvariation_all
  have hvariation_meas : Measurable variation := by
    dsimp [variation]
    exact nuclearNorm_measurable.comp
      (((objectiveGradient_measurable P.objective.f).comp
          (stochasticMuon_W_measurable P cfg i)).sub
        ((objectiveGradient_measurable P.objective.f).comp
          (stochasticMuon_W_measurable P cfg (i + 1))))
  have hvariation_int : Integrable variation mu := by
    apply hvariation_sum.mono' hvariation_meas.aestronglyMeasurable
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (nuclearNorm_nonneg _)]
    exact Finset.single_le_sum
      (fun k _hk => nuclearNorm_nonneg
        (P.objective.grad (stochasticMuonState P cfg omega k).W -
          P.objective.grad (stochasticMuonState P cfg omega (k + 1)).W)) hi
  have hDt_meas : Measurable
      (fun omega : SamplePath xi cfg.batchSize =>
        stochasticMuonDirection P cfg omega i) :=
    orthogonalizedDirection_measurable.comp (stochasticMuon_M_measurable P cfg i)
  have hDg_meas : Measurable
      (fun omega : SamplePath xi cfg.batchSize =>
        stochasticGradientDifferenceDirection P cfg omega i) := by
    unfold stochasticGradientDifferenceDirection
    exact orthogonalizedDirection_measurable.comp
      ((hthird.gradient_continuous.measurable.comp
          (stochasticMuon_W_measurable P cfg i)).sub
        (hthird.gradient_continuous.measurable.comp
          (stochasticMuon_W_measurable P cfg (i + 1))))
  have hDt_bound (omega : SamplePath xi cfg.batchSize) :
      frobeniusNorm (stochasticMuonDirection P cfg omega i) ≤
        Real.sqrt (matrixRankBound m n : ℝ) := by
    exact frobeniusNorm_le_sqrt_rankBound_of_isThinSVDWithPolar
      (orthogonalizedDirection_isThinSVDWithPolar
        (stochasticMuonState P cfg omega i).M)
  have hDg_bound (omega : SamplePath xi cfg.batchSize) :
      frobeniusNorm (stochasticGradientDifferenceDirection P cfg omega i) ≤
        Real.sqrt (matrixRankBound m n : ℝ) := by
    unfold stochasticGradientDifferenceDirection
    exact frobeniusNorm_le_sqrt_rankBound_of_isThinSVDWithPolar
      (orthogonalizedDirection_isThinSVDWithPolar _)
  have hcross_int : Integrable cross mu := by
    simpa [cross, mu, stochasticHessianCrossTerm] using
      stochasticHessianBilinearTerm_integrable_of_source_regularity
        P cfg i hthird
        (fun omega => stochasticGradientDifferenceDirection P cfg omega i)
        (fun omega => stochasticMuonDirection P cfg omega i)
        hDg_meas hDt_meas hDg_bound hDt_bound
  have hgap_int : Integrable (fun omega => variation omega - eta * cross omega) mu :=
    hvariation_int.sub (hcross_int.const_mul eta)
  have hpoint (omega : SamplePath xi cfg.batchSize) :
      |variation omega - eta * cross omega| ≤ K := by
    simpa [variation, cross, K] using
      theorem_4_15_gradient_increment_cross_approximation
        P cfg omega hiT hthird heta heta_nonneg
  have hmean :
      |∫ omega, variation omega - eta * cross omega ∂mu| ≤ K := by
    calc
      |∫ omega, variation omega - eta * cross omega ∂mu| ≤
          ∫ omega, |variation omega - eta * cross omega| ∂mu :=
        abs_integral_le_integral_abs
      _ ≤ ∫ _omega, K ∂mu := by
        exact integral_mono hgap_int.abs (integrable_const K) hpoint
      _ = K := by
        rw [integral_const, measureReal_univ_eq_one, one_smul]
  rw [integral_sub hvariation_int (hcross_int.const_mul eta),
    integral_const_mul] at hmean
  simpa [variation, cross, K, mu] using hmean

/- Weighting preserves the two-sided content of a pointwise absolute
   approximation.  This elementary form is kept separate from the geometric
   history identity: it makes explicit that nonnegative terminal-memory
   weights cannot turn an approximation into a new independent estimate. -/
theorem weighted_sum_abs_approximation
    (eta K : ℝ) (weight value approximation : ℕ → ℝ) (T : ℕ)
    (hweight : ∀ i ∈ Finset.range T, 0 ≤ weight i)
    (happrox : ∀ i ∈ Finset.range T,
      |value i - eta * approximation i| ≤ K) :
    |(∑ i ∈ Finset.range T, weight i * value i) -
        eta * (∑ i ∈ Finset.range T, weight i * approximation i)| ≤
      (∑ i ∈ Finset.range T, weight i) * K := by
  have hrearrange :
      (∑ i ∈ Finset.range T, weight i * value i) -
          eta * (∑ i ∈ Finset.range T, weight i * approximation i) =
        ∑ i ∈ Finset.range T,
          weight i * (value i - eta * approximation i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [hrearrange]
  calc
    |∑ i ∈ Finset.range T,
        weight i * (value i - eta * approximation i)| ≤
        ∑ i ∈ Finset.range T,
          |weight i * (value i - eta * approximation i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range T,
          weight i * |value i - eta * approximation i| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, abs_of_nonneg (hweight i hi)]
    _ ≤ ∑ i ∈ Finset.range T, weight i * K := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (happrox i hi) (hweight i hi)
    _ = (∑ i ∈ Finset.range T, weight i) * K := by
      rw [Finset.sum_mul]

/- On the exact generated path law, the terminal-weighted consecutive-gradient
   variation and the terminal-weighted mixed-Hessian contribution are the same
   object up to the accumulated third-order Taylor remainder.  In particular,
   replacing the latter by the former in the finite-sum descent inequality does
   not create a quantity controlled by the source directional-J premise. -/
theorem theorem_4_15_terminal_weighted_gradient_variation_cross_abs_bound
    {xi : Type*} [MeasurableSpace xi] {m n : ℕ}
    (P : StochasticProblem xi m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) {s eta : ℝ}
    (hwd : stochasticMuonExpectationsWellDefined P cfg T)
    (hthird : ThirdDerivativeBounded P.objective s)
    (heta : ∀ k ∈ Finset.range T, cfg.eta k = eta)
    (heta_nonneg : 0 ≤ eta) :
    |(∑ i ∈ Finset.range (T - 1),
          (1 - cfg.beta ^ (T - 1 - i)) *
            (∫ omega,
              nuclearNorm
                (P.objective.grad (stochasticMuonState P cfg omega i).W -
                  P.objective.grad
                    (stochasticMuonState P cfg omega (i + 1)).W)
              ∂(samplePathLaw P cfg.batchSize))) -
        eta * (∑ i ∈ Finset.range (T - 1),
          (1 - cfg.beta ^ (T - 1 - i)) *
            (∫ omega, stochasticHessianCrossTerm P cfg omega i
              ∂(samplePathLaw P cfg.batchSize)))| ≤
      (∑ i ∈ Finset.range (T - 1),
          (1 - cfg.beta ^ (T - 1 - i))) *
        (s * eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2) := by
  apply weighted_sum_abs_approximation eta
    (s * eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2)
    (fun i => 1 - cfg.beta ^ (T - 1 - i))
    (fun i =>
      ∫ omega,
        nuclearNorm
          (P.objective.grad (stochasticMuonState P cfg omega i).W -
            P.objective.grad (stochasticMuonState P cfg omega (i + 1)).W)
        ∂(samplePathLaw P cfg.batchSize))
    (fun i =>
      ∫ omega, stochasticHessianCrossTerm P cfg omega i
        ∂(samplePathLaw P cfg.batchSize))
    (T - 1)
  · intro i _hi
    exact sub_nonneg.mpr
      (pow_le_one₀ cfg.beta_mem.1 cfg.beta_mem.2.le)
  · intro i hi
    exact theorem_4_15_gradient_increment_cross_expectation_approximation
      P cfg T hi hwd hthird heta heta_nonneg

/- The reverse one-sided consequence is the route-closing half absent from the
   preceding upper-bound-only formulation.  Any upper control of the terminal
   variation therefore supplies, up to the displayed remainder, exactly the
   missing weighted cross control rather than bypassing it. -/
theorem theorem_4_15_terminal_weighted_gradient_variation_upper_bound
    {xi : Type*} [MeasurableSpace xi] {m n : ℕ}
    (P : StochasticProblem xi m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) {s eta : ℝ}
    (hwd : stochasticMuonExpectationsWellDefined P cfg T)
    (hthird : ThirdDerivativeBounded P.objective s)
    (heta : ∀ k ∈ Finset.range T, cfg.eta k = eta)
    (heta_nonneg : 0 ≤ eta) :
    (∑ i ∈ Finset.range (T - 1),
        (1 - cfg.beta ^ (T - 1 - i)) *
          (∫ omega,
            nuclearNorm
              (P.objective.grad (stochasticMuonState P cfg omega i).W -
                P.objective.grad
                  (stochasticMuonState P cfg omega (i + 1)).W)
            ∂(samplePathLaw P cfg.batchSize))) ≤
      eta * (∑ i ∈ Finset.range (T - 1),
        (1 - cfg.beta ^ (T - 1 - i)) *
          (∫ omega, stochasticHessianCrossTerm P cfg omega i
            ∂(samplePathLaw P cfg.batchSize))) +
        (∑ i ∈ Finset.range (T - 1),
          (1 - cfg.beta ^ (T - 1 - i))) *
          (s * eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2) := by
  have habs :=
    theorem_4_15_terminal_weighted_gradient_variation_cross_abs_bound
      P cfg T hwd hthird heta heta_nonneg
  have hle := le_abs_self
    ((∑ i ∈ Finset.range (T - 1),
        (1 - cfg.beta ^ (T - 1 - i)) *
          (∫ omega,
            nuclearNorm
              (P.objective.grad (stochasticMuonState P cfg omega i).W -
                P.objective.grad
                  (stochasticMuonState P cfg omega (i + 1)).W)
            ∂(samplePathLaw P cfg.batchSize))) -
      eta * (∑ i ∈ Finset.range (T - 1),
        (1 - cfg.beta ^ (T - 1 - i)) *
          (∫ omega, stochasticHessianCrossTerm P cfg omega i
            ∂(samplePathLaw P cfg.batchSize))))
  linarith

/- Expected, generated-process version of the terminal-corrected pathwise
   estimate.  Its right side contains neither the mixed curvature average,
   `Jstar`, nor the desired stationarity average. -/
theorem theorem_4_15_weighted_cross_history_expectation_upper_bound
    {xi : Type*} [MeasurableSpace xi] {m n : ℕ}
    (P : StochasticProblem xi m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (hT : 0 < T) {s eta : ℝ}
    (hwd : stochasticMuonExpectationsWellDefined P cfg T)
    (hthird : ThirdDerivativeBounded P.objective s)
    (heta : ∀ k ∈ Finset.range T, cfg.eta k = eta)
    (heta_nonneg : 0 ≤ eta) :
    eta * (1 - cfg.beta) *
        (∑ t ∈ Finset.range T, ∑ i ∈ Finset.range t,
          cfg.beta ^ (t - i) *
            (∫ omega, stochasticHessianCrossTerm P cfg omega i
              ∂(samplePathLaw P cfg.batchSize))) ≤
      cfg.beta * ∑ i ∈ Finset.range (T - 1),
        (1 - cfg.beta ^ (T - 1 - i)) *
          ((∫ omega,
              nuclearNorm
                (P.objective.grad (stochasticMuonState P cfg omega i).W -
                  P.objective.grad
                    (stochasticMuonState P cfg omega (i + 1)).W)
              ∂(samplePathLaw P cfg.batchSize)) +
            s * eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2) := by
  have hTsplit : T = (T - 1) + 1 := by omega
  rw [hTsplit]
  apply geometric_history_sum_le_of_abs_approximation
    cfg.beta eta
      (s * eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2)
    (fun i =>
      ∫ omega, stochasticHessianCrossTerm P cfg omega i
        ∂(samplePathLaw P cfg.batchSize))
    (fun i =>
      ∫ omega,
        nuclearNorm
          (P.objective.grad (stochasticMuonState P cfg omega i).W -
            P.objective.grad (stochasticMuonState P cfg omega (i + 1)).W)
        ∂(samplePathLaw P cfg.batchSize))
    (T - 1) cfg.beta_mem.1 cfg.beta_mem.2.le
  intro i hi
  exact theorem_4_15_gradient_increment_cross_expectation_approximation
    P cfg T hi hwd hthird heta heta_nonneg

/- Substitution into the retained finite-sum descent theorem gives a genuinely
   cross-free generated inequality.  The unresolved quantity is now the
   terminal-corrected variation of consecutive objective gradients; no
   occurrence of the cross average, `Jstar`, or the desired stationarity
   average remains on the right-hand side. -/
theorem theorem_4_15_finite_sum_descent_with_terminal_corrected_variation
    {xi : Type*} [MeasurableSpace xi] {m n : ℕ}
    (P : StochasticProblem xi m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (s sigma eta : ℝ)
    (hsrc : theorem_4_15_sourceDomain T eta)
    (hwd : stochasticMuonExpectationsWellDefined P cfg T)
    (hthird : ThirdDerivativeBounded P.objective s)
    (hvariance : BoundedVariance P sigma)
    (heta : ∀ k ∈ Finset.range T, cfg.eta k = eta) :
    eta * ∑ t ∈ Finset.range T,
        (∫ omega,
          nuclearNorm (P.objective.grad (stochasticMuonState P cfg omega t).W)
        ∂(samplePathLaw P cfg.batchSize)) ≤
      stochasticExpectedObjectiveDrop P cfg T +
        eta ^ 2 / 2 * ∑ t ∈ Finset.range T,
          (∫ omega, stochasticHessianDirectionalTerm P cfg omega t
            ∂(samplePathLaw P cfg.batchSize)) +
        (T : ℝ) *
          (s * eta ^ 3 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6) +
        2 * eta *
          ((T : ℝ) * Real.sqrt (matrixRankBound m n : ℝ) *
              (Real.sqrt ((1 - cfg.beta) / (1 + cfg.beta)) * sigma /
                Real.sqrt (cfg.batchSize.val : ℝ)) +
            Real.sqrt (matrixRankBound m n : ℝ) *
              (sigma / Real.sqrt (cfg.batchSize.val : ℝ)) / (1 - cfg.beta) +
            cfg.beta / (1 - cfg.beta) *
              (∑ i ∈ Finset.range (T - 1),
                (1 - cfg.beta ^ (T - 1 - i)) *
                  ((∫ omega,
                      nuclearNorm
                        (P.objective.grad
                            (stochasticMuonState P cfg omega i).W -
                          P.objective.grad
                            (stochasticMuonState P cfg omega (i + 1)).W)
                      ∂(samplePathLaw P cfg.batchSize)) +
                    s * eta ^ 2 *
                      Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2)) +
            (T : ℝ) *
              (s * eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) *
                cfg.beta / (2 * (1 - cfg.beta)))) := by
  let history : ℝ :=
    ∑ t ∈ Finset.range T, ∑ i ∈ Finset.range t,
      cfg.beta ^ (t - i) *
        (∫ omega, stochasticHessianCrossTerm P cfg omega i
          ∂(samplePathLaw P cfg.batchSize))
  let weightedVariation : ℝ :=
    ∑ i ∈ Finset.range (T - 1),
      (1 - cfg.beta ^ (T - 1 - i)) *
        ((∫ omega,
            nuclearNorm
              (P.objective.grad (stochasticMuonState P cfg omega i).W -
                P.objective.grad
                  (stochasticMuonState P cfg omega (i + 1)).W)
            ∂(samplePathLaw P cfg.batchSize)) +
          s * eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2)
  have hfinite := theorem_4_15_finite_sum_descent_with_history
    P cfg T s sigma eta hsrc hthird hvariance heta
  have hcorrected :=
    theorem_4_15_weighted_cross_history_expectation_upper_bound
      P cfg T hsrc.1.1 hwd hthird heta hsrc.2.le
  have hden : 0 < 1 - cfg.beta := sub_pos.mpr cfg.beta_mem.2
  have hhistory_bound :
      eta * history ≤ cfg.beta / (1 - cfg.beta) * weightedVariation := by
    rw [show cfg.beta / (1 - cfg.beta) * weightedVariation =
      (cfg.beta * weightedVariation) / (1 - cfg.beta) by ring]
    apply (le_div_iff₀ hden).2
    calc
      (eta * history) * (1 - cfg.beta) =
          eta * (1 - cfg.beta) * history := by ring
      _ ≤ cfg.beta * weightedVariation := by
        simpa [history, weightedVariation] using hcorrected
  have hscale : 0 ≤ 2 * eta := mul_nonneg (by norm_num) hsrc.2.le
  calc
    eta * ∑ t ∈ Finset.range T,
        (∫ omega,
          nuclearNorm (P.objective.grad (stochasticMuonState P cfg omega t).W)
        ∂(samplePathLaw P cfg.batchSize)) ≤
      stochasticExpectedObjectiveDrop P cfg T +
        eta ^ 2 / 2 * ∑ t ∈ Finset.range T,
          (∫ omega, stochasticHessianDirectionalTerm P cfg omega t
            ∂(samplePathLaw P cfg.batchSize)) +
        (T : ℝ) *
          (s * eta ^ 3 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6) +
        2 * eta *
          ((T : ℝ) * Real.sqrt (matrixRankBound m n : ℝ) *
              (Real.sqrt ((1 - cfg.beta) / (1 + cfg.beta)) * sigma /
                Real.sqrt (cfg.batchSize.val : ℝ)) +
            Real.sqrt (matrixRankBound m n : ℝ) *
              (sigma / Real.sqrt (cfg.batchSize.val : ℝ)) / (1 - cfg.beta) +
            eta * history +
            (T : ℝ) *
              (s * eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) *
                cfg.beta / (2 * (1 - cfg.beta)))) := by
          simpa [history] using hfinite
    _ ≤ stochasticExpectedObjectiveDrop P cfg T +
        eta ^ 2 / 2 * ∑ t ∈ Finset.range T,
          (∫ omega, stochasticHessianDirectionalTerm P cfg omega t
            ∂(samplePathLaw P cfg.batchSize)) +
        (T : ℝ) *
          (s * eta ^ 3 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6) +
        2 * eta *
          ((T : ℝ) * Real.sqrt (matrixRankBound m n : ℝ) *
              (Real.sqrt ((1 - cfg.beta) / (1 + cfg.beta)) * sigma /
                Real.sqrt (cfg.batchSize.val : ℝ)) +
            Real.sqrt (matrixRankBound m n : ℝ) *
              (sigma / Real.sqrt (cfg.batchSize.val : ℝ)) / (1 - cfg.beta) +
            cfg.beta / (1 - cfg.beta) * weightedVariation +
            (T : ℝ) *
              (s * eta ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) *
                cfg.beta / (2 * (1 - cfg.beta)))) := by
          gcongr
    _ = _ := by rfl

/- The cross term in `theorem_4_15_source_average_bound_at_horizon` is
   multiplied by `2 * eta * beta / (1 - beta)`.  Consequently, an upper bound
   on the cross average obtained only by dividing a gradient-variation bound
   by `eta` would have to absorb the scalar below.  The printed otherwise
   schedule makes that impossible at sufficiently small accuracy: `beta`
   approaches one at the `epsilon^2` scale.  This is a generated-run schedule
   consequence, not a counterexample to the source theorem and not an extra
   premise of its public endpoint. -/
theorem theorem_4_15_otherwise_source_small_j_cross_absorption_fails
    {xi : Type*} [MeasurableSpace xi] {m n : ℕ}
    (P : StochasticProblem xi m n)
    (cfgForAccuracyHorizon : ℝ → ℕ → StochasticMuonConfig m n)
    (W0 : Mat m n) (sigma Delta epsilon C s : ℝ)
    (betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ)
    (N : ℕ)
    (hN : theorem_4_15_otherwiseSourceSmallJGeneratedRunForAccuracyHorizon P
      cfgForAccuracyHorizon W0 sigma Delta epsilon C s
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N)
    (hsmall : betaUpper * epsilon ^ 2 ≤
      (matrixRankBound m n : ℝ) * sigma ^ 2 / 2) :
    1 ≤ 2 * (cfgForAccuracyHorizon epsilon N).beta /
      (1 - (cfgForAccuracyHorizon epsilon N).beta) := by
  rcases hN with
    ⟨_horizon, _hfinite, _hDelta, _hthird, _hvariance, _hwd, _hW0, hschedule,
      _hsource, _hHorizon, _hregDom, _hregime⟩
  rcases hschedule with
    ⟨hscheduleDom, _hbatch, hbeta, _heta, _hconstEta⟩
  rcases hscheduleDom with ⟨_horizon', hbetaDom, _hrankDom, _hetaDom⟩
  rcases hbeta with
    ⟨_hbetaLowerPos, _hbetaOrder, _hbetaLowerBound, hbetaUpperBound⟩
  let cfgN := cfgForAccuracyHorizon epsilon N
  let denominator : ℝ := (matrixRankBound m n : ℝ) * sigma ^ 2
  have hdenominator_nonneg : 0 ≤ denominator := by
    dsimp [denominator]
    positivity
  have hdenominator_ne : denominator ≠ 0 := by
    simpa [denominator, sourceQuotDomain] using hbetaDom
  have hdenominator_pos : 0 < denominator :=
    lt_of_le_of_ne hdenominator_nonneg (Ne.symm hdenominator_ne)
  have hscale :
      betaUpper * theorem_4_15_otherwiseOneMinusBetaScale
          m n sigma epsilon ≤ 1 / 2 := by
    unfold theorem_4_15_otherwiseOneMinusBetaScale sourceQuot
    change betaUpper * (epsilon ^ 2 / denominator) ≤ 1 / 2
    calc
      betaUpper * (epsilon ^ 2 / denominator) =
          (betaUpper * epsilon ^ 2) / denominator := by ring
      _ ≤ (denominator / 2) / denominator :=
        div_le_div_of_nonneg_right (by simpa [denominator] using hsmall)
          hdenominator_pos.le
      _ = 1 / 2 := by field_simp [hdenominator_ne]
  have hone_sub_beta : 1 - cfgN.beta ≤ 1 / 2 :=
    le_trans (by simpa [cfgN] using hbetaUpperBound) hscale
  have hbeta_half : 1 / 2 ≤ cfgN.beta := by linarith
  have hone_sub_beta_pos : 0 < 1 - cfgN.beta :=
    sub_pos.mpr cfgN.beta_mem.2
  apply (le_div_iff₀ hone_sub_beta_pos).2
  linarith

/- The actual periodic objective has a useful generated-prefix invariant that
   does not rely on the rejected constant-gradient-reversal toy pattern.  As
   long as the scalar phase stays in `(-pi / 2, pi / 2)`, every new gradient
   is a positive multiple of the one-dimensional coordinate matrix.  The
   momentum recursion therefore preserves a strictly positive coefficient,
   so its exact polar is the coordinate direction and the generated phase is
   exactly the initial phase minus `t * eta`.  This simultaneously discharges
   momentum nonvanishing on the whole prefix rather than assuming it. -/
theorem deterministicMomentumMuon_M_succ_eq_source_update
    {m n : ℕ} (P : Objective m n)
    (cfg : DeterministicMomentumMuonConfig m n) (t : ℕ) :
    (deterministicMomentumMuonState P cfg (t + 1)).M =
      cfg.beta • (deterministicMomentumMuonState P cfg t).M +
        (1 - cfg.beta) • deterministicGradient P
          (deterministicMomentumMuonState P cfg (t + 1)).W := by
  cases t <;> rfl

/- In one dimension the exact partial polar is the scalar sign, including at
   zero.  This packages the positive-rescaling and negation facts above into a
   formula that remains valid at every momentum switch.  In particular, later
   orbit calculations no longer need to assume that the generated momentum is
   nonzero. -/
theorem orthogonalizedDirection_eq_sign_smul_one_dimensional
    (A : Mat 1 1) :
    orthogonalizedDirection A =
      Real.sign (A 0 0) • coordinateMatrix 0 0 := by
  let E : Mat 1 1 := coordinateMatrix 0 0
  have hAeq : A = (A 0 0) • E := by
    ext i j
    fin_cases i
    fin_cases j
    simp [E, coordinateMatrix]
  by_cases hzero : A 0 0 = 0
  · have hAzero : A = 0 := by rw [hAeq, hzero, zero_smul]
    have hdirzero : orthogonalizedDirection (0 : Mat 1 1) = 0 := by
      unfold orthogonalizedDirection
      ext i j
      rw [Matrix.mul_apply]
      have hrank : (0 : Mat 1 1).rank = 0 := by simp
      apply Finset.sum_eq_zero
      intro k _hk
      have hklt : (k : ℕ) < 0 := by simpa [hrank] using k.isLt
      exact (Nat.not_lt_zero _ hklt).elim
    calc
      orthogonalizedDirection A = orthogonalizedDirection 0 := by rw [hAzero]
      _ = 0 := hdirzero
      _ = Real.sign (A 0 0) • coordinateMatrix 0 0 := by
        rw [hzero, Real.sign_zero, zero_smul]
  · by_cases hpos : 0 < A 0 0
    · have hE : E ≠ 0 := by
        intro hE
        have hentry := congrArg (fun M : Mat 1 1 => M 0 0) hE
        norm_num [E, coordinateMatrix] at hentry
      calc
        orthogonalizedDirection A =
            orthogonalizedDirection ((A 0 0) • E) :=
          congrArg orthogonalizedDirection hAeq
        _ = orthogonalizedDirection E :=
          orthogonalizedDirection_pos_smul_eq_one_dimensional E (A 0 0) hE hpos
        _ = E := theorem_4_15_periodicCandidate_coordinateDirection
        _ = Real.sign (A 0 0) • coordinateMatrix 0 0 := by
          rw [Real.sign_of_pos hpos, one_smul]
    · have hneg : A 0 0 < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hzero
      have hscaled : (A 0 0) • E = (-A 0 0) • (-E) := by module
      have hE : E ≠ 0 := by
        intro hE
        have hentry := congrArg (fun M : Mat 1 1 => M 0 0) hE
        norm_num [E, coordinateMatrix] at hentry
      calc
        orthogonalizedDirection A =
            orthogonalizedDirection ((A 0 0) • E) :=
          congrArg orthogonalizedDirection hAeq
        _ = orthogonalizedDirection ((-A 0 0) • (-E)) := by rw [hscaled]
        _ = orthogonalizedDirection (-E) :=
          orthogonalizedDirection_pos_smul_eq_one_dimensional (-E) (-A 0 0)
            (neg_ne_zero.mpr hE) (neg_pos.mpr hneg)
        _ = -orthogonalizedDirection E :=
          orthogonalizedDirection_neg_eq_neg_one_dimensional E hE
        _ = -E := by rw [theorem_4_15_periodicCandidate_coordinateDirection]
        _ = Real.sign (A 0 0) • coordinateMatrix 0 0 := by
          rw [Real.sign_of_neg hneg]
          module

/- On the strict positive ray the global cutoff is locally inactive, so the
   derivative of the actual fixed objective is the already computed derivative
   of the positive profile.  This is a local identity of the generated
   objective, not an assumed trajectory formula. -/
theorem theorem_4_15_nonperiodicCandidateGlobalProfile_hasDerivAt_of_pos
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt theorem_4_15_nonperiodicCandidateGlobalProfile
      (theorem_4_15_nonperiodicCandidatePositiveProfileFirst x) x := by
  have heq : theorem_4_15_nonperiodicCandidateGlobalProfile =ᶠ[nhds x]
      theorem_4_15_nonperiodicCandidatePositiveProfile := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact theorem_4_15_nonperiodicCandidateGlobalProfile_eq hy.le
  exact
    (theorem_4_15_nonperiodicCandidatePositiveProfile_hasDerivAt_first
      (by linarith : -1 < x)).congr_of_eventuallyEq heq

/- At the initial point, equality with the positive profile on the right-hand
   neighbourhood and uniqueness of the one-sided derivative identify the
   derivative of the smooth global P-factor. -/
theorem theorem_4_15_nonperiodicCandidateGlobalP_deriv_zero :
    deriv theorem_4_15_nonperiodicCandidateGlobalP 0 = 0 := by
  have hglobal : HasDerivAt theorem_4_15_nonperiodicCandidateGlobalP
      (deriv theorem_4_15_nonperiodicCandidateGlobalP 0) 0 :=
    (theorem_4_15_nonperiodicCandidateGlobalP_contDiff_three.differentiable
      (by norm_num)).differentiableAt.hasDerivAt
  have hpositive : HasDerivWithinAt theorem_4_15_nonperiodicCandidateGlobalP
      0 (Set.Ioi 0) 0 := by
    apply theorem_4_15_nonperiodicCandidateP_hasDerivAt_zero.hasDerivWithinAt.congr
    · intro x hx
      exact theorem_4_15_nonperiodicCandidateGlobalP_eq hx.le
    · exact theorem_4_15_nonperiodicCandidateGlobalP_eq (by norm_num : (0 : ℝ) ≤ 0)
  exact UniqueDiffWithinAt.eq_deriv (Set.Ioi 0) (uniqueDiffWithinAt_Ioi 0)
    hglobal.hasDerivWithinAt hpositive

theorem theorem_4_15_nonperiodicCandidateGlobalProfile_hasDerivAt_zero :
    HasDerivAt theorem_4_15_nonperiodicCandidateGlobalProfile (-2) 0 := by
  convert theorem_4_15_nonperiodicCandidateGlobalProfile_hasDerivAt 0 using 1
  rw [theorem_4_15_nonperiodicCandidateGlobalP_deriv_zero,
    theorem_4_15_nonperiodicCandidateGlobalP_eq (by norm_num),
    theorem_4_15_nonperiodicCandidate_initial_values.2.2]
  norm_num

theorem theorem_4_15_nonperiodicCandidateObjective_grad_of_pos
    (W : Mat 1 1) (hW : 0 < theorem_4_5_counterexampleEntry W) :
    theorem_4_15_nonperiodicCandidateObjective.grad W =
      theorem_4_15_nonperiodicCandidatePositiveProfileFirst
          (theorem_4_5_counterexampleEntry W) • coordinateMatrix 0 0 := by
  ext i j
  fin_cases i
  fin_cases j
  have hderiv : HasFDerivAt
      (fun X : Mat 1 1 => theorem_4_15_nonperiodicCandidateGlobalProfile
        (theorem_4_5_counterexampleEntry X))
      (theorem_4_5_counterexampleEntry.smulRight
        (theorem_4_15_nonperiodicCandidatePositiveProfileFirst
          (theorem_4_5_counterexampleEntry W))) W :=
    (theorem_4_15_nonperiodicCandidateGlobalProfile_hasDerivAt_of_pos hW).hasFDerivAt.comp
      W theorem_4_5_counterexampleEntry.hasFDerivAt
  rw [Objective.grad_eq_coordinate_fderiv]
  change fderiv ℝ
      (fun X : Mat 1 1 => theorem_4_15_nonperiodicCandidateGlobalProfile
        (theorem_4_5_counterexampleEntry X)) W (coordinateMatrix 0 0) = _
  rw [hderiv.fderiv]
  simp [coordinateMatrix]

theorem theorem_4_15_nonperiodicCandidateObjective_grad_zero :
    theorem_4_15_nonperiodicCandidateObjective.grad 0 =
      (-2 : ℝ) • coordinateMatrix 0 0 := by
  ext i j
  fin_cases i
  fin_cases j
  have hscalar : HasFDerivAt theorem_4_15_nonperiodicCandidateGlobalProfile
      (ContinuousLinearMap.toSpanSingleton ℝ (-2 : ℝ)) (0 : ℝ) :=
    theorem_4_15_nonperiodicCandidateGlobalProfile_hasDerivAt_zero.hasFDerivAt
  have hderiv : HasFDerivAt
      (fun X : Mat 1 1 => theorem_4_15_nonperiodicCandidateGlobalProfile
        (theorem_4_5_counterexampleEntry X))
      (theorem_4_5_counterexampleEntry.smulRight (-2 : ℝ)) 0 := by
    simpa only [Function.comp_apply, ContinuousLinearMap.toSpanSingleton_comp] using
      hscalar.comp (0 : Mat 1 1) theorem_4_5_counterexampleEntry.hasFDerivAt
  rw [Objective.grad_eq_coordinate_fderiv]
  change fderiv ℝ
      (fun X : Mat 1 1 => theorem_4_15_nonperiodicCandidateGlobalProfile
        (theorem_4_5_counterexampleEntry X)) 0 (coordinateMatrix 0 0) = _
  rw [hderiv.fderiv]
  simp [coordinateMatrix]

theorem theorem_4_15_nonperiodicCandidatePositiveProfileFirst_zero :
    theorem_4_15_nonperiodicCandidatePositiveProfileFirst 0 = -2 := by
  norm_num [theorem_4_15_nonperiodicCandidatePositiveProfileFirst,
    theorem_4_15_nonperiodicCandidatePFirst,
    theorem_4_15_nonperiodicCandidateQFirst,
    theorem_4_15_nonperiodicCandidateOscillation,
    theorem_4_15_nonperiodicCandidateOscillationFirst,
    theorem_4_15_nonperiodicCandidatePhaseFirst,
    theorem_4_15_nonperiodicCandidateQ,
    theorem_4_15_nonperiodicCandidateP,
    theorem_4_15_nonperiodicCandidatePhase]

def theorem_4_15_nonperiodicCandidateGradDerivative (W : Mat 1 1) :
    Mat 1 1 →L[ℝ] Mat 1 1 :=
  (theorem_4_5_counterexampleEntry.smulRight
    (theorem_4_15_nonperiodicCandidatePositiveProfileSecond
      (theorem_4_5_counterexampleEntry W))).smulRight
        (coordinateMatrix (m := 1) (n := 1) 0 0)

theorem theorem_4_15_nonperiodicCandidateObjective_hasFDerivAt_grad_of_pos
    (W : Mat 1 1) (hW : 0 < theorem_4_5_counterexampleEntry W) :
    HasFDerivAt theorem_4_15_nonperiodicCandidateObjective.grad
      (theorem_4_15_nonperiodicCandidateGradDerivative W) W := by
  have hpointwise : HasFDerivAt
      (fun X : Mat 1 1 =>
        theorem_4_15_nonperiodicCandidatePositiveProfileFirst
            (theorem_4_5_counterexampleEntry X) • coordinateMatrix 0 0)
      (theorem_4_15_nonperiodicCandidateGradDerivative W) W := by
    exact
      ((theorem_4_15_nonperiodicCandidatePositiveProfileFirst_hasDerivAt
          (by linarith : -1 < theorem_4_5_counterexampleEntry W)).hasFDerivAt.comp
        W theorem_4_5_counterexampleEntry.hasFDerivAt).smul_const
          (coordinateMatrix (m := 1) (n := 1) 0 0)
  have heq : theorem_4_15_nonperiodicCandidateObjective.grad =ᶠ[nhds W]
      (fun X : Mat 1 1 =>
        theorem_4_15_nonperiodicCandidatePositiveProfileFirst
            (theorem_4_5_counterexampleEntry X) • coordinateMatrix 0 0) := by
    have hcontinuous : Continuous theorem_4_5_counterexampleEntry :=
      theorem_4_5_counterexampleEntry.continuous
    filter_upwards [hcontinuous.continuousAt.eventually
      (eventually_gt_nhds hW)] with X hX
    exact theorem_4_15_nonperiodicCandidateObjective_grad_of_pos X hX
  exact hpointwise.congr_of_eventuallyEq heq

theorem theorem_4_15_nonperiodicCandidateObjective_hessianBilinear_of_pos
    (W A B : Mat 1 1) (hW : 0 < theorem_4_5_counterexampleEntry W) :
    hessianBilinear theorem_4_15_nonperiodicCandidateObjective W A B =
      theorem_4_15_nonperiodicCandidatePositiveProfileSecond
          (theorem_4_5_counterexampleEntry W) * A 0 0 * B 0 0 := by
  unfold hessianBilinear
  rw [(theorem_4_15_nonperiodicCandidateObjective_hasFDerivAt_grad_of_pos
    W hW).fderiv]
  simp only [frobeniusInner, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton]
  simp [theorem_4_15_nonperiodicCandidateGradDerivative, coordinateMatrix]
  ring

theorem theorem_4_15_nonperiodicCandidate_directionalTerm_of_pos
    (cfg : DeterministicMomentumMuonConfig 1 1) (t : ℕ)
    (hW : 0 < theorem_4_5_counterexampleEntry
      (deterministicMomentumMuonState
        theorem_4_15_nonperiodicCandidateObjective cfg t).W) :
    deterministicMomentumHessianDirectionalTerm
        theorem_4_15_nonperiodicCandidateObjective cfg t =
      theorem_4_15_nonperiodicCandidatePositiveProfileSecond
          (theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_nonperiodicCandidateObjective cfg t).W) *
        (orthogonalizedDirection
          (deterministicMomentumMuonState
            theorem_4_15_nonperiodicCandidateObjective cfg t).M 0 0) ^ 2 := by
  unfold deterministicMomentumHessianDirectionalTerm
  rw [theorem_4_15_nonperiodicCandidateObjective_hessianBilinear_of_pos _ _ _ hW]
  ring

/- These are the exact scalar recurrences of the fixed nonperiodic candidate on
   every generated step whose new iterate lies on the strict positive ray.
   The first component is unconditional and uses the exact one-dimensional
   partial polar; the second uses the proved objective gradient formula. -/
theorem theorem_4_15_nonperiodicCandidate_full_orbit_scalar_recurrence
    (cfg : DeterministicMomentumMuonConfig 1 1) (t : ℕ)
    (hnext : 0 < theorem_4_5_counterexampleEntry
      (deterministicMomentumMuonState
        theorem_4_15_nonperiodicCandidateObjective cfg (t + 1)).W) :
    let state := deterministicMomentumMuonState
      theorem_4_15_nonperiodicCandidateObjective cfg t
    let nextState := deterministicMomentumMuonState
      theorem_4_15_nonperiodicCandidateObjective cfg (t + 1)
    theorem_4_5_counterexampleEntry nextState.W =
        theorem_4_5_counterexampleEntry state.W -
          cfg.eta t * Real.sign (state.M 0 0) ∧
      nextState.M 0 0 =
        cfg.beta * state.M 0 0 +
          (1 - cfg.beta) *
            theorem_4_15_nonperiodicCandidatePositiveProfileFirst
              (theorem_4_5_counterexampleEntry nextState.W) := by
  dsimp only
  constructor
  · rw [deterministicMomentumMuon_W_succ_eq_source_update,
      orthogonalizedDirection_eq_sign_smul_one_dimensional]
    simp [theorem_4_5_counterexampleEntry_apply, coordinateMatrix]
  · rw [deterministicMomentumMuon_M_succ_eq_source_update]
    unfold deterministicGradient
    rw [theorem_4_15_nonperiodicCandidateObjective_grad_of_pos _ hnext]
    simp [coordinateMatrix]

/- Adding `P(x_t)` to the momentum exposes the cancellation designed into the
   fixed objective: the potentially large `P'` contribution survives only in
   a one-step finite-difference defect. -/
theorem theorem_4_15_nonperiodicCandidate_transformed_momentum_recurrence
    (cfg : DeterministicMomentumMuonConfig 1 1) (t : ℕ)
    (hnext : 0 < theorem_4_5_counterexampleEntry
      (deterministicMomentumMuonState
        theorem_4_15_nonperiodicCandidateObjective cfg (t + 1)).W) :
    let state := deterministicMomentumMuonState
      theorem_4_15_nonperiodicCandidateObjective cfg t
    let nextState := deterministicMomentumMuonState
      theorem_4_15_nonperiodicCandidateObjective cfg (t + 1)
    nextState.M 0 0 + theorem_4_15_nonperiodicCandidateP
        (theorem_4_5_counterexampleEntry nextState.W) =
      cfg.beta * (state.M 0 0 + theorem_4_15_nonperiodicCandidateP
        (theorem_4_5_counterexampleEntry state.W)) +
      cfg.beta * (theorem_4_15_nonperiodicCandidateP
          (theorem_4_5_counterexampleEntry nextState.W) -
        theorem_4_15_nonperiodicCandidateP
          (theorem_4_5_counterexampleEntry state.W)) -
      (1 - cfg.beta) * theorem_4_15_nonperiodicCandidatePFirst
        (theorem_4_5_counterexampleEntry nextState.W) := by
  dsimp only
  rw [(theorem_4_15_nonperiodicCandidate_full_orbit_scalar_recurrence
    cfg t hnext).2]
  unfold theorem_4_15_nonperiodicCandidatePositiveProfileFirst
  ring

theorem theorem_4_15_nonperiodicCandidate_transformed_momentum_step_bound
    (cfg : DeterministicMomentumMuonConfig 1 1) (t : ℕ)
    (hcurrent : 0 ≤ theorem_4_5_counterexampleEntry
      (deterministicMomentumMuonState
        theorem_4_15_nonperiodicCandidateObjective cfg t).W)
    (hnext : 0 < theorem_4_5_counterexampleEntry
      (deterministicMomentumMuonState
        theorem_4_15_nonperiodicCandidateObjective cfg (t + 1)).W)
    (hmomentum :
      (deterministicMomentumMuonState
        theorem_4_15_nonperiodicCandidateObjective cfg t).M 0 0 < 0)
    (heta : cfg.eta t = 1 - cfg.beta) :
    let state := deterministicMomentumMuonState
      theorem_4_15_nonperiodicCandidateObjective cfg t
    let nextState := deterministicMomentumMuonState
      theorem_4_15_nonperiodicCandidateObjective cfg (t + 1)
    |(nextState.M 0 0 + theorem_4_15_nonperiodicCandidateP
          (theorem_4_5_counterexampleEntry nextState.W)) -
        cfg.beta * (state.M 0 0 + theorem_4_15_nonperiodicCandidateP
          (theorem_4_5_counterexampleEntry state.W))| ≤
      ((660 : ℝ) / 25) * (1 - cfg.beta) ^ 2 := by
  dsimp only
  let state := deterministicMomentumMuonState
    theorem_4_15_nonperiodicCandidateObjective cfg t
  let nextState := deterministicMomentumMuonState
    theorem_4_15_nonperiodicCandidateObjective cfg (t + 1)
  have hscalar := theorem_4_15_nonperiodicCandidate_full_orbit_scalar_recurrence
    cfg t hnext
  have hposition : theorem_4_5_counterexampleEntry nextState.W =
      theorem_4_5_counterexampleEntry state.W + (1 - cfg.beta) := by
    have h := hscalar.1
    change theorem_4_5_counterexampleEntry nextState.W =
      theorem_4_5_counterexampleEntry state.W -
        cfg.eta t * Real.sign (state.M 0 0) at h
    rw [heta, Real.sign_of_neg hmomentum] at h
    linarith
  have hstep_pos : 0 < 1 - cfg.beta := sub_pos.mpr cfg.beta_mem.2
  have hrem := theorem_4_15_nonperiodicCandidateP_weighted_forward_remainder
    hcurrent hstep_pos cfg.beta_mem.1 cfg.beta_mem.2.le rfl
  have htransformed :=
    theorem_4_15_nonperiodicCandidate_transformed_momentum_recurrence
      cfg t hnext
  change (nextState.M 0 0 + theorem_4_15_nonperiodicCandidateP
      (theorem_4_5_counterexampleEntry nextState.W) = _) at htransformed
  rw [htransformed]
  have hcancel :
      cfg.beta * (state.M 0 0 + theorem_4_15_nonperiodicCandidateP
          (theorem_4_5_counterexampleEntry state.W)) +
          cfg.beta * (theorem_4_15_nonperiodicCandidateP
              (theorem_4_5_counterexampleEntry nextState.W) -
            theorem_4_15_nonperiodicCandidateP
              (theorem_4_5_counterexampleEntry state.W)) -
          (1 - cfg.beta) * theorem_4_15_nonperiodicCandidatePFirst
              (theorem_4_5_counterexampleEntry nextState.W) -
        cfg.beta * (state.M 0 0 + theorem_4_15_nonperiodicCandidateP
          (theorem_4_5_counterexampleEntry state.W)) =
        cfg.beta * (theorem_4_15_nonperiodicCandidateP
              (theorem_4_5_counterexampleEntry nextState.W) -
            theorem_4_15_nonperiodicCandidateP
              (theorem_4_5_counterexampleEntry state.W)) -
          (1 - cfg.beta) * theorem_4_15_nonperiodicCandidatePFirst
            (theorem_4_5_counterexampleEntry nextState.W) := by ring
  rw [hcancel, hposition]
  exact hrem

theorem theorem_4_15_nonperiodicCandidate_generatedState_zero
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_le_sigma :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma) :
    deterministicMomentumMuonState theorem_4_15_nonperiodicCandidateObjective
        (theorem_4_15_nonperiodicCandidateConfig epsilon hepsilon
          hepsilon_le_sigma) 0 =
      { W := 0, M := (-2 : ℝ) • coordinateMatrix 0 0 } := by
  simp [deterministicMomentumMuonState, deterministicMomentumMuonBaseState,
    deterministicGradient, theorem_4_15_nonperiodicCandidateConfig,
    theorem_4_15_periodicCandidateShrinkingConfig,
    theorem_4_15_nonperiodicCandidateObjective_grad_zero]

/- The exact initialization forces the first generated iterate onto the strict
   positive ray.  This is the base case needed before the positive-ray scalar
   recurrence can be iterated. -/
theorem theorem_4_15_nonperiodicCandidate_generatedState_one_position
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_le_sigma :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma) :
    let cfg := theorem_4_15_nonperiodicCandidateConfig epsilon hepsilon
      hepsilon_le_sigma
    theorem_4_5_counterexampleEntry
        (deterministicMomentumMuonState theorem_4_15_nonperiodicCandidateObjective
          cfg 1).W =
        epsilon ^ 2 / theorem_4_15_nonperiodicCandidateSigma ^ 2 ∧
      0 < theorem_4_5_counterexampleEntry
        (deterministicMomentumMuonState theorem_4_15_nonperiodicCandidateObjective
          cfg 1).W := by
  let cfg := theorem_4_15_nonperiodicCandidateConfig epsilon hepsilon
    hepsilon_le_sigma
  have hzero := theorem_4_15_nonperiodicCandidate_generatedState_zero
    epsilon hepsilon hepsilon_le_sigma
  have heta := (theorem_4_15_nonperiodicCandidateConfig_exact_parameters
    epsilon hepsilon hepsilon_le_sigma).2
  have hzero_cfg : deterministicMomentumMuonState
      theorem_4_15_nonperiodicCandidateObjective cfg 0 =
      { W := 0, M := (-2 : ℝ) • coordinateMatrix 0 0 } := by
    simpa [cfg] using hzero
  have hstep := deterministicMomentumMuon_W_succ_eq_source_update
    theorem_4_15_nonperiodicCandidateObjective cfg 0
  have hposition : theorem_4_5_counterexampleEntry
      (deterministicMomentumMuonState theorem_4_15_nonperiodicCandidateObjective
        cfg 1).W = cfg.eta 0 := by
    change theorem_4_5_counterexampleEntry
      (deterministicMomentumMuonState theorem_4_15_nonperiodicCandidateObjective
        cfg (0 + 1)).W = cfg.eta 0
    rw [hstep, hzero_cfg]
    simp only [orthogonalizedDirection_eq_sign_smul_one_dimensional,
      MuonState.W, MuonState.M, Matrix.smul_apply, smul_eq_mul,
      theorem_4_5_counterexampleEntry_apply]
    norm_num [coordinateMatrix, Real.sign_of_neg]
  have heta_eq : cfg.eta 0 =
      epsilon ^ 2 / theorem_4_15_nonperiodicCandidateSigma ^ 2 := by
    simpa [cfg] using heta
  dsimp only
  constructor
  · exact hposition.trans heta_eq
  · rw [hposition, heta_eq]
    exact div_pos (sq_pos_of_pos hepsilon)
      (sq_pos_of_pos theorem_4_15_nonperiodicCandidateSigma_pos)

theorem theorem_4_15_nonperiodicCandidate_generatedState_one_momentum
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_le_sigma :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma) :
    let cfg := theorem_4_15_nonperiodicCandidateConfig epsilon hepsilon
      hepsilon_le_sigma
    let stateOne := deterministicMomentumMuonState
      theorem_4_15_nonperiodicCandidateObjective cfg 1
    stateOne.M 0 0 =
      cfg.beta * (-2) + (1 - cfg.beta) *
        theorem_4_15_nonperiodicCandidatePositiveProfileFirst
          (epsilon ^ 2 / theorem_4_15_nonperiodicCandidateSigma ^ 2) := by
  let cfg := theorem_4_15_nonperiodicCandidateConfig epsilon hepsilon
    hepsilon_le_sigma
  have hposition :=
    theorem_4_15_nonperiodicCandidate_generatedState_one_position
      epsilon hepsilon hepsilon_le_sigma
  have hrecurrence :=
    theorem_4_15_nonperiodicCandidate_full_orbit_scalar_recurrence cfg 0
      hposition.2
  dsimp only at hrecurrence ⊢
  rw [hrecurrence.2,
    theorem_4_15_nonperiodicCandidate_generatedState_zero
      epsilon hepsilon hepsilon_le_sigma, hposition.1]
  simp [coordinateMatrix, cfg]

/- Iterate the transformed-momentum estimate on the exact generated orbit.
   The sole remaining quantitative input is the pointwise comparison saying
   that the fixed candidate's positive envelope dominates the accumulated
   `O(1 - beta)` momentum error on the requested prefix.  In particular, this
   theorem does not assume a trajectory, curvature average, or stationarity
   conclusion: it proves the position and momentum sign simultaneously from
   Algorithm 1's recurrence. -/
theorem theorem_4_15_nonperiodicCandidate_generated_orbit_prefix
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_le_sigma :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma)
    (T : ℕ)
    (hfloor : ∀ t : ℕ, t ≤ T →
      ((660 : ℝ) / 25) *
          (epsilon ^ 2 / theorem_4_15_nonperiodicCandidateSigma ^ 2) <
        theorem_4_15_nonperiodicCandidateP
          ((t : ℝ) *
            (epsilon ^ 2 /
              theorem_4_15_nonperiodicCandidateSigma ^ 2))) :
    ∀ t : ℕ, t ≤ T →
      let cfg := theorem_4_15_nonperiodicCandidateConfig epsilon hepsilon
        hepsilon_le_sigma
      let state := deterministicMomentumMuonState
        theorem_4_15_nonperiodicCandidateObjective cfg t
      theorem_4_5_counterexampleEntry state.W =
          (t : ℝ) *
            (epsilon ^ 2 /
              theorem_4_15_nonperiodicCandidateSigma ^ 2) ∧
        state.M 0 0 < 0 ∧
        |state.M 0 0 + theorem_4_15_nonperiodicCandidateP
            (theorem_4_5_counterexampleEntry state.W)| ≤
          ((660 : ℝ) / 25) *
            (epsilon ^ 2 /
              theorem_4_15_nonperiodicCandidateSigma ^ 2) := by
  let cfg := theorem_4_15_nonperiodicCandidateConfig epsilon hepsilon
    hepsilon_le_sigma
  let h : ℝ := epsilon ^ 2 /
    theorem_4_15_nonperiodicCandidateSigma ^ 2
  have hhpos : 0 < h := by
    dsimp [h]
    exact div_pos (sq_pos_of_pos hepsilon)
      (sq_pos_of_pos theorem_4_15_nonperiodicCandidateSigma_pos)
  have hbetaStep : 1 - cfg.beta = h := by
    simpa [cfg, h] using
      (theorem_4_15_nonperiodicCandidateConfig_exact_parameters
        epsilon hepsilon hepsilon_le_sigma).1
  have heta : ∀ t : ℕ, cfg.eta t = h := by
    intro t
    dsimp [cfg, theorem_4_15_nonperiodicCandidateConfig,
      theorem_4_15_periodicCandidateShrinkingConfig, h,
      theorem_4_15_otherwiseEtaRate, sourceQuot, matrixRankBound]
    norm_num
    field_simp [ne_of_gt theorem_4_15_nonperiodicCandidateSigma_pos]
  intro t ht
  induction t with
  | zero =>
      dsimp only
      rw [theorem_4_15_nonperiodicCandidate_generatedState_zero
        epsilon hepsilon hepsilon_le_sigma]
      dsimp only [MuonState.W, MuonState.M]
      refine ⟨by simp, ?_, ?_⟩
      · norm_num [coordinateMatrix]
      · simp [theorem_4_5_counterexampleEntry_apply, coordinateMatrix,
          theorem_4_15_nonperiodicCandidate_initial_values.2.2]
        positivity
  | succ t ih =>
      have ht_le : t ≤ T := Nat.le_trans (Nat.le_succ t) ht
      have ih' := ih ht_le
      dsimp only at ih' ⊢
      let state := deterministicMomentumMuonState
        theorem_4_15_nonperiodicCandidateObjective cfg t
      let nextState := deterministicMomentumMuonState
        theorem_4_15_nonperiodicCandidateObjective cfg (t + 1)
      have hposition : theorem_4_5_counterexampleEntry nextState.W =
          ((t + 1 : ℕ) : ℝ) * h := by
        calc
          theorem_4_5_counterexampleEntry nextState.W =
              theorem_4_5_counterexampleEntry state.W -
                cfg.eta t * Real.sign (state.M 0 0) := by
            dsimp [state, nextState]
            rw [deterministicMomentumMuon_W_succ_eq_source_update,
              orthogonalizedDirection_eq_sign_smul_one_dimensional]
            simp [theorem_4_5_counterexampleEntry_apply, coordinateMatrix]
          _ = (t : ℝ) * h - h * (-1) := by
            rw [ih'.1, heta, Real.sign_of_neg ih'.2.1]
          _ = ((t + 1 : ℕ) : ℝ) * h := by
            push_cast
            ring
      have hcurrent : 0 ≤ theorem_4_5_counterexampleEntry state.W := by
        rw [ih'.1]
        positivity
      have hnext : 0 < theorem_4_5_counterexampleEntry nextState.W := by
        rw [hposition]
        positivity
      have hstep :=
        theorem_4_15_nonperiodicCandidate_transformed_momentum_step_bound
          cfg t hcurrent hnext ih'.2.1 (by rw [heta, hbetaStep])
      dsimp only at hstep
      rw [hbetaStep] at hstep
      have hnextError :
          |nextState.M 0 0 + theorem_4_15_nonperiodicCandidateP
              (theorem_4_5_counterexampleEntry nextState.W)| ≤
            ((660 : ℝ) / 25) * h := by
        let nextError := nextState.M 0 0 +
          theorem_4_15_nonperiodicCandidateP
            (theorem_4_5_counterexampleEntry nextState.W)
        let currentError := state.M 0 0 +
          theorem_4_15_nonperiodicCandidateP
            (theorem_4_5_counterexampleEntry state.W)
        have htriangle : |nextError| ≤
            |nextError - cfg.beta * currentError| +
              |cfg.beta * currentError| := by
          calc
            |nextError| =
                |(nextError - cfg.beta * currentError) +
                  cfg.beta * currentError| := by congr 1 <;> ring
            _ ≤ |nextError - cfg.beta * currentError| +
                |cfg.beta * currentError| := abs_add_le _ _
        have hscaled : |cfg.beta * currentError| ≤
            cfg.beta * (((660 : ℝ) / 25) * h) := by
          rw [abs_mul, abs_of_nonneg cfg.beta_mem.1]
          exact mul_le_mul_of_nonneg_left ih'.2.2 cfg.beta_mem.1
        change |nextError - cfg.beta * currentError| ≤
          ((660 : ℝ) / 25) * h ^ 2 at hstep
        change |nextError| ≤ ((660 : ℝ) / 25) * h
        calc
          |nextError| ≤ |nextError - cfg.beta * currentError| +
              |cfg.beta * currentError| := htriangle
          _ ≤ ((660 : ℝ) / 25) * h ^ 2 +
              cfg.beta * (((660 : ℝ) / 25) * h) :=
            add_le_add hstep hscaled
          _ = ((660 : ℝ) / 25) * h := by
            rw [← hbetaStep]
            ring
      have hPfloor : ((660 : ℝ) / 25) * h <
          theorem_4_15_nonperiodicCandidateP
            (theorem_4_5_counterexampleEntry nextState.W) := by
        rw [hposition]
        simpa [h] using hfloor (t + 1) ht
      have hmomentum : nextState.M 0 0 < 0 := by
        have herror_le := le_abs_self
          (nextState.M 0 0 + theorem_4_15_nonperiodicCandidateP
            (theorem_4_5_counterexampleEntry nextState.W))
        linarith
      exact ⟨by simpa [nextState, cfg, h] using hposition,
        hmomentum, by simpa [nextState, cfg, h] using hnextError⟩

/- The scalar smallness premise used by the selected-horizon orbit is
   automatic below one explicit accuracy threshold.  Raising both sides to
   the fifth power removes the fractional exponent: after writing
   `x = epsilon / sigma`, the comparison reduces to
   `(132 / 5)^5 * x^4 * (x + 2)^6 < 1`.  The deliberately coarse threshold
   `x ≤ 1 / 1000` makes that final estimate entirely rational. -/
theorem theorem_4_15_nonperiodicCandidate_selectedHorizon_smallness
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_small :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma / 1000) :
    ((660 : ℝ) / 25) *
          (epsilon ^ 2 / theorem_4_15_nonperiodicCandidateSigma ^ 2) <
        (1 + 2 * theorem_4_15_nonperiodicCandidateSigma / epsilon) ^
          (-(6 : ℝ) / 5) := by
  let sigma := theorem_4_15_nonperiodicCandidateSigma
  let x := epsilon / sigma
  let A : ℝ := 660 / 25
  have hsigma : 0 < sigma := by
    simpa [sigma] using theorem_4_15_nonperiodicCandidateSigma_pos
  have hxpos : 0 < x := div_pos hepsilon hsigma
  have hxsmall : x ≤ (1 : ℝ) / 1000 := by
    dsimp [x]
    apply (div_le_iff₀ hsigma).2
    simpa [sigma, div_eq_mul_inv, mul_comm] using hepsilon_small
  have hxone : x ≤ 1 := hxsmall.trans (by norm_num)
  have hbase_eq :
      1 + 2 * sigma / epsilon = (x + 2) / x := by
    dsimp [x]
    field_simp [ne_of_gt hepsilon, ne_of_gt hsigma]
  have hbase_pos : 0 < 1 + 2 * sigma / epsilon := by
    rw [hbase_eq]
    exact div_pos (by linarith) hxpos
  have hleft_eq :
      ((660 : ℝ) / 25) * (epsilon ^ 2 / sigma ^ 2) = A * x ^ 2 := by
    dsimp [A, x]
    field_simp [ne_of_gt hsigma]
  have hcancel :
      (A * x ^ 2) ^ 5 * (((x + 2) / x) ^ 6) =
        A ^ 5 * x ^ 4 * (x + 2) ^ 6 := by
    field_simp [ne_of_gt hxpos]
  have hpoly :
      (A * x ^ 2) ^ 5 *
          (1 + 2 * sigma / epsilon) ^ 6 < 1 := by
    rw [hbase_eq, hcancel]
    calc
      A ^ 5 * x ^ 4 * (x + 2) ^ 6 ≤
          A ^ 5 * ((1 : ℝ) / 1000) ^ 4 * 3 ^ 6 := by
        have hx4 : x ^ 4 ≤ ((1 : ℝ) / 1000) ^ 4 :=
          pow_le_pow_left₀ hxpos.le hxsmall 4
        have hxplus : x + 2 ≤ (3 : ℝ) := by linarith
        have hxplus6 : (x + 2) ^ 6 ≤ (3 : ℝ) ^ 6 :=
          pow_le_pow_left₀ (by linarith) hxplus 6
        have hAnonneg : 0 ≤ A ^ 5 := by
          dsimp [A]
          positivity
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hx4 hAnonneg) hxplus6
          (by positivity)
          (mul_nonneg hAnonneg (pow_nonneg (by norm_num) 4))
      _ < 1 := by norm_num [A]
  have hpow :
      (A * x ^ 2) ^ 5 <
        ((1 + 2 * sigma / epsilon) ^ 6)⁻¹ := by
    rw [inv_eq_one_div]
    apply (lt_div_iff₀ (pow_pos hbase_pos 6)).2
    simpa using hpoly
  have hrhs_pow :
      ((1 + 2 * sigma / epsilon) ^ (-(6 : ℝ) / 5)) ^ (5 : ℕ) =
        ((1 + 2 * sigma / epsilon) ^ 6)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase_pos.le]
    convert Real.rpow_neg hbase_pos.le 6 using 1 <;>
      norm_num [Real.rpow_natCast]
  rw [show theorem_4_15_nonperiodicCandidateSigma = sigma by rfl, hleft_eq]
  apply lt_of_pow_lt_pow_left₀ 5 (by positivity)
  rw [hrhs_pow]
  exact hpow

/- On the printed selected horizon, the prefix theorem's objective-floor
   premise follows from one explicit small-accuracy inequality.  The horizon
   upper scale gives `t * h <= 2 * sigma / epsilon`; the fixed envelope
   `P(x) >= (1+x)^(-6/5)` then keeps the momentum negative for every generated
   step.  The displayed smallness condition is independent of the orbit and
   will be discharged asymptotically in the counterexample endpoint. -/
theorem theorem_4_15_nonperiodicCandidate_selectedHorizon_generated_orbit
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_le_sigma :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma)
    (hsmall : ((660 : ℝ) / 25) *
          (epsilon ^ 2 / theorem_4_15_nonperiodicCandidateSigma ^ 2) <
        (1 + 2 * theorem_4_15_nonperiodicCandidateSigma / epsilon) ^
          (-(6 : ℝ) / 5)) :
    ∀ t : ℕ, t ≤ theorem_4_15_nonperiodicCandidateHorizon epsilon →
      let cfg := theorem_4_15_nonperiodicCandidateConfig epsilon hepsilon
        hepsilon_le_sigma
      let state := deterministicMomentumMuonState
        theorem_4_15_nonperiodicCandidateObjective cfg t
      theorem_4_5_counterexampleEntry state.W =
          (t : ℝ) *
            (epsilon ^ 2 /
              theorem_4_15_nonperiodicCandidateSigma ^ 2) ∧
        state.M 0 0 < 0 ∧
        |state.M 0 0 + theorem_4_15_nonperiodicCandidateP
            (theorem_4_5_counterexampleEntry state.W)| ≤
          ((660 : ℝ) / 25) *
            (epsilon ^ 2 /
              theorem_4_15_nonperiodicCandidateSigma ^ 2) := by
  apply theorem_4_15_nonperiodicCandidate_generated_orbit_prefix
    epsilon hepsilon hepsilon_le_sigma
      (theorem_4_15_nonperiodicCandidateHorizon epsilon)
  intro t ht
  let sigma := theorem_4_15_nonperiodicCandidateSigma
  let N := theorem_4_15_nonperiodicCandidateHorizon epsilon
  let h : ℝ := epsilon ^ 2 / sigma ^ 2
  have hsigma : 0 < sigma := by
    simpa [sigma] using theorem_4_15_nonperiodicCandidateSigma_pos
  have hscale := theorem_4_15_periodicCandidate_shrinkingHorizon_scale
    sigma epsilon hsigma hepsilon (by simpa [sigma] using hepsilon_le_sigma)
  have hrate : theorem_4_15_otherwiseComplexityRate 1 1 sigma epsilon =
      (sigma / epsilon) ^ 3 := by
    dsimp [theorem_4_15_otherwiseComplexityRate, matrixRankBound]
    norm_num
    field_simp [ne_of_gt hepsilon]
  have hNupper : (N : ℝ) ≤ 2 * (sigma / epsilon) ^ 3 := by
    have hupper := hscale.2.2.2.2
    rw [hrate] at hupper
    simpa [N, theorem_4_15_nonperiodicCandidateHorizon,
      sigma] using hupper
  have htcast : (t : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast ht
  have hh_nonneg : 0 ≤ h := by
    dsimp [h]
    positivity
  have hxupper : (t : ℝ) * h ≤ 2 * sigma / epsilon := by
    have hmul := mul_le_mul_of_nonneg_right
      (htcast.trans hNupper) hh_nonneg
    calc
      (t : ℝ) * h ≤ (2 * (sigma / epsilon) ^ 3) * h := hmul
      _ = 2 * sigma / epsilon := by
        dsimp [h]
        field_simp [ne_of_gt hsigma, ne_of_gt hepsilon]
  have hx_nonneg : 0 ≤ (t : ℝ) * h := by positivity
  have hbase_pos : 0 < 1 + (t : ℝ) * h := by linarith
  have hbase_le : 1 + (t : ℝ) * h ≤
      1 + 2 * sigma / epsilon := by linarith
  have hqLower :
      (1 + 2 * sigma / epsilon) ^ (-(6 : ℝ) / 5) ≤
        theorem_4_15_nonperiodicCandidateQ ((t : ℝ) * h) := by
    unfold theorem_4_15_nonperiodicCandidateQ
    exact Real.rpow_le_rpow_of_nonpos hbase_pos hbase_le (by norm_num)
  have hpLower : theorem_4_15_nonperiodicCandidateQ ((t : ℝ) * h) ≤
      theorem_4_15_nonperiodicCandidateP ((t : ℝ) * h) :=
    (theorem_4_15_nonperiodicCandidateP_envelope (by linarith)).1
  exact lt_of_lt_of_le (by simpa [sigma, h] using hsmall)
    (hqLower.trans hpLower)

/- The selected-horizon orbit above is the literal stochastic Algorithm 1
   orbit for the singleton deterministic oracle.  This transfer introduces no
   trajectory assumption: it is the pointwise state identity already proved
   for `deterministicOracleProblem`. -/
theorem theorem_4_15_nonperiodicCandidate_selectedHorizon_stochastic_orbit
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_le_sigma :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma)
    (hsmall : ((660 : ℝ) / 25) *
          (epsilon ^ 2 / theorem_4_15_nonperiodicCandidateSigma ^ 2) <
        (1 + 2 * theorem_4_15_nonperiodicCandidateSigma / epsilon) ^
          (-(6 : ℝ) / 5))
    (omega : SamplePath Unit
      (deterministicOracleConfig
        (theorem_4_15_nonperiodicCandidateConfig epsilon hepsilon
          hepsilon_le_sigma)).batchSize) :
    ∀ t : ℕ, t ≤ theorem_4_15_nonperiodicCandidateHorizon epsilon →
      let cfg := theorem_4_15_nonperiodicCandidateConfig epsilon hepsilon
        hepsilon_le_sigma
      let state := stochasticMuonState theorem_4_15_nonperiodicCandidateProblem
        (deterministicOracleConfig cfg) omega t
      theorem_4_5_counterexampleEntry state.W =
          (t : ℝ) *
            (epsilon ^ 2 /
              theorem_4_15_nonperiodicCandidateSigma ^ 2) ∧
        state.M 0 0 < 0 ∧
        |state.M 0 0 + theorem_4_15_nonperiodicCandidateP
            (theorem_4_5_counterexampleEntry state.W)| ≤
          ((660 : ℝ) / 25) *
            (epsilon ^ 2 /
              theorem_4_15_nonperiodicCandidateSigma ^ 2) := by
  intro t ht
  dsimp only
  rw [show theorem_4_15_nonperiodicCandidateProblem =
      deterministicOracleProblem theorem_4_15_nonperiodicCandidateObjective by
    rfl,
    deterministicOracle_state_eq]
  exact theorem_4_15_nonperiodicCandidate_selectedHorizon_generated_orbit
    epsilon hepsilon hepsilon_le_sigma hsmall t ht

/- Hence the exact stochastic Algorithm 1 orbit no longer exposes the
   auxiliary envelope inequality as an input.  The sole additional restriction
   is an explicit punctured small-accuracy range, which is the form needed by
   an asymptotic counterexample consumer. -/
theorem theorem_4_15_nonperiodicCandidate_selectedHorizon_stochastic_orbit_of_small_accuracy
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_small :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma / 1000)
    (omega : SamplePath Unit
      (deterministicOracleConfig
        (theorem_4_15_nonperiodicCandidateConfig epsilon hepsilon (by
          nlinarith [theorem_4_15_nonperiodicCandidateSigma_pos]))).batchSize) :
    ∀ t : ℕ, t ≤ theorem_4_15_nonperiodicCandidateHorizon epsilon →
      let cfg := theorem_4_15_nonperiodicCandidateConfig epsilon hepsilon (by
        nlinarith [theorem_4_15_nonperiodicCandidateSigma_pos])
      let state := stochasticMuonState theorem_4_15_nonperiodicCandidateProblem
        (deterministicOracleConfig cfg) omega t
      theorem_4_5_counterexampleEntry state.W =
          (t : ℝ) *
            (epsilon ^ 2 /
              theorem_4_15_nonperiodicCandidateSigma ^ 2) ∧
        state.M 0 0 < 0 ∧
        |state.M 0 0 + theorem_4_15_nonperiodicCandidateP
            (theorem_4_5_counterexampleEntry state.W)| ≤
          ((660 : ℝ) / 25) *
            (epsilon ^ 2 /
              theorem_4_15_nonperiodicCandidateSigma ^ 2) := by
  have hepsilon_le_sigma :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma := by
    have hsigma := theorem_4_15_nonperiodicCandidateSigma_pos
    linarith
  have hsmall :=
    theorem_4_15_nonperiodicCandidate_selectedHorizon_smallness
      epsilon hepsilon hepsilon_small
  exact theorem_4_15_nonperiodicCandidate_selectedHorizon_stochastic_orbit
    epsilon hepsilon hepsilon_le_sigma hsmall omega

/- The scalar profile sum from the mesh estimate is exactly the nuclear-gradient
   sum of the generated deterministic-momentum process.  The initial iterate is
   handled separately because it lies at the cutoff boundary; every later
   selected iterate is on the strict positive ray by the generated-orbit
   theorem. -/
theorem theorem_4_15_nonperiodicCandidate_generatedNuclearGradient_eq_profile
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_le_sigma :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma)
    (hepsilon_small :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma / 1000)
    (t : ℕ) (ht : t < theorem_4_15_nonperiodicCandidateHorizon epsilon) :
    let cfg := theorem_4_15_nonperiodicCandidateConfig epsilon hepsilon
      hepsilon_le_sigma
    let h := epsilon ^ 2 / theorem_4_15_nonperiodicCandidateSigma ^ 2
    nuclearNorm
        (theorem_4_15_nonperiodicCandidateObjective.grad
          (deterministicMomentumMuonState
            theorem_4_15_nonperiodicCandidateObjective cfg t).W) =
      |theorem_4_15_nonperiodicCandidatePositiveProfileFirst ((t : ℝ) * h)| := by
  let cfg := theorem_4_15_nonperiodicCandidateConfig epsilon hepsilon
    hepsilon_le_sigma
  let h := epsilon ^ 2 / theorem_4_15_nonperiodicCandidateSigma ^ 2
  have hsmall :=
    theorem_4_15_nonperiodicCandidate_selectedHorizon_smallness
      epsilon hepsilon hepsilon_small
  have horbit :=
    theorem_4_15_nonperiodicCandidate_selectedHorizon_generated_orbit
      epsilon hepsilon hepsilon_le_sigma hsmall t (Nat.le_of_lt ht)
  dsimp only
  by_cases htzero : t = 0
  · subst t
    rw [theorem_4_15_nonperiodicCandidate_generatedState_zero
      epsilon hepsilon hepsilon_le_sigma,
      theorem_4_15_nonperiodicCandidateObjective_grad_zero,
      theorem_4_15_periodicCandidate_scalarCoordinateNuclearNorm]
    simp [theorem_4_15_nonperiodicCandidatePositiveProfileFirst_zero]
  · have htpos : 0 < t := Nat.pos_of_ne_zero htzero
    have hh : 0 < h := by
      dsimp [h]
      exact div_pos (sq_pos_of_pos hepsilon)
        (sq_pos_of_pos theorem_4_15_nonperiodicCandidateSigma_pos)
    have hWpos : 0 < theorem_4_5_counterexampleEntry
        (deterministicMomentumMuonState
          theorem_4_15_nonperiodicCandidateObjective cfg t).W := by
      rw [horbit.1]
      exact mul_pos (by exact_mod_cast htpos) hh
    rw [theorem_4_15_nonperiodicCandidateObjective_grad_of_pos _ hWpos,
      theorem_4_15_periodicCandidate_scalarCoordinateNuclearNorm, horbit.1]

theorem theorem_4_15_nonperiodicCandidate_selected_deterministicAverage_eq_profile
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_le_sigma :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma)
    (hepsilon_small :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma / 1000) :
    let cfg := theorem_4_15_nonperiodicCandidateConfig epsilon hepsilon
      hepsilon_le_sigma
    let N := theorem_4_15_nonperiodicCandidateHorizon epsilon
    let h := epsilon ^ 2 / theorem_4_15_nonperiodicCandidateSigma ^ 2
    deterministicMomentumAverageNuclearGradient
        theorem_4_15_nonperiodicCandidateObjective cfg N =
      ((N : ℝ)⁻¹) * ∑ t ∈ Finset.range N,
        |theorem_4_15_nonperiodicCandidatePositiveProfileFirst ((t : ℝ) * h)| := by
  let cfg := theorem_4_15_nonperiodicCandidateConfig epsilon hepsilon
    hepsilon_le_sigma
  let N := theorem_4_15_nonperiodicCandidateHorizon epsilon
  let h := epsilon ^ 2 / theorem_4_15_nonperiodicCandidateSigma ^ 2
  unfold deterministicMomentumAverageNuclearGradient
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  exact theorem_4_15_nonperiodicCandidate_generatedNuclearGradient_eq_profile
    epsilon hepsilon hepsilon_le_sigma hepsilon_small t
      (Finset.mem_range.mp ht)

/- Since the stochastic problem is the singleton deterministic oracle, the
   preceding generated identity is also the exact integral used by the source
   target.  This is the missing object-correspondence bridge from the scalar
   mesh lower bound to `stochasticAverageNuclearGradient`; it assumes no cross
   control, `Jstar`, or stationarity conclusion. -/
theorem theorem_4_15_nonperiodicCandidate_selected_stochasticAverage_eq_profile
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_small :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma / 1000) :
    let N := theorem_4_15_nonperiodicCandidateHorizon epsilon
    let h := epsilon ^ 2 / theorem_4_15_nonperiodicCandidateSigma ^ 2
    stochasticAverageNuclearGradient
        theorem_4_15_nonperiodicCandidateProblem
        (theorem_4_15_nonperiodicCandidateConfigForAccuracyHorizon epsilon N) N =
      ((N : ℝ)⁻¹) * ∑ t ∈ Finset.range N,
        |theorem_4_15_nonperiodicCandidatePositiveProfileFirst ((t : ℝ) * h)| := by
  let N := theorem_4_15_nonperiodicCandidateHorizon epsilon
  have hepsilon_le_sigma :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma := by
    nlinarith [theorem_4_15_nonperiodicCandidateSigma_pos]
  let cfg := theorem_4_15_nonperiodicCandidateConfig epsilon hepsilon
    hepsilon_le_sigma
  dsimp only
  rw [theorem_4_15_nonperiodicCandidateConfigForAccuracyHorizon_eq
    epsilon N hepsilon hepsilon_le_sigma]
  let hwd := theorem_4_15_nonperiodicCandidateProblem_expectationsWellDefined cfg N
  rw [← stochasticAverageNuclearGradientRealized_eq_integral
    theorem_4_15_nonperiodicCandidateProblem (deterministicOracleConfig cfg) N hwd.1]
  change stochasticAverageNuclearGradientRealized
      (deterministicOracleProblem theorem_4_15_nonperiodicCandidateObjective)
      (deterministicOracleConfig cfg) N hwd.1 = _
  rw [deterministicOracle_average_eq]
  exact theorem_4_15_nonperiodicCandidate_selected_deterministicAverage_eq_profile
    epsilon hepsilon hepsilon_le_sigma hepsilon_small

/- Normalizing the checked finite-sum lower bound by the selected horizon now
   gives the exact ratio that must diverge to refute an `O(epsilon)` conclusion.
   The only horizon estimate used is the printed upper theta bound
   `N * h <= 2 * sigma / epsilon`; the generated average itself is identified
   by the singleton-oracle theorem above. -/
theorem theorem_4_15_nonperiodicCandidate_selected_stochasticAverage_div_accuracy_lower
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_small :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma / 1000) :
    let sigma := theorem_4_15_nonperiodicCandidateSigma
    let lower := (6 : ℝ) / 5 *
        ((sigma / epsilon) *
            (1 + 2 * sigma / epsilon) ^ (-(4 : ℝ) / 5) -
          (5 : ℝ) / 12 - (56 : ℝ) / 5 * epsilon / sigma) -
        (396 : ℝ) / 5
    let N := theorem_4_15_nonperiodicCandidateHorizon epsilon
    lower / (2 * sigma) ≤
      stochasticAverageNuclearGradient
          theorem_4_15_nonperiodicCandidateProblem
          (theorem_4_15_nonperiodicCandidateConfigForAccuracyHorizon epsilon N) N /
        epsilon := by
  let sigma := theorem_4_15_nonperiodicCandidateSigma
  let h := epsilon ^ 2 / sigma ^ 2
  let lower := (6 : ℝ) / 5 *
      ((sigma / epsilon) *
          (1 + 2 * sigma / epsilon) ^ (-(4 : ℝ) / 5) -
        (5 : ℝ) / 12 - (56 : ℝ) / 5 * epsilon / sigma) -
      (396 : ℝ) / 5
  let N := theorem_4_15_nonperiodicCandidateHorizon epsilon
  let average := stochasticAverageNuclearGradient
    theorem_4_15_nonperiodicCandidateProblem
    (theorem_4_15_nonperiodicCandidateConfigForAccuracyHorizon epsilon N) N
  have hsigma : 0 < sigma := by
    simpa [sigma] using theorem_4_15_nonperiodicCandidateSigma_pos
  have hepsilon_le_sigma : epsilon ≤ sigma := by
    dsimp [sigma]
    nlinarith [theorem_4_15_nonperiodicCandidateSigma_pos]
  have hscale := theorem_4_15_nonperiodicCandidateHorizon_scale
    epsilon hepsilon (by simpa [sigma] using hepsilon_le_sigma)
  have hNpos : 0 < N := by simpa [N] using hscale.1
  have hrate :
      theorem_4_15_otherwiseComplexityRate 1 1 sigma epsilon =
        (sigma / epsilon) ^ 3 := by
    dsimp [theorem_4_15_otherwiseComplexityRate, matrixRankBound]
    norm_num
    field_simp [ne_of_gt hepsilon]
  have hNupper : (N : ℝ) ≤ 2 * (sigma / epsilon) ^ 3 := by
    have hraw := hscale.2.2.2.2
    rw [show theorem_4_15_otherwiseComplexityRate 1 1
        theorem_4_15_nonperiodicCandidateSigma epsilon =
          (sigma / epsilon) ^ 3 by simpa [sigma] using hrate] at hraw
    simpa [N] using hraw
  have hh : 0 < h := by
    dsimp [h]
    exact div_pos (sq_pos_of_pos hepsilon) (sq_pos_of_pos hsigma)
  have hNhUpper : (N : ℝ) * h ≤ 2 * sigma / epsilon := by
    have hmul := mul_le_mul_of_nonneg_right hNupper hh.le
    calc
      (N : ℝ) * h ≤ 2 * (sigma / epsilon) ^ 3 * h := hmul
      _ = 2 * sigma / epsilon := by
        dsimp [h]
        field_simp [ne_of_gt hepsilon, ne_of_gt hsigma]
  have havgEq :=
    theorem_4_15_nonperiodicCandidate_selected_stochasticAverage_eq_profile
      epsilon hepsilon hepsilon_small
  have havgNonneg : 0 ≤ average := by
    rw [show average = stochasticAverageNuclearGradient
        theorem_4_15_nonperiodicCandidateProblem
        (theorem_4_15_nonperiodicCandidateConfigForAccuracyHorizon epsilon N) N by rfl,
      havgEq]
    positivity
  have hlower :=
    theorem_4_15_nonperiodicCandidate_selected_gradient_scaled_lower
      epsilon hepsilon (by simpa [sigma] using hepsilon_le_sigma)
  have hscaled : lower ≤ (N : ℝ) * h * average := by
    rw [show average = stochasticAverageNuclearGradient
        theorem_4_15_nonperiodicCandidateProblem
        (theorem_4_15_nonperiodicCandidateConfigForAccuracyHorizon epsilon N) N by rfl,
      havgEq]
    have hNne : (N : ℝ) ≠ 0 := by positivity
    dsimp [sigma, h, lower, N] at hlower ⊢
    calc
      _ ≤ (epsilon ^ 2 / theorem_4_15_nonperiodicCandidateSigma ^ 2) *
          ∑ t ∈ Finset.range (theorem_4_15_nonperiodicCandidateHorizon epsilon),
            |theorem_4_15_nonperiodicCandidatePositiveProfileFirst
              ((t : ℝ) *
                (epsilon ^ 2 / theorem_4_15_nonperiodicCandidateSigma ^ 2))| := hlower
      _ = _ := by
        symm
        calc
          (theorem_4_15_nonperiodicCandidateHorizon epsilon : ℝ) *
                (epsilon ^ 2 / theorem_4_15_nonperiodicCandidateSigma ^ 2) *
                ((theorem_4_15_nonperiodicCandidateHorizon epsilon : ℝ)⁻¹ *
                  ∑ t ∈ Finset.range
                      (theorem_4_15_nonperiodicCandidateHorizon epsilon),
                    |theorem_4_15_nonperiodicCandidatePositiveProfileFirst
                      ((t : ℝ) *
                        (epsilon ^ 2 /
                          theorem_4_15_nonperiodicCandidateSigma ^ 2))|) =
              ((theorem_4_15_nonperiodicCandidateHorizon epsilon : ℝ) *
                (theorem_4_15_nonperiodicCandidateHorizon epsilon : ℝ)⁻¹) *
                ((epsilon ^ 2 / theorem_4_15_nonperiodicCandidateSigma ^ 2) *
                  ∑ t ∈ Finset.range
                      (theorem_4_15_nonperiodicCandidateHorizon epsilon),
                    |theorem_4_15_nonperiodicCandidatePositiveProfileFirst
                      ((t : ℝ) *
                        (epsilon ^ 2 /
                          theorem_4_15_nonperiodicCandidateSigma ^ 2))|) := by ring
          _ = _ := by rw [mul_inv_cancel₀ hNne, one_mul]
  have hscaledUpper : lower ≤ (2 * sigma / epsilon) * average :=
    hscaled.trans (mul_le_mul_of_nonneg_right hNhUpper havgNonneg)
  dsimp [sigma, lower, N, average]
  apply (div_le_iff₀ (mul_pos (by norm_num) hsigma)).2
  calc
    _ ≤ (2 * sigma / epsilon) * average := hscaledUpper
    _ = average / epsilon * (2 * sigma) := by ring

theorem theorem_4_15_nonperiodicCandidate_generated_direction_of_small_accuracy
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_le_sigma :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma)
    (hepsilon_small :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma / 1000)
    (omega : SamplePath Unit
      (deterministicOracleConfig
        (theorem_4_15_nonperiodicCandidateConfig epsilon hepsilon
          hepsilon_le_sigma)).batchSize)
    (t : ℕ) (ht : t ≤ theorem_4_15_nonperiodicCandidateHorizon epsilon) :
    stochasticMuonDirection theorem_4_15_nonperiodicCandidateProblem
        (deterministicOracleConfig
          (theorem_4_15_nonperiodicCandidateConfig epsilon hepsilon
            hepsilon_le_sigma)) omega t =
      (-1 : ℝ) • coordinateMatrix 0 0 := by
  have hsmall :=
    theorem_4_15_nonperiodicCandidate_selectedHorizon_smallness
      epsilon hepsilon hepsilon_small
  have horbit :=
    theorem_4_15_nonperiodicCandidate_selectedHorizon_stochastic_orbit
      epsilon hepsilon hepsilon_le_sigma hsmall omega t ht
  unfold stochasticMuonDirection
  rw [orthogonalizedDirection_eq_sign_smul_one_dimensional,
    Real.sign_of_neg horbit.2.1]

/- Specializing the existing signed directional Taylor telescope to the exact
   small-accuracy orbit gives a cross-free, source-object estimate.  Its right
   side contains only the fixed third-derivative scale and the printed step;
   in particular it contains neither the directional average itself nor a
   cross/Jstar or stationarity term. -/
theorem theorem_4_15_nonperiodicCandidate_directional_sum_telescope_of_small_accuracy
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_le_sigma :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma)
    (hepsilon_small :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma / 1000)
    (omega : SamplePath Unit
      (deterministicOracleConfig
        (theorem_4_15_nonperiodicCandidateConfig epsilon hepsilon
          hepsilon_le_sigma)).batchSize) :
    let cfg := theorem_4_15_nonperiodicCandidateConfig epsilon hepsilon
      hepsilon_le_sigma
    let scfg := deterministicOracleConfig cfg
    let N := theorem_4_15_nonperiodicCandidateHorizon epsilon
    let h := epsilon ^ 2 / theorem_4_15_nonperiodicCandidateSigma ^ 2
    let D : Mat 1 1 := (-1 : ℝ) • coordinateMatrix 0 0
    |frobeniusInner
          (theorem_4_15_nonperiodicCandidateProblem.objective.grad
              (stochasticMuonState theorem_4_15_nonperiodicCandidateProblem
                scfg omega 0).W -
            theorem_4_15_nonperiodicCandidateProblem.objective.grad
              (stochasticMuonState theorem_4_15_nonperiodicCandidateProblem
                scfg omega N).W) D -
        h * ∑ t ∈ Finset.range N,
          stochasticHessianDirectionalTerm
            theorem_4_15_nonperiodicCandidateProblem scfg omega t| ≤
      (N : ℝ) *
        (theorem_4_15_nonperiodicCandidateThirdDerivativeScale * h ^ 2 / 2) := by
  let cfg := theorem_4_15_nonperiodicCandidateConfig epsilon hepsilon
    hepsilon_le_sigma
  let scfg := deterministicOracleConfig cfg
  let N := theorem_4_15_nonperiodicCandidateHorizon epsilon
  let h := epsilon ^ 2 / theorem_4_15_nonperiodicCandidateSigma ^ 2
  let D : Mat 1 1 := (-1 : ℝ) • coordinateMatrix 0 0
  have heta : ∀ k ∈ Finset.range N, scfg.eta k = h := by
    intro k _hk
    have hconst :=
      (theorem_4_15_nonperiodicCandidateConfig_schedule epsilon hepsilon
        hepsilon_le_sigma).2.2.2.2 k _hk
    have heta0 :=
      (theorem_4_15_nonperiodicCandidateConfig_exact_parameters epsilon hepsilon
        hepsilon_le_sigma).2
    exact hconst.trans (by simpa [scfg, cfg, h] using heta0)
  have hdir : ∀ t ∈ Finset.range N,
      stochasticMuonDirection theorem_4_15_nonperiodicCandidateProblem
        scfg omega t = D := by
    intro t ht
    apply theorem_4_15_nonperiodicCandidate_generated_direction_of_small_accuracy
      epsilon hepsilon hepsilon_le_sigma hepsilon_small omega t
    exact (Finset.mem_range.mp ht).le
  have htelescope :=
    theorem_4_15_fixed_generated_direction_directional_sum_telescope
      theorem_4_15_nonperiodicCandidateProblem scfg omega N D
      theorem_4_15_nonperiodicCandidateProblem_thirdDerivativeBounded
      heta (by dsimp [h]; positivity) hdir
  simpa [cfg, scfg, N, h, D, matrixRankBound] using htelescope

/- The endpoint pairing in the preceding telescope is uniformly bounded.
   This uses the literal generated endpoints: the initial gradient is `-2`,
   while the positive-ray terminal gradient has absolute value at most `9`.
   No curvature average or stationarity quantity occurs as an input. -/
theorem theorem_4_15_nonperiodicCandidate_gradient_endpoint_pairing_abs_le
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_le_sigma :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma)
    (hepsilon_small :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma / 1000)
    (omega : SamplePath Unit
      (deterministicOracleConfig
        (theorem_4_15_nonperiodicCandidateConfig epsilon hepsilon
          hepsilon_le_sigma)).batchSize) :
    let cfg := theorem_4_15_nonperiodicCandidateConfig epsilon hepsilon
      hepsilon_le_sigma
    let scfg := deterministicOracleConfig cfg
    let N := theorem_4_15_nonperiodicCandidateHorizon epsilon
    let D : Mat 1 1 := (-1 : ℝ) • coordinateMatrix 0 0
    |frobeniusInner
        (theorem_4_15_nonperiodicCandidateProblem.objective.grad
            (stochasticMuonState theorem_4_15_nonperiodicCandidateProblem
              scfg omega 0).W -
          theorem_4_15_nonperiodicCandidateProblem.objective.grad
            (stochasticMuonState theorem_4_15_nonperiodicCandidateProblem
              scfg omega N).W) D| ≤ 11 := by
  let cfg := theorem_4_15_nonperiodicCandidateConfig epsilon hepsilon
    hepsilon_le_sigma
  let scfg := deterministicOracleConfig cfg
  let N := theorem_4_15_nonperiodicCandidateHorizon epsilon
  let h := epsilon ^ 2 / theorem_4_15_nonperiodicCandidateSigma ^ 2
  let D : Mat 1 1 := (-1 : ℝ) • coordinateMatrix 0 0
  have hNpos : horizonDomain N := by
    exact (theorem_4_15_nonperiodicCandidateHorizon_scale epsilon hepsilon
      hepsilon_le_sigma).1
  have hsmall :=
    theorem_4_15_nonperiodicCandidate_selectedHorizon_smallness
      epsilon hepsilon hepsilon_small
  have hhorbit :=
    theorem_4_15_nonperiodicCandidate_selectedHorizon_generated_orbit
      epsilon hepsilon hepsilon_le_sigma hsmall N (le_refl N)
  have hhpos : 0 < h := by
    dsimp [h]
    exact div_pos (sq_pos_of_pos hepsilon)
      (sq_pos_of_pos theorem_4_15_nonperiodicCandidateSigma_pos)
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hterminal_pos : 0 < (N : ℝ) * h := mul_pos hNreal hhpos
  have hgradTerminal :=
    theorem_4_15_nonperiodicCandidateObjective_grad_of_pos
      (deterministicMomentumMuonState
        theorem_4_15_nonperiodicCandidateObjective cfg N).W (by
          rw [hhorbit.1]
          exact hterminal_pos)
  have hterminal_abs :
      |theorem_4_15_nonperiodicCandidatePositiveProfileFirst ((N : ℝ) * h)|
        ≤ 9 :=
    theorem_4_15_nonperiodicCandidatePositiveProfileFirst_abs_le
      (mul_nonneg hNreal.le hhpos.le)
  dsimp only
  rw [show theorem_4_15_nonperiodicCandidateProblem =
      deterministicOracleProblem theorem_4_15_nonperiodicCandidateObjective by
        rfl,
    deterministicOracle_state_eq, deterministicOracle_state_eq,
    deterministicOracleProblem_objective,
    theorem_4_15_nonperiodicCandidate_generatedState_zero
      epsilon hepsilon hepsilon_le_sigma]
  dsimp only [MuonState.W]
  rw [theorem_4_15_nonperiodicCandidateObjective_grad_zero,
    hgradTerminal, hhorbit.1]
  simp only [frobeniusInner, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  norm_num [D, coordinateMatrix]
  calc
    |theorem_4_15_nonperiodicCandidatePositiveProfileFirst ((N : ℝ) * h) + 2|
        ≤ |theorem_4_15_nonperiodicCandidatePositiveProfileFirst ((N : ℝ) * h)| +
          |(2 : ℝ)| := abs_add_le _ _
    _ ≤ 9 + 2 := add_le_add hterminal_abs (by norm_num)
    _ = 11 := by norm_num

/- Normalizing the signed telescope by the printed selected horizon proves
   the actual source `J` estimate for this generated family.  The coefficient
   is fixed by the objective (`sigma` is its fixed initial gap and `s` its
   fixed third-derivative bound), so it is independent of accuracy and the
   selected horizon. -/
theorem theorem_4_15_nonperiodicCandidate_directional_average_le
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_le_sigma :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma)
    (hepsilon_small :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma / 1000) :
    deterministicMomentumHessianDirectionalAverage
        theorem_4_15_nonperiodicCandidateObjective
        (theorem_4_15_nonperiodicCandidateConfig epsilon hepsilon
          hepsilon_le_sigma)
        (theorem_4_15_nonperiodicCandidateHorizon epsilon) ≤
      (11 / theorem_4_15_nonperiodicCandidateSigma +
          theorem_4_15_nonperiodicCandidateThirdDerivativeScale /
            (2 * theorem_4_15_nonperiodicCandidateSigma)) * epsilon := by
  let sigma := theorem_4_15_nonperiodicCandidateSigma
  let s := theorem_4_15_nonperiodicCandidateThirdDerivativeScale
  let cfg := theorem_4_15_nonperiodicCandidateConfig epsilon hepsilon
    hepsilon_le_sigma
  let scfg := deterministicOracleConfig cfg
  let N := theorem_4_15_nonperiodicCandidateHorizon epsilon
  let h := epsilon ^ 2 / sigma ^ 2
  let D : Mat 1 1 := (-1 : ℝ) • coordinateMatrix 0 0
  let omega : SamplePath Unit scfg.batchSize := fun _ _ => ()
  let boundary : ℝ := frobeniusInner
    (theorem_4_15_nonperiodicCandidateProblem.objective.grad
        (stochasticMuonState theorem_4_15_nonperiodicCandidateProblem
          scfg omega 0).W -
      theorem_4_15_nonperiodicCandidateProblem.objective.grad
        (stochasticMuonState theorem_4_15_nonperiodicCandidateProblem
          scfg omega N).W) D
  let curvatureSum : ℝ := ∑ t ∈ Finset.range N,
    stochasticHessianDirectionalTerm
      theorem_4_15_nonperiodicCandidateProblem scfg omega t
  have hsigma : 0 < sigma := by
    simpa [sigma] using theorem_4_15_nonperiodicCandidateSigma_pos
  have hs_nonneg : 0 ≤ s := by
    exact le_trans (norm_nonneg _)
      (theorem_4_15_nonperiodicCandidateProblem_thirdDerivativeBounded.bound 0)
  have hhpos : 0 < h := by
    dsimp [h]
    exact div_pos (sq_pos_of_pos hepsilon) (sq_pos_of_pos hsigma)
  have hNpos : horizonDomain N := by
    simpa [N, sigma] using
      (theorem_4_15_nonperiodicCandidateHorizon_scale epsilon hepsilon
        hepsilon_le_sigma).1
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have htelescope : |boundary - h * curvatureSum| ≤
      (N : ℝ) * (s * h ^ 2 / 2) := by
    simpa [boundary, curvatureSum, cfg, scfg, N, h, D, omega, sigma, s] using
      (theorem_4_15_nonperiodicCandidate_directional_sum_telescope_of_small_accuracy
        epsilon hepsilon hepsilon_le_sigma hepsilon_small omega)
  have hboundary : |boundary| ≤ 11 := by
    simpa [boundary, cfg, scfg, N, D, omega] using
      (theorem_4_15_nonperiodicCandidate_gradient_endpoint_pairing_abs_le
        epsilon hepsilon hepsilon_le_sigma hepsilon_small omega)
  have hscaled : h * curvatureSum ≤
      11 + (N : ℝ) * (s * h ^ 2 / 2) := by
    calc
      h * curvatureSum ≤ boundary + |boundary - h * curvatureSum| := by
        linarith [neg_abs_le (boundary - h * curvatureSum)]
      _ ≤ |boundary| + (N : ℝ) * (s * h ^ 2 / 2) :=
        add_le_add (le_abs_self boundary) htelescope
      _ ≤ 11 + (N : ℝ) * (s * h ^ 2 / 2) :=
        add_le_add hboundary le_rfl
  have hsum : curvatureSum ≤
      (11 + (N : ℝ) * (s * h ^ 2 / 2)) / h :=
    (le_div_iff₀ hhpos).2 (by simpa [mul_comm] using hscaled)
  have havg : (N : ℝ)⁻¹ * curvatureSum ≤
      11 / ((N : ℝ) * h) + s * h / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hNreal.le)
    calc
      (N : ℝ)⁻¹ * curvatureSum ≤
          (N : ℝ)⁻¹ *
            ((11 + (N : ℝ) * (s * h ^ 2 / 2)) / h) := hmul
      _ = 11 / ((N : ℝ) * h) + s * h / 2 := by
        field_simp [ne_of_gt hNreal, ne_of_gt hhpos]
  have htravel : sigma / epsilon ≤ (N : ℝ) * h := by
    let rate := theorem_4_15_otherwiseComplexityRate 1 1 sigma epsilon
    have hscale := theorem_4_15_nonperiodicCandidateHorizon_scale
      epsilon hepsilon hepsilon_le_sigma
    have hNlower : rate ≤ (N : ℝ) := by
      simpa [rate, N, sigma] using hscale.2.2.2.1
    have hmul := mul_le_mul_of_nonneg_right hNlower hhpos.le
    calc
      sigma / epsilon = rate * h := by
        dsimp [rate, h, theorem_4_15_otherwiseComplexityRate, matrixRankBound]
        norm_num [matrixRankBound]
        field_simp [ne_of_gt hsigma, ne_of_gt hepsilon]
      _ ≤ (N : ℝ) * h := hmul
  have hinvProduct : (((N : ℝ) * h)⁻¹) ≤ epsilon / sigma := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (mul_pos hNreal hhpos)).2
    have hratio_nonneg : 0 ≤ epsilon / sigma :=
      (div_pos hepsilon hsigma).le
    have hmul := mul_le_mul_of_nonneg_left htravel hratio_nonneg
    calc
      (1 : ℝ) = (epsilon / sigma) * (sigma / epsilon) := by
        field_simp [ne_of_gt hsigma, ne_of_gt hepsilon]
      _ ≤ (epsilon / sigma) * ((N : ℝ) * h) := hmul
  have hfirst : 11 / ((N : ℝ) * h) ≤ 11 * (epsilon / sigma) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinvProduct (by norm_num)
  have hh_le : h ≤ epsilon / sigma := by
    dsimp [h]
    apply (div_le_iff₀ (sq_pos_of_pos hsigma)).2
    have hepsmul : epsilon ^ 2 ≤ epsilon * sigma := by nlinarith
    calc
      epsilon ^ 2 ≤ epsilon * sigma := hepsmul
      _ = epsilon / sigma * sigma ^ 2 := by
        field_simp [ne_of_gt hsigma]
  have hsecond : s * h / 2 ≤ (s / (2 * sigma)) * epsilon := by
    have hmul := mul_le_mul_of_nonneg_left hh_le hs_nonneg
    calc
      s * h / 2 ≤ s * (epsilon / sigma) / 2 := by linarith
      _ = (s / (2 * sigma)) * epsilon := by
        field_simp [ne_of_gt hsigma]
  change (N : ℝ)⁻¹ *
      ∑ t ∈ Finset.range N,
        deterministicMomentumHessianDirectionalTerm
          theorem_4_15_nonperiodicCandidateObjective cfg t ≤ _
  have hsum_eq : curvatureSum =
      ∑ t ∈ Finset.range N,
        deterministicMomentumHessianDirectionalTerm
          theorem_4_15_nonperiodicCandidateObjective cfg t := by
    dsimp [curvatureSum]
    apply Finset.sum_congr rfl
    intro t _ht
    exact deterministicOracle_hessianDirectionalTerm_eq
      theorem_4_15_nonperiodicCandidateObjective cfg omega t
  rw [← hsum_eq]
  calc
    (N : ℝ)⁻¹ * curvatureSum ≤
        11 / ((N : ℝ) * h) + s * h / 2 := havg
    _ ≤ 11 * (epsilon / sigma) + (s / (2 * sigma)) * epsilon :=
      add_le_add hfirst hsecond
    _ = (11 / sigma + s / (2 * sigma)) * epsilon := by ring

/- Thus the fixed problem and exact shrinking Algorithm 1 schedule satisfy
   every field of the original Appendix B.4 source-small-`J` run predicate for
   all sufficiently small positive accuracies.  In particular the realized
   directional-Hessian average is obtained by the singleton-oracle transfer;
   no cross or `Jstar` premise is introduced. -/
theorem theorem_4_15_nonperiodicCandidate_selected_source_run_of_small_accuracy
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_small :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma / 1000) :
    theorem_4_15_otherwiseSourceSmallJGeneratedRunForAccuracyHorizon
      theorem_4_15_nonperiodicCandidateProblem
      (fun _accuracy _horizon => deterministicOracleConfig
        (theorem_4_15_nonperiodicCandidateConfig epsilon hepsilon (by
          nlinarith [theorem_4_15_nonperiodicCandidateSigma_pos])))
      0 theorem_4_15_nonperiodicCandidateSigma
      theorem_4_15_nonperiodicCandidateSigma epsilon
      (11 / theorem_4_15_nonperiodicCandidateSigma +
        theorem_4_15_nonperiodicCandidateThirdDerivativeScale /
          (2 * theorem_4_15_nonperiodicCandidateSigma))
      theorem_4_15_nonperiodicCandidateThirdDerivativeScale
      1 1 1 1 1 2
      (theorem_4_15_nonperiodicCandidateHorizon epsilon) := by
  have hepsilon_le_sigma :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma := by
    nlinarith [theorem_4_15_nonperiodicCandidateSigma_pos]
  have hs_nonneg : 0 ≤
      theorem_4_15_nonperiodicCandidateThirdDerivativeScale := by
    exact le_trans (norm_nonneg _)
      (theorem_4_15_nonperiodicCandidateProblem_thirdDerivativeBounded.bound 0)
  have hC : 0 < 11 / theorem_4_15_nonperiodicCandidateSigma +
      theorem_4_15_nonperiodicCandidateThirdDerivativeScale /
        (2 * theorem_4_15_nonperiodicCandidateSigma) := by
    have hfirst : 0 < 11 / theorem_4_15_nonperiodicCandidateSigma :=
      div_pos (by norm_num) theorem_4_15_nonperiodicCandidateSigma_pos
    have hsecond : 0 ≤
        theorem_4_15_nonperiodicCandidateThirdDerivativeScale /
          (2 * theorem_4_15_nonperiodicCandidateSigma) :=
      div_nonneg hs_nonneg (mul_nonneg (by norm_num)
        theorem_4_15_nonperiodicCandidateSigma_pos.le)
    linarith
  apply theorem_4_15_nonperiodicCandidate_selected_source_run_of_directional_bound
    epsilon
    (11 / theorem_4_15_nonperiodicCandidateSigma +
      theorem_4_15_nonperiodicCandidateThirdDerivativeScale /
        (2 * theorem_4_15_nonperiodicCandidateSigma))
    hepsilon hepsilon_le_sigma hC
  exact theorem_4_15_nonperiodicCandidate_directional_average_le
    epsilon hepsilon hepsilon_le_sigma hepsilon_small

/- The same complete source-small-`J` witness, now packaged in the single
   accuracy-indexed family required by the universal Track-B counterexample
   target.  This removes the former per-accuracy closed-over configuration
   family without changing any generated state, schedule, or source object. -/
theorem theorem_4_15_nonperiodicCandidate_accuracyIndexed_source_run_of_small_accuracy
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_small :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma / 1000) :
    theorem_4_15_otherwiseSourceSmallJGeneratedRunForAccuracyHorizon
      theorem_4_15_nonperiodicCandidateProblem
      theorem_4_15_nonperiodicCandidateConfigForAccuracyHorizon
      0 theorem_4_15_nonperiodicCandidateSigma
      theorem_4_15_nonperiodicCandidateSigma epsilon
      (11 / theorem_4_15_nonperiodicCandidateSigma +
        theorem_4_15_nonperiodicCandidateThirdDerivativeScale /
          (2 * theorem_4_15_nonperiodicCandidateSigma))
      theorem_4_15_nonperiodicCandidateThirdDerivativeScale
      1 1 1 1 1 2
      (theorem_4_15_nonperiodicCandidateHorizon epsilon) := by
  have hepsilon_le_sigma :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma := by
    nlinarith [theorem_4_15_nonperiodicCandidateSigma_pos]
  have hrun :=
    theorem_4_15_nonperiodicCandidate_selected_source_run_of_small_accuracy
      epsilon hepsilon hepsilon_small
  let runAtConfig : StochasticMuonConfig 1 1 → Prop := fun cfg =>
    theorem_4_15_otherwiseSourceSmallJGeneratedRunForAccuracyHorizon
      theorem_4_15_nonperiodicCandidateProblem (fun _accuracy _horizon => cfg)
      0 theorem_4_15_nonperiodicCandidateSigma
      theorem_4_15_nonperiodicCandidateSigma epsilon
      (11 / theorem_4_15_nonperiodicCandidateSigma +
        theorem_4_15_nonperiodicCandidateThirdDerivativeScale /
          (2 * theorem_4_15_nonperiodicCandidateSigma))
      theorem_4_15_nonperiodicCandidateThirdDerivativeScale
      1 1 1 1 1 2 (theorem_4_15_nonperiodicCandidateHorizon epsilon)
  change runAtConfig
    (theorem_4_15_nonperiodicCandidateConfigForAccuracyHorizon epsilon
      (theorem_4_15_nonperiodicCandidateHorizon epsilon))
  change runAtConfig
    (deterministicOracleConfig
      (theorem_4_15_nonperiodicCandidateConfig epsilon hepsilon
        hepsilon_le_sigma)) at hrun
  rw [theorem_4_15_nonperiodicCandidateConfigForAccuracyHorizon_eq
    epsilon (theorem_4_15_nonperiodicCandidateHorizon epsilon)
    hepsilon hepsilon_le_sigma]
  exact hrun

/- At every sufficiently small accuracy for which the explicit analytic lower
   envelope exceeds a proposed coefficient `K`, the same fixed generated run
   both satisfies all source-small-`J` hypotheses and violates the claimed
   `K * epsilon` stationarity bound.  The remaining counterexample step is now
   purely the scalar fact that this displayed envelope is unbounded as
   `epsilon` tends to zero. -/
theorem theorem_4_15_nonperiodicCandidate_source_run_and_average_gt
    (K epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_small :
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma / 1000)
    (hK : K <
      ((6 : ℝ) / 5 *
          ((theorem_4_15_nonperiodicCandidateSigma / epsilon) *
              (1 + 2 * theorem_4_15_nonperiodicCandidateSigma / epsilon) ^
                (-(4 : ℝ) / 5) -
            (5 : ℝ) / 12 - (56 : ℝ) / 5 * epsilon /
              theorem_4_15_nonperiodicCandidateSigma) -
          (396 : ℝ) / 5) /
        (2 * theorem_4_15_nonperiodicCandidateSigma)) :
    theorem_4_15_otherwiseSourceSmallJGeneratedRunForAccuracyHorizon
        theorem_4_15_nonperiodicCandidateProblem
        theorem_4_15_nonperiodicCandidateConfigForAccuracyHorizon
        0 theorem_4_15_nonperiodicCandidateSigma
        theorem_4_15_nonperiodicCandidateSigma epsilon
        (11 / theorem_4_15_nonperiodicCandidateSigma +
          theorem_4_15_nonperiodicCandidateThirdDerivativeScale /
            (2 * theorem_4_15_nonperiodicCandidateSigma))
        theorem_4_15_nonperiodicCandidateThirdDerivativeScale
        1 1 1 1 1 2
        (theorem_4_15_nonperiodicCandidateHorizon epsilon) ∧
      K * epsilon <
        stochasticAverageNuclearGradient
          theorem_4_15_nonperiodicCandidateProblem
          (theorem_4_15_nonperiodicCandidateConfigForAccuracyHorizon epsilon
            (theorem_4_15_nonperiodicCandidateHorizon epsilon))
          (theorem_4_15_nonperiodicCandidateHorizon epsilon) := by
  constructor
  · exact theorem_4_15_nonperiodicCandidate_accuracyIndexed_source_run_of_small_accuracy
      epsilon hepsilon hepsilon_small
  · have hlower :=
      theorem_4_15_nonperiodicCandidate_selected_stochasticAverage_div_accuracy_lower
        epsilon hepsilon hepsilon_small
    have hratio := lt_of_lt_of_le hK hlower
    exact (lt_div_iff₀ hepsilon).mp hratio

/- The growing term in the explicit average lower envelope is bounded below by
   a positive multiple of `x^(1/5)`.  This is the scalar comparison suggested
   by the selected-horizon normalization: for `x >= 1`, `1 + 2*x <= 3*x`, and
   the negative exponent reverses the base inequality. -/
theorem theorem_4_15_nonperiodicCandidate_leading_envelope_lower
    (x : ℝ) (hx : 1 ≤ x) :
    (3 : ℝ) ^ (-(4 : ℝ) / 5) * x ^ ((1 : ℝ) / 5) ≤
      x * (1 + 2 * x) ^ (-(4 : ℝ) / 5) := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hxnonneg : 0 ≤ x := hxpos.le
  have hbasepos : 0 < 1 + 2 * x := by linarith
  have hbasele : 1 + 2 * x ≤ 3 * x := by linarith
  have hrpow : (3 * x) ^ (-(4 : ℝ) / 5) ≤
      (1 + 2 * x) ^ (-(4 : ℝ) / 5) :=
    Real.rpow_le_rpow_of_nonpos hbasepos hbasele (by norm_num)
  have hxpow : x ^ ((1 : ℝ) / 5) =
      x * x ^ (-(4 : ℝ) / 5) := by
    convert Real.rpow_one_add' (y := -(4 : ℝ) / 5) hxnonneg
      (by norm_num) using 1 <;> norm_num
  calc
    (3 : ℝ) ^ (-(4 : ℝ) / 5) * x ^ ((1 : ℝ) / 5) =
        x * (3 * x) ^ (-(4 : ℝ) / 5) := by
          rw [Real.mul_rpow (by norm_num) hxnonneg, hxpow]
          ring
    _ ≤ x * (1 + 2 * x) ^ (-(4 : ℝ) / 5) :=
      mul_le_mul_of_nonneg_left hrpow hxnonneg

/- The displayed lower envelope therefore exceeds every fixed coefficient on
   every punctured source-accuracy neighbourhood.  The witness accuracy is
   `sigma / x`, with `x` chosen far enough along the positive `x^(1/5)` tail;
   this keeps the proof quantitative and avoids importing any generated-run
   fact into the scalar selection step. -/
theorem theorem_4_15_nonperiodicCandidate_envelope_exceeds
    (K epsilon₀ : ℝ) (hepsilon₀ : 0 < epsilon₀) :
    ∃ epsilon : ℝ,
      epsilonDomain epsilon ∧ epsilon ≤ epsilon₀ ∧
      epsilon ≤ theorem_4_15_nonperiodicCandidateSigma / 1000 ∧
      K <
        ((6 : ℝ) / 5 *
            ((theorem_4_15_nonperiodicCandidateSigma / epsilon) *
                (1 + 2 * theorem_4_15_nonperiodicCandidateSigma / epsilon) ^
                  (-(4 : ℝ) / 5) -
              (5 : ℝ) / 12 - (56 : ℝ) / 5 * epsilon /
                theorem_4_15_nonperiodicCandidateSigma) -
            (396 : ℝ) / 5) /
          (2 * theorem_4_15_nonperiodicCandidateSigma) := by
  let sigma := theorem_4_15_nonperiodicCandidateSigma
  let c : ℝ := (3 : ℝ) ^ (-(4 : ℝ) / 5)
  let R : ℝ :=
    (2 * sigma * K + (396 : ℝ) / 5) * (5 / 6) +
      (5 : ℝ) / 12 + (56 : ℝ) / 5
  have hsigma : 0 < sigma := by
    simpa [sigma] using theorem_4_15_nonperiodicCandidateSigma_pos
  have hc : 0 < c := by
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hgrow : Filter.Tendsto (fun x : ℝ => x ^ ((1 : ℝ) / 5))
      Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop (by norm_num)
  obtain ⟨x₀, hx₀⟩ :=
    (hgrow.eventually_gt_atTop (R / c)).exists_forall_of_atTop
  let x : ℝ := max x₀ (max 1000 (sigma / epsilon₀))
  have hxx₀ : x₀ ≤ x := le_max_left _ _
  have hx1000 : (1000 : ℝ) ≤ x :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hxsigma : sigma / epsilon₀ ≤ x :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hxone : (1 : ℝ) ≤ x := by linarith
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx1000
  have hroot : R / c < x ^ ((1 : ℝ) / 5) := hx₀ x hxx₀
  have hR : R < c * x ^ ((1 : ℝ) / 5) :=
    by simpa [mul_comm] using (div_lt_iff₀ hc).mp hroot
  have hlead :=
    theorem_4_15_nonperiodicCandidate_leading_envelope_lower x hxone
  have hmain : R < x * (1 + 2 * x) ^ (-(4 : ℝ) / 5) :=
    hR.trans_le (by simpa [c] using hlead)
  let epsilon : ℝ := sigma / x
  have hepsilon : 0 < epsilon := div_pos hsigma hxpos
  have hepsilon_le : epsilon ≤ epsilon₀ := by
    apply (div_le_iff₀ hxpos).2
    calc
      sigma = epsilon₀ * (sigma / epsilon₀) := by
        field_simp [ne_of_gt hepsilon₀]
      _ ≤ epsilon₀ * x :=
        mul_le_mul_of_nonneg_left hxsigma hepsilon₀.le
  have hepsilon_small : epsilon ≤ sigma / 1000 := by
    exact (div_le_div_iff_of_pos_left hsigma hxpos (by norm_num)).2 hx1000
  have hsigma_div : sigma / epsilon = x := by
    dsimp [epsilon]
    field_simp [ne_of_gt hsigma, ne_of_gt hxpos]
  have hepsilon_div : epsilon / sigma = 1 / x := by
    dsimp [epsilon]
    field_simp [ne_of_gt hsigma, ne_of_gt hxpos]
  have htwo_sigma_div : 2 * sigma / epsilon = 2 * x := by
    calc
      2 * sigma / epsilon = 2 * (sigma / epsilon) := by ring
      _ = 2 * x := by rw [hsigma_div]
  have hcorrection_div : (56 : ℝ) / 5 * epsilon / sigma =
      (56 : ℝ) / 5 * (1 / x) := by
    calc
      (56 : ℝ) / 5 * epsilon / sigma =
          (56 : ℝ) / 5 * (epsilon / sigma) := by ring
      _ = (56 : ℝ) / 5 * (1 / x) := by rw [hepsilon_div]
  have hinv_le_one : 1 / x ≤ (1 : ℝ) := by
    exact (div_le_one hxpos).2 hxone
  refine ⟨epsilon, hepsilon, hepsilon_le, ?_, ?_⟩
  · simpa [sigma] using hepsilon_small
  · change K <
      ((6 : ℝ) / 5 *
          ((sigma / epsilon) * (1 + 2 * sigma / epsilon) ^ (-(4 : ℝ) / 5) -
            (5 : ℝ) / 12 - (56 : ℝ) / 5 * epsilon / sigma) -
        (396 : ℝ) / 5) / (2 * sigma)
    rw [hsigma_div, htwo_sigma_div, hcorrection_div]
    apply (lt_div_iff₀ (mul_pos (by norm_num) hsigma)).2
    dsimp [R] at hmain
    nlinarith

/- This is the completed original-object counterexample.  For every proposed
   `O(epsilon)` coefficient and every positive source neighbourhood, it selects
   an accuracy inside that neighbourhood and the registered printed-scale
   horizon.  The exact generated stochastic run satisfies Assumptions 4.13 and
   3.3, the constant-step schedule, and directional-`J` control, while its
   actual generated nuclear-gradient average is larger than `K * epsilon`. -/
theorem theorem_4_15_nonperiodicCandidate_source_smallJ_counterexample
    (K epsilon₀ : ℝ) (hepsilon₀ : 0 < epsilon₀) :
    ∃ epsilon : ℝ,
      epsilonDomain epsilon ∧ epsilon ≤ epsilon₀ ∧
      theorem_4_15_otherwiseSourceSmallJGeneratedRunForAccuracyHorizon
          theorem_4_15_nonperiodicCandidateProblem
          theorem_4_15_nonperiodicCandidateConfigForAccuracyHorizon
          0 theorem_4_15_nonperiodicCandidateSigma
          theorem_4_15_nonperiodicCandidateSigma epsilon
          (11 / theorem_4_15_nonperiodicCandidateSigma +
            theorem_4_15_nonperiodicCandidateThirdDerivativeScale /
              (2 * theorem_4_15_nonperiodicCandidateSigma))
          theorem_4_15_nonperiodicCandidateThirdDerivativeScale
          1 1 1 1 1 2
          (theorem_4_15_nonperiodicCandidateHorizon epsilon) ∧
      K * epsilon <
        stochasticAverageNuclearGradient
          theorem_4_15_nonperiodicCandidateProblem
          (theorem_4_15_nonperiodicCandidateConfigForAccuracyHorizon epsilon
            (theorem_4_15_nonperiodicCandidateHorizon epsilon))
          (theorem_4_15_nonperiodicCandidateHorizon epsilon) := by
  obtain ⟨epsilon, hepsilon, hepsilon_le, hepsilon_small, henvelope⟩ :=
    theorem_4_15_nonperiodicCandidate_envelope_exceeds K epsilon₀ hepsilon₀
  obtain ⟨hrun, havg⟩ :=
    theorem_4_15_nonperiodicCandidate_source_run_and_average_gt
      K epsilon hepsilon hepsilon_small henvelope
  exact ⟨epsilon, hepsilon, hepsilon_le, hrun, havg⟩

/- These are the exact scalar recurrences of the generated one-dimensional
   sine-objective Algorithm 1 orbit.  They cover positive momentum, negative
   momentum, and a zero-momentum index uniformly via `Real.sign`; hence every
   cosine sign change and every delayed momentum switch can now be studied on
   the actual generated process rather than through a prefix hypothesis. -/
theorem theorem_4_15_periodicCandidate_full_orbit_scalar_recurrence
    (cfg : DeterministicMomentumMuonConfig 1 1) (t : ℕ) :
    let state := deterministicMomentumMuonState
      theorem_4_15_periodicCandidateObjective cfg t
    let nextState := deterministicMomentumMuonState
      theorem_4_15_periodicCandidateObjective cfg (t + 1)
    theorem_4_5_counterexampleEntry nextState.W =
        theorem_4_5_counterexampleEntry state.W -
          cfg.eta t * Real.sign (state.M 0 0) ∧
      nextState.M 0 0 =
        cfg.beta * state.M 0 0 +
          (1 - cfg.beta) *
            Real.cos (theorem_4_5_counterexampleEntry nextState.W) := by
  dsimp only
  constructor
  · rw [deterministicMomentumMuon_W_succ_eq_source_update,
      orthogonalizedDirection_eq_sign_smul_one_dimensional]
    simp [theorem_4_5_counterexampleEntry_apply, coordinateMatrix]
  · rw [deterministicMomentumMuon_M_succ_eq_source_update]
    unfold deterministicGradient
    rw [theorem_4_15_periodicCandidateObjective_grad]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

/- The scalar momentum of the exact generated periodic-candidate orbit always
   remains in the convex hull of the cosine gradients.  This supplies the
   quantitative starting bound needed at every later reversal without adding
   a fresh momentum hypothesis at the restart index. -/
theorem theorem_4_15_periodicCandidate_momentum_mem_Icc
    (cfg : DeterministicMomentumMuonConfig 1 1) (t : ℕ) :
    (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg t).M 0 0 ∈
      Set.Icc (-1 : ℝ) 1 := by
  induction t with
  | zero =>
      rw [deterministicMomentumMuon_M_zero_eq_gradient]
      unfold deterministicGradient
      rw [theorem_4_15_periodicCandidateObjective_grad]
      simp only [Matrix.smul_apply, smul_eq_mul,
        theorem_4_5_counterexampleEntry_apply, coordinateMatrix]
      exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  | succ t ih =>
      have hrecurrence :=
        (theorem_4_15_periodicCandidate_full_orbit_scalar_recurrence cfg t).2
      have hbeta : 0 ≤ cfg.beta := cfg.beta_mem.1
      have honeSubBeta : 0 ≤ 1 - cfg.beta :=
        sub_nonneg.mpr cfg.beta_mem.2.le
      have hcosLower := mul_le_mul_of_nonneg_left
        (Real.neg_one_le_cos
          (theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg (t + 1)).W))
        honeSubBeta
      have hcosUpper := mul_le_mul_of_nonneg_left
        (Real.cos_le_one
          (theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg (t + 1)).W))
        honeSubBeta
      have hmomentumLower := mul_le_mul_of_nonneg_left ih.1 hbeta
      have hmomentumUpper := mul_le_mul_of_nonneg_left ih.2 hbeta
      rw [hrecurrence]
      constructor <;> nlinarith

/- A block of generated gradients bounded above by `-c` forces the exact
   momentum toward `-c` at the geometric rate `beta^t`.  The statement starts
   at an arbitrary generated index and uses only the Algorithm 1 recurrence;
   in particular, its conclusion is the negative seed needed by the return-leg
   lemmas rather than an assumption of that seed. -/
theorem theorem_4_15_periodicCandidate_momentum_upper_bound_after_negative_block
    (cfg : DeterministicMomentumMuonConfig 1 1) (c : ℝ)
    (start t : ℕ)
    (hMstart :
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg start).M 0 0 ≤ 1)
    (hgradient : ∀ k < t,
      Real.cos (theorem_4_5_counterexampleEntry
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg
          (start + k + 1)).W) ≤ -c) :
    (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + t)).M 0 0 ≤
      cfg.beta ^ t * (1 + c) - c := by
  induction t with
  | zero =>
      simpa using hMstart
  | succ t ih =>
      have hprefix : ∀ k < t,
          Real.cos (theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg
              (start + k + 1)).W) ≤ -c := by
        intro k hk
        exact hgradient k (lt_trans hk (Nat.lt_succ_self t))
      have hih := ih hprefix
      have hscaled := mul_le_mul_of_nonneg_left hih cfg.beta_mem.1
      have hcos := mul_le_mul_of_nonneg_left
        (hgradient t (Nat.lt_succ_self t))
        (sub_nonneg.mpr cfg.beta_mem.2.le)
      have hrecurrence :=
        (theorem_4_15_periodicCandidate_full_orbit_scalar_recurrence
          cfg (start + t)).2
      rw [show start + (t + 1) = start + t + 1 by omega, hrecurrence]
      calc
        cfg.beta *
              (deterministicMomentumMuonState
                theorem_4_15_periodicCandidateObjective cfg (start + t)).M 0 0 +
            (1 - cfg.beta) *
              Real.cos (theorem_4_5_counterexampleEntry
                (deterministicMomentumMuonState
                  theorem_4_15_periodicCandidateObjective cfg
                  (start + t + 1)).W) ≤
            cfg.beta * (cfg.beta ^ t * (1 + c) - c) +
              (1 - cfg.beta) * (-c) := add_le_add hscaled hcos
        _ = cfg.beta ^ (t + 1) * (1 + c) - c := by
          rw [pow_succ]
          ring

/- The sign-symmetric accumulation statement produces positive momentum from
   a block of generated gradients bounded below by `c`. -/
theorem theorem_4_15_periodicCandidate_momentum_lower_bound_after_positive_block
    (cfg : DeterministicMomentumMuonConfig 1 1) (c : ℝ)
    (start t : ℕ)
    (hMstart : (-1 : ℝ) ≤
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg start).M 0 0)
    (hgradient : ∀ k < t, c ≤
      Real.cos (theorem_4_5_counterexampleEntry
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg
          (start + k + 1)).W)) :
    c - cfg.beta ^ t * (1 + c) ≤
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + t)).M 0 0 := by
  induction t with
  | zero =>
      simpa using hMstart
  | succ t ih =>
      have hprefix : ∀ k < t, c ≤
          Real.cos (theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg
              (start + k + 1)).W) := by
        intro k hk
        exact hgradient k (lt_trans hk (Nat.lt_succ_self t))
      have hih := ih hprefix
      have hscaled := mul_le_mul_of_nonneg_left hih cfg.beta_mem.1
      have hcos := mul_le_mul_of_nonneg_left
        (hgradient t (Nat.lt_succ_self t))
        (sub_nonneg.mpr cfg.beta_mem.2.le)
      have hrecurrence :=
        (theorem_4_15_periodicCandidate_full_orbit_scalar_recurrence
          cfg (start + t)).2
      rw [show start + (t + 1) = start + t + 1 by omega, hrecurrence]
      calc
        c - cfg.beta ^ (t + 1) * (1 + c) =
            cfg.beta * (c - cfg.beta ^ t * (1 + c)) +
              (1 - cfg.beta) * c := by
          rw [pow_succ]
          ring
        _ ≤ cfg.beta *
              (deterministicMomentumMuonState
                theorem_4_15_periodicCandidateObjective cfg (start + t)).M 0 0 +
            (1 - cfg.beta) *
              Real.cos (theorem_4_5_counterexampleEntry
                (deterministicMomentumMuonState
                  theorem_4_15_periodicCandidateObjective cfg
                  (start + t + 1)).W) := add_le_add hscaled hcos

/- Once a negative-gradient block is long enough for its geometric remainder
   to fall below `c - m0`, the generated recurrence itself supplies a
   quantitative negative reversal seed. -/
theorem theorem_4_15_periodicCandidate_negative_reversal_seed
    (cfg : DeterministicMomentumMuonConfig 1 1) (c m0 : ℝ)
    (start t : ℕ) (hm0 : 0 < m0)
    (hdecay : cfg.beta ^ t * (1 + c) ≤ c - m0)
    (hgradient : ∀ k < t,
      Real.cos (theorem_4_5_counterexampleEntry
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg
          (start + k + 1)).W) ≤ -c) :
    (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + t)).M 0 0 ≤ -m0 ∧
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + t)).M 0 0 < 0 := by
  have hbound :=
    theorem_4_15_periodicCandidate_momentum_upper_bound_after_negative_block
      cfg c start t
      (theorem_4_15_periodicCandidate_momentum_mem_Icc cfg start).2 hgradient
  constructor <;> linarith

/- Likewise, a sufficiently long positive-gradient block supplies the
   quantitative positive seed for the next outgoing leg. -/
theorem theorem_4_15_periodicCandidate_positive_reversal_seed
    (cfg : DeterministicMomentumMuonConfig 1 1) (c m0 : ℝ)
    (start t : ℕ) (hm0 : 0 < m0)
    (hdecay : cfg.beta ^ t * (1 + c) ≤ c - m0)
    (hgradient : ∀ k < t, c ≤
      Real.cos (theorem_4_5_counterexampleEntry
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg
          (start + k + 1)).W)) :
    m0 ≤ (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + t)).M 0 0 ∧
      0 < (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + t)).M 0 0 := by
  have hbound :=
    theorem_4_15_periodicCandidate_momentum_lower_bound_after_positive_block
      cfg c start t
      (theorem_4_15_periodicCandidate_momentum_mem_Icc cfg start).1 hgradient
  constructor <;> linarith

/- While the generated scalar momentum remains positive, the exact Algorithm 1
   phase advances by `-eta` at every step.  Stating this from an arbitrary
   generated index isolates the only sign information needed to locate the
   first reversal block; no independent trajectory or direction is supplied. -/
theorem theorem_4_15_periodicCandidate_phase_after_positive_momentum_block
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta : ℝ)
    (start t : ℕ)
    (heta : ∀ k < t, cfg.eta (start + k) = eta)
    (hpositive : ∀ k < t, 0 <
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + k)).M 0 0) :
    theorem_4_5_counterexampleEntry
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg (start + t)).W =
      theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg start).W -
        (t : ℝ) * eta := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hetaPrefix : ∀ k < t, cfg.eta (start + k) = eta := by
        intro k hk
        exact heta k (lt_trans hk (Nat.lt_succ_self t))
      have hpositivePrefix : ∀ k < t, 0 <
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg (start + k)).M 0 0 := by
        intro k hk
        exact hpositive k (lt_trans hk (Nat.lt_succ_self t))
      have hphase := ih hetaPrefix hpositivePrefix
      have hstep :=
        (theorem_4_15_periodicCandidate_full_orbit_scalar_recurrence
          cfg (start + t)).1
      rw [show start + (t + 1) = start + t + 1 by omega, hstep,
        Real.sign_of_pos (hpositive t (Nat.lt_succ_self t)),
        heta t (Nat.lt_succ_self t), hphase]
      push_cast
      ring

/- Endpoint containment of a positive-momentum affine leg in a half-width
   `1/2` neighbourhood of a phase where `cos = -1` forces every generated
   gradient in the block below `-1/2`.  The geometric recurrence then supplies
   the negative reversal seed.  Thus the block hypothesis needed by the prior
   seed theorem is now reduced to phase endpoints and the pre-reversal sign,
   both properties of the exact generated orbit. -/
theorem theorem_4_15_periodicCandidate_negative_reversal_seed_from_phase_block
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta m0 center : ℝ)
    (start t : ℕ) (hm0 : 0 < m0) (hetaNonneg : 0 ≤ eta)
    (heta : ∀ k < t, cfg.eta (start + k) = eta)
    (hpositive : ∀ k < t, 0 <
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + k)).M 0 0)
    (hcenter : Real.cos center = -1)
    (hphaseLower : center - (1 : ℝ) / 2 ≤
      theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg start).W -
        (t : ℝ) * eta)
    (hphaseUpper :
      theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg start).W - eta ≤
        center + (1 : ℝ) / 2)
    (hdecay : cfg.beta ^ t * (1 + (1 : ℝ) / 2) ≤ (1 : ℝ) / 2 - m0) :
    (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + t)).M 0 0 ≤ -m0 ∧
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + t)).M 0 0 < 0 := by
  apply theorem_4_15_periodicCandidate_negative_reversal_seed
    cfg ((1 : ℝ) / 2) m0 start t hm0 hdecay
  intro k hk
  have hkSuccLe : k + 1 ≤ t := Nat.succ_le_iff.mpr hk
  have hetaPrefix : ∀ j < k + 1, cfg.eta (start + j) = eta := by
    intro j hj
    exact heta j (lt_of_lt_of_le hj hkSuccLe)
  have hpositivePrefix : ∀ j < k + 1, 0 <
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + j)).M 0 0 := by
    intro j hj
    exact hpositive j (lt_of_lt_of_le hj hkSuccLe)
  have hphase :=
    theorem_4_15_periodicCandidate_phase_after_positive_momentum_block
      cfg eta start (k + 1) hetaPrefix hpositivePrefix
  let x : ℝ := theorem_4_5_counterexampleEntry
    (deterministicMomentumMuonState
      theorem_4_15_periodicCandidateObjective cfg (start + k + 1)).W
  have hx : x =
      theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg start).W -
        ((k + 1 : ℕ) : ℝ) * eta := by
    simpa [x, Nat.add_assoc] using hphase
  have hkOne : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hkT : ((k + 1 : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast hkSuccLe
  have hxLower : center - (1 : ℝ) / 2 ≤ x := by
    rw [hx]
    have hmul := mul_le_mul_of_nonneg_right hkT hetaNonneg
    linarith
  have hxUpper : x ≤ center + (1 : ℝ) / 2 := by
    rw [hx]
    have hmul := mul_le_mul_of_nonneg_right hkOne hetaNonneg
    linarith
  have hdistance : |center - x| ≤ (1 : ℝ) / 2 := by
    rw [abs_le]
    constructor <;> linarith
  have hcosDistance := Real.abs_cos_sub_cos_le center x
  have hcosClose : |Real.cos center - Real.cos x| ≤ (1 : ℝ) / 2 :=
    le_trans hcosDistance hdistance
  rw [hcenter] at hcosClose
  have hcosUpper : Real.cos x ≤ -((2 : ℝ)⁻¹) := by
    have := (abs_le.mp hcosClose).1
    linarith
  simpa [x] using hcosUpper

/- The sign-symmetric affine phase identity is used after a proved negative
   reversal.  It makes the return leg advance by `+eta` from its generated
   restart state. -/
theorem theorem_4_15_periodicCandidate_phase_after_negative_momentum_block
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta : ℝ)
    (start t : ℕ)
    (heta : ∀ k < t, cfg.eta (start + k) = eta)
    (hnegative : ∀ k < t,
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + k)).M 0 0 < 0) :
    theorem_4_5_counterexampleEntry
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg (start + t)).W =
      theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg start).W +
        (t : ℝ) * eta := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hetaPrefix : ∀ k < t, cfg.eta (start + k) = eta := by
        intro k hk
        exact heta k (lt_trans hk (Nat.lt_succ_self t))
      have hnegativePrefix : ∀ k < t,
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg (start + k)).M 0 0 < 0 := by
        intro k hk
        exact hnegative k (lt_trans hk (Nat.lt_succ_self t))
      have hphase := ih hetaPrefix hnegativePrefix
      have hstep :=
        (theorem_4_15_periodicCandidate_full_orbit_scalar_recurrence
          cfg (start + t)).1
      rw [show start + (t + 1) = start + t + 1 by omega, hstep,
        Real.sign_of_neg (hnegative t (Nat.lt_succ_self t)),
        heta t (Nat.lt_succ_self t), hphase]
      push_cast
      ring

/- A descending arithmetic progression with mesh at most `pi / 8` cannot
   traverse a full period without visiting the `pi / 8` neighbourhood of an
   integer multiple of `pi`.  The selected index is bounded by the supplied
   travel horizon.  This is the discrete phase-selection fact needed to turn
   a long exact positive-momentum leg into a generated phase hit. -/
theorem theorem_4_15_periodicCandidate_descending_grid_has_phase_hit
    (x eta : ℝ) (t : ℕ) (heta : 0 < eta)
    (hetaSmall : eta ≤ Real.pi / 8)
    (htravel : Real.pi ≤ (t : ℝ) * eta) :
    ∃ k : ℕ, k ≤ t ∧ ∃ z : ℤ,
      |x - (k : ℝ) * eta - (z : ℝ) * Real.pi| ≤ Real.pi / 8 := by
  let z : ℤ := ⌊x / Real.pi⌋
  let d : ℝ := x - (z : ℝ) * Real.pi
  have hzLowerDiv : (z : ℝ) ≤ x / Real.pi := by
    simpa [z] using Int.floor_le (x / Real.pi)
  have hzLower : (z : ℝ) * Real.pi ≤ x :=
    (le_div_iff₀ Real.pi_pos).mp hzLowerDiv
  have hxUpperDiv : x / Real.pi < (z : ℝ) + 1 := by
    simpa [z] using Int.lt_floor_add_one (x / Real.pi)
  have hxUpper : x < ((z : ℝ) + 1) * Real.pi :=
    (div_lt_iff₀ Real.pi_pos).mp hxUpperDiv
  have hdNonneg : 0 ≤ d := by
    dsimp [d]
    linarith
  have hdLtPi : d < Real.pi := by
    dsimp [d]
    linarith
  let k : ℕ := Nat.floor (d / eta)
  have hratioNonneg : 0 ≤ d / eta := div_nonneg hdNonneg heta.le
  have hkRatio : (k : ℝ) ≤ d / eta := by
    simpa [k] using Nat.floor_le hratioNonneg
  have hkMul : (k : ℝ) * eta ≤ d :=
    (le_div_iff₀ heta).mp hkRatio
  have hratioSucc : d / eta < (k : ℝ) + 1 := by
    simpa [k] using Nat.lt_floor_add_one (d / eta)
  have hdSucc : d < ((k : ℝ) + 1) * eta :=
    (div_lt_iff₀ heta).mp hratioSucc
  have hdLeTravel : d ≤ (t : ℝ) * eta :=
    hdLtPi.le.trans htravel
  have hratioLeT : d / eta ≤ (t : ℝ) :=
    (div_le_iff₀ heta).2 hdLeTravel
  have hkCastLeT : (k : ℝ) ≤ (t : ℝ) := hkRatio.trans hratioLeT
  have hkLeT : k ≤ t := by exact_mod_cast hkCastLeT
  refine ⟨k, hkLeT, z, ?_⟩
  have herrorNonneg :
      0 ≤ x - (k : ℝ) * eta - (z : ℝ) * Real.pi := by
    dsimp [d] at hkMul
    linarith
  rw [abs_of_nonneg herrorNonneg]
  have herrorLtEta :
      x - (k : ℝ) * eta - (z : ℝ) * Real.pi < eta := by
    dsimp [d] at hdSucc
    linarith
  exact herrorLtEta.le.trans hetaSmall

/- The sign-symmetric ascending-grid selector.  Choosing the next integer
   multiple above the initial phase makes the endpoint case explicit and
   avoids any irrationality assumption on `eta / pi`. -/
theorem theorem_4_15_periodicCandidate_ascending_grid_has_phase_hit
    (x eta : ℝ) (t : ℕ) (heta : 0 < eta)
    (hetaSmall : eta ≤ Real.pi / 8)
    (htravel : Real.pi ≤ (t : ℝ) * eta) :
    ∃ k : ℕ, k ≤ t ∧ ∃ z : ℤ,
      |x + (k : ℝ) * eta - (z : ℝ) * Real.pi| ≤ Real.pi / 8 := by
  let z : ℤ := ⌊x / Real.pi⌋ + 1
  let d : ℝ := (z : ℝ) * Real.pi - x
  have hfloorLowerDiv : ((⌊x / Real.pi⌋ : ℤ) : ℝ) ≤ x / Real.pi :=
    Int.floor_le (x / Real.pi)
  have hfloorLower :
      ((⌊x / Real.pi⌋ : ℤ) : ℝ) * Real.pi ≤ x :=
    (le_div_iff₀ Real.pi_pos).mp hfloorLowerDiv
  have hxUpperDiv :
      x / Real.pi < (((⌊x / Real.pi⌋ : ℤ) : ℝ) + 1) := by
    simpa using Int.lt_floor_add_one (x / Real.pi)
  have hxUpper :
      x < (((⌊x / Real.pi⌋ : ℤ) : ℝ) + 1) * Real.pi :=
    (div_lt_iff₀ Real.pi_pos).mp hxUpperDiv
  have hzCast : (z : ℝ) = (((⌊x / Real.pi⌋ : ℤ) : ℝ) + 1) := by
    simp [z]
  have hdNonneg : 0 ≤ d := by
    dsimp [d]
    rw [hzCast]
    linarith
  have hdLePi : d ≤ Real.pi := by
    dsimp [d]
    rw [hzCast]
    linarith
  let k : ℕ := Nat.floor (d / eta)
  have hratioNonneg : 0 ≤ d / eta := div_nonneg hdNonneg heta.le
  have hkRatio : (k : ℝ) ≤ d / eta := by
    simpa [k] using Nat.floor_le hratioNonneg
  have hkMul : (k : ℝ) * eta ≤ d :=
    (le_div_iff₀ heta).mp hkRatio
  have hratioSucc : d / eta < (k : ℝ) + 1 := by
    simpa [k] using Nat.lt_floor_add_one (d / eta)
  have hdSucc : d < ((k : ℝ) + 1) * eta :=
    (div_lt_iff₀ heta).mp hratioSucc
  have hdLeTravel : d ≤ (t : ℝ) * eta := hdLePi.trans htravel
  have hratioLeT : d / eta ≤ (t : ℝ) :=
    (div_le_iff₀ heta).2 hdLeTravel
  have hkCastLeT : (k : ℝ) ≤ (t : ℝ) := hkRatio.trans hratioLeT
  have hkLeT : k ≤ t := by exact_mod_cast hkCastLeT
  refine ⟨k, hkLeT, z, ?_⟩
  have herrorNonpos :
      x + (k : ℝ) * eta - (z : ℝ) * Real.pi ≤ 0 := by
    dsimp [d] at hkMul
    linarith
  rw [abs_of_nonpos herrorNonpos]
  have herrorLtEta :
      -(x + (k : ℝ) * eta - (z : ℝ) * Real.pi) < eta := by
    dsimp [d] at hdSucc
    linarith
  exact herrorLtEta.le.trans hetaSmall

/- The floor construction used by the two phase-hit lemmas contains more
   information than the coarse `pi / 8` conclusion: the selected descending
   grid point lies on the nonnegative side of an integer multiple of `pi`, at
   distance strictly less than one mesh step.  Retaining this orientation is
   what permits a whole neighbouring window, rather than one point, to be
   counted below. -/
theorem theorem_4_15_periodicCandidate_descending_grid_has_oriented_phase_hit
    (x eta : ℝ) (t : ℕ) (heta : 0 < eta)
    (htravel : Real.pi ≤ (t : ℝ) * eta) :
    ∃ k : ℕ, k ≤ t ∧ ∃ z : ℤ,
      0 ≤ x - (k : ℝ) * eta - (z : ℝ) * Real.pi ∧
        x - (k : ℝ) * eta - (z : ℝ) * Real.pi < eta := by
  let z : ℤ := ⌊x / Real.pi⌋
  let d : ℝ := x - (z : ℝ) * Real.pi
  have hzLowerDiv : (z : ℝ) ≤ x / Real.pi := by
    simpa [z] using Int.floor_le (x / Real.pi)
  have hzLower : (z : ℝ) * Real.pi ≤ x :=
    (le_div_iff₀ Real.pi_pos).mp hzLowerDiv
  have hxUpperDiv : x / Real.pi < (z : ℝ) + 1 := by
    simpa [z] using Int.lt_floor_add_one (x / Real.pi)
  have hxUpper : x < ((z : ℝ) + 1) * Real.pi :=
    (div_lt_iff₀ Real.pi_pos).mp hxUpperDiv
  have hdNonneg : 0 ≤ d := by
    dsimp [d]
    linarith
  have hdLtPi : d < Real.pi := by
    dsimp [d]
    linarith
  let k : ℕ := Nat.floor (d / eta)
  have hratioNonneg : 0 ≤ d / eta := div_nonneg hdNonneg heta.le
  have hkRatio : (k : ℝ) ≤ d / eta := by
    simpa [k] using Nat.floor_le hratioNonneg
  have hkMul : (k : ℝ) * eta ≤ d :=
    (le_div_iff₀ heta).mp hkRatio
  have hratioSucc : d / eta < (k : ℝ) + 1 := by
    simpa [k] using Nat.lt_floor_add_one (d / eta)
  have hdSucc : d < ((k : ℝ) + 1) * eta :=
    (div_lt_iff₀ heta).mp hratioSucc
  have hdLeTravel : d ≤ (t : ℝ) * eta :=
    hdLtPi.le.trans htravel
  have hratioLeT : d / eta ≤ (t : ℝ) :=
    (div_le_iff₀ heta).2 hdLeTravel
  have hkCastLeT : (k : ℝ) ≤ (t : ℝ) := hkRatio.trans hratioLeT
  have hkLeT : k ≤ t := by exact_mod_cast hkCastLeT
  refine ⟨k, hkLeT, z, ?_, ?_⟩
  · dsimp [d] at hkMul
    linarith
  · dsimp [d] at hdSucc
    linarith

/- The ascending selector is obtained by reflecting the descending grid.  Its
   error is nonpositive and has magnitude less than one mesh step. -/
theorem theorem_4_15_periodicCandidate_ascending_grid_has_oriented_phase_hit
    (x eta : ℝ) (t : ℕ) (heta : 0 < eta)
    (htravel : Real.pi ≤ (t : ℝ) * eta) :
    ∃ k : ℕ, k ≤ t ∧ ∃ z : ℤ,
      -eta < x + (k : ℝ) * eta - (z : ℝ) * Real.pi ∧
        x + (k : ℝ) * eta - (z : ℝ) * Real.pi ≤ 0 := by
  rcases
      theorem_4_15_periodicCandidate_descending_grid_has_oriented_phase_hit
        (-x) eta t heta htravel with
    ⟨k, hk, z, hnonneg, hlt⟩
  refine ⟨k, hk, -z, ?_, ?_⟩ <;> push_cast at * <;> linarith

/- A full-period grid leg contains not just one phase hit but a contiguous
   window of any prescribed half-width `ell` whose mesh width fits in
   `pi / 8`.  The window is chosen on whichever side of the oriented hit has
   enough room.  Its exact cardinality is `ell + 1`, so later source-schedule
   arithmetic can retain the `1 / eta` multiplicity lost by a one-point
   certificate. -/
theorem theorem_4_15_periodicCandidate_descending_grid_dense_phase_window
    (x eta : ℝ) (t ell : ℕ) (heta : 0 < eta)
    (hroom : 2 * ell ≤ t)
    (hwidth : ((ell + 1 : ℕ) : ℝ) * eta ≤ Real.pi / 8)
    (htravel : Real.pi ≤ (t : ℝ) * eta) :
    ∃ S : Finset ℕ, S.card = ell + 1 ∧
      ∀ j ∈ S, j ≤ t ∧ ∃ z : ℤ,
        |x - (j : ℝ) * eta - (z : ℝ) * Real.pi| ≤ Real.pi / 8 := by
  rcases
      theorem_4_15_periodicCandidate_descending_grid_has_oriented_phase_hit
        x eta t heta htravel with
    ⟨k, hk, z, herrorNonneg, herrorLt⟩
  have hetaSmall : eta ≤ Real.pi / 8 := by
    calc
      eta ≤ ((ell + 1 : ℕ) : ℝ) * eta := by
        have hellNonneg : (0 : ℝ) ≤ (ell : ℝ) := by positivity
        push_cast
        nlinarith
      _ ≤ Real.pi / 8 := hwidth
  by_cases hellk : ell ≤ k
  · refine ⟨Finset.Icc (k - ell) k, ?_, ?_⟩
    · rw [Nat.card_Icc]
      omega
    · intro j hj
      have hjBounds := Finset.mem_Icc.mp hj
      have hjk : j ≤ k := hjBounds.2
      have hdiff : k - j ≤ ell := by omega
      have hdiffReal : ((k - j : ℕ) : ℝ) ≤ (ell : ℝ) := by
        exact_mod_cast hdiff
      have hmul : ((k - j : ℕ) : ℝ) * eta ≤ (ell : ℝ) * eta :=
        mul_le_mul_of_nonneg_right hdiffReal heta.le
      refine ⟨hjk.trans hk, z, ?_⟩
      have hcast : (k : ℝ) = (j : ℝ) + ((k - j : ℕ) : ℝ) := by
        exact_mod_cast (show k = j + (k - j) by omega)
      rw [abs_of_nonneg]
      · have hellWidth : (ell : ℝ) * eta + eta ≤ Real.pi / 8 := by
          norm_num at hwidth ⊢
          linarith
        rw [hcast] at herrorNonneg herrorLt
        linarith
      · rw [hcast] at herrorNonneg
        nlinarith
  · have hkell : k < ell := lt_of_not_ge hellk
    have hkend : k + ell ≤ t := by omega
    refine ⟨Finset.Icc k (k + ell), ?_, ?_⟩
    · rw [Nat.card_Icc]
      omega
    · intro j hj
      have hjBounds := Finset.mem_Icc.mp hj
      have hkj : k ≤ j := hjBounds.1
      have hjend : j ≤ k + ell := hjBounds.2
      have hdiff : j - k ≤ ell := by omega
      have hdiffReal : ((j - k : ℕ) : ℝ) ≤ (ell : ℝ) := by
        exact_mod_cast hdiff
      have hmul : ((j - k : ℕ) : ℝ) * eta ≤ (ell : ℝ) * eta :=
        mul_le_mul_of_nonneg_right hdiffReal heta.le
      refine ⟨hjend.trans hkend, z, ?_⟩
      have hcast : (j : ℝ) = (k : ℝ) + ((j - k : ℕ) : ℝ) := by
        exact_mod_cast (show j = k + (j - k) by omega)
      have herrorEq :
          x - (j : ℝ) * eta - (z : ℝ) * Real.pi =
            (x - (k : ℝ) * eta - (z : ℝ) * Real.pi) -
              ((j - k : ℕ) : ℝ) * eta := by
        rw [hcast]
        ring
      rw [abs_le]
      constructor
      · rw [herrorEq]
        have hellWidth : (ell : ℝ) * eta + eta ≤ Real.pi / 8 := by
          norm_num at hwidth ⊢
          linarith
        linarith
      · rw [herrorEq]
        have hdiffNonneg : 0 ≤ ((j - k : ℕ) : ℝ) * eta :=
          mul_nonneg (by positivity) heta.le
        linarith

/- Reflection gives the identical dense-window count for an ascending grid. -/
theorem theorem_4_15_periodicCandidate_ascending_grid_dense_phase_window
    (x eta : ℝ) (t ell : ℕ) (heta : 0 < eta)
    (hroom : 2 * ell ≤ t)
    (hwidth : ((ell + 1 : ℕ) : ℝ) * eta ≤ Real.pi / 8)
    (htravel : Real.pi ≤ (t : ℝ) * eta) :
    ∃ S : Finset ℕ, S.card = ell + 1 ∧
      ∀ j ∈ S, j ≤ t ∧ ∃ z : ℤ,
        |x + (j : ℝ) * eta - (z : ℝ) * Real.pi| ≤ Real.pi / 8 := by
  rcases theorem_4_15_periodicCandidate_descending_grid_dense_phase_window
      (-x) eta t ell heta hroom hwidth htravel with ⟨S, hcard, hS⟩
  refine ⟨S, hcard, ?_⟩
  intro j hj
  rcases hS j hj with ⟨hjt, z, hphase⟩
  refine ⟨hjt, -z, ?_⟩
  have hneg :
      x + (j : ℝ) * eta - ((-z : ℤ) : ℝ) * Real.pi =
        -((-x) - (j : ℝ) * eta - (z : ℝ) * Real.pi) := by
    push_cast
    ring
  rw [hneg, abs_neg]
  exact hphase

/- Hence every exact positive-momentum leg whose constant-step travel covers
   one full period contains a phase hit on the generated orbit.  The result
   derives the hit from the Algorithm 1 recurrence and does not postulate a
   phase-index family. -/
theorem theorem_4_15_periodicCandidate_positive_leg_has_phase_hit
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta : ℝ)
    (start t : ℕ) (hetaPos : 0 < eta)
    (hetaSmall : eta ≤ Real.pi / 8)
    (heta : ∀ k < t, cfg.eta (start + k) = eta)
    (hpositive : ∀ k < t, 0 <
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + k)).M 0 0)
    (htravel : Real.pi ≤ (t : ℝ) * eta) :
    ∃ k : ℕ, k ≤ t ∧ ∃ z : ℤ,
      |theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg (start + k)).W -
        (z : ℝ) * Real.pi| ≤ Real.pi / 8 := by
  let x := theorem_4_5_counterexampleEntry
    (deterministicMomentumMuonState
      theorem_4_15_periodicCandidateObjective cfg start).W
  rcases theorem_4_15_periodicCandidate_descending_grid_has_phase_hit
      x eta t hetaPos hetaSmall htravel with ⟨k, hk, z, hphase⟩
  refine ⟨k, hk, z, ?_⟩
  have hetaPrefix : ∀ j < k, cfg.eta (start + j) = eta := by
    intro j hj
    exact heta j (lt_of_lt_of_le hj hk)
  have hpositivePrefix : ∀ j < k, 0 <
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + j)).M 0 0 := by
    intro j hj
    exact hpositive j (lt_of_lt_of_le hj hk)
  rw [theorem_4_15_periodicCandidate_phase_after_positive_momentum_block
    cfg eta start k hetaPrefix hpositivePrefix]
  exact hphase

/- The return-leg analogue supplies the same generated phase hit for a
   negative-momentum leg. -/
theorem theorem_4_15_periodicCandidate_negative_leg_has_phase_hit
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta : ℝ)
    (start t : ℕ) (hetaPos : 0 < eta)
    (hetaSmall : eta ≤ Real.pi / 8)
    (heta : ∀ k < t, cfg.eta (start + k) = eta)
    (hnegative : ∀ k < t,
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + k)).M 0 0 < 0)
    (htravel : Real.pi ≤ (t : ℝ) * eta) :
    ∃ k : ℕ, k ≤ t ∧ ∃ z : ℤ,
      |theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg (start + k)).W -
        (z : ℝ) * Real.pi| ≤ Real.pi / 8 := by
  let x := theorem_4_5_counterexampleEntry
    (deterministicMomentumMuonState
      theorem_4_15_periodicCandidateObjective cfg start).W
  rcases theorem_4_15_periodicCandidate_ascending_grid_has_phase_hit
      x eta t hetaPos hetaSmall htravel with ⟨k, hk, z, hphase⟩
  refine ⟨k, hk, z, ?_⟩
  have hetaPrefix : ∀ j < k, cfg.eta (start + j) = eta := by
    intro j hj
    exact heta j (lt_of_lt_of_le hj hk)
  have hnegativePrefix : ∀ j < k,
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + j)).M 0 0 < 0 := by
    intro j hj
    exact hnegative j (lt_of_lt_of_le hj hk)
  rw [theorem_4_15_periodicCandidate_phase_after_negative_momentum_block
    cfg eta start k hetaPrefix hnegativePrefix]
  exact hphase

/- On a negative-momentum return leg, endpoint containment near a phase with
   `cos = 1` produces the complete positive-gradient block required by the
   positive reversal theorem. -/
theorem theorem_4_15_periodicCandidate_positive_reversal_seed_from_phase_block
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta m0 center : ℝ)
    (start t : ℕ) (hm0 : 0 < m0) (hetaNonneg : 0 ≤ eta)
    (heta : ∀ k < t, cfg.eta (start + k) = eta)
    (hnegative : ∀ k < t,
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + k)).M 0 0 < 0)
    (hcenter : Real.cos center = 1)
    (hphaseLower : center - (1 : ℝ) / 2 ≤
      theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg start).W + eta)
    (hphaseUpper :
      theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg start).W +
        (t : ℝ) * eta ≤ center + (1 : ℝ) / 2)
    (hdecay : cfg.beta ^ t * (1 + (1 : ℝ) / 2) ≤ (1 : ℝ) / 2 - m0) :
    m0 ≤ (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + t)).M 0 0 ∧
      0 < (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + t)).M 0 0 := by
  apply theorem_4_15_periodicCandidate_positive_reversal_seed
    cfg ((1 : ℝ) / 2) m0 start t hm0 hdecay
  intro k hk
  have hkSuccLe : k + 1 ≤ t := Nat.succ_le_iff.mpr hk
  have hetaPrefix : ∀ j < k + 1, cfg.eta (start + j) = eta := by
    intro j hj
    exact heta j (lt_of_lt_of_le hj hkSuccLe)
  have hnegativePrefix : ∀ j < k + 1,
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + j)).M 0 0 < 0 := by
    intro j hj
    exact hnegative j (lt_of_lt_of_le hj hkSuccLe)
  have hphase :=
    theorem_4_15_periodicCandidate_phase_after_negative_momentum_block
      cfg eta start (k + 1) hetaPrefix hnegativePrefix
  let x : ℝ := theorem_4_5_counterexampleEntry
    (deterministicMomentumMuonState
      theorem_4_15_periodicCandidateObjective cfg (start + k + 1)).W
  have hx : x =
      theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg start).W +
        ((k + 1 : ℕ) : ℝ) * eta := by
    simpa [x, Nat.add_assoc] using hphase
  have hkOne : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hkT : ((k + 1 : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast hkSuccLe
  have hxLower : center - (1 : ℝ) / 2 ≤ x := by
    rw [hx]
    have hmul := mul_le_mul_of_nonneg_right hkOne hetaNonneg
    linarith
  have hxUpper : x ≤ center + (1 : ℝ) / 2 := by
    rw [hx]
    have hmul := mul_le_mul_of_nonneg_right hkT hetaNonneg
    linarith
  have hdistance : |center - x| ≤ (1 : ℝ) / 2 := by
    rw [abs_le]
    constructor <;> linarith
  have hcosDistance := Real.abs_cos_sub_cos_le center x
  have hcosClose : |Real.cos center - Real.cos x| ≤ (1 : ℝ) / 2 :=
    le_trans hcosDistance hdistance
  rw [hcenter] at hcosClose
  have hcosLower : (1 : ℝ) / 2 ≤ Real.cos x := by
    have := (abs_le.mp hcosClose).2
    linarith
  simpa [x] using hcosLower

/- A positive generated restart seed and the phase-block endpoint conditions
   force an actual first nonpositive-momentum index no later than the displayed
   block length.  The pre-reversal positivity is now a conclusion: if no
   earlier index reverses, the affine phase theorem and geometric decay force
   the endpoint below `-m0`.  This is the least-index bridge needed to iterate
   shrinking-step legs without assuming their sign histories separately. -/
theorem theorem_4_15_periodicCandidate_first_nonpositive_reversal_by_phase_block
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta m0 center : ℝ)
    (start t : ℕ) (hm0 : 0 < m0) (hetaNonneg : 0 ≤ eta)
    (hMstart : m0 ≤
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg start).M 0 0)
    (heta : ∀ k < t, cfg.eta (start + k) = eta)
    (hcenter : Real.cos center = -1)
    (hphaseLower : center - (1 : ℝ) / 2 ≤
      theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg start).W -
        (t : ℝ) * eta)
    (hphaseUpper :
      theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg start).W - eta ≤
        center + (1 : ℝ) / 2)
    (hdecay : cfg.beta ^ t * (1 + (1 : ℝ) / 2) ≤ (1 : ℝ) / 2 - m0) :
    ∃ first : ℕ,
      0 < first ∧ first ≤ t ∧
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg (start + first)).M 0 0 ≤ 0 ∧
        ∀ k < first, 0 <
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg (start + k)).M 0 0 := by
  have hexists : ∃ q : ℕ, q ≤ t ∧
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + q)).M 0 0 ≤ 0 := by
    by_contra hnone
    have hpositive : ∀ k < t, 0 <
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg (start + k)).M 0 0 := by
      intro k hk
      have hnotNonpositive : ¬
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg (start + k)).M 0 0 ≤ 0 := by
        intro hkNonpositive
        exact hnone ⟨k, Nat.le_of_lt hk, hkNonpositive⟩
      exact lt_of_not_ge hnotNonpositive
    have hseed :=
      theorem_4_15_periodicCandidate_negative_reversal_seed_from_phase_block
        cfg eta m0 center start t hm0 hetaNonneg heta hpositive hcenter
          hphaseLower hphaseUpper hdecay
    exact hnone ⟨t, le_rfl, le_trans hseed.1 (neg_nonpos.mpr hm0.le)⟩
  let first := Nat.find hexists
  have hfirstSpec : first ≤ t ∧
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + first)).M 0 0 ≤ 0 :=
    Nat.find_spec hexists
  have hfirstPositive : 0 < first := by
    by_contra hfirstZero
    have hzero : first = 0 := Nat.eq_zero_of_not_pos hfirstZero
    rw [hzero, Nat.add_zero] at hfirstSpec
    linarith
  refine ⟨first, hfirstPositive, hfirstSpec.1, hfirstSpec.2, ?_⟩
  intro k hk
  have hkLeT : k ≤ t := le_trans (Nat.le_of_lt hk) hfirstSpec.1
  have hminimal := Nat.find_min hexists hk
  have hnotNonpositive : ¬
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + k)).M 0 0 ≤ 0 := by
    intro hkNonpositive
    exact hminimal ⟨hkLeT, hkNonpositive⟩
  exact lt_of_not_ge hnotNonpositive

/- The sign-symmetric first-hitting result starts from a proved negative seed.
   It returns the least nonnegative-momentum restart together with the complete
   negative sign history preceding it, again using only the exact generated
   phase block and not an independently supplied trajectory. -/
theorem theorem_4_15_periodicCandidate_first_nonnegative_reversal_by_phase_block
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta m0 center : ℝ)
    (start t : ℕ) (hm0 : 0 < m0) (hetaNonneg : 0 ≤ eta)
    (hMstart :
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg start).M 0 0 ≤ -m0)
    (heta : ∀ k < t, cfg.eta (start + k) = eta)
    (hcenter : Real.cos center = 1)
    (hphaseLower : center - (1 : ℝ) / 2 ≤
      theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg start).W + eta)
    (hphaseUpper :
      theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg start).W +
        (t : ℝ) * eta ≤ center + (1 : ℝ) / 2)
    (hdecay : cfg.beta ^ t * (1 + (1 : ℝ) / 2) ≤ (1 : ℝ) / 2 - m0) :
    ∃ first : ℕ,
      0 < first ∧ first ≤ t ∧
        0 ≤ (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg (start + first)).M 0 0 ∧
        ∀ k < first,
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg (start + k)).M 0 0 < 0 := by
  have hexists : ∃ q : ℕ, q ≤ t ∧
      0 ≤ (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + q)).M 0 0 := by
    by_contra hnone
    have hnegative : ∀ k < t,
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg (start + k)).M 0 0 < 0 := by
      intro k hk
      have hnotNonnegative : ¬ 0 ≤
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg (start + k)).M 0 0 := by
        intro hkNonnegative
        exact hnone ⟨k, Nat.le_of_lt hk, hkNonnegative⟩
      exact lt_of_not_ge hnotNonnegative
    have hseed :=
      theorem_4_15_periodicCandidate_positive_reversal_seed_from_phase_block
        cfg eta m0 center start t hm0 hetaNonneg heta hnegative hcenter
          hphaseLower hphaseUpper hdecay
    exact hnone ⟨t, le_rfl, le_trans hm0.le hseed.1⟩
  let first := Nat.find hexists
  have hfirstSpec : first ≤ t ∧
      0 ≤ (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + first)).M 0 0 :=
    Nat.find_spec hexists
  have hfirstPositive : 0 < first := by
    by_contra hfirstZero
    have hzero : first = 0 := Nat.eq_zero_of_not_pos hfirstZero
    rw [hzero, Nat.add_zero] at hfirstSpec
    linarith
  refine ⟨first, hfirstPositive, hfirstSpec.1, hfirstSpec.2, ?_⟩
  intro k hk
  have hkLeT : k ≤ t := le_trans (Nat.le_of_lt hk) hfirstSpec.1
  have hminimal := Nat.find_min hexists hk
  have hnotNonnegative : ¬ 0 ≤
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + k)).M 0 0 := by
    intro hkNonnegative
    exact hminimal ⟨hkLeT, hkNonnegative⟩
  exact lt_of_not_ge hnotNonnegative

/- The first nonpositive hit can be advanced by one exact generated step to a
   quantitative negative restart.  The slightly stronger endpoint containment
   includes the initial phase itself; this ensures that the possible one-step
   rebound caused by a negative (rather than zero) hitting momentum remains in
   the same negative-gradient block.  No sign history after the hit is assumed. -/
theorem theorem_4_15_periodicCandidate_negative_restart_after_first_hit
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta m0 center : ℝ)
    (start t : ℕ) (hm0 : 0 < m0) (hetaNonneg : 0 ≤ eta)
    (hMstart : m0 ≤
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg start).M 0 0)
    (heta : ∀ k ≤ t, cfg.eta (start + k) = eta)
    (hcenter : Real.cos center = -1)
    (hphaseLower : center - (1 : ℝ) / 2 ≤
      theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg start).W -
        (t : ℝ) * eta)
    (hphaseUpper :
      theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg start).W ≤
        center + (1 : ℝ) / 2)
    (hdecay : cfg.beta ^ t * (1 + (1 : ℝ) / 2) ≤ (1 : ℝ) / 2 - m0) :
    ∃ first : ℕ,
      0 < first ∧ first ≤ t ∧
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg (start + first)).M 0 0 ≤ 0 ∧
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg (start + first + 1)).M 0 0 ≤
            -(1 - cfg.beta) / 2 ∧
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg (start + first + 1)).M 0 0 < 0 ∧
        ∀ k < first, 0 <
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg (start + k)).M 0 0 := by
  have hphaseUpperOld :
      theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg start).W - eta ≤
        center + (1 : ℝ) / 2 := by
    linarith
  obtain ⟨first, hfirstPos, hfirstLe, hfirstNonpos, hpositive⟩ :=
    theorem_4_15_periodicCandidate_first_nonpositive_reversal_by_phase_block
      cfg eta m0 center start t hm0 hetaNonneg hMstart
        (fun k hk => heta k (Nat.le_of_lt hk)) hcenter hphaseLower
        hphaseUpperOld hdecay
  have hetaFirst : cfg.eta (start + first) = eta := heta first hfirstLe
  have hphaseFirst :=
    theorem_4_15_periodicCandidate_phase_after_positive_momentum_block
      cfg eta start first (fun k hk => heta k (le_trans (Nat.le_of_lt hk) hfirstLe))
        hpositive
  let x0 : ℝ := theorem_4_5_counterexampleEntry
    (deterministicMomentumMuonState
      theorem_4_15_periodicCandidateObjective cfg start).W
  let xFirst : ℝ := theorem_4_5_counterexampleEntry
    (deterministicMomentumMuonState
      theorem_4_15_periodicCandidateObjective cfg (start + first)).W
  let xNext : ℝ := theorem_4_5_counterexampleEntry
    (deterministicMomentumMuonState
      theorem_4_15_periodicCandidateObjective cfg (start + first + 1)).W
  have hxFirst : xFirst = x0 - (first : ℝ) * eta := by
    simpa [xFirst, x0] using hphaseFirst
  have hxFirstLower : center - (1 : ℝ) / 2 ≤ xFirst := by
    rw [hxFirst]
    have hmul := mul_le_mul_of_nonneg_right (show (first : ℝ) ≤ (t : ℝ) by
      exact_mod_cast hfirstLe) hetaNonneg
    dsimp [x0] at hphaseLower ⊢
    linarith
  have hxFirstUpper : xFirst ≤ center + (1 : ℝ) / 2 := by
    rw [hxFirst]
    have hmul : 0 ≤ (first : ℝ) * eta := mul_nonneg (by positivity) hetaNonneg
    dsimp [x0] at hphaseUpper ⊢
    linarith
  have hstep :=
    (theorem_4_15_periodicCandidate_full_orbit_scalar_recurrence
      cfg (start + first)).1
  have hxNextBounds : center - (1 : ℝ) / 2 ≤ xNext ∧
      xNext ≤ center + (1 : ℝ) / 2 := by
    rcases hfirstNonpos.lt_or_eq with hnegative | hzero
    · have hxNext : xNext = xFirst + eta := by
        rw [show start + first + 1 = start + first + 1 by rfl] at hstep
        simpa [xNext, xFirst, hetaFirst, Real.sign_of_neg hnegative] using hstep
      rw [hxNext]
      constructor
      · exact le_trans hxFirstLower (le_add_of_nonneg_right hetaNonneg)
      · rw [hxFirst]
        have hfirstOne : (1 : ℝ) ≤ (first : ℝ) := by exact_mod_cast hfirstPos
        have hmul := mul_le_mul_of_nonneg_right hfirstOne hetaNonneg
        dsimp [x0] at hphaseUpper ⊢
        linarith
    · have hxNext : xNext = xFirst := by
        rw [show start + first + 1 = start + first + 1 by rfl] at hstep
        simpa [xNext, xFirst, hetaFirst, hzero, Real.sign_zero] using hstep
      simpa [hxNext] using And.intro hxFirstLower hxFirstUpper
  have hdistance : |center - xNext| ≤ (1 : ℝ) / 2 := by
    rw [abs_le]
    constructor <;> linarith [hxNextBounds.1, hxNextBounds.2]
  have hcosDistance := Real.abs_cos_sub_cos_le center xNext
  have hcosClose : |Real.cos center - Real.cos xNext| ≤ (1 : ℝ) / 2 :=
    le_trans hcosDistance hdistance
  rw [hcenter] at hcosClose
  have hcosUpper : Real.cos xNext ≤ -((2 : ℝ)⁻¹) := by
    have := (abs_le.mp hcosClose).1
    linarith
  have hrecurrence :=
    (theorem_4_15_periodicCandidate_full_orbit_scalar_recurrence
      cfg (start + first)).2
  have hmomentum := mul_nonpos_of_nonneg_of_nonpos cfg.beta_mem.1 hfirstNonpos
  have hgradient :
      (1 - cfg.beta) *
          Real.cos (theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg
                (start + first + 1)).W) ≤
        (1 - cfg.beta) * (-((2 : ℝ)⁻¹)) := by
    exact mul_le_mul_of_nonneg_left hcosUpper
      (sub_nonneg.mpr cfg.beta_mem.2.le)
  have hnextBound :
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + first + 1)).M 0 0 ≤
          -(1 - cfg.beta) / 2 := by
    rw [hrecurrence]
    calc
      cfg.beta *
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg
                (start + first)).M 0 0 +
          (1 - cfg.beta) *
            Real.cos (theorem_4_5_counterexampleEntry
              (deterministicMomentumMuonState
                theorem_4_15_periodicCandidateObjective cfg
                  (start + first + 1)).W) ≤
          0 + (1 - cfg.beta) * (-((2 : ℝ)⁻¹)) :=
        add_le_add hmomentum hgradient
      _ = -(1 - cfg.beta) / 2 := by ring
  have hnextNeg :
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + first + 1)).M 0 0 < 0 := by
    have : 0 < 1 - cfg.beta := sub_pos.mpr cfg.beta_mem.2
    linarith
  exact ⟨first, hfirstPos, hfirstLe, hfirstNonpos, hnextBound, hnextNeg, hpositive⟩

/- The sign-symmetric companion turns the first nonnegative hit into a
   quantitative positive restart one generated step later. -/
theorem theorem_4_15_periodicCandidate_positive_restart_after_first_hit
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta m0 center : ℝ)
    (start t : ℕ) (hm0 : 0 < m0) (hetaNonneg : 0 ≤ eta)
    (hMstart :
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg start).M 0 0 ≤ -m0)
    (heta : ∀ k ≤ t, cfg.eta (start + k) = eta)
    (hcenter : Real.cos center = 1)
    (hphaseLower : center - (1 : ℝ) / 2 ≤
      theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg start).W)
    (hphaseUpper :
      theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg start).W +
        (t : ℝ) * eta ≤ center + (1 : ℝ) / 2)
    (hdecay : cfg.beta ^ t * (1 + (1 : ℝ) / 2) ≤ (1 : ℝ) / 2 - m0) :
    ∃ first : ℕ,
      0 < first ∧ first ≤ t ∧
        0 ≤ (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg (start + first)).M 0 0 ∧
        (1 - cfg.beta) / 2 ≤
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg (start + first + 1)).M 0 0 ∧
        0 < (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg (start + first + 1)).M 0 0 ∧
        ∀ k < first,
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg (start + k)).M 0 0 < 0 := by
  have hphaseLowerOld : center - (1 : ℝ) / 2 ≤
      theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg start).W + eta := by
    linarith
  obtain ⟨first, hfirstPos, hfirstLe, hfirstNonneg, hnegative⟩ :=
    theorem_4_15_periodicCandidate_first_nonnegative_reversal_by_phase_block
      cfg eta m0 center start t hm0 hetaNonneg hMstart
        (fun k hk => heta k (Nat.le_of_lt hk)) hcenter hphaseLowerOld
        hphaseUpper hdecay
  have hetaFirst : cfg.eta (start + first) = eta := heta first hfirstLe
  have hphaseFirst :=
    theorem_4_15_periodicCandidate_phase_after_negative_momentum_block
      cfg eta start first (fun k hk => heta k (le_trans (Nat.le_of_lt hk) hfirstLe))
        hnegative
  let x0 : ℝ := theorem_4_5_counterexampleEntry
    (deterministicMomentumMuonState
      theorem_4_15_periodicCandidateObjective cfg start).W
  let xFirst : ℝ := theorem_4_5_counterexampleEntry
    (deterministicMomentumMuonState
      theorem_4_15_periodicCandidateObjective cfg (start + first)).W
  let xNext : ℝ := theorem_4_5_counterexampleEntry
    (deterministicMomentumMuonState
      theorem_4_15_periodicCandidateObjective cfg (start + first + 1)).W
  have hxFirst : xFirst = x0 + (first : ℝ) * eta := by
    simpa [xFirst, x0] using hphaseFirst
  have hxFirstLower : center - (1 : ℝ) / 2 ≤ xFirst := by
    rw [hxFirst]
    have hmul : 0 ≤ (first : ℝ) * eta := mul_nonneg (by positivity) hetaNonneg
    dsimp [x0] at hphaseLower ⊢
    linarith
  have hxFirstUpper : xFirst ≤ center + (1 : ℝ) / 2 := by
    rw [hxFirst]
    have hmul := mul_le_mul_of_nonneg_right (show (first : ℝ) ≤ (t : ℝ) by
      exact_mod_cast hfirstLe) hetaNonneg
    dsimp [x0] at hphaseUpper ⊢
    linarith
  have hstep :=
    (theorem_4_15_periodicCandidate_full_orbit_scalar_recurrence
      cfg (start + first)).1
  have hxNextBounds : center - (1 : ℝ) / 2 ≤ xNext ∧
      xNext ≤ center + (1 : ℝ) / 2 := by
    rcases hfirstNonneg.lt_or_eq with hpositive | hzero
    · have hxNext : xNext = xFirst - eta := by
        rw [show start + first + 1 = start + first + 1 by rfl] at hstep
        simpa [xNext, xFirst, hetaFirst, Real.sign_of_pos hpositive] using hstep
      rw [hxNext]
      constructor
      · rw [hxFirst]
        have hfirstOne : (1 : ℝ) ≤ (first : ℝ) := by exact_mod_cast hfirstPos
        have hmul := mul_le_mul_of_nonneg_right hfirstOne hetaNonneg
        dsimp [x0] at hphaseLower ⊢
        linarith
      · exact le_trans (sub_le_self _ hetaNonneg) hxFirstUpper
    · have hxNext : xNext = xFirst := by
        rw [show start + first + 1 = start + first + 1 by rfl] at hstep
        simpa [xNext, xFirst, hetaFirst, hzero.symm, Real.sign_zero] using hstep
      simpa [hxNext] using And.intro hxFirstLower hxFirstUpper
  have hdistance : |center - xNext| ≤ (1 : ℝ) / 2 := by
    rw [abs_le]
    constructor <;> linarith [hxNextBounds.1, hxNextBounds.2]
  have hcosDistance := Real.abs_cos_sub_cos_le center xNext
  have hcosClose : |Real.cos center - Real.cos xNext| ≤ (1 : ℝ) / 2 :=
    le_trans hcosDistance hdistance
  rw [hcenter] at hcosClose
  have hcosLower : (1 : ℝ) / 2 ≤ Real.cos xNext := by
    have := (abs_le.mp hcosClose).2
    linarith
  have hrecurrence :=
    (theorem_4_15_periodicCandidate_full_orbit_scalar_recurrence
      cfg (start + first)).2
  have hmomentum := mul_nonneg cfg.beta_mem.1 hfirstNonneg
  have hgradient :
      (1 - cfg.beta) * (1 / 2 : ℝ) ≤
        (1 - cfg.beta) *
          Real.cos (theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg
                (start + first + 1)).W) := by
    exact mul_le_mul_of_nonneg_left hcosLower
      (sub_nonneg.mpr cfg.beta_mem.2.le)
  have hnextBound : (1 - cfg.beta) / 2 ≤
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + first + 1)).M 0 0 := by
    rw [hrecurrence]
    calc
      (1 - cfg.beta) / 2 =
          0 + (1 - cfg.beta) * (1 / 2 : ℝ) := by ring
      _ ≤ cfg.beta *
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg
                (start + first)).M 0 0 +
          (1 - cfg.beta) *
            Real.cos (theorem_4_5_counterexampleEntry
              (deterministicMomentumMuonState
                theorem_4_15_periodicCandidateObjective cfg
                  (start + first + 1)).W) :=
        add_le_add hmomentum hgradient
  have hnextPos : 0 <
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + first + 1)).M 0 0 := by
    have : 0 < 1 - cfg.beta := sub_pos.mpr cfg.beta_mem.2
    linarith
  exact ⟨first, hfirstPos, hfirstLe, hfirstNonneg, hnextBound, hnextPos, hnegative⟩

/- Five momentum-memory times are enough to discharge the geometric remainder
   used by both quantitative restart lemmas with the fixed restart size `1/4`.
   This is a purely scalar consequence of `0 ≤ beta < 1`: comparison with
   `(1 + (1 - beta))⁻¹` and Bernoulli's inequality give
   `beta^t ≤ 1 / (1 + t * (1 - beta)) ≤ 1/6`. -/
theorem theorem_4_15_geometric_decay_after_five_memory_times
    (beta : ℝ) (hbeta : beta ∈ Set.Ico 0 1) (t : ℕ)
    (hwindow : (5 : ℝ) ≤ (t : ℝ) * (1 - beta)) :
    beta ^ t * (1 + (1 : ℝ) / 2) ≤ (1 : ℝ) / 2 - 1 / 4 := by
  let delta := 1 - beta
  have hdeltaPos : 0 < delta := by
    dsimp [delta]
    linarith [hbeta.2]
  have hbasePos : 0 < 1 + delta := by linarith
  have hproduct : beta * (1 + delta) ≤ 1 := by
    dsimp [delta]
    nlinarith [sq_nonneg (1 - beta)]
  have hbetaInv : beta ≤ (1 + delta)⁻¹ := by
    rw [inv_eq_one_div]
    exact (le_div_iff₀ hbasePos).2 (by simpa using hproduct)
  have hpower : beta ^ t ≤ ((1 + delta)⁻¹) ^ t :=
    (pow_le_pow_left₀ hbeta.1 hbetaInv) t
  have hbernoulli : 1 + (t : ℝ) * delta ≤ (1 + delta) ^ t := by
    exact one_add_mul_le_pow (a := delta) (n := t) (by linarith [hdeltaPos])
  have hsix : (6 : ℝ) ≤ (1 + delta) ^ t := by
    apply le_trans (show (6 : ℝ) ≤ 1 + (t : ℝ) * delta by
      dsimp [delta] at hwindow ⊢
      linarith)
    exact hbernoulli
  have hinv : ((1 + delta) ^ t)⁻¹ ≤ (6 : ℝ)⁻¹ :=
    inv_anti₀ (by norm_num) hsix
  have hpowerSixth : beta ^ t ≤ (6 : ℝ)⁻¹ := by
    calc
      beta ^ t ≤ ((1 + delta)⁻¹) ^ t := hpower
      _ = ((1 + delta) ^ t)⁻¹ := by rw [inv_pow]
      _ ≤ (6 : ℝ)⁻¹ := hinv
  have hpowerNonneg : 0 ≤ beta ^ t := pow_nonneg hbeta.1 t
  norm_num at hpowerSixth ⊢
  nlinarith

/- The printed source-small-`J` schedule contains a complete five-memory-time
   integer window once its existing horizon-memory lower bound reaches six.
   The selected `q` is constructed from the actual `beta` of the same
   generated run, lies inside its selected horizon, and automatically supplies
   the exact decay premise required by the two restart theorems.  No phase,
   gradient-pattern, cross-curvature, or stationarity premise is used. -/
theorem theorem_4_15_otherwise_source_small_j_five_memory_window
    {xi : Type*} [MeasurableSpace xi]
    (P : StochasticProblem xi 1 1)
    (cfgForAccuracyHorizon : ℝ → ℕ → StochasticMuonConfig 1 1)
    (W0 : Mat 1 1) (sigma Delta epsilon C s : ℝ)
    (betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ)
    (N : ℕ)
    (hN : theorem_4_15_otherwiseSourceSmallJGeneratedRunForAccuracyHorizon P
      cfgForAccuracyHorizon W0 sigma Delta epsilon C s
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N)
    (hlong : (6 : ℝ) ≤
      (betaLower * horizonLower) * (sigma / epsilon)) :
    let cfgN := cfgForAccuracyHorizon epsilon N
    let q := Nat.ceil (5 / (1 - cfgN.beta))
    q ≤ N ∧
      cfgN.beta ^ q * (1 + (1 : ℝ) / 2) ≤ (1 : ℝ) / 2 - 1 / 4 := by
  dsimp only
  let cfgN := cfgForAccuracyHorizon epsilon N
  let delta := 1 - cfgN.beta
  let q := Nat.ceil (5 / delta)
  have hcount :=
    theorem_4_15_otherwise_source_small_j_horizon_memory_count_one_dimensional
      P cfgForAccuracyHorizon W0 sigma Delta epsilon C s
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N hN
  have hdeltaPos : 0 < delta := by
    dsimp [delta, cfgN]
    exact sub_pos.mpr (cfgForAccuracyHorizon epsilon N).beta_mem.2
  have hdeltaLe : delta ≤ 1 := by
    dsimp [delta, cfgN]
    linarith [(cfgForAccuracyHorizon epsilon N).beta_mem.1]
  have hceilNonneg : 0 ≤ 5 / delta := by positivity
  have hqLower : 5 / delta ≤ (q : ℝ) := by
    simpa [q] using Nat.le_ceil (5 / delta)
  have hqUpper : (q : ℝ) < 5 / delta + 1 := by
    simpa [q] using Nat.ceil_lt_add_one hceilNonneg
  have hwindow : (5 : ℝ) ≤ (q : ℝ) * delta := by
    have hmul := mul_le_mul_of_nonneg_right hqLower hdeltaPos.le
    calc
      (5 : ℝ) = (5 / delta) * delta := by field_simp [ne_of_gt hdeltaPos]
      _ ≤ (q : ℝ) * delta := hmul
  have hqProductUpper : (q : ℝ) * delta < 6 := by
    have hmul := mul_lt_mul_of_pos_right hqUpper hdeltaPos
    have hid : (5 / delta + 1) * delta = 5 + delta := by
      field_simp [ne_of_gt hdeltaPos]
      <;> ring
    rw [hid] at hmul
    linarith
  have hNProduct : (6 : ℝ) ≤ (N : ℝ) * delta := by
    exact hlong.trans (by simpa [delta, cfgN] using hcount)
  have hqRealLtN : (q : ℝ) < (N : ℝ) := by
    have hproductLt : (q : ℝ) * delta < (N : ℝ) * delta :=
      hqProductUpper.trans_le hNProduct
    nlinarith
  have hqN : q ≤ N := Nat.le_of_lt (by exact_mod_cast hqRealLtN)
  refine ⟨hqN, ?_⟩
  apply theorem_4_15_geometric_decay_after_five_memory_times cfgN.beta
    cfgN.beta_mem q
  simpa [delta] using hwindow

/- The same integer window has an exact spatial interpretation for every
   positive constant step.  Its displacement is between five and six times
   the actual momentum-memory displacement `eta / (1 - beta)`.  The strict
   upper bound records the single-step ceiling loss and is why no asymptotic
   approximation or independently chosen block length is needed. -/
theorem theorem_4_15_five_memory_window_displacement
    (beta eta : ℝ) (hbeta : beta ∈ Set.Ico 0 1) (heta : 0 < eta) :
    let delta := 1 - beta
    let q := Nat.ceil (5 / delta)
    5 * (eta / delta) ≤ (q : ℝ) * eta ∧
      (q : ℝ) * eta < 6 * (eta / delta) := by
  dsimp only
  let delta := 1 - beta
  let q := Nat.ceil (5 / delta)
  have hdeltaPos : 0 < delta := by
    dsimp [delta]
    linarith [hbeta.2]
  have hdeltaLe : delta ≤ 1 := by
    dsimp [delta]
    linarith [hbeta.1]
  have hceilNonneg : 0 ≤ 5 / delta := by positivity
  have hqLower : 5 / delta ≤ (q : ℝ) := by
    simpa [q] using Nat.le_ceil (5 / delta)
  have hqUpper : (q : ℝ) < 5 / delta + 1 := by
    simpa [q] using Nat.ceil_lt_add_one hceilNonneg
  have hwindowLower : (5 : ℝ) ≤ (q : ℝ) * delta := by
    have hmul := mul_le_mul_of_nonneg_right hqLower hdeltaPos.le
    calc
      (5 : ℝ) = (5 / delta) * delta := by
        field_simp [ne_of_gt hdeltaPos]
      _ ≤ (q : ℝ) * delta := hmul
  have hwindowUpper : (q : ℝ) * delta < 6 := by
    have hmul := mul_lt_mul_of_pos_right hqUpper hdeltaPos
    have hid : (5 / delta + 1) * delta = 5 + delta := by
      field_simp [ne_of_gt hdeltaPos]
    rw [hid] at hmul
    linarith
  have hratioPos : 0 < eta / delta := div_pos heta hdeltaPos
  have hlower := mul_le_mul_of_nonneg_right hwindowLower hratioPos.le
  have hupper := mul_lt_mul_of_pos_right hwindowUpper hratioPos
  constructor
  · calc
      5 * (eta / delta) ≤ ((q : ℝ) * delta) * (eta / delta) := hlower
      _ = (q : ℝ) * eta := by
        field_simp [ne_of_gt hdeltaPos]
  · calc
      (q : ℝ) * eta = ((q : ℝ) * delta) * (eta / delta) := by
        field_simp [ne_of_gt hdeltaPos]
      _ < 6 * (eta / delta) := hupper

/- A five-memory-time block whose exact generated momentum keeps one sign now
   supplies a phase hit, rather than requiring one as an additional block
   premise.  The only scalar size condition says that the actual memory-scale
   displacement covers one spatial period; the mesh condition is the printed
   shrinking-step property used to select a discrete iterate. -/
theorem theorem_4_15_periodicCandidate_five_memory_signed_leg_has_phase_hit
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta : ℝ) (start : ℕ)
    (hetaPos : 0 < eta) (hetaSmall : eta ≤ Real.pi / 8)
    (hmemoryTravel : Real.pi ≤ 5 * (eta / (1 - cfg.beta)))
    (heta : ∀ k < Nat.ceil (5 / (1 - cfg.beta)),
      cfg.eta (start + k) = eta)
    (hsign :
      (∀ k < Nat.ceil (5 / (1 - cfg.beta)), 0 <
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg (start + k)).M 0 0) ∨
      (∀ k < Nat.ceil (5 / (1 - cfg.beta)),
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg (start + k)).M 0 0 < 0)) :
    ∃ k : ℕ, k ≤ Nat.ceil (5 / (1 - cfg.beta)) ∧ ∃ z : ℤ,
      |theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg (start + k)).W -
        (z : ℝ) * Real.pi| ≤ Real.pi / 8 := by
  let q := Nat.ceil (5 / (1 - cfg.beta))
  have hdisplacement := theorem_4_15_five_memory_window_displacement
    cfg.beta eta cfg.beta_mem hetaPos
  dsimp only at hdisplacement
  have htravel : Real.pi ≤ (q : ℝ) * eta := by
    exact hmemoryTravel.trans (by simpa [q] using hdisplacement.1)
  rcases hsign with hpositive | hnegative
  · exact theorem_4_15_periodicCandidate_positive_leg_has_phase_hit
      cfg eta start q hetaPos hetaSmall
      (by simpa [q] using heta) (by simpa [q] using hpositive) htravel
  · exact theorem_4_15_periodicCandidate_negative_leg_has_phase_hit
      cfg eta start q hetaPos hetaSmall
      (by simpa [q] using heta) (by simpa [q] using hnegative) htravel

/- On an actual source-small-`J` generated run, the five-memory-time window
   therefore lies inside the selected Appendix B.4 horizon, supplies the
   quantitative restart decay, and travels a controlled nonvanishing multiple
   of the run's exact memory displacement.  This packages only consequences of
   the printed schedule; phase containment and gradient density remain to be
   proved from the generated periodic orbit. -/
theorem theorem_4_15_otherwise_source_small_j_five_memory_window_geometry
    {xi : Type*} [MeasurableSpace xi]
    (P : StochasticProblem xi 1 1)
    (cfgForAccuracyHorizon : ℝ → ℕ → StochasticMuonConfig 1 1)
    (W0 : Mat 1 1) (sigma Delta epsilon C s : ℝ)
    (betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ)
    (N : ℕ)
    (hN : theorem_4_15_otherwiseSourceSmallJGeneratedRunForAccuracyHorizon P
      cfgForAccuracyHorizon W0 sigma Delta epsilon C s
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N)
    (hlong : (6 : ℝ) ≤
      (betaLower * horizonLower) * (sigma / epsilon)) :
    let cfgN := cfgForAccuracyHorizon epsilon N
    let q := Nat.ceil (5 / (1 - cfgN.beta))
    q ≤ N ∧
      cfgN.beta ^ q * (1 + (1 : ℝ) / 2) ≤ (1 : ℝ) / 2 - 1 / 4 ∧
      5 * (cfgN.eta 0 / (1 - cfgN.beta)) ≤ (q : ℝ) * cfgN.eta 0 ∧
      (q : ℝ) * cfgN.eta 0 <
        6 * (cfgN.eta 0 / (1 - cfgN.beta)) := by
  dsimp only
  let cfgN := cfgForAccuracyHorizon epsilon N
  let q := Nat.ceil (5 / (1 - cfgN.beta))
  have hwindow :=
    theorem_4_15_otherwise_source_small_j_five_memory_window
      P cfgForAccuracyHorizon W0 sigma Delta epsilon C s
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N hN hlong
  dsimp only at hwindow
  have hfields := hN
  rcases hfields with
    ⟨_horizon, _hfinite, _hDelta, _hthird, _hvariance, _hwd, _hW0,
      _hschedule, hsource, _hHorizon, _hregDom, _hregime⟩
  have hdisplacement := theorem_4_15_five_memory_window_displacement
    cfgN.beta (cfgN.eta 0) cfgN.beta_mem (by
      simpa [cfgN] using hsource.2)
  dsimp only at hdisplacement
  exact ⟨hwindow.1, hwindow.2, hdisplacement.1, hdisplacement.2⟩

/- The auxiliary horizon-length premise in the preceding geometry theorem is
   automatic in the source asymptotic regime.  All positivity facts used here
   come from the same generated source-small-`J` run: the lower theta
   coefficients are positive, the printed schedule forces positive `sigma`,
   and the source regime forces positive `epsilon`.  Thus the explicit
   accuracy threshold below is a scalar consequence of the printed schedule,
   not a new generated-process or stationarity assumption. -/
theorem theorem_4_15_otherwise_source_small_j_five_memory_window_geometry_of_small_accuracy
    {xi : Type*} [MeasurableSpace xi]
    (P : StochasticProblem xi 1 1)
    (cfgForAccuracyHorizon : ℝ → ℕ → StochasticMuonConfig 1 1)
    (W0 : Mat 1 1) (sigma Delta epsilon C s : ℝ)
    (betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ)
    (N : ℕ)
    (hN : theorem_4_15_otherwiseSourceSmallJGeneratedRunForAccuracyHorizon P
      cfgForAccuracyHorizon W0 sigma Delta epsilon C s
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N)
    (hsmall : epsilon ≤
      (betaLower * horizonLower * sigma) / 6) :
    let cfgN := cfgForAccuracyHorizon epsilon N
    let q := Nat.ceil (5 / (1 - cfgN.beta))
    0 < (betaLower * horizonLower * sigma) / 6 ∧
      q ≤ N ∧
      cfgN.beta ^ q * (1 + (1 : ℝ) / 2) ≤ (1 : ℝ) / 2 - 1 / 4 ∧
      5 * (cfgN.eta 0 / (1 - cfgN.beta)) ≤ (q : ℝ) * cfgN.eta 0 ∧
      (q : ℝ) * cfgN.eta 0 <
        6 * (cfgN.eta 0 / (1 - cfgN.beta)) := by
  have hfields := hN
  rcases hfields with
    ⟨_horizon, _hfinite, _hDelta, _hthird, hvariance, _hwd, _hW0,
      hschedule, _hsource, hHorizon, _hregDom, hregime⟩
  have hbetaLowerPos : 0 < betaLower := hschedule.2.2.1.1
  have hhorizonLowerPos : 0 < horizonLower := hHorizon.1
  have hsigmaNe : sigma ≠ 0 := by
    intro hsigma
    apply hschedule.1.2.1
    simp [hsigma]
  have hsigmaPos : 0 < sigma :=
    lt_of_le_of_ne hvariance.nonneg (Ne.symm hsigmaNe)
  have hepsilonPos : 0 < epsilon := hregime.1
  have hthresholdPos : 0 <
      (betaLower * horizonLower * sigma) / 6 := by positivity
  have hscaled : 6 * epsilon ≤ betaLower * horizonLower * sigma := by
    calc
      6 * epsilon ≤ 6 * ((betaLower * horizonLower * sigma) / 6) :=
        mul_le_mul_of_nonneg_left hsmall (by norm_num)
      _ = betaLower * horizonLower * sigma := by ring
  have hlong : (6 : ℝ) ≤
      (betaLower * horizonLower) * (sigma / epsilon) := by
    have hdiv : (6 : ℝ) ≤
        (betaLower * horizonLower * sigma) / epsilon :=
      (le_div_iff₀ hepsilonPos).2 (by simpa [mul_assoc] using hscaled)
    calc
      (6 : ℝ) ≤ (betaLower * horizonLower * sigma) / epsilon := hdiv
      _ = (betaLower * horizonLower) * (sigma / epsilon) := by ring
  exact ⟨hthresholdPos,
    theorem_4_15_otherwise_source_small_j_five_memory_window_geometry
      P cfgForAccuracyHorizon W0 sigma Delta epsilon C s
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N hN hlong⟩

/- For every constant step, the complete generated sine-objective orbit lies
   on one affine step lattice.  This holds through every delayed momentum
   reversal (and through a zero-momentum step), so it is a genuine all-horizon
   reduction rather than a first-leg or fixed-resonance calculation. -/
theorem theorem_4_15_periodicCandidate_full_orbit_phase_on_step_lattice
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta : ℝ)
    (heta : ∀ t : ℕ, cfg.eta t = eta) (t : ℕ) :
    ∃ k : ℤ,
      theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg t).W =
        theorem_4_5_counterexampleEntry cfg.W0 + (k : ℝ) * eta := by
  induction t with
  | zero =>
      refine ⟨0, ?_⟩
      simp [deterministicMomentumMuonState, deterministicMomentumMuonBaseState]
  | succ t ih =>
      rcases ih with ⟨k, hk⟩
      let state := deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg t
      let nextState := deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (t + 1)
      have hstep :=
        (theorem_4_15_periodicCandidate_full_orbit_scalar_recurrence cfg t).1
      change theorem_4_5_counterexampleEntry nextState.W =
        theorem_4_5_counterexampleEntry state.W -
          cfg.eta t * Real.sign (state.M 0 0) at hstep
      change theorem_4_5_counterexampleEntry state.W =
        theorem_4_5_counterexampleEntry cfg.W0 + (k : ℝ) * eta at hk
      rcases lt_trichotomy (state.M 0 0) 0 with hneg | hzero | hpos
      · refine ⟨k + 1, ?_⟩
        rw [hstep, heta t, hk, Real.sign_of_neg hneg]
        push_cast
        ring
      · refine ⟨k, ?_⟩
        rw [hstep, heta t, hk, hzero, Real.sign_zero, mul_zero, sub_zero]
      · refine ⟨k - 1, ?_⟩
        rw [hstep, heta t, hk, Real.sign_of_pos hpos]
        push_cast
        ring

/- The directional-curvature term also has an exact all-index scalar form.
   At a zero-momentum index the partial polar is zero and the square of the
   sign correctly removes that summand; no nonvanishing assumption is hidden
   in this identity. -/
theorem theorem_4_15_periodicCandidate_generatedDirectionalTerm_eq_sign
    (cfg : DeterministicMomentumMuonConfig 1 1) (t : ℕ) :
    deterministicMomentumHessianDirectionalTerm
        theorem_4_15_periodicCandidateObjective cfg t =
      -Real.sin (theorem_4_5_counterexampleEntry
        (deterministicMomentumMuonState theorem_4_15_periodicCandidateObjective
          cfg t).W) *
        (Real.sign ((deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg t).M 0 0)) ^ 2 := by
  rw [theorem_4_15_periodicCandidate_directionalTerm,
    orthogonalizedDirection_eq_sign_smul_one_dimensional]
  simp [coordinateMatrix]

/- Consequently both quantities relevant to the proposed counterexample have
   exact full-horizon finite-sum descriptions even when momentum vanishes or
   changes sign.  This strictly strengthens the earlier reduction requiring
   nonvanishing momentum, while leaving that public helper available. -/
theorem theorem_4_15_periodicCandidate_fullHorizon_scalar_reduction_with_sign
    (cfg : DeterministicMomentumMuonConfig 1 1) (T : ℕ) :
    deterministicMomentumHessianDirectionalAverage
        theorem_4_15_periodicCandidateObjective cfg T =
        ((T : ℝ)⁻¹) * Finset.sum (Finset.range T) (fun t =>
          -Real.sin (theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg t).W) *
            (Real.sign ((deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg t).M 0 0)) ^ 2) ∧
      deterministicMomentumAverageNuclearGradient
        theorem_4_15_periodicCandidateObjective cfg T =
        ((T : ℝ)⁻¹) * Finset.sum (Finset.range T) (fun t =>
          |Real.cos (theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg t).W)|) := by
  constructor
  · unfold deterministicMomentumHessianDirectionalAverage
    congr 1
    apply Finset.sum_congr rfl
    intro t _ht
    exact theorem_4_15_periodicCandidate_generatedDirectionalTerm_eq_sign cfg t
  · unfold deterministicMomentumAverageNuclearGradient
    congr 1
    apply Finset.sum_congr rfl
    intro t _ht
    exact theorem_4_15_periodicCandidate_generatedNuclearGradient_eq_abs_cos cfg t

/- A resonant constant-step specialization turns the full-orbit reduction into
   an exact quantitative separation.  Starting at zero and taking step `pi`,
   every generated iterate remains on the integer-`pi` lattice, independently
   of the momentum sign and including a possible zero-momentum step.  Thus the
   source directional Hessian term vanishes at every generated state while the
   nuclear gradient norm is exactly one.  This is still only the orbit part of
   a source counterexample: the Appendix B.4 accuracy-indexed schedule fields
   must be instantiated before changing the source-facing theorem. -/
def theorem_4_15_periodicCandidateResonantConfig
    (beta : ℝ) (hbeta : beta ∈ Set.Ico (0 : ℝ) 1) :
    DeterministicMomentumMuonConfig 1 1 where
  W0 := 0
  eta := fun _ => Real.pi
  beta := beta
  beta_mem := hbeta

/- The resonant orbit has a fixed step `pi`, whereas the Appendix B.4
   otherwise schedule requires a step uniformly comparable to a multiple of
   `epsilon^2`.  The upper half of that schedule alone therefore rules out
   this configuration whenever its prescribed scale is below `pi`. -/
theorem theorem_4_15_periodicCandidate_resonant_eta_schedule_obstruction
    (beta : ℝ) (hbeta : beta ∈ Set.Ico (0 : ℝ) 1)
    (T : ℕ) (sigma Delta epsilon : ℝ)
    (betaLower betaUpper etaLower etaUpper : ℝ)
    (hsmall : etaUpper *
        theorem_4_15_otherwiseEtaRate 1 1 sigma Delta epsilon T < Real.pi) :
    ¬ theorem_4_15_otherwiseBranchSchedule
        (deterministicOracleConfig
          (theorem_4_15_periodicCandidateResonantConfig beta hbeta))
        T sigma Delta epsilon betaLower betaUpper etaLower etaUpper := by
  intro hschedule
  have heta := hschedule.2.2.2.1
  unfold theorem_4_15_uniformThetaAt at heta
  have hupper := heta.2.2.2
  simp only [deterministicOracleConfig,
    theorem_4_15_periodicCandidateResonantConfig] at hupper
  exact (not_le_of_gt hsmall) hupper

/- For fixed positive noise, initial gap, and uniform upper theta constant,
   the preceding obstruction holds throughout a punctured neighbourhood of
   zero accuracy.  Thus the exact resonant separation is not a counterexample
   to the source theorem's accuracy-indexed otherwise branch: its fixed `pi`
   step is incompatible with the printed shrinking-step schedule. -/
theorem theorem_4_15_periodicCandidate_resonant_eta_schedule_eventually_impossible
    (beta : ℝ) (hbeta : beta ∈ Set.Ico (0 : ℝ) 1)
    (sigma Delta etaUpper : ℝ)
    (hsigma : 0 < sigma) (hDelta : 0 < Delta) (hetaUpper : 0 < etaUpper) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧
      ∀ epsilon : ℝ, epsilonDomain epsilon → epsilon ≤ epsilon0 →
      ∀ T : ℕ, ∀ betaLower betaUpper etaLower : ℝ,
        ¬ theorem_4_15_otherwiseBranchSchedule
            (deterministicOracleConfig
              (theorem_4_15_periodicCandidateResonantConfig beta hbeta))
            T sigma Delta epsilon betaLower betaUpper etaLower etaUpper := by
  let epsilon0 : ℝ :=
    min 1 (Real.pi * sigma ^ 3 / (2 * etaUpper * Delta))
  have hsigma3 : 0 < sigma ^ 3 := pow_pos hsigma _
  have hdenom : 0 < 2 * etaUpper * Delta := by positivity
  have hratio : 0 < Real.pi * sigma ^ 3 / (2 * etaUpper * Delta) :=
    div_pos (mul_pos Real.pi_pos hsigma3) hdenom
  have hepsilon0 : 0 < epsilon0 := by
    exact lt_min zero_lt_one hratio
  refine ⟨epsilon0, hepsilon0, ?_⟩
  intro epsilon hepsilon hepsilon0Bound T betaLower betaUpper etaLower
  apply theorem_4_15_periodicCandidate_resonant_eta_schedule_obstruction
  have hepsilonOne : epsilon ≤ 1 :=
    le_trans hepsilon0Bound (min_le_left _ _)
  have hepsilonRatio :
      epsilon ≤ Real.pi * sigma ^ 3 / (2 * etaUpper * Delta) :=
    le_trans hepsilon0Bound (min_le_right _ _)
  have hepsilonPos : 0 < epsilon := hepsilon
  have hepsilonSq : epsilon ^ 2 ≤ epsilon := by
    nlinarith
  have hscaledSq :
      2 * etaUpper * Delta * epsilon ^ 2 ≤
        2 * etaUpper * Delta * epsilon :=
    mul_le_mul_of_nonneg_left hepsilonSq hdenom.le
  have hscaled :
      2 * etaUpper * Delta * epsilon ≤ Real.pi * sigma ^ 3 := by
    have hmul := (le_div_iff₀ hdenom).mp hepsilonRatio
    nlinarith
  have hhalf :
      etaUpper * Delta * epsilon ^ 2 / sigma ^ 3 ≤ Real.pi / 2 := by
    apply (div_le_iff₀ hsigma3).2
    nlinarith [le_trans hscaledSq hscaled]
  have hpiHalf : Real.pi / 2 < Real.pi := by
    nlinarith [Real.pi_pos]
  have hrate :
      theorem_4_15_otherwiseEtaRate 1 1 sigma Delta epsilon T =
        Delta * epsilon ^ 2 / sigma ^ 3 := by
    unfold theorem_4_15_otherwiseEtaRate sourceQuot matrixRankBound
    norm_num
  rw [hrate]
  have hhalf' :
      etaUpper * (Delta * epsilon ^ 2 / sigma ^ 3) ≤ Real.pi / 2 := by
    calc
      _ = etaUpper * Delta * epsilon ^ 2 / sigma ^ 3 := by ring
      _ ≤ Real.pi / 2 := hhalf
  exact lt_of_le_of_lt hhalf' hpiHalf

/- The preceding failure is exactly a failure of the schedule field of the
   full source-small-`J` generated-run predicate.  Packaging it at that level
   records why the resonant separation cannot be promoted to a source
   counterexample: for every sufficiently small positive accuracy, no choice
   of the remaining source constants can make this fixed-step generated family
   an Appendix B.4 otherwise run. -/
theorem theorem_4_15_periodicCandidate_resonant_source_run_eventually_impossible
    (beta : ℝ) (hbeta : beta ∈ Set.Ico (0 : ℝ) 1)
    (sigma etaUpper : ℝ)
    (hsigma : 0 < sigma) (hetaUpper : 0 < etaUpper) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧
      ∀ epsilon : ℝ, epsilonDomain epsilon → epsilon ≤ epsilon0 →
      ∀ T : ℕ, ∀ C s betaLower betaUpper etaLower
          horizonLower horizonUpper : ℝ,
        ¬ theorem_4_15_otherwiseSourceSmallJGeneratedRunForAccuracyHorizon
            (deterministicOracleProblem
              theorem_4_15_periodicCandidateObjective)
            (fun _ _ => deterministicOracleConfig
              (theorem_4_15_periodicCandidateResonantConfig beta hbeta))
            0 sigma 1 epsilon C s
            betaLower betaUpper etaLower etaUpper horizonLower horizonUpper T := by
  obtain ⟨epsilon0, hepsilon0, himpossible⟩ :=
    theorem_4_15_periodicCandidate_resonant_eta_schedule_eventually_impossible
      beta hbeta sigma 1 etaUpper hsigma zero_lt_one hetaUpper
  refine ⟨epsilon0, hepsilon0, ?_⟩
  intro epsilon hepsilon hepsilon0Bound T C s betaLower betaUpper etaLower
    horizonLower horizonUpper hrun
  rcases hrun with
    ⟨_horizon, _hfinite, _hDelta, _hthird, _hvariance, _hwd, _hW0,
      hschedule, _hsource, _hHorizon, _hregDom, _hregime⟩
  exact himpossible epsilon hepsilon hepsilon0Bound T betaLower betaUpper
    etaLower hschedule

theorem theorem_4_15_periodicCandidate_resonant_phase_int_mul_pi
    (beta : ℝ) (hbeta : beta ∈ Set.Ico (0 : ℝ) 1) (t : ℕ) :
    ∃ k : ℤ,
      theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective
            (theorem_4_15_periodicCandidateResonantConfig beta hbeta) t).W =
        (k : ℝ) * Real.pi := by
  induction t with
  | zero =>
      refine ⟨0, ?_⟩
      simp [deterministicMomentumMuonState, deterministicMomentumMuonBaseState,
        theorem_4_15_periodicCandidateResonantConfig,
        theorem_4_5_counterexampleEntry]
  | succ t ih =>
      rcases ih with ⟨k, hk⟩
      let cfg := theorem_4_15_periodicCandidateResonantConfig beta hbeta
      let state := deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg t
      let nextState := deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (t + 1)
      have hstep :=
        (theorem_4_15_periodicCandidate_full_orbit_scalar_recurrence cfg t).1
      change theorem_4_5_counterexampleEntry nextState.W =
        theorem_4_5_counterexampleEntry state.W -
          cfg.eta t * Real.sign (state.M 0 0) at hstep
      change theorem_4_5_counterexampleEntry state.W = (k : ℝ) * Real.pi at hk
      rcases lt_trichotomy (state.M 0 0) 0 with hneg | hzero | hpos
      · refine ⟨k + 1, ?_⟩
        rw [hstep, hk, Real.sign_of_neg hneg]
        simp only [cfg, theorem_4_15_periodicCandidateResonantConfig]
        push_cast
        ring
      · refine ⟨k, ?_⟩
        rw [hstep, hk, hzero, Real.sign_zero, mul_zero, sub_zero]
      · refine ⟨k - 1, ?_⟩
        rw [hstep, hk, Real.sign_of_pos hpos]
        simp only [cfg, theorem_4_15_periodicCandidateResonantConfig]
        push_cast
        ring

theorem theorem_4_15_periodicCandidate_resonant_directionalTerm_eq_zero
    (beta : ℝ) (hbeta : beta ∈ Set.Ico (0 : ℝ) 1) (t : ℕ) :
    deterministicMomentumHessianDirectionalTerm
        theorem_4_15_periodicCandidateObjective
        (theorem_4_15_periodicCandidateResonantConfig beta hbeta) t = 0 := by
  rw [theorem_4_15_periodicCandidate_generatedDirectionalTerm_eq_sign]
  obtain ⟨k, hk⟩ :=
    theorem_4_15_periodicCandidate_resonant_phase_int_mul_pi beta hbeta t
  rw [hk, Real.sin_int_mul_pi]
  ring

theorem theorem_4_15_periodicCandidate_resonant_nuclearGradient_eq_one
    (beta : ℝ) (hbeta : beta ∈ Set.Ico (0 : ℝ) 1) (t : ℕ) :
    nuclearNorm
        (theorem_4_15_periodicCandidateObjective.grad
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective
            (theorem_4_15_periodicCandidateResonantConfig beta hbeta) t).W) = 1 := by
  rw [theorem_4_15_periodicCandidate_generatedNuclearGradient_eq_abs_cos]
  obtain ⟨k, hk⟩ :=
    theorem_4_15_periodicCandidate_resonant_phase_int_mul_pi beta hbeta t
  rw [hk, Real.abs_cos_int_mul_pi]

theorem theorem_4_15_periodicCandidate_resonant_fullHorizon_separation
    (beta : ℝ) (hbeta : beta ∈ Set.Ico (0 : ℝ) 1) (T : ℕ)
    (hT : horizonDomain T) :
    deterministicMomentumHessianDirectionalAverage
        theorem_4_15_periodicCandidateObjective
        (theorem_4_15_periodicCandidateResonantConfig beta hbeta) T = 0 ∧
      deterministicMomentumAverageNuclearGradient
        theorem_4_15_periodicCandidateObjective
        (theorem_4_15_periodicCandidateResonantConfig beta hbeta) T = 1 := by
  constructor
  · unfold deterministicMomentumHessianDirectionalAverage
    rw [Finset.sum_eq_zero (fun t _ht =>
      theorem_4_15_periodicCandidate_resonant_directionalTerm_eq_zero
        beta hbeta t), mul_zero]
  · unfold deterministicMomentumAverageNuclearGradient
    have hsum :
        Finset.sum (Finset.range T) (fun t =>
          nuclearNorm
            (theorem_4_15_periodicCandidateObjective.grad
              (deterministicMomentumMuonState
                theorem_4_15_periodicCandidateObjective
                (theorem_4_15_periodicCandidateResonantConfig beta hbeta) t).W)) =
          (T : ℝ) := by
      calc
        _ = Finset.sum (Finset.range T) (fun _ => (1 : ℝ)) := by
          apply Finset.sum_congr rfl
          intro t _ht
          exact theorem_4_15_periodicCandidate_resonant_nuclearGradient_eq_one
            beta hbeta t
        _ = (T : ℝ) := by simp
    rw [hsum]
    exact inv_mul_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hT))

/- The singleton-oracle well-definedness argument does not depend on the
   resonant step size.  Stating it for an arbitrary generated momentum config
   lets every later shrinking-step window theorem live on the exact
   `stochasticMuonState` source objects without adding an integrability
   premise to the counterexample route. -/
theorem theorem_4_15_periodicCandidate_expectationsWellDefined
    (cfg : DeterministicMomentumMuonConfig 1 1) (T : ℕ)
    (sigma : ℝ) (hsigma : 0 ≤ sigma) :
    stochasticMuonExpectationsWellDefined
      (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
      (deterministicOracleConfig cfg) T := by
  let P := deterministicOracleProblem theorem_4_15_periodicCandidateObjective
  let scfg := deterministicOracleConfig cfg
  have hthird : ThirdDerivativeBounded P.objective 6 := by
    simpa [P, deterministicOracleProblem_objective] using
      theorem_4_15_periodicCandidateObjective_thirdDerivativeBounded
  have hregularity : StochasticObjectiveRegularity P.objective :=
    Or.inr (Or.inr ⟨6, hthird⟩)
  have hvariance : BoundedVariance P sigma := by
    exact deterministicOracleProblem_boundedVariance_of_nonneg
      theorem_4_15_periodicCandidateObjective hsigma
  exact ⟨
    stochasticAverageNuclearGradient_wellDefined_of_source_assumptions
      P scfg T sigma hregularity hvariance,
    stochasticExpectedObjectiveDrop_wellDefined_of_source_assumptions
      P scfg T sigma hregularity hvariance,
    stochasticHessianJstar_wellDefined_of_source_assumptions
      P scfg T 6 sigma hthird hvariance⟩

/- At the selected shrinking horizon, every field of the original
   source-small-`J` generated-run predicate except the directional-curvature
   inequality is now automatic.  The remaining premise below is exactly that
   source quantity after the proved singleton-oracle transfer; it contains no
   cross term, `Jstar`, descent estimate, or stationarity conclusion. -/
theorem theorem_4_15_periodicCandidate_shrinking_selected_source_run_of_directional_bound
    (sigma epsilon C : ℝ)
    (hsigma : 0 < sigma) (hepsilon : 0 < epsilon)
    (hepsilon_le_sigma : epsilon ≤ sigma) (hC : 0 < C)
    (hdirectional :
      deterministicMomentumHessianDirectionalAverage
          theorem_4_15_periodicCandidateObjective
          (theorem_4_15_periodicCandidateShrinkingConfig
            sigma 1 epsilon hsigma hepsilon hepsilon_le_sigma)
          (theorem_4_15_periodicCandidateShrinkingHorizon sigma epsilon) ≤
        C * (sigma * epsilon)) :
    theorem_4_15_otherwiseSourceSmallJGeneratedRunForAccuracyHorizon
      (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
      (fun _accuracy _horizon =>
        deterministicOracleConfig
          (theorem_4_15_periodicCandidateShrinkingConfig
            sigma 1 epsilon hsigma hepsilon hepsilon_le_sigma))
      0 sigma 1 epsilon C 6 1 1 1 1 1 2
      (theorem_4_15_periodicCandidateShrinkingHorizon sigma epsilon) := by
  let dcfg := theorem_4_15_periodicCandidateShrinkingConfig
    sigma 1 epsilon hsigma hepsilon hepsilon_le_sigma
  let scfg := deterministicOracleConfig dcfg
  let N := theorem_4_15_periodicCandidateShrinkingHorizon sigma epsilon
  have hscale := theorem_4_15_periodicCandidate_shrinkingHorizon_scale
    sigma epsilon hsigma hepsilon hepsilon_le_sigma
  have hschedule := theorem_4_15_periodicCandidate_shrinkingConfig_schedule
    N sigma 1 epsilon hscale.1 hsigma hepsilon hepsilon_le_sigma
  have hsource := theorem_4_15_periodicCandidate_shrinkingConfig_sourceDomain
    N sigma 1 epsilon hscale.1 hsigma (by norm_num) hepsilon
      hepsilon_le_sigma
  let hwd := theorem_4_15_periodicCandidate_expectationsWellDefined
    dcfg N sigma hsigma.le
  have hvariance : BoundedVariance
      (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
      sigma :=
    deterministicOracleProblem_boundedVariance_of_nonneg
      theorem_4_15_periodicCandidateObjective hsigma.le
  have hfinite :
      (deterministicOracleProblem
        theorem_4_15_periodicCandidateObjective).objective.HasFiniteInfimum := by
    simpa [deterministicOracleProblem_objective] using
      theorem_4_15_periodicCandidateObjective_hasFiniteInfimum
  have hgap : sourceObjectiveInitialGap
      (deterministicOracleProblem
        theorem_4_15_periodicCandidateObjective).objective 0 hfinite = 1 := by
    simpa [deterministicOracleProblem_objective] using
      theorem_4_15_periodicCandidateObjective_sourceInitialGap_zero
  have hregDom : theorem_4_15_branchRegimeThresholdDomain 1 1 sigma 1 := by
    simp [theorem_4_15_branchRegimeThresholdDomain, sourceInvDomain]
  refine ⟨hscale.1, hfinite, hgap, ?_, hvariance, hwd, ?_, ?_, ?_,
    hscale.2, hregDom, ?_⟩
  · simpa [deterministicOracleProblem_objective] using
      theorem_4_15_periodicCandidateObjective_thirdDerivativeBounded
  · rfl
  · simpa [scfg, dcfg] using hschedule
  · simpa [scfg, dcfg] using hsource
  · refine ⟨hepsilon, hC, ?_⟩
    rw [deterministicOracle_hessianDirectionalAverageRealized_eq]
    simpa [dcfg, N, theorem_4_15_branchRegimeThreshold, matrixRankBound,
      realizedSourceSqrt, sourceSqrt, realizedSourceInv, sourceInv] using
      hdirectional

theorem theorem_4_15_periodicCandidate_resonant_expectationsWellDefined
    (beta : ℝ) (hbeta : beta ∈ Set.Ico (0 : ℝ) 1) (T : ℕ)
    (sigma : ℝ) (hsigma : 0 ≤ sigma) :
    stochasticMuonExpectationsWellDefined
      (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
      (deterministicOracleConfig
        (theorem_4_15_periodicCandidateResonantConfig beta hbeta)) T := by
  exact theorem_4_15_periodicCandidate_expectationsWellDefined
    (theorem_4_15_periodicCandidateResonantConfig beta hbeta) T sigma hsigma

/- This is the same separation on the stochastic source objects, obtained by
   the proved singleton-oracle realization.  In particular, the zero
   directional average and unit generated-gradient average are not facts
   about an arbitrary deterministic trajectory. -/
theorem theorem_4_15_periodicCandidate_resonant_stochastic_separation
    (beta : ℝ) (hbeta : beta ∈ Set.Ico (0 : ℝ) 1) (T : ℕ)
    (hT : horizonDomain T) (sigma : ℝ) (hsigma : 0 ≤ sigma) :
    ∃ hwd : stochasticMuonExpectationsWellDefined
        (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
        (deterministicOracleConfig
          (theorem_4_15_periodicCandidateResonantConfig beta hbeta)) T,
      stochasticHessianDirectionalAverageRealized
          (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
          (deterministicOracleConfig
            (theorem_4_15_periodicCandidateResonantConfig beta hbeta)) T
          hwd.2.2.1 = 0 ∧
        stochasticAverageNuclearGradientRealized
          (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
          (deterministicOracleConfig
            (theorem_4_15_periodicCandidateResonantConfig beta hbeta)) T
          hwd.1 = 1 := by
  let hwd := theorem_4_15_periodicCandidate_resonant_expectationsWellDefined
    beta hbeta T sigma hsigma
  refine ⟨hwd, ?_, ?_⟩
  · rw [deterministicOracle_hessianDirectionalAverageRealized_eq]
    exact (theorem_4_15_periodicCandidate_resonant_fullHorizon_separation
      beta hbeta T hT).1
  · rw [deterministicOracle_average_eq]
    exact (theorem_4_15_periodicCandidate_resonant_fullHorizon_separation
      beta hbeta T hT).2

/- The resonant stochastic run satisfies the actual Appendix B.4 directional
   small-`J` predicate (with the candidate's exact initial gap `Delta = 1`),
   yet its generated expected nuclear-gradient average is one.  This proves
   the source-object obstruction and all analytic/source-assumption fields
   independently of the still-open printed eta/beta/horizon schedule
   instantiation. -/
theorem theorem_4_15_periodicCandidate_resonant_source_smallJ_separation
    (beta : ℝ) (hbeta : beta ∈ Set.Ico (0 : ℝ) 1) (T : ℕ)
    (hT : horizonDomain T) (sigma epsilon C : ℝ)
    (hsigma : 0 < sigma) (hepsilon : epsilonDomain epsilon) (hC : 0 < C) :
    ∃ (hwd : stochasticMuonExpectationsWellDefined
        (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
        (deterministicOracleConfig
          (theorem_4_15_periodicCandidateResonantConfig beta hbeta)) T)
      (hregDom : theorem_4_15_branchRegimeThresholdDomain 1 1 sigma 1),
      theorem_4_15_otherwiseSourceBranchRegimeRealized
          (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
          (deterministicOracleConfig
            (theorem_4_15_periodicCandidateResonantConfig beta hbeta))
          T sigma 1 epsilon C hwd.2.2 hregDom ∧
        stochasticAverageNuclearGradientRealized
          (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
          (deterministicOracleConfig
            (theorem_4_15_periodicCandidateResonantConfig beta hbeta)) T
          hwd.1 = 1 := by
  let hwd := theorem_4_15_periodicCandidate_resonant_expectationsWellDefined
    beta hbeta T sigma hsigma.le
  have hregDom : theorem_4_15_branchRegimeThresholdDomain 1 1 sigma 1 := by
    simp [theorem_4_15_branchRegimeThresholdDomain, sourceInvDomain]
  refine ⟨hwd, hregDom, ?_, ?_⟩
  · refine ⟨hepsilon, hC, ?_⟩
    rw [deterministicOracle_hessianDirectionalAverageRealized_eq]
    rw [(theorem_4_15_periodicCandidate_resonant_fullHorizon_separation
      beta hbeta T hT).1]
    apply mul_nonneg hC.le
    unfold theorem_4_15_branchRegimeThreshold
    simp only [matrixRankBound, Nat.min_self, Nat.cast_one, pow_one,
      realizedSourceSqrt, sourceSqrt, Real.sqrt_one, one_mul,
      realizedSourceInv, sourceInv, inv_one, mul_one]
    exact mul_nonneg hsigma.le hepsilon.le
  · rw [deterministicOracle_average_eq]
    exact (theorem_4_15_periodicCandidate_resonant_fullHorizon_separation
      beta hbeta T hT).2

theorem theorem_4_15_periodicCandidate_positive_gradient_prefix
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta : ℝ) (t : ℕ)
    (hW0 : cfg.W0 = (Real.pi / 4) • coordinateMatrix 0 0)
    (hetaNonneg : 0 ≤ eta)
    (heta : ∀ k < t, cfg.eta k = eta)
    (hphase : (t : ℝ) * eta < 3 * Real.pi / 4) :
    (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg t).W =
        (Real.pi / 4 - (t : ℝ) * eta) • coordinateMatrix 0 0 ∧
      ∃ c : ℝ, 0 < c ∧
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg t).M =
          c • coordinateMatrix 0 0 := by
  let E : Mat 1 1 := coordinateMatrix 0 0
  have hE : E ≠ 0 := by
    intro hzero
    have hentry := congrArg (fun M : Mat 1 1 => M 0 0) hzero
    norm_num [E, coordinateMatrix] at hentry
  induction t with
  | zero =>
      constructor
      · change cfg.W0 = _
        simpa [E] using hW0
      · refine ⟨Real.sqrt 2 / 2, by positivity, ?_⟩
        rw [deterministicMomentumMuon_M_zero_eq_gradient]
        unfold deterministicGradient
        rw [hW0, theorem_4_15_periodicCandidateObjective_grad]
        ext i j
        fin_cases i
        fin_cases j
        simp [E, coordinateMatrix, Real.cos_pi_div_four]
  | succ t ih =>
      have hprefixPhase : (t : ℝ) * eta < 3 * Real.pi / 4 := by
        have ht : (t : ℝ) ≤ (t + 1 : ℕ) := by
          exact_mod_cast Nat.le_succ t
        have hmul : (t : ℝ) * eta ≤ ((t + 1 : ℕ) : ℝ) * eta :=
          mul_le_mul_of_nonneg_right ht hetaNonneg
        exact lt_of_le_of_lt hmul hphase
      have hetaPrefix : ∀ k < t, cfg.eta k = eta := by
        intro k hk
        exact heta k (lt_trans hk (Nat.lt_succ_self t))
      rcases ih hetaPrefix hprefixPhase with ⟨hWt, c, hc, hMt⟩
      have hdirection : orthogonalizedDirection
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg t).M = E := by
        rw [hMt,
          orthogonalizedDirection_pos_smul_eq_one_dimensional E c hE hc,
          theorem_4_15_periodicCandidate_coordinateDirection]
      have hetaCurrent : cfg.eta t = eta :=
        heta t (Nat.lt_succ_self t)
      have hWsucc :
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg (t + 1)).W =
            (Real.pi / 4 - ((t + 1 : ℕ) : ℝ) * eta) • E := by
        rw [deterministicMomentumMuon_W_succ_eq_source_update,
          hWt, hdirection, hetaCurrent]
        push_cast
        module
      have hphaseLower :
          -(Real.pi / 2) < Real.pi / 4 - ((t + 1 : ℕ) : ℝ) * eta := by
        linarith
      have hphaseUpper :
          Real.pi / 4 - ((t + 1 : ℕ) : ℝ) * eta < Real.pi / 2 := by
        have hnonneg : 0 ≤ ((t + 1 : ℕ) : ℝ) * eta := by positivity
        linarith [Real.pi_pos]
      let g : ℝ := Real.cos
        (Real.pi / 4 - ((t + 1 : ℕ) : ℝ) * eta)
      have hg : 0 < g := by
        exact Real.cos_pos_of_mem_Ioo ⟨hphaseLower, hphaseUpper⟩
      let cnext : ℝ := cfg.beta * c + (1 - cfg.beta) * g
      have hcnext : 0 < cnext := by
        dsimp [cnext]
        have hfirst : 0 ≤ cfg.beta * c :=
          mul_nonneg cfg.beta_mem.1 hc.le
        have hsecond : 0 < (1 - cfg.beta) * g :=
          mul_pos (sub_pos.mpr cfg.beta_mem.2) hg
        linarith
      refine ⟨by simpa [E] using hWsucc, cnext, hcnext, ?_⟩
      rw [deterministicMomentumMuon_M_succ_eq_source_update,
        hMt, hWsucc]
      unfold deterministicGradient
      rw [theorem_4_15_periodicCandidateObjective_grad]
      ext i j
      fin_cases i
      fin_cases j
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        theorem_4_5_counterexampleEntry_apply]
      simp [E, coordinateMatrix, g, cnext]

/- The first sign change of the true gradient does not immediately reverse the
   generated momentum.  The exact scalar recurrence gives the uniform lower
   bound below using only `cos x >= -1`.  Hence, for every index at which the
   displayed geometric lower bound is positive, the Algorithm 1 direction is
   still the positive coordinate direction and the phase continues along the
   same affine leg.  Unlike `positive_gradient_prefix`, this statement remains
   applicable after the cosine gradient has become negative. -/
theorem theorem_4_15_periodicCandidate_positive_momentum_delay_lower_bound
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta : ℝ) (t : ℕ)
    (hW0 : cfg.W0 = (Real.pi / 4) • coordinateMatrix 0 0)
    (heta : ∀ k < t, cfg.eta k = eta)
    (hdelay : ∀ k < t,
      1 < cfg.beta ^ k * (Real.sqrt 2 / 2 + 1)) :
    (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg t).W =
        (Real.pi / 4 - (t : ℝ) * eta) • coordinateMatrix 0 0 ∧
      cfg.beta ^ t * (Real.sqrt 2 / 2 + 1) - 1 ≤
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg t).M 0 0 := by
  induction t with
  | zero =>
      constructor
      · change cfg.W0 = _
        simpa using hW0
      · rw [deterministicMomentumMuon_M_zero_eq_gradient]
        unfold deterministicGradient
        rw [hW0, theorem_4_15_periodicCandidateObjective_grad]
        simp [theorem_4_5_counterexampleEntry_apply, coordinateMatrix,
          Real.cos_pi_div_four]
  | succ t ih =>
      have hetaPrefix : ∀ k < t, cfg.eta k = eta := by
        intro k hk
        exact heta k (lt_trans hk (Nat.lt_succ_self t))
      have hdelayPrefix : ∀ k < t,
          1 < cfg.beta ^ k * (Real.sqrt 2 / 2 + 1) := by
        intro k hk
        exact hdelay k (lt_trans hk (Nat.lt_succ_self t))
      rcases ih hetaPrefix hdelayPrefix with ⟨hWt, hMtLower⟩
      have hboundPositive :
          0 < cfg.beta ^ t * (Real.sqrt 2 / 2 + 1) - 1 := by
        linarith [hdelay t (Nat.lt_succ_self t)]
      have hMtPositive : 0 <
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg t).M 0 0 :=
        lt_of_lt_of_le hboundPositive hMtLower
      have hWsucc :
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg (t + 1)).W =
            (Real.pi / 4 - ((t + 1 : ℕ) : ℝ) * eta) •
              coordinateMatrix 0 0 := by
        rw [deterministicMomentumMuon_W_succ_eq_source_update, hWt,
          orthogonalizedDirection_eq_sign_smul_one_dimensional,
          Real.sign_of_pos hMtPositive, one_smul,
          heta t (Nat.lt_succ_self t)]
        push_cast
        module
      have hrecurrence :=
        (theorem_4_15_periodicCandidate_full_orbit_scalar_recurrence cfg t).2
      have hscaledLower := mul_le_mul_of_nonneg_left hMtLower cfg.beta_mem.1
      have hcosLower := mul_le_mul_of_nonneg_left
        (Real.neg_one_le_cos
          (theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg (t + 1)).W))
        (sub_nonneg.mpr cfg.beta_mem.2.le)
      constructor
      · exact hWsucc
      · rw [hrecurrence]
        rw [pow_succ]
        linarith

/- Bernoulli's inequality turns the geometric condition above into the natural
   momentum time scale `t * (1 - beta)`.  Thus the affine leg and positive
   momentum persist for a constant amount of rescaled time, exactly the scale
   on which the Appendix B.4 choice `1 - beta = Theta(epsilon^2)` operates. -/
theorem theorem_4_15_periodicCandidate_positive_momentum_delay_of_time_budget
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta : ℝ) (t : ℕ)
    (hW0 : cfg.W0 = (Real.pi / 4) • coordinateMatrix 0 0)
    (heta : ∀ k < t, cfg.eta k = eta)
    (htimeBudget :
      (t : ℝ) * (1 - cfg.beta) * (Real.sqrt 2 / 2 + 1) <
        Real.sqrt 2 / 2) :
    (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg t).W =
        (Real.pi / 4 - (t : ℝ) * eta) • coordinateMatrix 0 0 ∧
      0 < (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg t).M 0 0 := by
  have hcoefficient : 0 < Real.sqrt 2 / 2 + 1 := by positivity
  have hdelay : ∀ k ≤ t,
      1 < cfg.beta ^ k * (Real.sqrt 2 / 2 + 1) := by
    intro k hk
    have hkReal : (k : ℝ) ≤ (t : ℝ) := by exact_mod_cast hk
    have hkScaled :
        (k : ℝ) * (1 - cfg.beta) ≤ (t : ℝ) * (1 - cfg.beta) :=
      mul_le_mul_of_nonneg_right hkReal (sub_nonneg.mpr cfg.beta_mem.2.le)
    have hkBudget :
        (k : ℝ) * (1 - cfg.beta) * (Real.sqrt 2 / 2 + 1) <
          Real.sqrt 2 / 2 := by
      exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_right hkScaled hcoefficient.le) htimeBudget
    have hbern :
        1 + (k : ℝ) * (cfg.beta - 1) ≤ cfg.beta ^ k := by
      exact one_add_mul_sub_le_pow (a := cfg.beta)
        (by linarith [cfg.beta_mem.1]) k
    have hbernScaled :=
      mul_le_mul_of_nonneg_right hbern hcoefficient.le
    have hlinear :
        1 < (1 + (k : ℝ) * (cfg.beta - 1)) *
          (Real.sqrt 2 / 2 + 1) := by
      nlinarith
    exact lt_of_lt_of_le hlinear hbernScaled
  rcases theorem_4_15_periodicCandidate_positive_momentum_delay_lower_bound
      cfg eta t hW0 heta (fun k hk => hdelay k (Nat.le_of_lt hk)) with
    ⟨hWt, hMtLower⟩
  have hboundPositive :
      0 < cfg.beta ^ t * (Real.sqrt 2 / 2 + 1) - 1 := by
    linarith [hdelay t le_rfl]
  exact ⟨hWt, lt_of_lt_of_le hboundPositive hMtLower⟩

/- The preceding delay estimate can be restarted at any generated index.  Its
   clock is the elapsed time `t` after `start`, not the absolute iteration
   number.  This is the recurrence form needed to study repeated momentum
   reversals under the shrinking Appendix B.4 schedule: once a positive
   momentum lower bound is established at a new leg, earlier iterations no
   longer consume that leg's time budget. -/
theorem theorem_4_15_periodicCandidate_positive_momentum_delay_lower_bound_from_index
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta m0 : ℝ)
    (start t : ℕ)
    (hMstart : m0 ≤
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg start).M 0 0)
    (heta : ∀ k < t, cfg.eta (start + k) = eta)
    (hdelay : ∀ k < t, 1 < cfg.beta ^ k * (m0 + 1)) :
    theorem_4_5_counterexampleEntry
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg (start + t)).W =
        theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg start).W -
          (t : ℝ) * eta ∧
      cfg.beta ^ t * (m0 + 1) - 1 ≤
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg (start + t)).M 0 0 := by
  induction t with
  | zero =>
      constructor
      · simp
      · simpa using hMstart
  | succ t ih =>
      have hetaPrefix : ∀ k < t, cfg.eta (start + k) = eta := by
        intro k hk
        exact heta k (lt_trans hk (Nat.lt_succ_self t))
      have hdelayPrefix : ∀ k < t,
          1 < cfg.beta ^ k * (m0 + 1) := by
        intro k hk
        exact hdelay k (lt_trans hk (Nat.lt_succ_self t))
      rcases ih hetaPrefix hdelayPrefix with ⟨hWt, hMtLower⟩
      have hboundPositive : 0 < cfg.beta ^ t * (m0 + 1) - 1 := by
        linarith [hdelay t (Nat.lt_succ_self t)]
      have hMtPositive : 0 <
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg (start + t)).M 0 0 :=
        lt_of_lt_of_le hboundPositive hMtLower
      have hrecurrence :=
        theorem_4_15_periodicCandidate_full_orbit_scalar_recurrence
          cfg (start + t)
      have hWsucc :
          theorem_4_5_counterexampleEntry
              (deterministicMomentumMuonState
                theorem_4_15_periodicCandidateObjective cfg
                  (start + (t + 1))).W =
            theorem_4_5_counterexampleEntry
              (deterministicMomentumMuonState
                theorem_4_15_periodicCandidateObjective cfg (start + t)).W -
              eta := by
        rw [show start + (t + 1) = (start + t) + 1 by omega]
        rw [hrecurrence.1, Real.sign_of_pos hMtPositive,
          heta t (Nat.lt_succ_self t)]
        ring
      have hscaledLower :=
        mul_le_mul_of_nonneg_left hMtLower cfg.beta_mem.1
      have hcosLower := mul_le_mul_of_nonneg_left
        (Real.neg_one_le_cos
          (theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg
                (start + (t + 1))).W))
        (sub_nonneg.mpr cfg.beta_mem.2.le)
      constructor
      · rw [hWsucc, hWt]
        push_cast
        ring
      · rw [show start + (t + 1) = (start + t) + 1 by omega,
          hrecurrence.2, pow_succ]
        have hcosLower' := hcosLower
        rw [show start + (t + 1) = (start + t) + 1 by omega] at hcosLower'
        linarith

/- Bernoulli's inequality gives the corresponding restarted elapsed-time
   criterion.  Unlike the old global condition, this hypothesis can be
   discharged separately after each proved momentum reversal. -/
theorem theorem_4_15_periodicCandidate_positive_momentum_delay_from_index_of_time_budget
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta m0 : ℝ)
    (start t : ℕ)
    (hm0 : 0 < m0)
    (hMstart : m0 ≤
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg start).M 0 0)
    (heta : ∀ k < t, cfg.eta (start + k) = eta)
    (htimeBudget :
      (t : ℝ) * (1 - cfg.beta) * (m0 + 1) < m0) :
    theorem_4_5_counterexampleEntry
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg (start + t)).W =
        theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg start).W -
          (t : ℝ) * eta ∧
      0 < (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + t)).M 0 0 := by
  have hcoefficient : 0 < m0 + 1 := by linarith
  have hdelay : ∀ k ≤ t, 1 < cfg.beta ^ k * (m0 + 1) := by
    intro k hk
    have hkReal : (k : ℝ) ≤ (t : ℝ) := by exact_mod_cast hk
    have hkScaled :
        (k : ℝ) * (1 - cfg.beta) ≤ (t : ℝ) * (1 - cfg.beta) :=
      mul_le_mul_of_nonneg_right hkReal (sub_nonneg.mpr cfg.beta_mem.2.le)
    have hkBudget :
        (k : ℝ) * (1 - cfg.beta) * (m0 + 1) < m0 := by
      exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_right hkScaled hcoefficient.le) htimeBudget
    have hbern : 1 + (k : ℝ) * (cfg.beta - 1) ≤ cfg.beta ^ k := by
      exact one_add_mul_sub_le_pow (a := cfg.beta)
        (by linarith [cfg.beta_mem.1]) k
    have hbernScaled :=
      mul_le_mul_of_nonneg_right hbern hcoefficient.le
    have hlinear :
        1 < (1 + (k : ℝ) * (cfg.beta - 1)) * (m0 + 1) := by
      nlinarith
    exact lt_of_lt_of_le hlinear hbernScaled
  rcases
      theorem_4_15_periodicCandidate_positive_momentum_delay_lower_bound_from_index
        cfg eta m0 start t hMstart heta
          (fun k hk => hdelay k (Nat.le_of_lt hk)) with
    ⟨hWt, hMtLower⟩
  have hboundPositive : 0 < cfg.beta ^ t * (m0 + 1) - 1 := by
    linarith [hdelay t le_rfl]
  exact ⟨hWt, lt_of_lt_of_le hboundPositive hMtLower⟩

/- The sign-symmetric restarted estimate controls a return leg.  Starting
   from momentum at most `-m0`, the generated phase advances by the constant
   step while the momentum remains negative, and the exact recurrence gives
   the displayed geometric upper bound using only `cos x ≤ 1`. -/
theorem theorem_4_15_periodicCandidate_negative_momentum_delay_upper_bound_from_index
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta m0 : ℝ)
    (start t : ℕ)
    (hMstart :
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg start).M 0 0 ≤ -m0)
    (heta : ∀ k < t, cfg.eta (start + k) = eta)
    (hdelay : ∀ k < t, 1 < cfg.beta ^ k * (m0 + 1)) :
    theorem_4_5_counterexampleEntry
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg (start + t)).W =
        theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg start).W +
          (t : ℝ) * eta ∧
      (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg (start + t)).M 0 0 ≤
        1 - cfg.beta ^ t * (m0 + 1) := by
  induction t with
  | zero =>
      constructor
      · simp
      · simpa using hMstart
  | succ t ih =>
      have hetaPrefix : ∀ k < t, cfg.eta (start + k) = eta := by
        intro k hk
        exact heta k (lt_trans hk (Nat.lt_succ_self t))
      have hdelayPrefix : ∀ k < t,
          1 < cfg.beta ^ k * (m0 + 1) := by
        intro k hk
        exact hdelay k (lt_trans hk (Nat.lt_succ_self t))
      rcases ih hetaPrefix hdelayPrefix with ⟨hWt, hMtUpper⟩
      have hboundNegative : 1 - cfg.beta ^ t * (m0 + 1) < 0 := by
        linarith [hdelay t (Nat.lt_succ_self t)]
      have hMtNegative :
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg (start + t)).M 0 0 < 0 :=
        lt_of_le_of_lt hMtUpper hboundNegative
      have hrecurrence :=
        theorem_4_15_periodicCandidate_full_orbit_scalar_recurrence
          cfg (start + t)
      have hWsucc :
          theorem_4_5_counterexampleEntry
              (deterministicMomentumMuonState
                theorem_4_15_periodicCandidateObjective cfg
                  (start + (t + 1))).W =
            theorem_4_5_counterexampleEntry
              (deterministicMomentumMuonState
                theorem_4_15_periodicCandidateObjective cfg (start + t)).W +
              eta := by
        rw [show start + (t + 1) = (start + t) + 1 by omega]
        rw [hrecurrence.1, Real.sign_of_neg hMtNegative,
          heta t (Nat.lt_succ_self t)]
        ring
      have hscaledUpper :=
        mul_le_mul_of_nonneg_left hMtUpper cfg.beta_mem.1
      have hcosUpper := mul_le_mul_of_nonneg_left
        (Real.cos_le_one
          (theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg
                (start + (t + 1))).W))
        (sub_nonneg.mpr cfg.beta_mem.2.le)
      constructor
      · rw [hWsucc, hWt]
        push_cast
        ring
      · rw [show start + (t + 1) = (start + t) + 1 by omega,
          hrecurrence.2, pow_succ]
        have hcosUpper' := hcosUpper
        rw [show start + (t + 1) = (start + t) + 1 by omega] at hcosUpper'
        linarith

theorem theorem_4_15_periodicCandidate_negative_momentum_delay_from_index_of_time_budget
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta m0 : ℝ)
    (start t : ℕ)
    (hm0 : 0 < m0)
    (hMstart :
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg start).M 0 0 ≤ -m0)
    (heta : ∀ k < t, cfg.eta (start + k) = eta)
    (htimeBudget :
      (t : ℝ) * (1 - cfg.beta) * (m0 + 1) < m0) :
    theorem_4_5_counterexampleEntry
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg (start + t)).W =
        theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg start).W +
          (t : ℝ) * eta ∧
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + t)).M 0 0 < 0 := by
  have hcoefficient : 0 < m0 + 1 := by linarith
  have hdelay : ∀ k ≤ t, 1 < cfg.beta ^ k * (m0 + 1) := by
    intro k hk
    have hkReal : (k : ℝ) ≤ (t : ℝ) := by exact_mod_cast hk
    have hkScaled :
        (k : ℝ) * (1 - cfg.beta) ≤ (t : ℝ) * (1 - cfg.beta) :=
      mul_le_mul_of_nonneg_right hkReal (sub_nonneg.mpr cfg.beta_mem.2.le)
    have hkBudget :
        (k : ℝ) * (1 - cfg.beta) * (m0 + 1) < m0 := by
      exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_right hkScaled hcoefficient.le) htimeBudget
    have hbern : 1 + (k : ℝ) * (cfg.beta - 1) ≤ cfg.beta ^ k := by
      exact one_add_mul_sub_le_pow (a := cfg.beta)
        (by linarith [cfg.beta_mem.1]) k
    have hbernScaled :=
      mul_le_mul_of_nonneg_right hbern hcoefficient.le
    have hlinear :
        1 < (1 + (k : ℝ) * (cfg.beta - 1)) * (m0 + 1) := by
      nlinarith
    exact lt_of_lt_of_le hlinear hbernScaled
  rcases
      theorem_4_15_periodicCandidate_negative_momentum_delay_upper_bound_from_index
        cfg eta m0 start t hMstart heta
          (fun k hk => hdelay k (Nat.le_of_lt hk)) with
    ⟨hWt, hMtUpper⟩
  have hboundNegative : 1 - cfg.beta ^ t * (m0 + 1) < 0 := by
    linarith [hdelay t le_rfl]
  exact ⟨hWt, lt_of_le_of_lt hMtUpper hboundNegative⟩

/- This is the first genuinely momentum-delayed leg of the shrinking-step
   candidate.  The phase has crossed past `-pi/2`, so the true cosine gradient
   is strictly negative, while the generated momentum (and therefore its exact
   polar direction) is still strictly positive.  The hypotheses are expressed
   by the quantitative geometric lower bound proved above, not by assuming a
   gradient or direction sign. -/
theorem theorem_4_15_periodicCandidate_negative_gradient_during_momentum_delay
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta : ℝ) (t : ℕ)
    (hW0 : cfg.W0 = (Real.pi / 4) • coordinateMatrix 0 0)
    (heta : ∀ k < t, cfg.eta k = eta)
    (htimeBudget :
      (t : ℝ) * (1 - cfg.beta) * (Real.sqrt 2 / 2 + 1) <
        Real.sqrt 2 / 2)
    (htravelLower : 3 * Real.pi / 4 < (t : ℝ) * eta)
    (htravelUpper : (t : ℝ) * eta < 7 * Real.pi / 4) :
    0 < (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg t).M 0 0 ∧
      Real.cos (theorem_4_5_counterexampleEntry
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg t).W) < 0 := by
  rcases theorem_4_15_periodicCandidate_positive_momentum_delay_of_time_budget
      cfg eta t hW0 heta htimeBudget with ⟨hWt, hMtPositive⟩
  constructor
  · exact hMtPositive
  · have hentry :
        theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg t).W =
          Real.pi / 4 - (t : ℝ) * eta := by
      rw [hWt]
      simp [theorem_4_5_counterexampleEntry_apply, coordinateMatrix]
    rw [hentry]
    rw [← Real.cos_neg]
    apply Real.cos_neg_of_pi_div_two_lt_of_lt <;> linarith

/- A central subinterval of the delayed leg has not merely a negative true
   gradient but a uniform, strictly positive nuclear-gradient norm.  The
   constant below is deliberately obtained from the global one-Lipschitz
   estimate for cosine around phase `-pi`; this avoids importing any
   unproved periodic-orbit monotonicity.  The state and momentum conclusions
   still come from the exact generated recurrence. -/
theorem theorem_4_15_periodicCandidate_gradient_lower_bound_during_momentum_delay
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta : ℝ) (t : ℕ)
    (hW0 : cfg.W0 = (Real.pi / 4) • coordinateMatrix 0 0)
    (heta : ∀ k < t, cfg.eta k = eta)
    (htimeBudget :
      (t : ℝ) * (1 - cfg.beta) * (Real.sqrt 2 / 2 + 1) <
        Real.sqrt 2 / 2)
    (htravelLower : 9 * Real.pi / 8 ≤ (t : ℝ) * eta)
    (htravelUpper : (t : ℝ) * eta ≤ 11 * Real.pi / 8) :
    0 < (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg t).M 0 0 ∧
      (1 : ℝ) / 2 ≤
        nuclearNorm (theorem_4_15_periodicCandidateObjective.grad
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg t).W) := by
  rcases theorem_4_15_periodicCandidate_positive_momentum_delay_of_time_budget
      cfg eta t hW0 heta htimeBudget with ⟨hWt, hMtPositive⟩
  refine ⟨hMtPositive, ?_⟩
  rw [theorem_4_15_periodicCandidate_generatedNuclearGradient_eq_abs_cos]
  have hentry :
      theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg t).W =
        Real.pi / 4 - (t : ℝ) * eta := by
    rw [hWt]
    simp [theorem_4_5_counterexampleEntry_apply, coordinateMatrix]
  rw [hentry]
  have hphaseDistance :
      |(Real.pi / 4 - (t : ℝ) * eta) - (-Real.pi)| ≤
        Real.pi / 8 := by
    rw [abs_le]
    constructor <;> linarith [Real.pi_pos]
  have hcosDistance := Real.abs_cos_sub_cos_le
    (-Real.pi) (Real.pi / 4 - (t : ℝ) * eta)
  have habsDistance := abs_sub_abs_le_abs_sub
    (Real.cos (-Real.pi))
    (Real.cos (Real.pi / 4 - (t : ℝ) * eta))
  have habsBound :
      1 - |Real.cos (Real.pi / 4 - (t : ℝ) * eta)| ≤
        Real.pi / 8 := by
    calc
      1 - |Real.cos (Real.pi / 4 - (t : ℝ) * eta)| =
          |Real.cos (-Real.pi)| -
            |Real.cos (Real.pi / 4 - (t : ℝ) * eta)| := by simp
      _ ≤ |Real.cos (-Real.pi) -
          Real.cos (Real.pi / 4 - (t : ℝ) * eta)| := habsDistance
      _ ≤ |(-Real.pi) - (Real.pi / 4 - (t : ℝ) * eta)| :=
        hcosDistance
      _ = |(Real.pi / 4 - (t : ℝ) * eta) - (-Real.pi)| :=
        abs_sub_comm _ _
      _ ≤ Real.pi / 8 := hphaseDistance
  linarith [Real.pi_le_four]

/- The same uniform gradient lower bound is restartable at an arbitrary
   generated index.  The only seed is a quantitative momentum bound already
   established on the exact orbit.  The phase window is allowed around any
   integer multiple of `pi`, so later oscillations can reuse the result without
   pretending that each leg starts from the original `W0`. -/
theorem theorem_4_15_periodicCandidate_gradient_lower_bound_from_index
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta m0 : ℝ)
    (start t : ℕ) (z : ℤ)
    (hm0 : 0 < m0)
    (hMstart : m0 ≤
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg start).M 0 0)
    (heta : ∀ k < t, cfg.eta (start + k) = eta)
    (htimeBudget :
      (t : ℝ) * (1 - cfg.beta) * (m0 + 1) < m0)
    (hphaseDistance :
      |(theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg start).W -
          (t : ℝ) * eta) - (z : ℝ) * Real.pi| ≤ Real.pi / 8) :
    0 < (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + t)).M 0 0 ∧
      (1 : ℝ) / 2 ≤
        nuclearNorm (theorem_4_15_periodicCandidateObjective.grad
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg (start + t)).W) := by
  rcases
      theorem_4_15_periodicCandidate_positive_momentum_delay_from_index_of_time_budget
        cfg eta m0 start t hm0 hMstart heta htimeBudget with
    ⟨hWt, hMtPositive⟩
  refine ⟨hMtPositive, ?_⟩
  rw [theorem_4_15_periodicCandidate_generatedNuclearGradient_eq_abs_cos,
    hWt]
  have hcosDistance := Real.abs_cos_sub_cos_le
    ((z : ℝ) * Real.pi)
    (theorem_4_5_counterexampleEntry
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg start).W -
      (t : ℝ) * eta)
  have habsDistance := abs_sub_abs_le_abs_sub
    (Real.cos ((z : ℝ) * Real.pi))
    (Real.cos
      (theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg start).W -
        (t : ℝ) * eta))
  have habsBound :
      1 - |Real.cos
          (theorem_4_5_counterexampleEntry
              (deterministicMomentumMuonState
                theorem_4_15_periodicCandidateObjective cfg start).W -
            (t : ℝ) * eta)| ≤ Real.pi / 8 := by
    calc
      1 - |Real.cos
          (theorem_4_5_counterexampleEntry
              (deterministicMomentumMuonState
                theorem_4_15_periodicCandidateObjective cfg start).W -
            (t : ℝ) * eta)| =
          |Real.cos ((z : ℝ) * Real.pi)| -
            |Real.cos
              (theorem_4_5_counterexampleEntry
                  (deterministicMomentumMuonState
                    theorem_4_15_periodicCandidateObjective cfg start).W -
                (t : ℝ) * eta)| := by
            rw [Real.abs_cos_int_mul_pi]
      _ ≤ |Real.cos ((z : ℝ) * Real.pi) -
          Real.cos
            (theorem_4_5_counterexampleEntry
                (deterministicMomentumMuonState
                  theorem_4_15_periodicCandidateObjective cfg start).W -
              (t : ℝ) * eta)| := habsDistance
      _ ≤ |((z : ℝ) * Real.pi) -
          (theorem_4_5_counterexampleEntry
              (deterministicMomentumMuonState
                theorem_4_15_periodicCandidateObjective cfg start).W -
            (t : ℝ) * eta)| := hcosDistance
      _ = |(theorem_4_5_counterexampleEntry
              (deterministicMomentumMuonState
                theorem_4_15_periodicCandidateObjective cfg start).W -
            (t : ℝ) * eta) - (z : ℝ) * Real.pi| := abs_sub_comm _ _
      _ ≤ Real.pi / 8 := hphaseDistance
  linarith [Real.pi_le_four]

/- The return-leg analogue uses the proved negative-momentum recurrence.  It
   provides the same phase-local gradient lower bound while the exact generated
   direction moves forward, and therefore supports alternating restarted legs. -/
theorem theorem_4_15_periodicCandidate_gradient_lower_bound_from_index_negative
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta m0 : ℝ)
    (start t : ℕ) (z : ℤ)
    (hm0 : 0 < m0)
    (hMstart :
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg start).M 0 0 ≤ -m0)
    (heta : ∀ k < t, cfg.eta (start + k) = eta)
    (htimeBudget :
      (t : ℝ) * (1 - cfg.beta) * (m0 + 1) < m0)
    (hphaseDistance :
      |(theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg start).W +
          (t : ℝ) * eta) - (z : ℝ) * Real.pi| ≤ Real.pi / 8) :
    (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + t)).M 0 0 < 0 ∧
      (1 : ℝ) / 2 ≤
        nuclearNorm (theorem_4_15_periodicCandidateObjective.grad
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg (start + t)).W) := by
  rcases
      theorem_4_15_periodicCandidate_negative_momentum_delay_from_index_of_time_budget
        cfg eta m0 start t hm0 hMstart heta htimeBudget with
    ⟨hWt, hMtNegative⟩
  refine ⟨hMtNegative, ?_⟩
  rw [theorem_4_15_periodicCandidate_generatedNuclearGradient_eq_abs_cos,
    hWt]
  have hcosDistance := Real.abs_cos_sub_cos_le
    ((z : ℝ) * Real.pi)
    (theorem_4_5_counterexampleEntry
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg start).W +
      (t : ℝ) * eta)
  have habsDistance := abs_sub_abs_le_abs_sub
    (Real.cos ((z : ℝ) * Real.pi))
    (Real.cos
      (theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg start).W +
        (t : ℝ) * eta))
  have habsBound :
      1 - |Real.cos
          (theorem_4_5_counterexampleEntry
              (deterministicMomentumMuonState
                theorem_4_15_periodicCandidateObjective cfg start).W +
            (t : ℝ) * eta)| ≤ Real.pi / 8 := by
    calc
      1 - |Real.cos
          (theorem_4_5_counterexampleEntry
              (deterministicMomentumMuonState
                theorem_4_15_periodicCandidateObjective cfg start).W +
            (t : ℝ) * eta)| =
          |Real.cos ((z : ℝ) * Real.pi)| -
            |Real.cos
              (theorem_4_5_counterexampleEntry
                  (deterministicMomentumMuonState
                    theorem_4_15_periodicCandidateObjective cfg start).W +
                (t : ℝ) * eta)| := by
            rw [Real.abs_cos_int_mul_pi]
      _ ≤ |Real.cos ((z : ℝ) * Real.pi) -
          Real.cos
            (theorem_4_5_counterexampleEntry
                (deterministicMomentumMuonState
                  theorem_4_15_periodicCandidateObjective cfg start).W +
              (t : ℝ) * eta)| := habsDistance
      _ ≤ |((z : ℝ) * Real.pi) -
          (theorem_4_5_counterexampleEntry
              (deterministicMomentumMuonState
                theorem_4_15_periodicCandidateObjective cfg start).W +
            (t : ℝ) * eta)| := hcosDistance
      _ = |(theorem_4_5_counterexampleEntry
              (deterministicMomentumMuonState
                theorem_4_15_periodicCandidateObjective cfg start).W +
            (t : ℝ) * eta) - (z : ℝ) * Real.pi| := abs_sub_comm _ _
      _ ≤ Real.pi / 8 := hphaseDistance
  linarith [Real.pi_le_four]

/- The pointwise delayed-leg estimate lifts to a finite-index density bound on
   the complete generated average.  A future schedule instantiation therefore
   only has to count indices in the displayed window; it no longer has to
   reprove any state, momentum, or gradient facts at those indices. -/
theorem theorem_4_15_periodicCandidate_delayed_window_density_lower_bound
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta : ℝ) (T : ℕ)
    (S : Finset ℕ) (hT : horizonDomain T)
    (hW0 : cfg.W0 = (Real.pi / 4) • coordinateMatrix 0 0)
    (heta : ∀ k < T, cfg.eta k = eta)
    (hwindow : ∀ t ∈ S,
      t < T ∧
        (t : ℝ) * (1 - cfg.beta) * (Real.sqrt 2 / 2 + 1) <
          Real.sqrt 2 / 2 ∧
        9 * Real.pi / 8 ≤ (t : ℝ) * eta ∧
        (t : ℝ) * eta ≤ 11 * Real.pi / 8) :
    ((T : ℝ)⁻¹) * (S.card : ℝ) * ((1 : ℝ) / 2) ≤
      deterministicMomentumAverageNuclearGradient
        theorem_4_15_periodicCandidateObjective cfg T := by
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hsubset : S ⊆ Finset.range T := by
    intro t ht
    exact Finset.mem_range.mpr (hwindow t ht).1
  have hpoint : ∀ t ∈ S,
      (1 : ℝ) / 2 ≤
        |Real.cos (theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg t).W)| := by
    intro t ht
    rcases hwindow t ht with ⟨htT, hbudget, hlower, hupper⟩
    have hgradient :=
      (theorem_4_15_periodicCandidate_gradient_lower_bound_during_momentum_delay
        cfg eta t hW0 (fun k hk => heta k (lt_trans hk htT))
        hbudget hlower hupper).2
    simpa [theorem_4_15_periodicCandidate_generatedNuclearGradient_eq_abs_cos]
      using hgradient
  have hsumS : (S.card : ℝ) * ((1 : ℝ) / 2) ≤
      Finset.sum S (fun t =>
        |Real.cos (theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg t).W)|) := by
    calc
      (S.card : ℝ) * ((1 : ℝ) / 2) =
          Finset.sum S (fun _ => (1 : ℝ) / 2) := by simp
      _ ≤ Finset.sum S (fun t =>
          |Real.cos (theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg t).W)|) :=
        Finset.sum_le_sum hpoint
  have hsumSubset :
      Finset.sum S (fun t =>
          |Real.cos (theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg t).W)|) ≤
        Finset.sum (Finset.range T) (fun t =>
          |Real.cos (theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg t).W)|) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => abs_nonneg _)
  rw [(theorem_4_15_periodicCandidate_fullHorizon_scalar_reduction_with_sign
    cfg T).2]
  calc
    ((T : ℝ)⁻¹) * (S.card : ℝ) * ((1 : ℝ) / 2) =
        ((T : ℝ)⁻¹) * ((S.card : ℝ) * ((1 : ℝ) / 2)) := by ring
    _ ≤ ((T : ℝ)⁻¹) * Finset.sum S (fun t =>
        |Real.cos (theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg t).W)|) :=
      mul_le_mul_of_nonneg_left hsumS (inv_nonneg.mpr hTreal.le)
    _ ≤ ((T : ℝ)⁻¹) * Finset.sum (Finset.range T) (fun t =>
        |Real.cos (theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg t).W)|) :=
      mul_le_mul_of_nonneg_left hsumSubset (inv_nonneg.mpr hTreal.le)

/- A counted family of restartable delayed windows gives a lower bound on the
   complete generated average.  Each absolute index in `S` is reduced to its
   elapsed time after `start`; the momentum seed is used once and propagated by
   the exact recurrence, so no fresh seed is assumed at individual indices. -/
theorem theorem_4_15_periodicCandidate_restarted_window_density_lower_bound
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta m0 : ℝ)
    (start T : ℕ) (S : Finset ℕ) (hT : horizonDomain T)
    (hm0 : 0 < m0)
    (hMstart : m0 ≤
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg start).M 0 0)
    (heta : ∀ k, start + k < T → cfg.eta (start + k) = eta)
    (hwindow : ∀ t ∈ S,
      start ≤ t ∧ t < T ∧
        ((t - start : ℕ) : ℝ) * (1 - cfg.beta) * (m0 + 1) < m0 ∧
        ∃ z : ℤ,
          |(theorem_4_5_counterexampleEntry
              (deterministicMomentumMuonState
                theorem_4_15_periodicCandidateObjective cfg start).W -
              ((t - start : ℕ) : ℝ) * eta) - (z : ℝ) * Real.pi| ≤
            Real.pi / 8) :
    ((T : ℝ)⁻¹) * (S.card : ℝ) * ((1 : ℝ) / 2) ≤
      deterministicMomentumAverageNuclearGradient
        theorem_4_15_periodicCandidateObjective cfg T := by
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hsubset : S ⊆ Finset.range T := by
    intro t ht
    exact Finset.mem_range.mpr (hwindow t ht).2.1
  have hpoint : ∀ t ∈ S,
      (1 : ℝ) / 2 ≤
        |Real.cos (theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg t).W)| := by
    intro t ht
    rcases hwindow t ht with ⟨hstart, htT, hbudget, z, hphase⟩
    have hadd : start + (t - start) = t := Nat.add_sub_of_le hstart
    have hetaElapsed : ∀ k < t - start, cfg.eta (start + k) = eta := by
      intro k hk
      apply heta k
      have hkt : start + k < t := by
        rw [← hadd]
        exact Nat.add_lt_add_left hk start
      exact lt_trans hkt htT
    have hgradient :=
      (theorem_4_15_periodicCandidate_gradient_lower_bound_from_index
        cfg eta m0 start (t - start) z hm0 hMstart hetaElapsed
          hbudget hphase).2
    rw [hadd] at hgradient
    simpa [theorem_4_15_periodicCandidate_generatedNuclearGradient_eq_abs_cos]
      using hgradient
  have hsumS : (S.card : ℝ) * ((1 : ℝ) / 2) ≤
      Finset.sum S (fun t =>
        |Real.cos (theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg t).W)|) := by
    calc
      (S.card : ℝ) * ((1 : ℝ) / 2) =
          Finset.sum S (fun _ => (1 : ℝ) / 2) := by simp
      _ ≤ Finset.sum S (fun t =>
          |Real.cos (theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg t).W)|) :=
        Finset.sum_le_sum hpoint
  have hsumSubset :
      Finset.sum S (fun t =>
          |Real.cos (theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg t).W)|) ≤
        Finset.sum (Finset.range T) (fun t =>
          |Real.cos (theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg t).W)|) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => abs_nonneg _)
  rw [(theorem_4_15_periodicCandidate_fullHorizon_scalar_reduction_with_sign
    cfg T).2]
  calc
    ((T : ℝ)⁻¹) * (S.card : ℝ) * ((1 : ℝ) / 2) =
        ((T : ℝ)⁻¹) * ((S.card : ℝ) * ((1 : ℝ) / 2)) := by ring
    _ ≤ ((T : ℝ)⁻¹) * Finset.sum S (fun t =>
        |Real.cos (theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg t).W)|) :=
      mul_le_mul_of_nonneg_left hsumS (inv_nonneg.mpr hTreal.le)
    _ ≤ ((T : ℝ)⁻¹) * Finset.sum (Finset.range T) (fun t =>
        |Real.cos (theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg t).W)|) :=
      mul_le_mul_of_nonneg_left hsumSubset (inv_nonneg.mpr hTreal.le)

/- The corresponding return-leg density theorem has the same conclusion.  Its
   hypotheses differ only in the sign of the proved seed and in the forward
   affine phase furnished by the negative-momentum generated recurrence. -/
theorem theorem_4_15_periodicCandidate_restarted_negative_window_density_lower_bound
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta m0 : ℝ)
    (start T : ℕ) (S : Finset ℕ) (hT : horizonDomain T)
    (hm0 : 0 < m0)
    (hMstart :
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg start).M 0 0 ≤ -m0)
    (heta : ∀ k, start + k < T → cfg.eta (start + k) = eta)
    (hwindow : ∀ t ∈ S,
      start ≤ t ∧ t < T ∧
        ((t - start : ℕ) : ℝ) * (1 - cfg.beta) * (m0 + 1) < m0 ∧
        ∃ z : ℤ,
          |(theorem_4_5_counterexampleEntry
              (deterministicMomentumMuonState
                theorem_4_15_periodicCandidateObjective cfg start).W +
              ((t - start : ℕ) : ℝ) * eta) - (z : ℝ) * Real.pi| ≤
            Real.pi / 8) :
    ((T : ℝ)⁻¹) * (S.card : ℝ) * ((1 : ℝ) / 2) ≤
      deterministicMomentumAverageNuclearGradient
        theorem_4_15_periodicCandidateObjective cfg T := by
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hsubset : S ⊆ Finset.range T := by
    intro t ht
    exact Finset.mem_range.mpr (hwindow t ht).2.1
  have hpoint : ∀ t ∈ S,
      (1 : ℝ) / 2 ≤
        |Real.cos (theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg t).W)| := by
    intro t ht
    rcases hwindow t ht with ⟨hstart, htT, hbudget, z, hphase⟩
    have hadd : start + (t - start) = t := Nat.add_sub_of_le hstart
    have hetaElapsed : ∀ k < t - start, cfg.eta (start + k) = eta := by
      intro k hk
      apply heta k
      have hkt : start + k < t := by
        rw [← hadd]
        exact Nat.add_lt_add_left hk start
      exact lt_trans hkt htT
    have hgradient :=
      (theorem_4_15_periodicCandidate_gradient_lower_bound_from_index_negative
        cfg eta m0 start (t - start) z hm0 hMstart hetaElapsed
          hbudget hphase).2
    rw [hadd] at hgradient
    simpa [theorem_4_15_periodicCandidate_generatedNuclearGradient_eq_abs_cos]
      using hgradient
  have hsumS : (S.card : ℝ) * ((1 : ℝ) / 2) ≤
      Finset.sum S (fun t =>
        |Real.cos (theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg t).W)|) := by
    calc
      (S.card : ℝ) * ((1 : ℝ) / 2) =
          Finset.sum S (fun _ => (1 : ℝ) / 2) := by simp
      _ ≤ Finset.sum S (fun t =>
          |Real.cos (theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg t).W)|) :=
        Finset.sum_le_sum hpoint
  have hsumSubset :
      Finset.sum S (fun t =>
          |Real.cos (theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg t).W)|) ≤
        Finset.sum (Finset.range T) (fun t =>
          |Real.cos (theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg t).W)|) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => abs_nonneg _)
  rw [(theorem_4_15_periodicCandidate_fullHorizon_scalar_reduction_with_sign
    cfg T).2]
  calc
    ((T : ℝ)⁻¹) * (S.card : ℝ) * ((1 : ℝ) / 2) =
        ((T : ℝ)⁻¹) * ((S.card : ℝ) * ((1 : ℝ) / 2)) := by ring
    _ ≤ ((T : ℝ)⁻¹) * Finset.sum S (fun t =>
        |Real.cos (theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg t).W)|) :=
      mul_le_mul_of_nonneg_left hsumS (inv_nonneg.mpr hTreal.le)
    _ ≤ ((T : ℝ)⁻¹) * Finset.sum (Finset.range T) (fun t =>
        |Real.cos (theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg t).W)|) :=
      mul_le_mul_of_nonneg_left hsumSubset (inv_nonneg.mpr hTreal.le)

/- A horizon-wide restart certificate records, for one absolute generated
   index, either a positive- or negative-momentum leg beginning at an earlier
   generated state.  The seed, elapsed-time budget, and phase window all refer
   to the same exact orbit.  In particular, the definition does not restart
   Algorithm 1, assume a fresh momentum, or mention the desired average. -/
def theorem_4_15_periodicCandidateRestartCertificate
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta : ℝ) (t : ℕ) : Prop :=
  (∃ start : ℕ, ∃ m0 : ℝ, ∃ z : ℤ,
      start ≤ t ∧ 0 < m0 ∧
      m0 ≤ (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg start).M 0 0 ∧
      (∀ k < t - start, cfg.eta (start + k) = eta) ∧
      ((t - start : ℕ) : ℝ) * (1 - cfg.beta) * (m0 + 1) < m0 ∧
      |(theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg start).W -
          ((t - start : ℕ) : ℝ) * eta) - (z : ℝ) * Real.pi| ≤
        Real.pi / 8) ∨
  (∃ start : ℕ, ∃ m0 : ℝ, ∃ z : ℤ,
      start ≤ t ∧ 0 < m0 ∧
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg start).M 0 0 ≤ -m0 ∧
      (∀ k < t - start, cfg.eta (start + k) = eta) ∧
      ((t - start : ℕ) : ℝ) * (1 - cfg.beta) * (m0 + 1) < m0 ∧
      |(theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg start).W +
          ((t - start : ℕ) : ℝ) * eta) - (z : ℝ) * Real.pi| ≤
        Real.pi / 8)

/- A phase hit already carries a restart certificate when the generated
   momentum at that same index is positive.  Taking `start = t` is legitimate:
   the elapsed schedule and time-budget obligations are empty, while the seed
   and phase facts remain facts about the one generated orbit. -/
theorem theorem_4_15_periodicCandidate_restartCertificate_of_positive_momentum
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta : ℝ) (t : ℕ) (z : ℤ)
    (hM : 0 < (deterministicMomentumMuonState
      theorem_4_15_periodicCandidateObjective cfg t).M 0 0)
    (hphase :
      |theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg t).W -
        (z : ℝ) * Real.pi| ≤ Real.pi / 8) :
    theorem_4_15_periodicCandidateRestartCertificate cfg eta t := by
  left
  refine ⟨t,
    (deterministicMomentumMuonState
      theorem_4_15_periodicCandidateObjective cfg t).M 0 0,
    z, le_rfl, hM, le_rfl, ?_, ?_, ?_⟩
  · intro k hk
    omega
  · simpa using hM
  · simpa using hphase

/- The sign-symmetric zero-length restart constructor. -/
theorem theorem_4_15_periodicCandidate_restartCertificate_of_negative_momentum
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta : ℝ) (t : ℕ) (z : ℤ)
    (hM : (deterministicMomentumMuonState
      theorem_4_15_periodicCandidateObjective cfg t).M 0 0 < 0)
    (hphase :
      |theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg t).W -
        (z : ℝ) * Real.pi| ≤ Real.pi / 8) :
    theorem_4_15_periodicCandidateRestartCertificate cfg eta t := by
  right
  refine ⟨t,
    -(deterministicMomentumMuonState
      theorem_4_15_periodicCandidateObjective cfg t).M 0 0,
    z, le_rfl, neg_pos.mpr hM, ?_, ?_, ?_, ?_⟩
  · rw [neg_neg]
  · intro k hk
    omega
  · simpa using (neg_pos.mpr hM)
  · simpa using hphase

/- Proximity to an integer multiple of `pi` makes the cosine magnitude at
   least `1/2`.  This is the quantitative fact that prevents a zero-momentum
   phase hit from remaining at zero after the exact Algorithm 1 update. -/
theorem theorem_4_15_periodicCandidate_abs_cos_ge_half_of_phase_near_int_mul_pi
    (x : ℝ) (z : ℤ)
    (hphase : |x - (z : ℝ) * Real.pi| ≤ Real.pi / 8) :
    (1 : ℝ) / 2 ≤ |Real.cos x| := by
  have hcosDistance := Real.abs_cos_sub_cos_le ((z : ℝ) * Real.pi) x
  have habsDistance := abs_sub_abs_le_abs_sub
    (Real.cos ((z : ℝ) * Real.pi)) (Real.cos x)
  have habsBound : 1 - |Real.cos x| ≤ Real.pi / 8 := by
    calc
      1 - |Real.cos x| =
          |Real.cos ((z : ℝ) * Real.pi)| - |Real.cos x| := by
            rw [Real.abs_cos_int_mul_pi]
      _ ≤ |Real.cos ((z : ℝ) * Real.pi) - Real.cos x| := habsDistance
      _ ≤ |((z : ℝ) * Real.pi) - x| := hcosDistance
      _ = |x - (z : ℝ) * Real.pi| := abs_sub_comm _ _
      _ ≤ Real.pi / 8 := hphase
  linarith [Real.pi_le_four]

/- A fixed-sign generated leg now contributes `ell + 1` high-gradient
   iterates, not merely one restart certificate.  The set consists of elapsed
   indices on the same exact orbit, and its cardinality is independent of any
   witness-selection or restart convention.  Instantiating `ell` at order
   `1 / eta` is the quantitative step needed to keep a positive fraction under
   the shrinking Appendix B.4 mesh. -/
theorem theorem_4_15_periodicCandidate_signed_leg_dense_gradient_window
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta : ℝ)
    (start t ell : ℕ) (hetaPos : 0 < eta)
    (hroom : 2 * ell ≤ t)
    (hwidth : ((ell + 1 : ℕ) : ℝ) * eta ≤ Real.pi / 8)
    (heta : ∀ k < t, cfg.eta (start + k) = eta)
    (hsign :
      (∀ k < t, 0 <
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg (start + k)).M 0 0) ∨
      (∀ k < t,
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg (start + k)).M 0 0 < 0))
    (htravel : Real.pi ≤ (t : ℝ) * eta) :
    ∃ S : Finset ℕ, S.card = ell + 1 ∧
      ∀ j ∈ S, j ≤ t ∧
        (1 : ℝ) / 2 ≤
          nuclearNorm (theorem_4_15_periodicCandidateObjective.grad
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg (start + j)).W) := by
  let x := theorem_4_5_counterexampleEntry
    (deterministicMomentumMuonState
      theorem_4_15_periodicCandidateObjective cfg start).W
  rcases hsign with hpositive | hnegative
  · rcases theorem_4_15_periodicCandidate_descending_grid_dense_phase_window
        x eta t ell hetaPos hroom hwidth htravel with ⟨S, hcard, hS⟩
    refine ⟨S, hcard, ?_⟩
    intro j hj
    rcases hS j hj with ⟨hjt, z, hphase⟩
    have hetaPrefix : ∀ k < j, cfg.eta (start + k) = eta := by
      intro k hk
      exact heta k (lt_of_lt_of_le hk hjt)
    have hpositivePrefix : ∀ k < j, 0 <
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg (start + k)).M 0 0 := by
      intro k hk
      exact hpositive k (lt_of_lt_of_le hk hjt)
    have hphaseGenerated :
        |theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg (start + j)).W -
          (z : ℝ) * Real.pi| ≤ Real.pi / 8 := by
      rw [theorem_4_15_periodicCandidate_phase_after_positive_momentum_block
        cfg eta start j hetaPrefix hpositivePrefix]
      exact hphase
    refine ⟨hjt, ?_⟩
    rw [theorem_4_15_periodicCandidate_generatedNuclearGradient_eq_abs_cos]
    exact theorem_4_15_periodicCandidate_abs_cos_ge_half_of_phase_near_int_mul_pi
      _ z hphaseGenerated
  · rcases theorem_4_15_periodicCandidate_ascending_grid_dense_phase_window
        x eta t ell hetaPos hroom hwidth htravel with ⟨S, hcard, hS⟩
    refine ⟨S, hcard, ?_⟩
    intro j hj
    rcases hS j hj with ⟨hjt, z, hphase⟩
    have hetaPrefix : ∀ k < j, cfg.eta (start + k) = eta := by
      intro k hk
      exact heta k (lt_of_lt_of_le hk hjt)
    have hnegativePrefix : ∀ k < j,
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg (start + k)).M 0 0 < 0 := by
      intro k hk
      exact hnegative k (lt_of_lt_of_le hk hjt)
    have hphaseGenerated :
        |theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg (start + j)).W -
          (z : ℝ) * Real.pi| ≤ Real.pi / 8 := by
      rw [theorem_4_15_periodicCandidate_phase_after_negative_momentum_block
        cfg eta start j hetaPrefix hnegativePrefix]
      exact hphase
    refine ⟨hjt, ?_⟩
    rw [theorem_4_15_periodicCandidate_generatedNuclearGradient_eq_abs_cos]
    exact theorem_4_15_periodicCandidate_abs_cos_ge_half_of_phase_near_int_mul_pi
      _ z hphaseGenerated

/- The dense elapsed window embeds injectively into the full generated
   horizon.  Consequently one fixed-sign leg contributes the explicit
   `(ell + 1) / (2T)` lower bound on the exact stochastic source average,
   replacing the previous one-point `1 / (2T)` contribution. -/
theorem theorem_4_15_periodicCandidate_signed_leg_stochastic_density_lower_bound
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta sigma : ℝ)
    (start t ell T : ℕ) (hT : horizonDomain T) (hinside : start + t < T)
    (hetaPos : 0 < eta) (hroom : 2 * ell ≤ t)
    (hwidth : ((ell + 1 : ℕ) : ℝ) * eta ≤ Real.pi / 8)
    (heta : ∀ k < t, cfg.eta (start + k) = eta)
    (hsign :
      (∀ k < t, 0 <
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg (start + k)).M 0 0) ∨
      (∀ k < t,
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg (start + k)).M 0 0 < 0))
    (htravel : Real.pi ≤ (t : ℝ) * eta) (hsigma : 0 ≤ sigma) :
    ∃ hwd : stochasticMuonExpectationsWellDefined
        (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
        (deterministicOracleConfig cfg) T,
      stochasticHessianDirectionalAverageRealized
          (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
          (deterministicOracleConfig cfg) T hwd.2.2.1 =
          deterministicMomentumHessianDirectionalAverage
            theorem_4_15_periodicCandidateObjective cfg T ∧
        ((T : ℝ)⁻¹) * ((ell + 1 : ℕ) : ℝ) * ((1 : ℝ) / 2) ≤
          stochasticAverageNuclearGradientRealized
            (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
            (deterministicOracleConfig cfg) T hwd.1 := by
  classical
  rcases theorem_4_15_periodicCandidate_signed_leg_dense_gradient_window
      cfg eta start t ell hetaPos hroom hwidth heta hsign htravel with
    ⟨S, hScard, hS⟩
  let A : Finset ℕ := S.image (fun j => start + j)
  have hAcard : A.card = ell + 1 := by
    calc
      A.card = S.card := by
        dsimp [A]
        apply Finset.card_image_of_injOn
        intro a _ha b _hb hab
        exact Nat.add_left_cancel hab
      _ = ell + 1 := hScard
  have hAsubset : A ⊆ Finset.range T := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨j, hj, rfl⟩
    exact Finset.mem_range.mpr (lt_of_le_of_lt
      (Nat.add_le_add_left (hS j hj).1 start) hinside)
  have hApoint : ∀ u ∈ A, (1 : ℝ) / 2 ≤
      |Real.cos (theorem_4_5_counterexampleEntry
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg u).W)| := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨j, hj, rfl⟩
    simpa [theorem_4_15_periodicCandidate_generatedNuclearGradient_eq_abs_cos]
      using (hS j hj).2
  have hsumA : (A.card : ℝ) * ((1 : ℝ) / 2) ≤
      Finset.sum A (fun u =>
        |Real.cos (theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg u).W)|) := by
    calc
      (A.card : ℝ) * ((1 : ℝ) / 2) =
          Finset.sum A (fun _ => (1 : ℝ) / 2) := by simp
      _ ≤ Finset.sum A (fun u =>
          |Real.cos (theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg u).W)|) :=
        Finset.sum_le_sum hApoint
  have hsumSubset :
      Finset.sum A (fun u =>
          |Real.cos (theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg u).W)|) ≤
        Finset.sum (Finset.range T) (fun u =>
          |Real.cos (theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg u).W)|) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hAsubset
      (fun _ _ _ => abs_nonneg _)
  let hwd := theorem_4_15_periodicCandidate_expectationsWellDefined
    cfg T sigma hsigma
  refine ⟨hwd, ?_, ?_⟩
  · rw [deterministicOracle_hessianDirectionalAverageRealized_eq]
  · rw [deterministicOracle_average_eq,
      (theorem_4_15_periodicCandidate_fullHorizon_scalar_reduction_with_sign
        cfg T).2]
    have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
    calc
      ((T : ℝ)⁻¹) * ((ell + 1 : ℕ) : ℝ) * ((1 : ℝ) / 2) =
          ((T : ℝ)⁻¹) * ((A.card : ℝ) * ((1 : ℝ) / 2)) := by
        rw [hAcard]
        ring
      _ ≤ ((T : ℝ)⁻¹) * Finset.sum A (fun u =>
          |Real.cos (theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg u).W)|) :=
        mul_le_mul_of_nonneg_left hsumA (inv_nonneg.mpr hTreal.le)
      _ ≤ ((T : ℝ)⁻¹) * Finset.sum (Finset.range T) (fun u =>
          |Real.cos (theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg u).W)|) :=
        mul_le_mul_of_nonneg_left hsumSubset (inv_nonneg.mpr hTreal.le)

/- Dense windows from disjoint fixed-sign legs can be counted simultaneously
   on the one generated orbit.  The half-open block separation makes the
   translated windows pairwise disjoint, so the lower bound retains the full
   `q * (ell + 1)` multiplicity rather than selecting one certificate per
   block.  This is the schedule-level aggregation needed after the local
   dense-window theorem; the only orbit premise left explicit is the still
   open fixed-sign supply in each block. -/
theorem theorem_4_15_periodicCandidate_signed_blocks_dense_stochastic_lower_bound
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta sigma : ℝ)
    (q blockLength t ell T : ℕ) (hT : horizonDomain T)
    (hblocks : q * blockLength ≤ T) (htBlock : t < blockLength)
    (hetaPos : 0 < eta) (hroom : 2 * ell ≤ t)
    (hwidth : ((ell + 1 : ℕ) : ℝ) * eta ≤ Real.pi / 8)
    (heta : ∀ k : Fin q, ∀ j < t,
      cfg.eta (k.1 * blockLength + j) = eta)
    (hsign : ∀ k : Fin q,
      (∀ j < t, 0 <
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg
          (k.1 * blockLength + j)).M 0 0) ∨
      (∀ j < t,
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg
          (k.1 * blockLength + j)).M 0 0 < 0))
    (htravel : Real.pi ≤ (t : ℝ) * eta) (hsigma : 0 ≤ sigma) :
    ∃ hwd : stochasticMuonExpectationsWellDefined
        (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
        (deterministicOracleConfig cfg) T,
      stochasticHessianDirectionalAverageRealized
          (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
          (deterministicOracleConfig cfg) T hwd.2.2.1 =
          deterministicMomentumHessianDirectionalAverage
            theorem_4_15_periodicCandidateObjective cfg T ∧
        ((T : ℝ)⁻¹) * ((q * (ell + 1) : ℕ) : ℝ) * ((1 : ℝ) / 2) ≤
          stochasticAverageNuclearGradientRealized
            (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
            (deterministicOracleConfig cfg) T hwd.1 := by
  classical
  have hlocal : ∀ k : Fin q, ∃ S : Finset ℕ, S.card = ell + 1 ∧
      ∀ j ∈ S, j ≤ t ∧
        (1 : ℝ) / 2 ≤
          nuclearNorm (theorem_4_15_periodicCandidateObjective.grad
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg
              (k.1 * blockLength + j)).W) := by
    intro k
    exact theorem_4_15_periodicCandidate_signed_leg_dense_gradient_window
      cfg eta (k.1 * blockLength) t ell hetaPos hroom hwidth
        (heta k) (hsign k) htravel
  let S : Fin q → Finset ℕ := fun k => Classical.choose (hlocal k)
  have hS : ∀ k : Fin q, (S k).card = ell + 1 ∧
      ∀ j ∈ S k, j ≤ t ∧
        (1 : ℝ) / 2 ≤
          nuclearNorm (theorem_4_15_periodicCandidateObjective.grad
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg
              (k.1 * blockLength + j)).W) := by
    intro k
    exact Classical.choose_spec (hlocal k)
  let A : Fin q → Finset ℕ := fun k =>
    (S k).image (fun j => k.1 * blockLength + j)
  have hAcard (k : Fin q) : (A k).card = ell + 1 := by
    calc
      (A k).card = (S k).card := by
        dsimp [A]
        apply Finset.card_image_of_injOn
        intro a _ha b _hb hab
        exact Nat.add_left_cancel hab
      _ = ell + 1 := (hS k).1
  have hAdisjoint :
      ((Finset.univ : Finset (Fin q)) : Set (Fin q)).PairwiseDisjoint A := by
    intro a _ha b _hb hab
    change Disjoint (A a) (A b)
    rw [Finset.disjoint_left]
    intro u hua hub
    rcases Finset.mem_image.mp hua with ⟨ja, hja, huaeq⟩
    rcases Finset.mem_image.mp hub with ⟨jb, hjb, hubeq⟩
    have hjaBound : ja ≤ t := (hS a).2 ja hja |>.1
    have hjbBound : jb ≤ t := (hS b).2 jb hjb |>.1
    have habVal : a.1 ≠ b.1 := by
      intro heq
      exact hab (Fin.ext heq)
    rcases lt_or_gt_of_ne habVal with halt | hblt
    · have hstrict : a.1 * blockLength + ja < b.1 * blockLength + jb := by
        calc
          a.1 * blockLength + ja ≤ a.1 * blockLength + t :=
            Nat.add_le_add_left hjaBound _
          _ < (a.1 + 1) * blockLength := by
            rw [Nat.add_mul, one_mul]
            omega
          _ ≤ b.1 * blockLength := Nat.mul_le_mul_right blockLength halt
          _ ≤ b.1 * blockLength + jb := Nat.le_add_right _ _
      rw [huaeq, hubeq] at hstrict
      exact (Nat.lt_irrefl u) hstrict
    · have hstrict : b.1 * blockLength + jb < a.1 * blockLength + ja := by
        calc
          b.1 * blockLength + jb ≤ b.1 * blockLength + t :=
            Nat.add_le_add_left hjbBound _
          _ < (b.1 + 1) * blockLength := by
            rw [Nat.add_mul, one_mul]
            omega
          _ ≤ a.1 * blockLength := Nat.mul_le_mul_right blockLength hblt
          _ ≤ a.1 * blockLength + ja := Nat.le_add_right _ _
      rw [huaeq, hubeq] at hstrict
      exact (Nat.lt_irrefl u) hstrict
  let U : Finset ℕ := (Finset.univ : Finset (Fin q)).biUnion A
  have hUcard : U.card = q * (ell + 1) := by
    calc
      U.card = ∑ k : Fin q, (A k).card := by
        dsimp [U]
        rw [Finset.card_biUnion hAdisjoint]
      _ = ∑ _k : Fin q, (ell + 1) := by
        apply Finset.sum_congr rfl
        intro k _hk
        exact hAcard k
      _ = q * (ell + 1) := by simp
  have hUsubset : U ⊆ Finset.range T := by
    intro u hu
    rcases Finset.mem_biUnion.mp hu with ⟨k, _hk, huk⟩
    rcases Finset.mem_image.mp huk with ⟨j, hj, rfl⟩
    have hjt : j ≤ t := (hS k).2 j hj |>.1
    apply Finset.mem_range.mpr
    calc
      k.1 * blockLength + j ≤ k.1 * blockLength + t :=
        Nat.add_le_add_left hjt _
      _ < (k.1 + 1) * blockLength := by
        rw [Nat.add_mul, one_mul]
        omega
      _ ≤ q * blockLength := Nat.mul_le_mul_right blockLength k.2
      _ ≤ T := hblocks
  have hUpoint : ∀ u ∈ U, (1 : ℝ) / 2 ≤
      |Real.cos (theorem_4_5_counterexampleEntry
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg u).W)| := by
    intro u hu
    rcases Finset.mem_biUnion.mp hu with ⟨k, _hk, huk⟩
    rcases Finset.mem_image.mp huk with ⟨j, hj, rfl⟩
    simpa [theorem_4_15_periodicCandidate_generatedNuclearGradient_eq_abs_cos]
      using (hS k).2 j hj |>.2
  have hsumU : (U.card : ℝ) * ((1 : ℝ) / 2) ≤
      Finset.sum U (fun u =>
        |Real.cos (theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg u).W)|) := by
    calc
      (U.card : ℝ) * ((1 : ℝ) / 2) =
          Finset.sum U (fun _ => (1 : ℝ) / 2) := by simp
      _ ≤ Finset.sum U (fun u =>
          |Real.cos (theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg u).W)|) :=
        Finset.sum_le_sum hUpoint
  have hsumSubset :
      Finset.sum U (fun u =>
          |Real.cos (theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg u).W)|) ≤
        Finset.sum (Finset.range T) (fun u =>
          |Real.cos (theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg u).W)|) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hUsubset
      (fun _ _ _ => abs_nonneg _)
  let hwd := theorem_4_15_periodicCandidate_expectationsWellDefined
    cfg T sigma hsigma
  refine ⟨hwd, ?_, ?_⟩
  · rw [deterministicOracle_hessianDirectionalAverageRealized_eq]
  · rw [deterministicOracle_average_eq,
      (theorem_4_15_periodicCandidate_fullHorizon_scalar_reduction_with_sign
        cfg T).2]
    have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
    calc
      ((T : ℝ)⁻¹) * ((q * (ell + 1) : ℕ) : ℝ) * ((1 : ℝ) / 2) =
          ((T : ℝ)⁻¹) * ((U.card : ℝ) * ((1 : ℝ) / 2)) := by
        rw [hUcard]
        ring
      _ ≤ ((T : ℝ)⁻¹) * Finset.sum U (fun u =>
          |Real.cos (theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg u).W)|) :=
        mul_le_mul_of_nonneg_left hsumU (inv_nonneg.mpr hTreal.le)
      _ ≤ ((T : ℝ)⁻¹) * Finset.sum (Finset.range T) (fun u =>
          |Real.cos (theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg u).W)|) :=
        mul_le_mul_of_nonneg_left hsumSubset (inv_nonneg.mpr hTreal.le)

/- A maximal packing of blocks whose dense windows occupy at least one
   sixteenth of each block makes the preceding lower bound uniform in the
   horizon.  This is the exact arithmetic bridge needed at the printed
   shrinking scales:
   once orbit dynamics supplies the block hypotheses, no accuracy-dependent
   loss remains in `q * (ell + 1) / T`. -/
theorem theorem_4_15_packed_dense_windows_fraction_lower_bound
    (q blockLength ell T : ℕ) (hT : horizonDomain T) (hq : 0 < q)
    (hmaximal : T < (q + 1) * blockLength)
    (hdense : blockLength ≤ 16 * (ell + 1)) :
    (1 : ℝ) / 64 ≤
      ((T : ℝ)⁻¹) * ((q * (ell + 1) : ℕ) : ℝ) * ((1 : ℝ) / 2) := by
  have hqDouble : q + 1 ≤ 2 * q := by omega
  have hTbound : T < 32 * (q * (ell + 1)) := by
    calc
      T < (q + 1) * blockLength := hmaximal
      _ ≤ (2 * q) * blockLength :=
        Nat.mul_le_mul_right blockLength hqDouble
      _ ≤ (2 * q) * (16 * (ell + 1)) :=
        Nat.mul_le_mul_left (2 * q) hdense
      _ = 32 * (q * (ell + 1)) := by ring
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hTboundReal : (T : ℝ) ≤
      32 * (((q * (ell + 1) : ℕ) : ℝ)) := by
    exact_mod_cast (Nat.le_of_lt hTbound)
  rw [show
    ((T : ℝ)⁻¹) * ((q * (ell + 1) : ℕ) : ℝ) * ((1 : ℝ) / 2) =
      ((((q * (ell + 1) : ℕ) : ℝ)) / 2) / (T : ℝ) by
        field_simp [ne_of_gt hTreal]]
  rw [le_div_iff₀ hTreal]
  nlinarith

/- The maximal block count used above need not be supplied independently.
   Euclidean division of the selected horizon by any positive block length
   produces exactly the two packing inequalities, and a block that fits in
   the horizon makes the resulting count nonzero.  This is the canonical
   schedule instantiation of `q`; it removes an auxiliary choice from the
   shrinking-step counterexample route without making an orbit assumption. -/
theorem theorem_4_15_horizon_div_blockLength_packing
    (blockLength T : ℕ) (hblockPos : 0 < blockLength)
    (hblockFits : blockLength ≤ T) :
    let q := T / blockLength
    0 < q ∧ q * blockLength ≤ T ∧ T < (q + 1) * blockLength := by
  dsimp only
  constructor
  · exact Nat.div_pos hblockFits hblockPos
  constructor
  · exact Nat.div_mul_le_self T blockLength
  · have hdivision := Nat.lt_div_mul_add (a := T) hblockPos
    simpa [Nat.add_mul] using hdivision

/- Consuming the packing arithmetic in the exact generated-orbit theorem
   isolates the remaining counterexample obligations to dynamics and signed
   directional-curvature cancellation.  In particular, the lower bound here
   is independent of `eta`, `beta`, the selected horizon, and accuracy. -/
theorem theorem_4_15_periodicCandidate_signed_blocks_uniform_stochastic_lower_bound
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta sigma : ℝ)
    (q blockLength t ell T : ℕ) (hT : horizonDomain T)
    (hblocks : q * blockLength ≤ T) (htBlock : t < blockLength)
    (hq : 0 < q) (hmaximal : T < (q + 1) * blockLength)
    (hdense : blockLength ≤ 16 * (ell + 1))
    (hetaPos : 0 < eta) (hroom : 2 * ell ≤ t)
    (hwidth : ((ell + 1 : ℕ) : ℝ) * eta ≤ Real.pi / 8)
    (heta : ∀ k : Fin q, ∀ j < t,
      cfg.eta (k.1 * blockLength + j) = eta)
    (hsign : ∀ k : Fin q,
      (∀ j < t, 0 <
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg
          (k.1 * blockLength + j)).M 0 0) ∨
      (∀ j < t,
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg
          (k.1 * blockLength + j)).M 0 0 < 0))
    (htravel : Real.pi ≤ (t : ℝ) * eta) (hsigma : 0 ≤ sigma) :
    ∃ hwd : stochasticMuonExpectationsWellDefined
        (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
        (deterministicOracleConfig cfg) T,
      stochasticHessianDirectionalAverageRealized
          (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
          (deterministicOracleConfig cfg) T hwd.2.2.1 =
          deterministicMomentumHessianDirectionalAverage
            theorem_4_15_periodicCandidateObjective cfg T ∧
        (1 : ℝ) / 64 ≤
          stochasticAverageNuclearGradientRealized
            (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
            (deterministicOracleConfig cfg) T hwd.1 := by
  rcases theorem_4_15_periodicCandidate_signed_blocks_dense_stochastic_lower_bound
      cfg eta sigma q blockLength t ell T hT hblocks htBlock hetaPos hroom
        hwidth heta hsign htravel hsigma with ⟨hwd, hdirectional, havg⟩
  refine ⟨hwd, hdirectional, ?_⟩
  exact (theorem_4_15_packed_dense_windows_fraction_lower_bound
    q blockLength ell T hT hq hmaximal hdense).trans havg

/- Consequently the uniform generated lower bound has a version in which the
   block family is the maximal family determined by the actual horizon.  The
   hypotheses that remain are precisely the unresolved orbit facts (constant
   schedule and fixed-sign dense legs) plus the local density arithmetic; no
   caller may now choose a smaller `q` and separately assume maximality. -/
theorem theorem_4_15_periodicCandidate_maximally_packed_signed_blocks_uniform_stochastic_lower_bound
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta sigma : ℝ)
    (blockLength t ell T : ℕ) (hT : horizonDomain T)
    (hblockPos : 0 < blockLength) (hblockFits : blockLength ≤ T)
    (htBlock : t < blockLength)
    (hdense : blockLength ≤ 16 * (ell + 1))
    (hetaPos : 0 < eta) (hroom : 2 * ell ≤ t)
    (hwidth : ((ell + 1 : ℕ) : ℝ) * eta ≤ Real.pi / 8)
    (heta : ∀ k : Fin (T / blockLength), ∀ j < t,
      cfg.eta (k.1 * blockLength + j) = eta)
    (hsign : ∀ k : Fin (T / blockLength),
      (∀ j < t, 0 <
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg
          (k.1 * blockLength + j)).M 0 0) ∨
      (∀ j < t,
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg
          (k.1 * blockLength + j)).M 0 0 < 0))
    (htravel : Real.pi ≤ (t : ℝ) * eta) (hsigma : 0 ≤ sigma) :
    ∃ hwd : stochasticMuonExpectationsWellDefined
        (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
        (deterministicOracleConfig cfg) T,
      stochasticHessianDirectionalAverageRealized
          (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
          (deterministicOracleConfig cfg) T hwd.2.2.1 =
          deterministicMomentumHessianDirectionalAverage
            theorem_4_15_periodicCandidateObjective cfg T ∧
        (1 : ℝ) / 64 ≤
          stochasticAverageNuclearGradientRealized
            (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
            (deterministicOracleConfig cfg) T hwd.1 := by
  have hpacking := theorem_4_15_horizon_div_blockLength_packing
    blockLength T hblockPos hblockFits
  dsimp only at hpacking
  exact
    theorem_4_15_periodicCandidate_signed_blocks_uniform_stochastic_lower_bound
      cfg eta sigma (T / blockLength) blockLength t ell T hT
        hpacking.2.1 htBlock hpacking.1 hpacking.2.2 hdense hetaPos hroom
        hwidth heta hsign htravel hsigma

/- Every phase hit yields a certificate at that generated index or its exact
   successor.  The only exceptional case at the hit is zero momentum.  Then
   the update leaves the phase fixed and the nonzero cosine creates nonzero
   momentum at the successor, so one of the two signed zero-length restart
   constructors applies. -/
theorem theorem_4_15_periodicCandidate_restartCertificate_at_or_succ_of_phase
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta : ℝ) (t : ℕ) (z : ℤ)
    (hphase :
      |theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg t).W -
        (z : ℝ) * Real.pi| ≤ Real.pi / 8) :
    theorem_4_15_periodicCandidateRestartCertificate cfg eta t ∨
      theorem_4_15_periodicCandidateRestartCertificate cfg eta (t + 1) := by
  let Mt := (deterministicMomentumMuonState
    theorem_4_15_periodicCandidateObjective cfg t).M 0 0
  by_cases hpos : 0 < Mt
  · left
    exact theorem_4_15_periodicCandidate_restartCertificate_of_positive_momentum
      cfg eta t z hpos hphase
  by_cases hneg : Mt < 0
  · left
    exact theorem_4_15_periodicCandidate_restartCertificate_of_negative_momentum
      cfg eta t z hneg hphase
  have hzero : Mt = 0 := le_antisymm (le_of_not_gt hpos) (le_of_not_gt hneg)
  have hrecurrence :=
    theorem_4_15_periodicCandidate_full_orbit_scalar_recurrence cfg t
  have hphaseNext :
      |theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg (t + 1)).W -
        (z : ℝ) * Real.pi| ≤ Real.pi / 8 := by
    rw [hrecurrence.1, show
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg t).M 0 0 = 0 from hzero,
      Real.sign_zero, mul_zero, sub_zero]
    exact hphase
  have hcosLower :=
    theorem_4_15_periodicCandidate_abs_cos_ge_half_of_phase_near_int_mul_pi
      (theorem_4_5_counterexampleEntry
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg t).W) z hphase
  have hcosNe : Real.cos (theorem_4_5_counterexampleEntry
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg t).W) ≠ 0 := by
    intro hcos
    rw [hcos, abs_zero] at hcosLower
    norm_num at hcosLower
  have hnextNe : (deterministicMomentumMuonState
      theorem_4_15_periodicCandidateObjective cfg (t + 1)).M 0 0 ≠ 0 := by
    rw [hrecurrence.2, show
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg t).M 0 0 = 0 from hzero,
      mul_zero, zero_add]
    rw [hrecurrence.1, show
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg t).M 0 0 = 0 from hzero,
      Real.sign_zero, mul_zero, sub_zero]
    exact mul_ne_zero (ne_of_gt (sub_pos.mpr cfg.beta_mem.2)) hcosNe
  right
  rcases lt_or_gt_of_ne hnextNe with hnextNeg | hnextPos
  · exact theorem_4_15_periodicCandidate_restartCertificate_of_negative_momentum
      cfg eta (t + 1) z hnextNeg hphaseNext
  · exact theorem_4_15_periodicCandidate_restartCertificate_of_positive_momentum
      cfg eta (t + 1) z hnextPos hphaseNext

theorem theorem_4_15_periodicCandidate_exists_nearby_restartCertificate_of_phase
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta : ℝ) (t : ℕ) (z : ℤ)
    (hphase :
      |theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg t).W -
        (z : ℝ) * Real.pi| ≤ Real.pi / 8) :
    ∃ u : ℕ, t ≤ u ∧ u ≤ t + 1 ∧
      theorem_4_15_periodicCandidateRestartCertificate cfg eta u := by
  rcases theorem_4_15_periodicCandidate_restartCertificate_at_or_succ_of_phase
      cfg eta t z hphase with ht | hsucc
  · exact ⟨t, le_rfl, Nat.le_succ t, ht⟩
  · exact ⟨t + 1, Nat.le_succ t, le_rfl, hsucc⟩

/- Combining the five-memory phase selector with the exact zero-momentum
   successor bridge gives a restart certificate inside the same signed block,
   with at most one additional generated step.  This is the block-local
   certificate needed by the existing disjoint-block density theorem. -/
theorem theorem_4_15_periodicCandidate_five_memory_signed_leg_has_restartCertificate
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta : ℝ) (start : ℕ)
    (hetaPos : 0 < eta) (hetaSmall : eta ≤ Real.pi / 8)
    (hmemoryTravel : Real.pi ≤ 5 * (eta / (1 - cfg.beta)))
    (heta : ∀ k < Nat.ceil (5 / (1 - cfg.beta)),
      cfg.eta (start + k) = eta)
    (hsign :
      (∀ k < Nat.ceil (5 / (1 - cfg.beta)), 0 <
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg (start + k)).M 0 0) ∨
      (∀ k < Nat.ceil (5 / (1 - cfg.beta)),
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg (start + k)).M 0 0 < 0)) :
    ∃ u : ℕ,
      start ≤ u ∧
        u ≤ start + Nat.ceil (5 / (1 - cfg.beta)) + 1 ∧
        theorem_4_15_periodicCandidateRestartCertificate cfg eta u := by
  rcases theorem_4_15_periodicCandidate_five_memory_signed_leg_has_phase_hit
      cfg eta start hetaPos hetaSmall hmemoryTravel heta hsign with
    ⟨k, hk, z, hphase⟩
  rcases theorem_4_15_periodicCandidate_exists_nearby_restartCertificate_of_phase
      cfg eta (start + k) z hphase with ⟨u, huLower, huUpper, hcert⟩
  refine ⟨u, ?_, ?_, hcert⟩
  · exact (Nat.le_add_right start k).trans huLower
  · omega

/- The candidate family is the set of all certified indices in the selected
   horizon.  Using a filter makes overlap between different restart witnesses
   irrelevant: every generated time is present at most once. -/
noncomputable def theorem_4_15_periodicCandidateRestartSet
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta : ℝ) (T : ℕ) :
    Finset ℕ := by
  classical
  exact (Finset.range T).filter
    (theorem_4_15_periodicCandidateRestartCertificate cfg eta)

theorem theorem_4_15_periodicCandidate_mem_restartSet_iff
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta : ℝ) (T t : ℕ) :
    t ∈ theorem_4_15_periodicCandidateRestartSet cfg eta T ↔
      t < T ∧ theorem_4_15_periodicCandidateRestartCertificate cfg eta t := by
  classical
  simp [theorem_4_15_periodicCandidateRestartSet]

/- Disjoint source-orbit blocks give a concrete way to discharge the remaining
   restart-set count.  The selected index in each block is an index of the one
   generated orbit, not a restarted trajectory.  No injectivity assumption is
   needed: the half-open block bounds prove that distinct block indices select
   distinct generated times. -/
theorem theorem_4_15_periodicCandidate_restartSet_card_lower_bound_of_blocks
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta : ℝ)
    (q blockLength T : ℕ) (pick : Fin q → ℕ)
    (hblocks : q * blockLength ≤ T)
    (hlower : ∀ k, k.1 * blockLength ≤ pick k)
    (hupper : ∀ k, pick k < (k.1 + 1) * blockLength)
    (hcert : ∀ k,
      theorem_4_15_periodicCandidateRestartCertificate cfg eta (pick k)) :
    q ≤ (theorem_4_15_periodicCandidateRestartSet cfg eta T).card := by
  classical
  let selected : Fin q →
      ↥(theorem_4_15_periodicCandidateRestartSet cfg eta T) := fun k =>
    ⟨pick k, (theorem_4_15_periodicCandidate_mem_restartSet_iff
      cfg eta T (pick k)).2 ⟨by
        calc
          pick k < (k.1 + 1) * blockLength := hupper k
          _ ≤ q * blockLength := Nat.mul_le_mul_right blockLength k.2
          _ ≤ T := hblocks,
      hcert k⟩⟩
  have hselected : Function.Injective selected := by
    intro a b hab
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hablt | hbalt
    · have hpick : pick a < pick b := by
        calc
          pick a < (a.1 + 1) * blockLength := hupper a
          _ ≤ b.1 * blockLength :=
            Nat.mul_le_mul_right blockLength hablt
          _ ≤ pick b := hlower b
      have hvalues : pick a = pick b := congrArg Subtype.val hab
      exact (Nat.ne_of_lt hpick) hvalues
    · have hpick : pick b < pick a := by
        calc
          pick b < (b.1 + 1) * blockLength := hupper b
          _ ≤ a.1 * blockLength :=
            Nat.mul_le_mul_right blockLength hbalt
          _ ≤ pick a := hlower a
      have hvalues : pick a = pick b := congrArg Subtype.val hab
      exact (Nat.ne_of_lt hpick) hvalues.symm
  simpa [selected] using Fintype.card_le_of_injective selected hselected

/- Either signed restart certificate supplies the same pointwise gradient
   lower bound.  This is the bridge needed to count alternating legs without
   selecting one common restart index for the whole horizon. -/
theorem theorem_4_15_periodicCandidate_gradient_lower_bound_of_restart_certificate
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta : ℝ) (t : ℕ)
    (hcert : theorem_4_15_periodicCandidateRestartCertificate cfg eta t) :
    (1 : ℝ) / 2 ≤
      nuclearNorm (theorem_4_15_periodicCandidateObjective.grad
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg t).W) := by
  rcases hcert with hpositive | hnegative
  · rcases hpositive with
      ⟨start, m0, z, hstart, hm0, hMstart, heta, hbudget, hphase⟩
    have hgradient :=
      (theorem_4_15_periodicCandidate_gradient_lower_bound_from_index
        cfg eta m0 start (t - start) z hm0 hMstart heta hbudget hphase).2
    rw [Nat.add_sub_of_le hstart] at hgradient
    exact hgradient
  · rcases hnegative with
      ⟨start, m0, z, hstart, hm0, hMstart, heta, hbudget, hphase⟩
    have hgradient :=
      (theorem_4_15_periodicCandidate_gradient_lower_bound_from_index_negative
        cfg eta m0 start (t - start) z hm0 hMstart heta hbudget hphase).2
    rw [Nat.add_sub_of_le hstart] at hgradient
    exact hgradient

/- A single finite set may now contain points from arbitrarily many positive
   and negative restart windows.  Its cardinality is counted once, so overlap
   cannot be double-counted.  This closes the aggregation gap between the two
   local-window theorems and a positive-density full-horizon family; producing
   such a family from the shrinking source schedule remains separate. -/
theorem theorem_4_15_periodicCandidate_mixed_restarted_family_density_lower_bound
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta rho : ℝ)
    (T : ℕ) (S : Finset ℕ) (hT : horizonDomain T)
    (hinside : ∀ t ∈ S, t < T)
    (hcert : ∀ t ∈ S,
      theorem_4_15_periodicCandidateRestartCertificate cfg eta t)
    (hdensity : rho * (T : ℝ) ≤ (S.card : ℝ)) :
    rho / 2 ≤ deterministicMomentumAverageNuclearGradient
      theorem_4_15_periodicCandidateObjective cfg T := by
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hsubset : S ⊆ Finset.range T := by
    intro t ht
    exact Finset.mem_range.mpr (hinside t ht)
  have hpoint : ∀ t ∈ S,
      (1 : ℝ) / 2 ≤
        |Real.cos (theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg t).W)| := by
    intro t ht
    have hgradient :=
      theorem_4_15_periodicCandidate_gradient_lower_bound_of_restart_certificate
        cfg eta t (hcert t ht)
    simpa [theorem_4_15_periodicCandidate_generatedNuclearGradient_eq_abs_cos]
      using hgradient
  have hsumS : (S.card : ℝ) * ((1 : ℝ) / 2) ≤
      Finset.sum S (fun t =>
        |Real.cos (theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg t).W)|) := by
    calc
      (S.card : ℝ) * ((1 : ℝ) / 2) =
          Finset.sum S (fun _ => (1 : ℝ) / 2) := by simp
      _ ≤ Finset.sum S (fun t =>
          |Real.cos (theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg t).W)|) :=
        Finset.sum_le_sum hpoint
  have hsumSubset :
      Finset.sum S (fun t =>
          |Real.cos (theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg t).W)|) ≤
        Finset.sum (Finset.range T) (fun t =>
          |Real.cos (theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg t).W)|) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => abs_nonneg _)
  have hscaledDensity :
      ((T : ℝ)⁻¹) * (rho * (T : ℝ)) ≤
        ((T : ℝ)⁻¹) * (S.card : ℝ) :=
    mul_le_mul_of_nonneg_left hdensity (inv_nonneg.mpr hTreal.le)
  rw [(theorem_4_15_periodicCandidate_fullHorizon_scalar_reduction_with_sign
    cfg T).2]
  calc
    rho / 2 = ((T : ℝ)⁻¹) * (rho * (T : ℝ)) * ((1 : ℝ) / 2) := by
      field_simp [ne_of_gt hTreal]
      <;> ring
    _ ≤ ((T : ℝ)⁻¹) * (S.card : ℝ) * ((1 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right hscaledDensity (by norm_num)
    _ = ((T : ℝ)⁻¹) * ((S.card : ℝ) * ((1 : ℝ) / 2)) := by ring
    _ ≤ ((T : ℝ)⁻¹) * Finset.sum S (fun t =>
        |Real.cos (theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg t).W)|) :=
      mul_le_mul_of_nonneg_left hsumS (inv_nonneg.mpr hTreal.le)
    _ ≤ ((T : ℝ)⁻¹) * Finset.sum (Finset.range T) (fun t =>
        |Real.cos (theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg t).W)|) :=
      mul_le_mul_of_nonneg_left hsumSubset (inv_nonneg.mpr hTreal.le)

/- The mixed-family count is finally transferred to the exact source-level
   stochastic quantities on the singleton oracle.  The directional quantity
   is identified at the same horizon, while the lower bound is on the actual
   generated expected nuclear-gradient average. -/
theorem theorem_4_15_periodicCandidate_mixed_restarted_family_stochastic_density_lower_bound
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta rho sigma : ℝ)
    (T : ℕ) (S : Finset ℕ) (hT : horizonDomain T)
    (hinside : ∀ t ∈ S, t < T)
    (hcert : ∀ t ∈ S,
      theorem_4_15_periodicCandidateRestartCertificate cfg eta t)
    (hdensity : rho * (T : ℝ) ≤ (S.card : ℝ))
    (hsigma : 0 ≤ sigma) :
    ∃ hwd : stochasticMuonExpectationsWellDefined
        (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
        (deterministicOracleConfig cfg) T,
      stochasticHessianDirectionalAverageRealized
          (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
          (deterministicOracleConfig cfg) T hwd.2.2.1 =
          deterministicMomentumHessianDirectionalAverage
            theorem_4_15_periodicCandidateObjective cfg T ∧
        rho / 2 ≤ stochasticAverageNuclearGradientRealized
          (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
          (deterministicOracleConfig cfg) T hwd.1 := by
  let hwd := theorem_4_15_periodicCandidate_expectationsWellDefined
    cfg T sigma hsigma
  refine ⟨hwd, ?_, ?_⟩
  · rw [deterministicOracle_hessianDirectionalAverageRealized_eq]
  · rw [deterministicOracle_average_eq]
    exact
      theorem_4_15_periodicCandidate_mixed_restarted_family_density_lower_bound
        cfg eta rho T S hT hinside hcert hdensity

/- Therefore the remaining density obligation has a canonical form: count the
   filtered set of all certified generated indices.  Once that scalar count is
   supplied, the exact stochastic source-object lower bound follows without
   choosing windows again or risking overlap. -/
theorem theorem_4_15_periodicCandidate_restartSet_stochastic_density_lower_bound
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta rho sigma : ℝ)
    (T : ℕ) (hT : horizonDomain T)
    (hdensity : rho * (T : ℝ) ≤
      ((theorem_4_15_periodicCandidateRestartSet cfg eta T).card : ℝ))
    (hsigma : 0 ≤ sigma) :
    ∃ hwd : stochasticMuonExpectationsWellDefined
        (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
        (deterministicOracleConfig cfg) T,
      stochasticHessianDirectionalAverageRealized
          (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
          (deterministicOracleConfig cfg) T hwd.2.2.1 =
          deterministicMomentumHessianDirectionalAverage
            theorem_4_15_periodicCandidateObjective cfg T ∧
        rho / 2 ≤ stochasticAverageNuclearGradientRealized
          (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
          (deterministicOracleConfig cfg) T hwd.1 := by
  apply
    theorem_4_15_periodicCandidate_mixed_restarted_family_stochastic_density_lower_bound
      cfg eta rho sigma T
        (theorem_4_15_periodicCandidateRestartSet cfg eta T) hT
  · intro t ht
    exact (theorem_4_15_periodicCandidate_mem_restartSet_iff
      cfg eta T t).mp ht |>.1
  · intro t ht
    exact (theorem_4_15_periodicCandidate_mem_restartSet_iff
      cfg eta T t).mp ht |>.2
  · exact hdensity
  · exact hsigma

/- Thus it is enough to certify one generated index in each of `q` disjoint
   blocks.  The block count is converted to a density lower bound and then to
   the exact stochastic source quantity.  The remaining counterexample work is
   now local orbit analysis inside each block plus directional-J cancellation;
   neither is assumed by this conclusion. -/
theorem theorem_4_15_periodicCandidate_block_witnesses_stochastic_density_lower_bound
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta rho sigma : ℝ)
    (q blockLength T : ℕ) (pick : Fin q → ℕ)
    (hT : horizonDomain T)
    (hblocks : q * blockLength ≤ T)
    (hlower : ∀ k, k.1 * blockLength ≤ pick k)
    (hupper : ∀ k, pick k < (k.1 + 1) * blockLength)
    (hcert : ∀ k,
      theorem_4_15_periodicCandidateRestartCertificate cfg eta (pick k))
    (hdensity : rho * (T : ℝ) ≤ (q : ℝ))
    (hsigma : 0 ≤ sigma) :
    ∃ hwd : stochasticMuonExpectationsWellDefined
        (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
        (deterministicOracleConfig cfg) T,
      stochasticHessianDirectionalAverageRealized
          (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
          (deterministicOracleConfig cfg) T hwd.2.2.1 =
          deterministicMomentumHessianDirectionalAverage
            theorem_4_15_periodicCandidateObjective cfg T ∧
        rho / 2 ≤ stochasticAverageNuclearGradientRealized
          (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
          (deterministicOracleConfig cfg) T hwd.1 := by
  apply theorem_4_15_periodicCandidate_restartSet_stochastic_density_lower_bound
    cfg eta rho sigma T hT
  · have hcardNat :=
      theorem_4_15_periodicCandidate_restartSet_card_lower_bound_of_blocks
        cfg eta q blockLength T pick hblocks hlower hupper hcert
    have hcardReal : (q : ℝ) ≤
        ((theorem_4_15_periodicCandidateRestartSet cfg eta T).card : ℝ) := by
      exact_mod_cast hcardNat
    exact hdensity.trans hcardReal
  · exact hsigma

/- The canonical quantitative form needs no separately supplied density
   constant: `q` certified disjoint blocks contribute the exact fraction
   `q / T` of the selected horizon.  A later orbit argument only has to make
   this fraction uniformly positive under the printed schedule. -/
theorem theorem_4_15_periodicCandidate_block_fraction_stochastic_lower_bound
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta sigma : ℝ)
    (q blockLength T : ℕ) (pick : Fin q → ℕ)
    (hT : horizonDomain T)
    (hblocks : q * blockLength ≤ T)
    (hlower : ∀ k, k.1 * blockLength ≤ pick k)
    (hupper : ∀ k, pick k < (k.1 + 1) * blockLength)
    (hcert : ∀ k,
      theorem_4_15_periodicCandidateRestartCertificate cfg eta (pick k))
    (hsigma : 0 ≤ sigma) :
    ∃ hwd : stochasticMuonExpectationsWellDefined
        (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
        (deterministicOracleConfig cfg) T,
      stochasticHessianDirectionalAverageRealized
          (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
          (deterministicOracleConfig cfg) T hwd.2.2.1 =
          deterministicMomentumHessianDirectionalAverage
            theorem_4_15_periodicCandidateObjective cfg T ∧
        (((T : ℝ)⁻¹) * (q : ℝ)) / 2 ≤
          stochasticAverageNuclearGradientRealized
            (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
            (deterministicOracleConfig cfg) T hwd.1 := by
  apply
    theorem_4_15_periodicCandidate_block_witnesses_stochastic_density_lower_bound
      cfg eta (((T : ℝ)⁻¹) * (q : ℝ)) sigma q blockLength T pick hT
        hblocks hlower hupper hcert
  · have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
    exact le_of_eq (by field_simp [ne_of_gt hTreal])
  · exact hsigma

/- Disjoint five-memory signed legs now feed the stochastic density theorem
   directly.  The phase index, possible zero-momentum successor, and restart
   certificate are all selected from the exact generated orbit inside each
   block.  The two spare indices in every block provide the one-step room for
   the zero-momentum case.  Thus later orbit analysis need only establish the
   fixed-sign leg in each block; it does not supply phase hits, certificate
   indices, or an injective picker as additional hypotheses. -/
theorem theorem_4_15_periodicCandidate_five_memory_signed_blocks_stochastic_lower_bound
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta sigma : ℝ)
    (q T : ℕ)
    (hT : horizonDomain T)
    (hblocks : q * (Nat.ceil (5 / (1 - cfg.beta)) + 2) ≤ T)
    (hetaPos : 0 < eta) (hetaSmall : eta ≤ Real.pi / 8)
    (hmemoryTravel : Real.pi ≤ 5 * (eta / (1 - cfg.beta)))
    (heta : ∀ k : Fin q, ∀ j < Nat.ceil (5 / (1 - cfg.beta)),
      cfg.eta (k.1 * (Nat.ceil (5 / (1 - cfg.beta)) + 2) + j) = eta)
    (hsign : ∀ k : Fin q,
      (∀ j < Nat.ceil (5 / (1 - cfg.beta)), 0 <
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg
          (k.1 * (Nat.ceil (5 / (1 - cfg.beta)) + 2) + j)).M 0 0) ∨
      (∀ j < Nat.ceil (5 / (1 - cfg.beta)),
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg
          (k.1 * (Nat.ceil (5 / (1 - cfg.beta)) + 2) + j)).M 0 0 < 0))
    (hsigma : 0 ≤ sigma) :
    ∃ hwd : stochasticMuonExpectationsWellDefined
        (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
        (deterministicOracleConfig cfg) T,
      stochasticHessianDirectionalAverageRealized
          (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
          (deterministicOracleConfig cfg) T hwd.2.2.1 =
          deterministicMomentumHessianDirectionalAverage
            theorem_4_15_periodicCandidateObjective cfg T ∧
        (((T : ℝ)⁻¹) * (q : ℝ)) / 2 ≤
          stochasticAverageNuclearGradientRealized
            (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
            (deterministicOracleConfig cfg) T hwd.1 := by
  classical
  let blockLength := Nat.ceil (5 / (1 - cfg.beta)) + 2
  have hlocal : ∀ k : Fin q, ∃ u : ℕ,
      k.1 * blockLength ≤ u ∧
        u ≤ k.1 * blockLength + Nat.ceil (5 / (1 - cfg.beta)) + 1 ∧
        theorem_4_15_periodicCandidateRestartCertificate cfg eta u := by
    intro k
    exact
      theorem_4_15_periodicCandidate_five_memory_signed_leg_has_restartCertificate
        cfg eta (k.1 * blockLength) hetaPos hetaSmall hmemoryTravel
        (by simpa [blockLength] using heta k)
        (by simpa [blockLength] using hsign k)
  let pick : Fin q → ℕ := fun k => Classical.choose (hlocal k)
  have hpick : ∀ k : Fin q,
      k.1 * blockLength ≤ pick k ∧
        pick k ≤ k.1 * blockLength + Nat.ceil (5 / (1 - cfg.beta)) + 1 ∧
        theorem_4_15_periodicCandidateRestartCertificate cfg eta (pick k) := by
    intro k
    exact Classical.choose_spec (hlocal k)
  apply theorem_4_15_periodicCandidate_block_fraction_stochastic_lower_bound
    cfg eta sigma q blockLength T pick hT
  · simpa [blockLength] using hblocks
  · intro k
    exact (hpick k).1
  · intro k
    have hu := (hpick k).2.1
    calc
      pick k ≤
          k.1 * blockLength + Nat.ceil (5 / (1 - cfg.beta)) + 1 := hu
      _ < k.1 * blockLength + blockLength := by
        dsimp [blockLength]
        omega
      _ = (k.1 + 1) * blockLength := by
        rw [Nat.add_mul, one_mul]
  · intro k
    exact (hpick k).2.2
  · exact hsigma

/- Every finite block of the exact generated orbit has an exhaustive sign
   decomposition.  If it is neither a strictly positive nor a strictly
   negative momentum leg, the same block contains both a nonpositive and a
   nonnegative momentum index.  This elementary step is useful here because
   it prevents the fixed-sign hypothesis from being silently treated as a
   consequence of the recurrence: mixed-sign blocks are an explicit remaining
   dynamical case. -/
theorem theorem_4_15_periodicCandidate_momentum_block_sign_dichotomy
    (cfg : DeterministicMomentumMuonConfig 1 1) (start q : ℕ) :
    (∀ j < q, 0 <
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + j)).M 0 0) ∨
    (∀ j < q,
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + j)).M 0 0 < 0) ∨
    (∃ j < q, ∃ k < q,
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + j)).M 0 0 ≤ 0 ∧
      0 ≤ (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + k)).M 0 0) := by
  classical
  by_cases hpositive : ∀ j < q, 0 <
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + j)).M 0 0
  · exact Or.inl hpositive
  right
  by_cases hnegative : ∀ j < q,
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + j)).M 0 0 < 0
  · exact Or.inl hnegative
  right
  push Not at hpositive hnegative
  rcases hpositive with ⟨j, hj, hjNonpos⟩
  rcases hnegative with ⟨k, hk, hkNonneg⟩
  exact ⟨j, hj, k, hk, hjNonpos, hkNonneg⟩

/- An adjacent crossing of the exact generated momentum has a forced gradient
   sign.  This is the unconditional recurrence-level information available at
   a mixed block: a nonpositive-to-nonnegative crossing forces the cosine at
   the new state to be nonnegative.  Notice that it does not manufacture the
   stronger `|cos| ≥ 1/2` phase-hit conclusion needed by the density route. -/
theorem theorem_4_15_periodicCandidate_cos_nonnegative_at_upward_momentum_crossing
    (cfg : DeterministicMomentumMuonConfig 1 1) (t : ℕ)
    (hcurrent :
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg t).M 0 0 ≤ 0)
    (hnext : 0 ≤
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (t + 1)).M 0 0) :
    0 ≤ Real.cos (theorem_4_5_counterexampleEntry
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (t + 1)).W) := by
  have hscaled : cfg.beta *
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg t).M 0 0 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos cfg.beta_mem.1 hcurrent
  have hdelta : 0 < 1 - cfg.beta := sub_pos.mpr cfg.beta_mem.2
  have hrecurrence :=
    (theorem_4_15_periodicCandidate_full_orbit_scalar_recurrence cfg t).2
  rw [hrecurrence] at hnext
  nlinarith

/- The sign-symmetric recurrence consequence for a downward crossing. -/
theorem theorem_4_15_periodicCandidate_cos_nonpositive_at_downward_momentum_crossing
    (cfg : DeterministicMomentumMuonConfig 1 1) (t : ℕ)
    (hcurrent : 0 ≤
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg t).M 0 0)
    (hnext :
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (t + 1)).M 0 0 ≤ 0) :
    Real.cos (theorem_4_5_counterexampleEntry
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (t + 1)).W) ≤ 0 := by
  have hscaled : 0 ≤ cfg.beta *
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg t).M 0 0 :=
    mul_nonneg cfg.beta_mem.1 hcurrent
  have hdelta : 0 < 1 - cfg.beta := sub_pos.mpr cfg.beta_mem.2
  have hrecurrence :=
    (theorem_4_15_periodicCandidate_full_orbit_scalar_recurrence cfg t).2
  rw [hrecurrence] at hnext
  nlinarith

/- A finite exact-orbit segment whose endpoint momenta have opposite weak
   signs contains an adjacent crossing.  The conclusion also records the
   supporting cosine sign forced by the generated recurrence.  This is the
   correct discrete intermediate-value replacement for the previously
   unresolved jump from a mixed block directly to a phase hit. -/
theorem theorem_4_15_periodicCandidate_upward_momentum_crossing_in_segment
    (cfg : DeterministicMomentumMuonConfig 1 1) (start d : ℕ)
    (hstart :
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg start).M 0 0 ≤ 0)
    (hend : 0 ≤
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + d)).M 0 0)
    (hd : 0 < d) :
    ∃ k < d,
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + k)).M 0 0 ≤ 0 ∧
      0 ≤ (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + k + 1)).M 0 0 ∧
      0 ≤ Real.cos (theorem_4_5_counterexampleEntry
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg (start + k + 1)).W) := by
  induction d generalizing start with
  | zero => omega
  | succ d ih =>
      by_cases hnext : 0 ≤
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg (start + 1)).M 0 0
      · refine ⟨0, Nat.succ_pos _, ?_, ?_, ?_⟩
        · simpa using hstart
        · simpa using hnext
        · simpa using
            theorem_4_15_periodicCandidate_cos_nonnegative_at_upward_momentum_crossing
              cfg start hstart (by simpa using hnext)
      · have hnextNonpos :
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg (start + 1)).M 0 0 ≤ 0 :=
          le_of_not_ge hnext
        have hdPos : 0 < d := by
          by_contra hdZero
          have hdEq : d = 0 := Nat.eq_zero_of_not_pos hdZero
          subst d
          exact hnext (by simpa using hend)
        have hend' : 0 ≤
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg ((start + 1) + d)).M 0 0 := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hend
        obtain ⟨k, hk, hkCurrent, hkNext, hkCos⟩ :=
          ih (start + 1) hnextNonpos hend' hdPos
        refine ⟨k + 1, Nat.succ_lt_succ hk, ?_, ?_, ?_⟩
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hkCurrent
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hkNext
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hkCos

/- The corresponding downward segment theorem. -/
theorem theorem_4_15_periodicCandidate_downward_momentum_crossing_in_segment
    (cfg : DeterministicMomentumMuonConfig 1 1) (start d : ℕ)
    (hstart : 0 ≤
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg start).M 0 0)
    (hend :
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + d)).M 0 0 ≤ 0)
    (hd : 0 < d) :
    ∃ k < d,
      0 ≤ (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + k)).M 0 0 ∧
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + k + 1)).M 0 0 ≤ 0 ∧
      Real.cos (theorem_4_5_counterexampleEntry
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg (start + k + 1)).W) ≤ 0 := by
  induction d generalizing start with
  | zero => omega
  | succ d ih =>
      by_cases hnext :
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg (start + 1)).M 0 0 ≤ 0
      · refine ⟨0, Nat.succ_pos _, ?_, ?_, ?_⟩
        · simpa using hstart
        · simpa using hnext
        · simpa using
            theorem_4_15_periodicCandidate_cos_nonpositive_at_downward_momentum_crossing
              cfg start hstart (by simpa using hnext)
      · have hnextNonneg : 0 ≤
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg (start + 1)).M 0 0 :=
          le_of_not_ge hnext
        have hdPos : 0 < d := by
          by_contra hdZero
          have hdEq : d = 0 := Nat.eq_zero_of_not_pos hdZero
          subst d
          exact hnext (by simpa using hend)
        have hend' :
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg ((start + 1) + d)).M 0 0 ≤ 0 := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hend
        obtain ⟨k, hk, hkCurrent, hkNext, hkCos⟩ :=
          ih (start + 1) hnextNonneg hend' hdPos
        refine ⟨k + 1, Nat.succ_lt_succ hk, ?_, ?_, ?_⟩
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hkCurrent
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hkNext
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hkCos

/- Consequently the mixed case of the block sign dichotomy has a completely
   generated local witness: either the momentum is exactly zero at a block
   index, or two adjacent block indices cross weakly and the new gradient has
   the supporting sign.  This theorem deliberately stops short of a phase hit,
   because the recurrence alone gives no uniform lower bound on that cosine. -/
theorem theorem_4_15_periodicCandidate_mixed_momentum_block_has_local_crossing
    (cfg : DeterministicMomentumMuonConfig 1 1) (start q : ℕ)
    (hmixed : ∃ j < q, ∃ k < q,
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + j)).M 0 0 ≤ 0 ∧
      0 ≤ (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + k)).M 0 0) :
    (∃ u < q,
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + u)).M 0 0 = 0) ∨
    (∃ u, u + 1 < q ∧
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + u)).M 0 0 ≤ 0 ∧
      0 ≤ (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + u + 1)).M 0 0 ∧
      0 ≤ Real.cos (theorem_4_5_counterexampleEntry
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg (start + u + 1)).W)) ∨
    (∃ u, u + 1 < q ∧
      0 ≤ (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + u)).M 0 0 ∧
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg (start + u + 1)).M 0 0 ≤ 0 ∧
      Real.cos (theorem_4_5_counterexampleEntry
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg (start + u + 1)).W) ≤ 0) := by
  rcases hmixed with ⟨j, hj, k, hk, hjNonpos, hkNonneg⟩
  rcases lt_trichotomy j k with hjk | hjk | hkj
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hjk
    have hd : 0 < d + 1 := Nat.succ_pos d
    have hend : 0 ≤
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg ((start + j) + (d + 1))).M 0 0 := by
      simpa [Nat.add_assoc] using hkNonneg
    obtain ⟨u, hu, huCurrent, huNext, huCos⟩ :=
      theorem_4_15_periodicCandidate_upward_momentum_crossing_in_segment
        cfg (start + j) (d + 1) hjNonpos hend hd
    right
    left
    refine ⟨j + u, ?_, ?_, ?_, ?_⟩
    · omega
    · simpa [Nat.add_assoc] using huCurrent
    · simpa [Nat.add_assoc] using huNext
    · simpa [Nat.add_assoc] using huCos
  · subst k
    left
    exact ⟨j, hj, le_antisymm hjNonpos hkNonneg⟩
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hkj
    have hd : 0 < d + 1 := Nat.succ_pos d
    have hend :
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg ((start + k) + (d + 1))).M 0 0 ≤ 0 := by
      simpa [Nat.add_assoc] using hjNonpos
    obtain ⟨u, hu, huCurrent, huNext, huCos⟩ :=
      theorem_4_15_periodicCandidate_downward_momentum_crossing_in_segment
        cfg (start + k) (d + 1) hkNonneg hend hd
    right
    right
    refine ⟨k + u, ?_, ?_, ?_, ?_⟩
    · omega
    · simpa [Nat.add_assoc] using huCurrent
    · simpa [Nat.add_assoc] using huNext
    · simpa [Nat.add_assoc] using huCos

/- The weak-sign mixed-block condition cannot by itself be strengthened to a
   uniform gradient-magnitude conclusion, even on the exact generated sine
   orbit.  At phase `pi / 2` the generated gradient and initial momentum are
   both zero, so Algorithm 1 remains at that state for every iteration.  This
   is a generated-process obstruction to the proposed local phase-density
   argument only: its generated stationarity average is zero, so it is not a
   counterexample to the source Theorem 4.15 conclusion. -/
def theorem_4_15_periodicCandidateStationaryConfig :
    DeterministicMomentumMuonConfig 1 1 where
  W0 := (Real.pi / 2) • coordinateMatrix 0 0
  eta := fun _ => 1
  beta := 0
  beta_mem := by norm_num

theorem theorem_4_15_periodicCandidate_stationary_generatedState (t : ℕ) :
    deterministicMomentumMuonState theorem_4_15_periodicCandidateObjective
        theorem_4_15_periodicCandidateStationaryConfig t =
      { W := (Real.pi / 2) • coordinateMatrix 0 0
        M := 0 } := by
  induction t with
  | zero =>
      simp [deterministicMomentumMuonState, deterministicMomentumMuonBaseState,
        deterministicGradient, theorem_4_15_periodicCandidateStationaryConfig,
        theorem_4_15_periodicCandidateObjective_grad,
        theorem_4_5_counterexampleEntry_apply, coordinateMatrix] <;> rfl
  | succ t ih =>
      change deterministicMomentumMuonStep theorem_4_15_periodicCandidateObjective
          theorem_4_15_periodicCandidateStationaryConfig t
          (deterministicMomentumMuonState theorem_4_15_periodicCandidateObjective
            theorem_4_15_periodicCandidateStationaryConfig t) = _
      rw [ih]
      unfold deterministicMomentumMuonStep muonUpdate deterministicGradient
      simp [theorem_4_15_periodicCandidateStationaryConfig,
        orthogonalizedDirection_eq_sign_smul_one_dimensional,
        theorem_4_15_periodicCandidateObjective_grad,
        theorem_4_5_counterexampleEntry_apply, coordinateMatrix] <;> rfl

theorem theorem_4_15_periodicCandidate_stationary_gradient_magnitude_zero
    (t : ℕ) :
    |Real.cos (theorem_4_5_counterexampleEntry
      (deterministicMomentumMuonState theorem_4_15_periodicCandidateObjective
        theorem_4_15_periodicCandidateStationaryConfig t).W)| = 0 := by
  rw [theorem_4_15_periodicCandidate_stationary_generatedState]
  simp [theorem_4_5_counterexampleEntry_apply, coordinateMatrix]

theorem theorem_4_15_periodicCandidate_stationary_generatedAverage_zero
    (T : ℕ) :
    deterministicMomentumAverageNuclearGradient
        theorem_4_15_periodicCandidateObjective
        theorem_4_15_periodicCandidateStationaryConfig T = 0 := by
  have hsum : Finset.sum (Finset.range T) (fun t =>
      |Real.cos (theorem_4_5_counterexampleEntry
        (deterministicMomentumMuonState theorem_4_15_periodicCandidateObjective
          theorem_4_15_periodicCandidateStationaryConfig t).W)|) = 0 := by
    apply Finset.sum_eq_zero
    intro t _ht
    exact theorem_4_15_periodicCandidate_stationary_gradient_magnitude_zero t
  rw [(theorem_4_15_periodicCandidate_fullHorizon_scalar_reduction_with_sign
    theorem_4_15_periodicCandidateStationaryConfig T).2, hsum, mul_zero]

theorem theorem_4_15_periodicCandidate_mixed_block_does_not_force_gradient_magnitude :
    ¬ (∀ (cfg : DeterministicMomentumMuonConfig 1 1) (start q : ℕ),
      (∃ j < q, ∃ k < q,
        (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg (start + j)).M 0 0 ≤ 0 ∧
        0 ≤ (deterministicMomentumMuonState
          theorem_4_15_periodicCandidateObjective cfg (start + k)).M 0 0) →
      ∃ hit < q, (1 : ℝ) / 2 ≤
        |Real.cos (theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg (start + hit)).W)|) := by
  intro hforce
  have hmixed : ∃ j < 1, ∃ k < 1,
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective
        theorem_4_15_periodicCandidateStationaryConfig (0 + j)).M 0 0 ≤ 0 ∧
      0 ≤ (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective
        theorem_4_15_periodicCandidateStationaryConfig (0 + k)).M 0 0 := by
    refine ⟨0, by omega, 0, by omega, ?_⟩
    rw [theorem_4_15_periodicCandidate_stationary_generatedState]
    simp
  obtain ⟨hit, hhit, hlarge⟩ :=
    hforce theorem_4_15_periodicCandidateStationaryConfig 0 1 hmixed
  have hhitZero : hit = 0 := by omega
  subst hit
  rw [theorem_4_15_periodicCandidate_stationary_gradient_magnitude_zero] at hlarge
  norm_num at hlarge

/- The block-density route can therefore consume all fixed-sign blocks
   automatically.  Its only extra local input concerns genuinely mixed-sign
   blocks: such a block must contain one phase hit.  The hit itself is then
   converted to a restart certificate by the exact zero-momentum successor
   bridge, and the two spare block indices keep that successor in the same
   half-open block.  Thus `hsign` is no longer an input to this consumer; the
   unresolved orbit obligation is isolated to the mixed-sign phase statement. -/
theorem theorem_4_15_periodicCandidate_five_memory_blocks_of_mixed_phase_hits_stochastic_lower_bound
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta sigma : ℝ)
    (q T : ℕ)
    (hT : horizonDomain T)
    (hblocks : q * (Nat.ceil (5 / (1 - cfg.beta)) + 2) ≤ T)
    (hetaPos : 0 < eta) (hetaSmall : eta ≤ Real.pi / 8)
    (hmemoryTravel : Real.pi ≤ 5 * (eta / (1 - cfg.beta)))
    (heta : ∀ k : Fin q, ∀ j < Nat.ceil (5 / (1 - cfg.beta)),
      cfg.eta (k.1 * (Nat.ceil (5 / (1 - cfg.beta)) + 2) + j) = eta)
    (hmixedPhase : ∀ k : Fin q,
      (∃ j < Nat.ceil (5 / (1 - cfg.beta)),
        ∃ l < Nat.ceil (5 / (1 - cfg.beta)),
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg
            (k.1 * (Nat.ceil (5 / (1 - cfg.beta)) + 2) + j)).M 0 0 ≤ 0 ∧
          0 ≤ (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg
            (k.1 * (Nat.ceil (5 / (1 - cfg.beta)) + 2) + l)).M 0 0) →
      ∃ hit ≤ Nat.ceil (5 / (1 - cfg.beta)), ∃ z : ℤ,
        |theorem_4_5_counterexampleEntry
            (deterministicMomentumMuonState
              theorem_4_15_periodicCandidateObjective cfg
              (k.1 * (Nat.ceil (5 / (1 - cfg.beta)) + 2) + hit)).W -
          (z : ℝ) * Real.pi| ≤ Real.pi / 8)
    (hsigma : 0 ≤ sigma) :
    ∃ hwd : stochasticMuonExpectationsWellDefined
        (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
        (deterministicOracleConfig cfg) T,
      stochasticHessianDirectionalAverageRealized
          (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
          (deterministicOracleConfig cfg) T hwd.2.2.1 =
          deterministicMomentumHessianDirectionalAverage
            theorem_4_15_periodicCandidateObjective cfg T ∧
        (((T : ℝ)⁻¹) * (q : ℝ)) / 2 ≤
          stochasticAverageNuclearGradientRealized
            (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
            (deterministicOracleConfig cfg) T hwd.1 := by
  classical
  let blockLength := Nat.ceil (5 / (1 - cfg.beta)) + 2
  let memoryLength := Nat.ceil (5 / (1 - cfg.beta))
  have hlocal : ∀ k : Fin q, ∃ u : ℕ,
      k.1 * blockLength ≤ u ∧
        u ≤ k.1 * blockLength + memoryLength + 1 ∧
        theorem_4_15_periodicCandidateRestartCertificate cfg eta u := by
    intro k
    rcases theorem_4_15_periodicCandidate_momentum_block_sign_dichotomy
        cfg (k.1 * blockLength) memoryLength with
      hpositive | hnegative | hmixed
    · exact
        theorem_4_15_periodicCandidate_five_memory_signed_leg_has_restartCertificate
          cfg eta (k.1 * blockLength) hetaPos hetaSmall hmemoryTravel
          (by simpa [blockLength, memoryLength] using heta k)
          (Or.inl (by simpa [memoryLength] using hpositive))
    · exact
        theorem_4_15_periodicCandidate_five_memory_signed_leg_has_restartCertificate
          cfg eta (k.1 * blockLength) hetaPos hetaSmall hmemoryTravel
          (by simpa [blockLength, memoryLength] using heta k)
          (Or.inr (by simpa [memoryLength] using hnegative))
    · obtain ⟨hit, hhit, z, hphase⟩ :=
        hmixedPhase k (by simpa [blockLength, memoryLength] using hmixed)
      obtain ⟨u, huLower, huUpper, hcert⟩ :=
        theorem_4_15_periodicCandidate_exists_nearby_restartCertificate_of_phase
          cfg eta (k.1 * blockLength + hit) z hphase
      exact ⟨u,
        (Nat.le_add_right (k.1 * blockLength) hit).trans huLower,
        by omega, hcert⟩
  let pick : Fin q → ℕ := fun k => Classical.choose (hlocal k)
  have hpick : ∀ k : Fin q,
      k.1 * blockLength ≤ pick k ∧
        pick k ≤ k.1 * blockLength + memoryLength + 1 ∧
        theorem_4_15_periodicCandidateRestartCertificate cfg eta (pick k) := by
    intro k
    exact Classical.choose_spec (hlocal k)
  apply theorem_4_15_periodicCandidate_block_fraction_stochastic_lower_bound
    cfg eta sigma q blockLength T pick hT
  · simpa [blockLength] using hblocks
  · intro k
    exact (hpick k).1
  · intro k
    calc
      pick k ≤ k.1 * blockLength + memoryLength + 1 := (hpick k).2.1
      _ < k.1 * blockLength + blockLength := by
        dsimp [blockLength, memoryLength]
        omega
      _ = (k.1 + 1) * blockLength := by
        rw [Nat.add_mul, one_mul]
  · intro k
    exact (hpick k).2.2
  · exact hsigma

/- Phase hits strictly before the end of disjoint blocks now discharge the
   local restart-certificate premises rather than merely postulating them.
   A hit may move to its successor only in the zero-momentum case, and the
   one-step room hypothesis keeps that successor in the same half-open block.
   What remains for the shrinking-schedule counterexample is therefore a
   phase-density theorem for the exact orbit, not a separate momentum seed. -/
theorem theorem_4_15_periodicCandidate_block_phase_hits_stochastic_lower_bound
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta sigma : ℝ)
    (q blockLength T : ℕ) (hit : Fin q → ℕ) (z : Fin q → ℤ)
    (hT : horizonDomain T)
    (hblocks : q * blockLength ≤ T)
    (hlower : ∀ k, k.1 * blockLength ≤ hit k)
    (hroom : ∀ k, hit k + 1 < (k.1 + 1) * blockLength)
    (hphase : ∀ k,
      |theorem_4_5_counterexampleEntry
          (deterministicMomentumMuonState
            theorem_4_15_periodicCandidateObjective cfg (hit k)).W -
        (z k : ℝ) * Real.pi| ≤ Real.pi / 8)
    (hsigma : 0 ≤ sigma) :
    ∃ hwd : stochasticMuonExpectationsWellDefined
        (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
        (deterministicOracleConfig cfg) T,
      stochasticHessianDirectionalAverageRealized
          (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
          (deterministicOracleConfig cfg) T hwd.2.2.1 =
          deterministicMomentumHessianDirectionalAverage
            theorem_4_15_periodicCandidateObjective cfg T ∧
        (((T : ℝ)⁻¹) * (q : ℝ)) / 2 ≤
          stochasticAverageNuclearGradientRealized
            (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
            (deterministicOracleConfig cfg) T hwd.1 := by
  classical
  have hnear : ∀ k : Fin q, ∃ u : ℕ,
      hit k ≤ u ∧ u ≤ hit k + 1 ∧
        theorem_4_15_periodicCandidateRestartCertificate cfg eta u := by
    intro k
    exact
      theorem_4_15_periodicCandidate_exists_nearby_restartCertificate_of_phase
        cfg eta (hit k) (z k) (hphase k)
  let pick : Fin q → ℕ := fun k => Classical.choose (hnear k)
  have hpick : ∀ k : Fin q,
      hit k ≤ pick k ∧ pick k ≤ hit k + 1 ∧
        theorem_4_15_periodicCandidateRestartCertificate cfg eta (pick k) := by
    intro k
    exact Classical.choose_spec (hnear k)
  apply theorem_4_15_periodicCandidate_block_fraction_stochastic_lower_bound
    cfg eta sigma q blockLength T pick hT hblocks
  · intro k
    exact (hlower k).trans (hpick k).1
  · intro k
    exact (hpick k).2.1.trans_lt (hroom k)
  · intro k
    exact (hpick k).2.2
  · exact hsigma

/- The restarted positive-leg density estimate now transfers to the exact
   stochastic source family.  The well-definedness witness is derived from
   Assumptions 4.13 and 3.3 for the singleton oracle; the conclusion measures
   the same generated expected nuclear-gradient average used by Theorem 4.15. -/
theorem theorem_4_15_periodicCandidate_restarted_window_stochastic_density_lower_bound
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta m0 : ℝ)
    (start T : ℕ) (S : Finset ℕ) (hT : horizonDomain T)
    (hm0 : 0 < m0)
    (hMstart : m0 ≤
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg start).M 0 0)
    (heta : ∀ k, start + k < T → cfg.eta (start + k) = eta)
    (hwindow : ∀ t ∈ S,
      start ≤ t ∧ t < T ∧
        ((t - start : ℕ) : ℝ) * (1 - cfg.beta) * (m0 + 1) < m0 ∧
        ∃ z : ℤ,
          |(theorem_4_5_counterexampleEntry
              (deterministicMomentumMuonState
                theorem_4_15_periodicCandidateObjective cfg start).W -
              ((t - start : ℕ) : ℝ) * eta) - (z : ℝ) * Real.pi| ≤
            Real.pi / 8)
    (sigma : ℝ) (hsigma : 0 ≤ sigma) :
    ∃ hwd : stochasticMuonExpectationsWellDefined
        (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
        (deterministicOracleConfig cfg) T,
      stochasticHessianDirectionalAverageRealized
          (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
          (deterministicOracleConfig cfg) T hwd.2.2.1 =
          deterministicMomentumHessianDirectionalAverage
            theorem_4_15_periodicCandidateObjective cfg T ∧
        ((T : ℝ)⁻¹) * (S.card : ℝ) * ((1 : ℝ) / 2) ≤
        stochasticAverageNuclearGradientRealized
          (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
          (deterministicOracleConfig cfg) T hwd.1 := by
  let hwd := theorem_4_15_periodicCandidate_expectationsWellDefined
    cfg T sigma hsigma
  refine ⟨hwd, ?_, ?_⟩
  · rw [deterministicOracle_hessianDirectionalAverageRealized_eq]
  · rw [deterministicOracle_average_eq]
    exact theorem_4_15_periodicCandidate_restarted_window_density_lower_bound
      cfg eta m0 start T S hT hm0 hMstart heta hwindow

/- The return-leg analogue uses the same singleton-oracle realization.  Thus
   positive- and negative-momentum restart windows can both contribute density
   bounds on one source-level generated family; neither bridge assumes the
   desired average or any cross/`Jstar` estimate. -/
theorem theorem_4_15_periodicCandidate_restarted_negative_window_stochastic_density_lower_bound
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta m0 : ℝ)
    (start T : ℕ) (S : Finset ℕ) (hT : horizonDomain T)
    (hm0 : 0 < m0)
    (hMstart :
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg start).M 0 0 ≤ -m0)
    (heta : ∀ k, start + k < T → cfg.eta (start + k) = eta)
    (hwindow : ∀ t ∈ S,
      start ≤ t ∧ t < T ∧
        ((t - start : ℕ) : ℝ) * (1 - cfg.beta) * (m0 + 1) < m0 ∧
        ∃ z : ℤ,
          |(theorem_4_5_counterexampleEntry
              (deterministicMomentumMuonState
                theorem_4_15_periodicCandidateObjective cfg start).W +
              ((t - start : ℕ) : ℝ) * eta) - (z : ℝ) * Real.pi| ≤
            Real.pi / 8)
    (sigma : ℝ) (hsigma : 0 ≤ sigma) :
    ∃ hwd : stochasticMuonExpectationsWellDefined
        (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
        (deterministicOracleConfig cfg) T,
      stochasticHessianDirectionalAverageRealized
          (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
          (deterministicOracleConfig cfg) T hwd.2.2.1 =
          deterministicMomentumHessianDirectionalAverage
            theorem_4_15_periodicCandidateObjective cfg T ∧
        ((T : ℝ)⁻¹) * (S.card : ℝ) * ((1 : ℝ) / 2) ≤
        stochasticAverageNuclearGradientRealized
          (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
          (deterministicOracleConfig cfg) T hwd.1 := by
  let hwd := theorem_4_15_periodicCandidate_expectationsWellDefined
    cfg T sigma hsigma
  refine ⟨hwd, ?_, ?_⟩
  · rw [deterministicOracle_hessianDirectionalAverageRealized_eq]
  · rw [deterministicOracle_average_eq]
    exact
      theorem_4_15_periodicCandidate_restarted_negative_window_density_lower_bound
        cfg eta m0 start T S hT hm0 hMstart heta hwindow

/- In particular, every index in such a prefix satisfies the concrete
   nonvanishing condition used by the horizon-level scalar reduction.  This is
   a conclusion of the generated recurrence, not an added source assumption. -/
theorem theorem_4_15_periodicCandidate_momentum_ne_zero_on_positive_gradient_prefix
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta : ℝ) (T : ℕ)
    (hW0 : cfg.W0 = (Real.pi / 4) • coordinateMatrix 0 0)
    (hetaNonneg : 0 ≤ eta)
    (heta : ∀ k < T, cfg.eta k = eta)
    (hphase : (T : ℝ) * eta < 3 * Real.pi / 4) :
    ∀ t ∈ Finset.range T,
      (deterministicMomentumMuonState
        theorem_4_15_periodicCandidateObjective cfg t).M ≠ 0 := by
  intro t ht
  have htT : t < T := Finset.mem_range.mp ht
  have htLe : (t : ℝ) ≤ (T : ℝ) := by
    exact_mod_cast (Nat.le_of_lt htT)
  have htPhase : (t : ℝ) * eta < 3 * Real.pi / 4 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right htLe hetaNonneg) hphase
  rcases theorem_4_15_periodicCandidate_positive_gradient_prefix
      cfg eta t hW0 hetaNonneg
      (fun k hk => heta k (lt_trans hk htT)) htPhase with
    ⟨_W, c, hc, hM⟩
  rw [hM]
  exact smul_ne_zero (ne_of_gt hc) (by
    intro hzero
    have hentry := congrArg (fun M : Mat 1 1 => M 0 0) hzero
    norm_num [coordinateMatrix] at hentry)

/- Combining the generated-prefix invariant with the earlier horizon reduction
   removes its auxiliary nonvanishing hypothesis on the entire positive-gradient
   leg.  Both source-relevant quantities are now explicit Riemann-type sums on
   the actual Algorithm 1 orbit, with the same step and the same indices. -/
theorem theorem_4_15_periodicCandidate_positive_gradient_prefix_scalar_reduction
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta : ℝ) (T : ℕ)
    (hW0 : cfg.W0 = (Real.pi / 4) • coordinateMatrix 0 0)
    (hetaNonneg : 0 ≤ eta)
    (heta : ∀ k < T, cfg.eta k = eta)
    (hphase : (T : ℝ) * eta < 3 * Real.pi / 4) :
    deterministicMomentumHessianDirectionalAverage
        theorem_4_15_periodicCandidateObjective cfg T =
        ((T : ℝ)⁻¹) * Finset.sum (Finset.range T) (fun t =>
          -Real.sin (Real.pi / 4 - (t : ℝ) * eta)) ∧
      deterministicMomentumAverageNuclearGradient
        theorem_4_15_periodicCandidateObjective cfg T =
        ((T : ℝ)⁻¹) * Finset.sum (Finset.range T) (fun t =>
          |Real.cos (Real.pi / 4 - (t : ℝ) * eta)|) := by
  have hM :=
    theorem_4_15_periodicCandidate_momentum_ne_zero_on_positive_gradient_prefix
      cfg eta T hW0 hetaNonneg heta hphase
  rcases theorem_4_15_periodicCandidate_fullHorizon_scalar_reduction cfg T hM with
    ⟨hdir, hgrad⟩
  constructor
  · rw [hdir]
    congr 1
    apply Finset.sum_congr rfl
    intro t ht
    have htT : t < T := Finset.mem_range.mp ht
    have htLe : (t : ℝ) ≤ (T : ℝ) := by
      exact_mod_cast (Nat.le_of_lt htT)
    have htPhase : (t : ℝ) * eta < 3 * Real.pi / 4 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right htLe hetaNonneg) hphase
    rcases theorem_4_15_periodicCandidate_positive_gradient_prefix
        cfg eta t hW0 hetaNonneg
        (fun k hk => heta k (lt_trans hk htT)) htPhase with
      ⟨hWt, _c, _hc, _hMt⟩
    rw [hWt]
    simp only [theorem_4_5_counterexampleEntry_apply, Matrix.smul_apply,
      smul_eq_mul, coordinateMatrix, Matrix.single_apply, if_pos, mul_one]
    simp
  · rw [hgrad]
    congr 1
    apply Finset.sum_congr rfl
    intro t ht
    have htT : t < T := Finset.mem_range.mp ht
    have htLe : (t : ℝ) ≤ (T : ℝ) := by
      exact_mod_cast (Nat.le_of_lt htT)
    have htPhase : (t : ℝ) * eta < 3 * Real.pi / 4 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right htLe hetaNonneg) hphase
    rcases theorem_4_15_periodicCandidate_positive_gradient_prefix
        cfg eta t hW0 hetaNonneg
        (fun k hk => heta k (lt_trans hk htT)) htPhase with
      ⟨hWt, _c, _hc, _hMt⟩
    rw [hWt]
    simp only [theorem_4_5_counterexampleEntry_apply, Matrix.smul_apply,
      smul_eq_mul, coordinateMatrix, Matrix.single_apply, if_pos, mul_one]
    simp

/- On every constant-step prefix that remains between phases zero and `pi / 4`,
   the same generated orbit already exhibits the source-relevant separation:
   its signed directional-curvature average is nonpositive, while its nuclear
   gradient average is bounded below by `sqrt 2 / 2`.  This is a genuine
   shrinking-step prefix statement for the fixed bounded-below objective.  It
   does not claim a full-horizon counterexample: the printed horizon is longer
   than this first monotone leg, so recurrence over the subsequent legs remains
   the outstanding obligation. -/
theorem theorem_4_15_periodicCandidate_positive_gradient_prefix_separation
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta : ℝ) (T : ℕ)
    (hT : horizonDomain T)
    (hW0 : cfg.W0 = (Real.pi / 4) • coordinateMatrix 0 0)
    (hetaNonneg : 0 ≤ eta)
    (heta : ∀ k < T, cfg.eta k = eta)
    (htravel : (T : ℝ) * eta ≤ Real.pi / 4) :
    deterministicMomentumHessianDirectionalAverage
          theorem_4_15_periodicCandidateObjective cfg T ≤ 0 ∧
      Real.sqrt 2 / 2 ≤
        deterministicMomentumAverageNuclearGradient
          theorem_4_15_periodicCandidateObjective cfg T := by
  have hphase : (T : ℝ) * eta < 3 * Real.pi / 4 := by
    linarith [Real.pi_pos]
  rcases theorem_4_15_periodicCandidate_positive_gradient_prefix_scalar_reduction
      cfg eta T hW0 hetaNonneg heta hphase with ⟨hdir, hgrad⟩
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hphaseBounds (t : ℕ) (ht : t ∈ Finset.range T) :
      0 ≤ Real.pi / 4 - (t : ℝ) * eta ∧
        Real.pi / 4 - (t : ℝ) * eta ≤ Real.pi / 4 := by
    have htT : t < T := Finset.mem_range.mp ht
    have htLe : (t : ℝ) ≤ (T : ℝ) := by
      exact_mod_cast (Nat.le_of_lt htT)
    have hmul : (t : ℝ) * eta ≤ (T : ℝ) * eta :=
      mul_le_mul_of_nonneg_right htLe hetaNonneg
    have hmulNonneg : 0 ≤ (t : ℝ) * eta :=
      mul_nonneg (by positivity) hetaNonneg
    constructor <;> linarith
  constructor
  · rw [hdir]
    apply mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hTreal.le)
    apply Finset.sum_nonpos
    intro t ht
    have hb := hphaseBounds t ht
    exact neg_nonpos.mpr
      (Real.sin_nonneg_of_nonneg_of_le_pi hb.1 (by linarith [Real.pi_pos]))
  · rw [hgrad]
    have hpoint : ∀ t ∈ Finset.range T,
        Real.sqrt 2 / 2 ≤
          |Real.cos (Real.pi / 4 - (t : ℝ) * eta)| := by
      intro t ht
      have hb := hphaseBounds t ht
      have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
        hb.1 (by linarith [Real.pi_pos]) hb.2
      rw [Real.cos_pi_div_four] at hcos
      rw [abs_of_nonneg (le_trans (by positivity) hcos)]
      exact hcos
    have hsum : (T : ℝ) * (Real.sqrt 2 / 2) ≤
        Finset.sum (Finset.range T) (fun t =>
          |Real.cos (Real.pi / 4 - (t : ℝ) * eta)|) := by
      simpa using Finset.sum_le_sum hpoint
    have hscaled := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hTreal.le)
    calc
      Real.sqrt 2 / 2 = (T : ℝ)⁻¹ * ((T : ℝ) * (Real.sqrt 2 / 2)) := by
        field_simp [ne_of_gt hTreal]
      _ ≤ (T : ℝ)⁻¹ * Finset.sum (Finset.range T) (fun t =>
          |Real.cos (Real.pi / 4 - (t : ℝ) * eta)|) := hscaled

/- The prefix separation is also stated on the exact stochastic source objects.
   The singleton oracle has zero variance, and the expectation witnesses are
   derived from the periodic objective's proved third-derivative regularity.
   This avoids treating a deterministic trajectory as a substitute for the
   generated `stochasticMuonState` family. -/
theorem theorem_4_15_periodicCandidate_positive_gradient_prefix_stochastic_separation
    (cfg : DeterministicMomentumMuonConfig 1 1) (eta : ℝ) (T : ℕ)
    (hT : horizonDomain T)
    (hW0 : cfg.W0 = (Real.pi / 4) • coordinateMatrix 0 0)
    (hetaNonneg : 0 ≤ eta)
    (heta : ∀ k < T, cfg.eta k = eta)
    (htravel : (T : ℝ) * eta ≤ Real.pi / 4) (sigma : ℝ)
    (hsigma : 0 ≤ sigma) :
    ∃ hwd : stochasticMuonExpectationsWellDefined
        (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
        (deterministicOracleConfig cfg) T,
      stochasticHessianDirectionalAverageRealized
          (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
          (deterministicOracleConfig cfg) T hwd.2.2.1 ≤ 0 ∧
        Real.sqrt 2 / 2 ≤
          stochasticAverageNuclearGradientRealized
            (deterministicOracleProblem theorem_4_15_periodicCandidateObjective)
            (deterministicOracleConfig cfg) T hwd.1 := by
  let P := deterministicOracleProblem theorem_4_15_periodicCandidateObjective
  let scfg := deterministicOracleConfig cfg
  have hthird : ThirdDerivativeBounded P.objective 6 := by
    simpa [P, deterministicOracleProblem_objective] using
      theorem_4_15_periodicCandidateObjective_thirdDerivativeBounded
  have hregularity : StochasticObjectiveRegularity P.objective :=
    Or.inr (Or.inr ⟨6, hthird⟩)
  have hvariance : BoundedVariance P sigma := by
    exact deterministicOracleProblem_boundedVariance_of_nonneg
      theorem_4_15_periodicCandidateObjective hsigma
  let hwd : stochasticMuonExpectationsWellDefined P scfg T := ⟨
    stochasticAverageNuclearGradient_wellDefined_of_source_assumptions
      P scfg T sigma hregularity hvariance,
    stochasticExpectedObjectiveDrop_wellDefined_of_source_assumptions
      P scfg T sigma hregularity hvariance,
    stochasticHessianJstar_wellDefined_of_source_assumptions
      P scfg T 6 sigma hthird hvariance⟩
  refine ⟨hwd, ?_, ?_⟩
  · rw [deterministicOracle_hessianDirectionalAverageRealized_eq]
    exact (theorem_4_15_periodicCandidate_positive_gradient_prefix_separation
      cfg eta T hT hW0 hetaNonneg heta htravel).1
  · rw [deterministicOracle_average_eq]
    exact (theorem_4_15_periodicCandidate_positive_gradient_prefix_separation
      cfg eta T hT hW0 hetaNonneg heta htravel).2

/- Exact Track-A target for Appendix B.4 steps 27--28.  This proposition fixes
   one generated Algorithm 1 family and asks for a single coefficient and
   accuracy neighbourhood, uniform in both the printed accuracy and every
   selected horizon satisfying the source-small-J run predicate.  In
   particular, neither the coefficient nor the antecedent contains cross/Jstar
   control or the desired average.  Keeping this target separate from the
   Jstar-conditioned helper prevents the latter from being mistaken for a
   proof of the source implication. -/
private def theorem_4_15_otherwiseSourceSmallJGeneratedAverageTarget
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n)
    (cfgForAccuracyHorizon : ℝ → ℕ → StochasticMuonConfig m n)
    (W0 : Mat m n) (σ Δ C s : ℝ)
    (betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ) : Prop :=
  ∃ K ε₀ : ℝ, 0 < K ∧ 0 < ε₀ ∧
    ∀ ε : ℝ, epsilonDomain ε → ε ≤ ε₀ →
    ∀ N : ℕ,
      theorem_4_15_otherwiseSourceSmallJGeneratedRunForAccuracyHorizon P
          cfgForAccuracyHorizon W0 σ Δ ε C s
          betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N →
        stochasticAverageNuclearGradient P (cfgForAccuracyHorizon ε N) N ≤ K * ε

/- The public generated-process counterexample above negates the exact Track-A
   target, rather than an auxiliary scalar bridge.  In particular, its witness
   uses the same `stochasticMuonState` family and selected horizon quantified by
   this target. -/
private theorem theorem_4_15_otherwiseSourceSmallJGeneratedAverageTarget_false :
    ¬ theorem_4_15_otherwiseSourceSmallJGeneratedAverageTarget
      theorem_4_15_nonperiodicCandidateProblem
      theorem_4_15_nonperiodicCandidateConfigForAccuracyHorizon
      0 theorem_4_15_nonperiodicCandidateSigma
      theorem_4_15_nonperiodicCandidateSigma
      (11 / theorem_4_15_nonperiodicCandidateSigma +
        theorem_4_15_nonperiodicCandidateThirdDerivativeScale /
          (2 * theorem_4_15_nonperiodicCandidateSigma))
      theorem_4_15_nonperiodicCandidateThirdDerivativeScale
      1 1 1 1 1 2 := by
  intro htarget
  rcases htarget with ⟨K, epsilon₀, hK, hepsilon₀, htarget⟩
  obtain ⟨epsilon, hepsilon, hepsilon_le, hrun, havg⟩ :=
    theorem_4_15_nonperiodicCandidate_source_smallJ_counterexample
      K epsilon₀ hepsilon₀
  have hle := htarget epsilon hepsilon hepsilon_le
    (theorem_4_15_nonperiodicCandidateHorizon epsilon) hrun
  exact (not_lt_of_ge hle) havg

theorem theorem_4_15_otherwise_complexity_from_schedule_accuracy
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (σ Δ C s : ℝ)
    (betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ)
    (hfinite : P.objective.HasFiniteInfimum)
    (hDelta : sourceObjectiveInitialGap P.objective cfg.W0 hfinite = Δ)
    (hthird : ThirdDerivativeBounded P.objective s)
    (hvariance : BoundedVariance P σ) :
    ∃ accuracyScale : ℝ, 0 < accuracyScale ∧
      ∀ cfgForAccuracyHorizon : ℝ → ℕ → StochasticMuonConfig m n,
      (∃ ε₀ : ℝ, 0 < ε₀ ∧
        ∀ ε : ℝ, epsilonDomain ε → ε ≤ ε₀ →
        ∃ N : ℕ,
          theorem_4_15_otherwiseReindexedRunRealizedForAccuracyHorizon P
            cfgForAccuracyHorizon cfg.W0 σ Δ C
            betaLower betaUpper etaLower etaUpper horizonLower horizonUpper
            accuracyScale ε N) →
      theorem_4_15_otherwise_branch_rate_and_complexity
        P cfg σ Δ C betaLower betaUpper etaLower etaUpper
          horizonLower horizonUpper accuracyScale cfgForAccuracyHorizon := by
  let r : ℝ := matrixRankBound m n
  let q : ℝ := Real.sqrt (r ^ 3)
  let sr : ℝ := Real.sqrt r
  let K : ℝ :=
    1 / (horizonLower * etaLower * q ^ 2) +
    C * etaUpper * sr * q / (2 * σ ^ 2) +
    2 * Real.sqrt betaUpper +
    2 * r * sr / (betaLower * horizonLower * q) +
    2 * etaUpper * C * q * sr * r / betaLower +
    s * etaUpper ^ 2 * q ^ 3 * Δ ^ 2 / (6 * σ ^ 6) +
    2 * s * etaUpper ^ 2 * q ^ 3 * Δ ^ 2 * r /
      (betaLower * σ ^ 4)
  let accuracyScale : ℝ := |K| + 1
  have hscale : 0 < accuracyScale := by
    dsimp [accuracyScale]
    positivity
  have hone_scale : 1 ≤ accuracyScale := by
    dsimp [accuracyScale]
    exact le_add_of_nonneg_left (abs_nonneg K)
  have hKscale : K ≤ accuracyScale := by
    dsimp [accuracyScale]
    linarith [le_abs_self K]
  refine ⟨accuracyScale, hscale, ?_⟩
  intro cfgForAccuracyHorizon hrunsSmall
  rcases hrunsSmall with ⟨εrun, hεrun, hruns⟩
  obtain ⟨Ntest, hNtest⟩ := hruns εrun hεrun le_rfl
  have hNtest' := hNtest
  unfold theorem_4_15_otherwiseReindexedRunRealizedForAccuracyHorizon
    theorem_4_15_otherwiseRunRealizedForAccuracyHorizon at hNtest'
  dsimp at hNtest'
  rcases hNtest' with
    ⟨_horizonTest, _hwdTest, _hW0Test, _hscheduleTest, _hsourceTest,
      hHorizonTest, _hregimeTest⟩
  have hhorizonUpperPos : 0 < horizonUpper :=
    lt_of_lt_of_le hHorizonTest.1 hHorizonTest.2.1
  let Couter : ℝ := horizonUpper * accuracyScale ^ 3
  have hCouter : 0 < Couter := by
    dsimp [Couter]
    positivity
  unfold theorem_4_15_otherwise_branch_rate_and_complexity
  constructor
  · unfold EpsilonHorizonNuclearStationarityComplexityWithHorizonRateOn
    refine ⟨Couter, min εrun 1, hCouter, lt_min hεrun (by norm_num), ?_, ?_⟩
    · simp [ConstantRespectsScope, theoremScope, hCouter]
    · intro ε hε hεsmall
      have hεrun' : ε ≤ εrun := le_trans hεsmall (min_le_left _ _)
      have hεone : ε ≤ 1 := le_trans hεsmall (min_le_right _ _)
      obtain ⟨N, hN⟩ := hruns ε hε hεrun'
      let delta : ℝ := theorem_4_15_otherwiseScheduleAccuracy accuracyScale ε
      have hdelta : epsilonDomain delta := by
        dsimp [delta]
        exact theorem_4_15_otherwiseScheduleAccuracy_pos hscale hε
      have hdelta_one : delta ≤ 1 := by
        have hdiv_le : ε / accuracyScale ≤ ε / 1 :=
          div_le_div_of_nonneg_left hε.le (by norm_num) hone_scale
        dsimp [delta, theorem_4_15_otherwiseScheduleAccuracy, sourceQuot]
        linarith
      have hNdelta :
          theorem_4_15_otherwiseReindexedRunRealizedForAccuracyHorizon P
            cfgForAccuracyHorizon cfg.W0 σ Δ C
            betaLower betaUpper etaLower etaUpper horizonLower horizonUpper
            1 delta N := by
        simpa [delta, theorem_4_15_otherwiseReindexedRunRealizedForAccuracyHorizon,
          theorem_4_15_otherwiseScheduleAccuracy, sourceQuot] using hN
      have hformula :=
        theorem_4_15_otherwise_source_average_bound_at_schedule_accuracy
          P cfgForAccuracyHorizon cfg.W0 σ Δ C s
          betaLower betaUpper etaLower etaUpper horizonLower horizonUpper
          delta N hfinite hDelta hthird hvariance hdelta_one hNdelta
      have havgRaw := hformula.2
      have haccOne : theorem_4_15_otherwiseScheduleAccuracy 1 delta = delta := by
        simp [theorem_4_15_otherwiseScheduleAccuracy, sourceQuot]
      rw [haccOne] at havgRaw
      have havg :
          theorem_4_15_otherwiseReindexedRunAverageRealized P
              cfgForAccuracyHorizon cfg.W0 σ Δ C
              betaLower betaUpper etaLower etaUpper horizonLower horizonUpper
              accuracyScale ε N hN ≤ K * delta := by
        simpa [theorem_4_15_otherwiseReindexedRunAverageRealized,
          theorem_4_15_otherwiseRunAverageRealized,
          stochasticAverageNuclearGradientRealized,
          stochasticAverageNuclearGradient, realizedExpectation,
          delta, theorem_4_15_otherwiseScheduleAccuracy, sourceQuot,
          K, r, q, sr] using havgRaw
      have hscale_delta : accuracyScale * delta = ε := by
        dsimp [delta, theorem_4_15_otherwiseScheduleAccuracy, sourceQuot]
        field_simp [ne_of_gt hscale]
      have hKdelta : K * delta ≤ accuracyScale * delta :=
        mul_le_mul_of_nonneg_right hKscale hdelta.le
      refine ⟨N, hN, ?_, ?_⟩
      · exact le_trans havg (by simpa [hscale_delta] using hKdelta)
      · dsimp [Couter]
        exact theorem_4_15_otherwise_reindexed_selected_horizon_upper_bound
          P cfgForAccuracyHorizon cfg.W0 σ Δ C
          betaLower betaUpper etaLower etaUpper horizonLower horizonUpper
          accuracyScale ε N hscale hε hN
  · intro ε
    unfold StochasticGeneratedOutputTransferOn
    intro N hN εout havg
    exact stochasticGeneratedOutputGuarantee_of_average_le
      P
      (cfgForAccuracyHorizon
        (theorem_4_15_otherwiseScheduleAccuracy accuracyScale ε) N)
      N hN.1 (Classical.choose hN.2).1 εout havg

theorem theorem_4_15 {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (σ η s : ℝ)
    (_hfinite : P.objective.HasFiniteInfimum)
    (_hthird : ThirdDerivativeBounded P.objective s)
    (_hvariance : BoundedVariance P σ)
    (_hη : ∀ t ∈ Finset.range T, cfg.eta t = η) :
    theorem_4_15_statement P cfg T σ η s _hfinite := by
  constructor
  · exact theorem_4_15_source_domain_obligation
      P cfg T σ η s _hfinite _hthird _hvariance _hη
  · intro hsrc
    rcases theorem_4_15_downstream_phase2_boundary_of_sourceDomain
        P cfg T σ η s _hfinite hsrc _hthird _hvariance _hη with
      ⟨hwd, hdom, _hηpos⟩
    refine ⟨hwd, hdom, ?_⟩
    rcases theorem_4_15_source_formula_bound
        P cfg T s σ η _hfinite hsrc _hthird _hvariance _hη with
      ⟨R, hR, hbound⟩
    refine ⟨⟨R, hR, ?_⟩, ?_⟩
    · rcases hdom with
        ⟨hTdom, hdropdom, hsNoise, hsBatchNoise, hqBatchNoise,
          hsRank, hsBatch, hqTail, hqMomentum⟩
      simpa [stochasticAverageNuclearGradientRealized,
        stochasticAverageNuclearGradient,
        stochasticHessianJstarRealized, stochasticHessianJstar,
        stochasticHessianDirectionalAverageRealized,
        stochasticHessianDirectionalAverage,
        stochasticHessianCrossAverageRealized,
        stochasticHessianCrossAverage, realizedExpectation,
        theorem_4_15_base_rhs, theorem_4_15_sourceBaseRhs,
        realizedSourceQuot, sourceQuot, realizedSourceSqrt, sourceSqrt] using hbound
    · dsimp [theorem_4_15_source_rate_consequences]
      constructor
      · intro hthird hvariance Jstar hpointwise cfgForHorizon hruns
        constructor
        · exact theorem_4_15_positive_branch_rate_from_source_assumptions
            P cfg Jstar σ
              (sourceObjectiveInitialGap P.objective cfg.W0 _hfinite) s
              _hfinite hthird hvariance rfl cfgForHorizon hruns
        · constructor
          · exact theorem_4_15_positive_complexity_witness
              P cfg Jstar σ
                (sourceObjectiveInitialGap P.objective cfg.W0 _hfinite) s
                _hfinite hthird hvariance rfl hpointwise cfgForHorizon hruns
          · unfold StochasticGeneratedOutputTransferOn
            intro N hN ε havg
            exact stochasticGeneratedOutputGuarantee_of_average_le
              P (cfgForHorizon N) N hN.1 (Classical.choose hN.2).1 ε havg
      · intro hthird hvariance C betaLower betaUpper etaLower etaUpper
          horizonLower horizonUpper
        rcases theorem_4_15_otherwise_complexity_from_schedule_accuracy
            P cfg σ (sourceObjectiveInitialGap P.objective cfg.W0 _hfinite) C s
            betaLower betaUpper etaLower etaUpper horizonLower horizonUpper
            _hfinite rfl hthird hvariance with
          ⟨accuracyScale, hscale, hroute⟩
        refine ⟨accuracyScale, hscale, ?_⟩
        intro cfgForAccuracyHorizon hruns
        apply hroute cfgForAccuracyHorizon
        rcases hruns with ⟨epsilon₀, hepsilon₀, hruns⟩
        refine ⟨epsilon₀, hepsilon₀, ?_⟩
        intro epsilon hepsilon hepsilon_le
        rcases hruns epsilon hepsilon hepsilon_le with ⟨N, hN⟩
        exact ⟨N,
          theorem_4_15_otherwise_corrected_source_reindexed_run_to_jstar_run
            P cfgForAccuracyHorizon cfg.W0 σ
            (sourceObjectiveInitialGap P.objective cfg.W0 _hfinite) C s
            betaLower betaUpper etaLower etaUpper horizonLower horizonUpper
            accuracyScale epsilon N hN⟩

/- Remaining formula-level handoff for ordinary reconstruction.  Its intended
   proof must combine the proved positive formula supplier and scalar crossing
   transfer with the proved corrected otherwise formula supplier.  The
   tombstoned coefficient-one declarations are absent from both its statement
   and the compiled environment. -/
theorem theorem_4_16_source_rate_consequences_from_corrected_formula_routes
    {m n : ℕ} (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (Wstar : Mat m n) (s Dop : ℝ) (hfinite : P.HasFiniteInfimum)
    (hstar : StarConvex P Wstar)
    (hthird : ThirdDerivativeBounded P s) :
    theorem_4_16_source_rate_consequences P cfg Wstar s Dop hfinite := by
  dsimp [theorem_4_16_source_rate_consequences]
  constructor
  · intro cfgForHorizon hruns hfamily
    have hboundary := theorem_4_16_positive_full_scale_boundary_of_source_runs
      P cfgForHorizon Wstar cfg.W0
        (sourceObjectiveInitialGap P cfg.W0 hfinite) s Dop hthird hruns
    refine ⟨hboundary, ?_, ?_⟩
    · intro hfull
      have hdisplay := theorem_4_16_positive_formula_to_displayed_family
        P cfgForHorizon Wstar cfg.W0
          (sourceObjectiveInitialGap P cfg.W0 hfinite) s Dop
          hfinite rfl hstar hthird
      have hlogEnvelope := theorem_4_16_positive_log_envelope_of_source_runs
        P cfgForHorizon Wstar cfg.W0
          (sourceObjectiveInitialGap P cfg.W0 hfinite) s Dop
          hfull hruns hfamily
      exact theorem_4_16_positive_display_to_tilde_rate
        P cfgForHorizon Wstar cfg.W0
          (sourceObjectiveInitialGap P cfg.W0 hfinite) s Dop
          hfinite hthird hfamily hdisplay hlogEnvelope
    · intro hcrossing
      exact theorem_4_16_positive_scalar_crossing_transfer
        P cfg cfgForHorizon Wstar
          (sourceObjectiveInitialGap P cfg.W0 hfinite) s Dop
          hfinite hstar hthird rfl hcrossing
  · intro cfgForHorizon hruns hfamily
    have hdisplay := theorem_4_16_otherwise_formula_to_corrected_displayed_family
      P cfgForHorizon Wstar cfg.W0
        (sourceObjectiveInitialGap P cfg.W0 hfinite) s Dop
        hfinite rfl hstar hthird hfamily
    have hlogEnvelope := theorem_4_16_otherwise_log_envelope_of_source_runs
      P cfgForHorizon Wstar cfg.W0
        (sourceObjectiveInitialGap P cfg.W0 hfinite) s Dop hthird hruns
    have hquad := theorem_4_16_otherwise_corrected_display_quadratic_bound
      P cfg cfgForHorizon Wstar
        (sourceObjectiveInitialGap P cfg.W0 hfinite) s Dop
        hfinite hthird hfamily hdisplay hlogEnvelope
    constructor
    · exact ⟨2, hquad⟩
    · exact theorem_4_16_otherwise_quadratic_bound_to_complexity
        P cfgForHorizon Wstar cfg.W0
          (sourceObjectiveInitialGap P cfg.W0 hfinite) s Dop
          hfinite hthird hruns hquad

theorem theorem_4_16 {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (T : ℕ) (Wstar : Mat m n) (s η Dop : ℝ)
    (_hfinite : P.HasFiniteInfimum)
    (_hstar : StarConvex P Wstar)
    (_hthird : ThirdDerivativeBounded P s)
    (_hbounded : BoundedOperatorDistance P cfg T Wstar Dop)
    (_hη : ∀ t ∈ Finset.range T, cfg.eta t = η) :
    theorem_4_16_statement P cfg T Wstar s η Dop _hfinite := by
  dsimp [theorem_4_16_statement]
  refine ⟨theorem_4_16_source_domain_obligation
    P cfg T s η Dop _hfinite, ?_, ?_, ?_, ?_, ?_⟩
  · intro hsrc
    have hdown := theorem_4_16_downstream_phase2_boundary_of_sourceDomain
      P cfg T s η Dop _hfinite hsrc
    rcases hdown with ⟨hdom, _hηpos, _hηle⟩
    refine ⟨hdom, ?_⟩
    rw [theorem_4_16_rhs_eq_sourceRhs]
    exact theorem_4_16_source_formula_bound_at_horizon
      P cfg T Wstar s η Dop _hfinite _hstar _hthird _hbounded hsrc _hη
  · intro hsrc
    have hq : 0 ≤ 1 - η / Dop :=
      (theorem_4_16_contraction_of_sourceDomain hsrc).1
    have hqle : 1 - η / Dop ≤ 1 :=
      (theorem_4_16_contraction_of_sourceDomain hsrc).2.le
    have hpowle : ∀ k : ℕ, (1 - η / Dop) ^ k ≤ 1 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [pow_succ]
          nlinarith [pow_nonneg hq k]
    unfold hessianDirectionalWeightedAverage
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg T))
    apply Finset.sum_le_sum
    intro t ht
    calc
      (1 - η / Dop) ^ (T - 1 - t) * hessianDirectionalTerm P cfg t ≤
          |(1 - η / Dop) ^ (T - 1 - t) * hessianDirectionalTerm P cfg t| :=
        le_abs_self _
      _ = (1 - η / Dop) ^ (T - 1 - t) *
          |hessianDirectionalTerm P cfg t| := by
        rw [abs_mul, abs_of_nonneg (pow_nonneg hq _)]
      _ ≤ |hessianDirectionalTerm P cfg t| := by
        simpa [one_mul] using mul_le_mul_of_nonneg_right
          (hpowle (T - 1 - t)) (abs_nonneg (hessianDirectionalTerm P cfg t))
  · intro _hregDom _hregime hlog hschedule
    have hzero : 0 ∈ Finset.range T := Finset.mem_range.mpr hlog.1
    have hetaEq : η = theorem_4_16_logEtaRealized T
        (sourceObjectiveInitialGap P cfg.W0 _hfinite)
        (hessianDirectionalWeightedAverage P cfg T η Dop) Dop hlog :=
      (_hη 0 hzero).symm.trans (hschedule 0 hzero)
    have hsrc : theorem_4_16_sourceDomain T η Dop := by
      refine ⟨hlog.1, ?_, ?_⟩
      · rw [hetaEq]
        exact theorem_4_16_logEtaRealized_pos T
          (sourceObjectiveInitialGap P cfg.W0 _hfinite)
          (hessianDirectionalWeightedAverage P cfg T η Dop) Dop hlog
      · rw [hetaEq]
        exact theorem_4_16_logEtaRealized_le T
          (sourceObjectiveInitialGap P cfg.W0 _hfinite)
          (hessianDirectionalWeightedAverage P cfg T η Dop) Dop hlog
    have hformula := theorem_4_16_source_formula_bound_at_horizon
      P cfg T Wstar s η Dop _hfinite _hstar _hthird _hbounded
        hsrc _hη
    have hgap_nonneg :
        0 ≤ sourceObjectiveInitialGap P cfg.W0 _hfinite := by
      unfold sourceObjectiveInitialGap Objective.sourceFStar
      have hinf : P.fStar ≤ P.f cfg.W0 := by
        simpa [Objective.fStar] using
          (csInf_le _hfinite
            (show P.f cfg.W0 ∈ Set.range P.f from ⟨cfg.W0, rfl⟩))
      linarith
    have hJ : 0 ≤ hessianDirectionalWeightedAverage P cfg T η Dop := by
      have hquotpos := hlog.2.2.1.2
      have hnum_nonneg :
          0 ≤ (T : ℝ) * sourceObjectiveInitialGap P cfg.W0 _hfinite :=
        mul_nonneg (Nat.cast_nonneg _) hgap_nonneg
      rcases (div_pos_iff.mp (by simpa [sourceQuot] using hquotpos)) with
        ⟨_hnumpos, hdenpos⟩ | ⟨hnumneg, _hdenneg⟩
      · have hDopSq : 0 < Dop ^ 2 := sq_pos_of_pos hlog.2.1
        rcases mul_pos_iff.mp hdenpos with hpos | hneg
        · exact hpos.2.le
        · exact False.elim (not_lt_of_ge hDopSq.le hneg.1)
      · exact False.elim (not_lt_of_ge hnum_nonneg hnumneg)
    have hs : 0 ≤ s := le_trans (norm_nonneg _) (_hthird.bound cfg.W0)
    have hsub := theorem_4_16_positive_schedule_substitution m n T
      (sourceObjectiveInitialGap P cfg.W0 _hfinite)
      (hessianDirectionalWeightedAverage P cfg T η Dop) s Dop hlog
      hgap_nonneg hJ hs
    calc
      sourceObjectiveGapAt P cfg T _hfinite ≤
          theorem_4_16_sourceRhs P cfg T
            (sourceObjectiveInitialGap P cfg.W0 _hfinite)
            (hessianDirectionalWeightedAverage P cfg T η Dop) s η Dop := hformula
      _ = theorem_4_16_sourceRhs (Objective.mk fun _ : Mat m n => 0)
          { W0 := 0, eta := fun _ => 0 } T
          (sourceObjectiveInitialGap P cfg.W0 _hfinite)
          (hessianDirectionalWeightedAverage P cfg T η Dop) s
          (theorem_4_16_logEtaRealized T
            (sourceObjectiveInitialGap P cfg.W0 _hfinite)
            (hessianDirectionalWeightedAverage P cfg T η Dop) Dop hlog) Dop := by
        exact congrArg (fun step => theorem_4_16_sourceRhs P cfg T
          (sourceObjectiveInitialGap P cfg.W0 _hfinite)
          (hessianDirectionalWeightedAverage P cfg T η Dop) s step Dop) hetaEq
      _ ≤ theorem_4_16_positiveDisplayedBound m n T
          (sourceObjectiveInitialGap P cfg.W0 _hfinite)
          (hessianDirectionalWeightedAverage P cfg T η Dop) s Dop := hsub
  · intro _hregDom _hregime hlog hschedule
    have hzero : 0 ∈ Finset.range T := Finset.mem_range.mpr hlog.1
    have hetaEq : η = theorem_4_16_otherwiseLogEtaRealized m n T
        (sourceObjectiveInitialGap P cfg.W0 _hfinite) s Dop hlog :=
      (_hη 0 hzero).symm.trans (hschedule 0 hzero)
    have hsrc : theorem_4_16_sourceDomain T η Dop := by
      refine ⟨hlog.1, ?_, ?_⟩
      · rw [hetaEq]
        exact theorem_4_16_otherwiseLogEtaRealized_pos m n T
          (sourceObjectiveInitialGap P cfg.W0 _hfinite) s Dop hlog
      · rw [hetaEq]
        exact theorem_4_16_otherwiseLogEtaRealized_le m n T
          (sourceObjectiveInitialGap P cfg.W0 _hfinite) s Dop hlog
    have hformula := theorem_4_16_source_formula_bound_at_horizon
      P cfg T Wstar s η Dop _hfinite _hstar _hthird _hbounded
        hsrc _hη
    calc
      sourceObjectiveGapAt P cfg T _hfinite ≤
          theorem_4_16_sourceRhs P cfg T
            (sourceObjectiveInitialGap P cfg.W0 _hfinite)
            (hessianDirectionalWeightedAverage P cfg T η Dop) s η Dop := hformula
      _ = theorem_4_16_sourceRhs P cfg T
          (sourceObjectiveInitialGap P cfg.W0 _hfinite)
          (hessianDirectionalWeightedAverage P cfg T η Dop) s
          (theorem_4_16_otherwiseLogEtaRealized m n T
            (sourceObjectiveInitialGap P cfg.W0 _hfinite) s Dop hlog) Dop := by
        exact congrArg (fun step => theorem_4_16_sourceRhs P cfg T
          (sourceObjectiveInitialGap P cfg.W0 _hfinite)
          (hessianDirectionalWeightedAverage P cfg T η Dop) s step Dop) hetaEq
  · exact theorem_4_16_source_rate_consequences_from_corrected_formula_routes
      P cfg Wstar s Dop _hfinite _hstar _hthird

theorem muon_all_main_results :
    (∀ (m n : ℕ) (P : Objective m n) (ε : ℝ) (W : Mat m n),
      (IsNuclearStationary P ε W → IsFrobeniusStationary P ε W) ∧
        (IsFrobeniusStationary P ε W →
          IsNuclearStationary P (Real.sqrt (matrixRankBound m n : ℝ) * ε) W)) ∧
    (∀ (ξ : Type*) [MeasurableSpace ξ] (m n : ℕ)
      (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
      (T : ℕ) (L σ η : ℝ),
      (∀ t ∈ Finset.range T, cfg.eta t = η) →
        FrobeniusSmooth P.objective L → BoundedVariance P σ →
          theorem_4_1_statement P cfg T L σ η) ∧
    (∀ (ξ : Type*) [MeasurableSpace ξ] (m n : ℕ)
      (P : StochasticProblem ξ m n) (W0 : Mat m n) (L σ : ℝ),
      (hfinite : P.objective.HasFiniteInfimum) → FrobeniusSmooth P.objective L →
        BoundedVariance P σ → corollary_4_2_statement P W0 L σ hfinite) ∧
    (∀ (m n : ℕ) (P : Objective m n) (cfg : DeterministicMuonConfig m n)
      (T : ℕ) (Wstar : Mat m n) (L Dop η : ℝ),
      (hfinite : P.HasFiniteInfimum) → StarConvex P Wstar → FrobeniusSmooth P L →
        BoundedOperatorDistance P cfg T Wstar Dop →
          (∀ t ∈ Finset.range T, cfg.eta t = η) →
            theorem_4_5_statement P cfg T Wstar L Dop η hfinite) ∧
    (∀ (m n : ℕ) (P : Objective m n) (cfg : DeterministicMuonConfig m n)
      (t : ℕ) (Wstar : Mat m n) (L Dop : ℝ),
      (hfinite : P.HasFiniteInfimum) → StarConvex P Wstar → FrobeniusSmooth P L →
        BoundedOperatorDistance P cfg t Wstar Dop →
          theorem_4_6_adaptiveSchedule P cfg t L →
            theorem_4_6_statement P cfg t Wstar L Dop hfinite) ∧
    (∀ (ξ : Type*) [MeasurableSpace ξ] (m n : ℕ)
      (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
      (T : ℕ) (Lstar σ η : ℝ),
      (∀ t ∈ Finset.range T, cfg.eta t = η) →
        SpectralSmooth P.objective Lstar → BoundedVariance P σ →
          theorem_4_7_statement P cfg T Lstar σ η) ∧
    (∀ (ξ : Type*) [MeasurableSpace ξ] (m n : ℕ)
      (P : StochasticProblem ξ m n) (W0 : Mat m n) (Lstar σ : ℝ),
      (hfinite : P.objective.HasFiniteInfimum) → SpectralSmooth P.objective Lstar →
        BoundedVariance P σ → corollary_4_8_statement P W0 Lstar σ hfinite) ∧
    (∀ (m n : ℕ) (P : Objective m n) (cfg : DeterministicMuonConfig m n)
      (T : ℕ) (Wstar : Mat m n) (Lstar Dop η : ℝ),
      (hfinite : P.HasFiniteInfimum) → StarConvex P Wstar → SpectralSmooth P Lstar →
        BoundedOperatorDistance P cfg T Wstar Dop →
          (∀ t ∈ Finset.range T, cfg.eta t = η) →
            theorem_4_9_statement P cfg T Wstar Lstar Dop η hfinite) ∧
    (∀ (m n : ℕ) (P : Objective m n) (cfg : DeterministicMuonConfig m n)
      (t : ℕ) (Wstar : Mat m n) (Lstar Dop : ℝ),
      (hfinite : P.HasFiniteInfimum) → StarConvex P Wstar → SpectralSmooth P Lstar →
        BoundedOperatorDistance P cfg t Wstar Dop →
          theorem_4_10_adaptiveSchedule P cfg t Lstar →
            theorem_4_10_statement P cfg t Wstar Lstar Dop hfinite) ∧
    (∀ (m n : ℕ) (P : Objective m n) (Λ : Mat n n),
      LambdaSmooth P Λ →
        FrobeniusSmooth P (spectralNorm Λ) ∧ SpectralSmooth P (nuclearNorm Λ)) ∧
    (∀ (m n : ℕ) (P : Objective m n) (cfg : DeterministicMuonConfig m n)
      (T : ℕ) (s η : ℝ),
      (hfinite : P.HasFiniteInfimum) → ThirdDerivativeBounded P s →
        (∀ t ∈ Finset.range T, cfg.eta t = η) →
        theorem_4_14_statement P cfg T s η hfinite) ∧
    (∀ (ξ : Type*) [MeasurableSpace ξ] (m n : ℕ)
      (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
      (T : ℕ) (σ η s : ℝ),
      (hfinite : P.objective.HasFiniteInfimum) → ThirdDerivativeBounded P.objective s →
        BoundedVariance P σ →
        (∀ t ∈ Finset.range T, cfg.eta t = η) →
          theorem_4_15_statement P cfg T σ η s hfinite) ∧
    (∀ (m n : ℕ) (P : Objective m n) (cfg : DeterministicMuonConfig m n)
      (T : ℕ) (Wstar : Mat m n) (s η Dop : ℝ),
      (hfinite : P.HasFiniteInfimum) → StarConvex P Wstar → ThirdDerivativeBounded P s →
        BoundedOperatorDistance P cfg T Wstar Dop →
          (∀ t ∈ Finset.range T, cfg.eta t = η) →
            theorem_4_16_statement P cfg T Wstar s η Dop hfinite) := by
  exact ⟨
    (fun m n P ε W => proposition_3_6 P ε W),
    (fun ξ _ m n P cfg T L σ η hη hsmooth hvariance =>
      theorem_4_1 P cfg T L σ η hη hsmooth hvariance),
    (fun ξ _ m n P W0 L σ hfinite hsmooth hvariance =>
      corollary_4_2 P W0 L σ hfinite hsmooth hvariance),
    (fun m n P cfg T Wstar L Dop η hfinite hstar hsmooth hbounded hη =>
      theorem_4_5 P cfg T Wstar L Dop η hfinite hstar hsmooth hbounded hη),
    (fun m n P cfg t Wstar L Dop hfinite hstar hsmooth hbounded hη =>
      theorem_4_6 P cfg t Wstar L Dop hfinite hstar hsmooth hbounded hη),
    (fun ξ _ m n P cfg T Lstar σ η hη hsmooth hvariance =>
      theorem_4_7 P cfg T Lstar σ η hη hsmooth hvariance),
    (fun ξ _ m n P W0 Lstar σ hfinite hsmooth hvariance =>
      corollary_4_8 P W0 Lstar σ hfinite hsmooth hvariance),
    (fun m n P cfg T Wstar Lstar Dop η hfinite hstar hsmooth hbounded hη =>
      theorem_4_9 P cfg T Wstar Lstar Dop η hfinite hstar hsmooth hbounded hη),
    (fun m n P cfg t Wstar Lstar Dop hfinite hstar hsmooth hbounded hη =>
      theorem_4_10 P cfg t Wstar Lstar Dop hfinite hstar hsmooth hbounded hη),
    (fun m n P Λ hΛ => lemma_4_12 P Λ hΛ),
    (fun m n P cfg T s η hfinite hthird hη =>
      theorem_4_14 P cfg T s η hfinite hthird hη),
    (fun ξ _ m n P cfg T σ η s hfinite hthird hvariance hη =>
      theorem_4_15 P cfg T σ η s hfinite hthird hvariance hη),
    (fun m n P cfg T Wstar s η Dop hfinite hstar hthird hbounded hη =>
      theorem_4_16 P cfg T Wstar s η Dop hfinite hstar hthird hbounded hη)⟩

end SGD.Muon

end
