import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ENNReal.Basic
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Probability.Process.Filtration
import SOptLib.Glue.Calculus
import SOptLib.Glue.Martingale
import SOptLib.Model.ConditionalExpectation
import SOptLib.Model.Iterates
import SOptLib.Model.NetworkMatrix
import Algorithms.Unverified.GeneralPushPull.Part002
import Algorithms.Unverified.GeneralPushPull.Part003.Part001

noncomputable section

open scoped BigOperators InnerProductSpace Matrix
open MeasureTheory

namespace Algorithms.Unverified.GeneralPushPull

/-! # General Push--Pull: source-facing object model

This file models the fixed algorithm in `book/GeneralPushPull/GeneralPushPull.json`.
The network is deterministic and horizon-independent by construction. An oracle
table and every algorithm state are derived below; neither is supplied as a witness.
-/

variable {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 5000000
set_option maxHeartbeats 1000000

/-- The source's finite `Z_m` bootstrap.  It inserts the genuine forced-fast
estimate at every prefix into the unrolled slow recurrence, absorbs the final
weighted maximum, and immediately substitutes the absorbed estimate back into
the fast bound. -/
theorem actual_quadratic_slow_fast_Zmax_decay
    (N : NetworkSetup n) (M s Lq : ℝ)
    (hM : 1 ≤ M) (hs : 0 < s) (hLq : 0 ≤ Lq)
    (K0 J0 B0 : ℝ) (hK0 : 0 ≤ K0) (hJ0 : 0 ≤ J0)
    (hB0 : 0 ≤ B0)
    (hK : ∀ (t : ℕ) (E K : Fin n → ℝ),
      dotProduct (absoluteProbability N t) E = 0 →
      (∑ i, K i) = 0 →
      |actualQuadraticCorrectedLift N t (E, K)| ≤
        K0 * (nodeSupNorm E + nodeL1Norm K))
    (hJ : ∀ (t : ℕ) (E K : Fin n → ℝ),
      nodeSupNorm (loadingFastPerturbationInput N t E K).1 +
          nodeL1Norm (loadingFastPerturbationInput N t E K).2 ≤
        J0 * (nodeSupNorm E + nodeL1Norm K))
    (hB : ∀ (t : ℕ) (z : ℝ),
      nodeSupNorm (loadingFastCenterInput N t z).1 +
          nodeL1Norm (loadingFastCenterInput N t z).2 ≤ B0 * |z|)
    (htriangular : ∀ (k t : ℕ), k ≤ t → ∀ (E K : Fin n → ℝ),
      dotProduct (absoluteProbability N k) E = 0 →
      (∑ i, K i) = 0 →
      nodeSupNorm (forwardProduct N.rowMix t k *ᵥ E) +
          nodeL1Norm
            (forwardProduct N.colMix t k *ᵥ K +
              ∑ q ∈ Finset.Ico k t,
                forwardProduct N.colMix t (q + 1) *ᵥ
                  ((N.colMix q - 1) *ᵥ
                    (forwardProduct N.rowMix q k *ᵥ E))) ≤
        M * loadingFastRate N ^ (t - k) *
          (nodeSupNorm E + nodeL1Norm K)) :
    ∀ (hfastCap : loadingFastRate N +
          M * (s * J0 + s ^ 2 * B0 * K0) ≤ loadingTransverseRate N)
        (hp : 0 ≤ 1 - s * gainFloor N / 2)
        (hq : 0 < 1 - gainFloor N * s / 4)
        (hrateq : loadingTransverseRate N <
          1 - gainFloor N * s / 4)
        (hg : 0 < gainFloor N)
        (hthetaHalf :
          4 * s ^ 2 * Lq * M * B0 /
              (gainFloor N *
                ((1 - gainFloor N * s / 4) -
                  loadingTransverseRate N)) ≤ 1 / 2)
        (z : ℕ → ℝ)
        (F : ℕ → (Fin n → ℝ) × (Fin n → ℝ)) (k m : ℕ),
        dotProduct (absoluteProbability N k) (F k).1 = 0 →
        (∑ i, (F k).2 i) = 0 →
        (∀ t, k ≤ t →
          F (t + 1) = actualQuadraticHomogeneousFastStep N s t (F t) -
            loadingFastScale s (loadingFastCenterInput N t (z t))) →
        (∀ t, k ≤ t →
          |z (t + 1)| ≤
            (1 - s * gainFloor N / 2) * |z t| +
              s ^ 2 * Lq *
                (nodeSupNorm (F t).1 + nodeL1Norm (F t).2)) →
        let q := 1 - gainFloor N * s / 4
        let G : ℕ → ℝ := fun t =>
          nodeSupNorm (F t).1 + nodeL1Norm (F t).2
        let A := |z k| + s ^ 2 * Lq * M /
          (q - loadingTransverseRate N) * G k
        |z (k + m)| ≤ 2 * A * q ^ m ∧
          G (k + m) ≤
            M * loadingTransverseRate N ^ m * G k +
              (s * M * B0 / (q - loadingTransverseRate N)) *
                (2 * A) * q ^ m := by
  have hfast := actual_quadratic_forced_fast_Zmax_bound
    N M s hM hs.le K0 J0 B0 hK0 hJ0 hB0 hK hJ hB htriangular
  intro hfastCap hp hq hrateq hg hthetaHalf z F k m
    hFcenter hFzero hFstep hslow
  dsimp only
  let q : ℝ := 1 - gainFloor N * s / 4
  let p : ℝ := 1 - s * gainFloor N / 2
  let G : ℕ → ℝ := fun t =>
    nodeSupNorm (F t).1 + nodeL1Norm (F t).2
  let u : ℕ → ℝ := fun i => |z (k + i)| / q ^ i
  have hq' : 0 < q := by simpa [q] using hq
  have hp' : 0 ≤ p := by simpa [p] using hp
  have hpq : p < q := by
    dsimp [p, q]
    have hsg : 0 < s * gainFloor N := mul_pos hs hg
    nlinarith
  have hrateq' : loadingTransverseRate N < q := by
    simpa [q] using hrateq
  have hgap : 0 < q - loadingTransverseRate N := sub_pos.mpr hrateq'
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM
  have hG : ∀ t, 0 ≤ G t := by
    intro t
    dsimp [G]
    exact add_nonneg (nodeSupNorm_nonneg N (F t).1)
      (Finset.sum_nonneg fun i _ => abs_nonneg ((F t).2 i))
  have hunroll (i : ℕ) :
      |z (k + i)| ≤ p ^ i * |z k| +
        (s ^ 2 * Lq) * ∑ j ∈ Finset.range i,
          p ^ (i - j - 1) * G (k + j) := by
    apply abs_slow_recurrence_geometric_unroll z G k p (s ^ 2 * Lq)
      hp' (mul_nonneg (sq_nonneg s) hLq) hG
    intro t hkt
    simpa [p, G] using hslow t hkt
  have hS : ((Finset.range (m + 1)).image u).Nonempty := by
    exact ⟨u 0, Finset.mem_image.mpr ⟨0, by simp, rfl⟩⟩
  let Zm := ((Finset.range (m + 1)).image u).max' hS
  have hZm0 : 0 ≤ Zm := by
    have hu0 : 0 ≤ u 0 := by dsimp [u]; positivity
    exact hu0.trans (Finset.le_max' _ _
      (Finset.mem_image.mpr ⟨0, by simp, rfl⟩))
  have hfastPrefix (j : ℕ) (hj : j ∈ Finset.range (m + 1)) :
      G (k + j) ≤
        M * loadingTransverseRate N ^ j * G k +
          (s * M * B0 / (q - loadingTransverseRate N)) * Zm * q ^ j := by
    have hSj : ((Finset.range (j + 1)).image u).Nonempty := by
      exact ⟨u 0, Finset.mem_image.mpr ⟨0, by simp, rfl⟩⟩
    have hjraw := hfast q hq' hrateq' hfastCap z F k j
      hFcenter hFzero hFstep hSj
    have hpref : ((Finset.range (j + 1)).image u).max' hSj ≤ Zm := by
      have hmem := Finset.max'_mem ((Finset.range (j + 1)).image u) hSj
      obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp hmem
      rw [← hae]
      apply Finset.le_max'
      apply Finset.mem_image.mpr
      refine ⟨a, ?_, rfl⟩
      have haj : a < j + 1 := Finset.mem_range.mp ha
      have hjm : j < m + 1 := Finset.mem_range.mp hj
      exact Finset.mem_range.mpr (by omega)
    have hcoef : 0 ≤ s * M * B0 / (q - loadingTransverseRate N) := by
      exact div_nonneg (mul_nonneg (mul_nonneg hs.le hM0) hB0) hgap.le
    change G (k + j) ≤
      M * loadingTransverseRate N ^ j * G k +
        (s * M * B0 / (q - loadingTransverseRate N)) * Zm * q ^ j
    calc
      G (k + j) ≤
          M * loadingTransverseRate N ^ j * G k +
            (s * M * B0 / (q - loadingTransverseRate N)) *
              ((Finset.range (j + 1)).image u).max' hSj * q ^ j := by
        simpa [G, u] using hjraw
      _ ≤ M * loadingTransverseRate N ^ j * G k +
            (s * M * B0 / (q - loadingTransverseRate N)) * Zm * q ^ j := by
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpref hcoef)
            (pow_nonneg hq'.le j))
  have hpoint : ∀ (hS' : ((Finset.range (m + 1)).image u).Nonempty)
      (i : ℕ), i ∈ Finset.range (m + 1) →
      u i ≤
        (|z k| + s ^ 2 * Lq * M /
          (q - loadingTransverseRate N) * G k) +
        (4 * s ^ 2 * Lq * M * B0 /
          (gainFloor N * (q - loadingTransverseRate N))) *
          ((Finset.range (m + 1)).image u).max' hS' := by
    intro hS' i hi
    have hS_eq : ((Finset.range (m + 1)).image u).max' hS' = Zm := by
      dsimp [Zm]
    rw [hS_eq]
    have hraw := hunroll i
    have hsum :
        (∑ j ∈ Finset.range i, p ^ (i - j - 1) * G (k + j)) ≤
          M * G k * (q ^ i / (q - loadingTransverseRate N)) +
            (s * M * B0 / (q - loadingTransverseRate N)) * Zm *
              (q ^ i / (q - p)) := by
      have hjmem (j : ℕ) (hj : j ∈ Finset.range i) :
          j ∈ Finset.range (m + 1) := by
        have hji := Finset.mem_range.mp hj
        have him := Finset.mem_range.mp hi
        exact Finset.mem_range.mpr (by omega)
      have hterm :
          (∑ j ∈ Finset.range i, p ^ (i - j - 1) * G (k + j)) ≤
            ∑ j ∈ Finset.range i, p ^ (i - j - 1) *
              (M * loadingTransverseRate N ^ j * G k +
                (s * M * B0 / (q - loadingTransverseRate N)) *
                  Zm * q ^ j) := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hfastPrefix j (hjmem j hj))
          (pow_nonneg hp' _)
      have hp_le_q : p ≤ q := hpq.le
      have hhom :
          (∑ j ∈ Finset.range i,
            p ^ (i - j - 1) * loadingTransverseRate N ^ j) ≤
            q ^ i / (q - loadingTransverseRate N) := by
        calc
          _ ≤ ∑ j ∈ Finset.range i,
              q ^ (i - j - 1) * loadingTransverseRate N ^ j := by
            apply Finset.sum_le_sum
            intro j hj
            exact mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ hp' hp_le_q _)
              (pow_nonneg
                (by
                  unfold loadingTransverseRate loadingFastRate
                    loadingTriangularRate
                  linarith [mixingRate_nonneg N]) j)
          _ = ∑ j ∈ Finset.range i,
              loadingTransverseRate N ^ (i - j - 1) * q ^ j :=
            sum_range_geometric_convolution_comm
              (loadingTransverseRate N) q i
          _ ≤ q ^ i / (q - loadingTransverseRate N) :=
            sum_range_separated_geometric_convolution_le
              (loadingTransverseRate N) q
              (by
                unfold loadingTransverseRate loadingFastRate
                  loadingTriangularRate
                linarith [mixingRate_nonneg N]) hrateq' i
      have hfeedback :
          (∑ j ∈ Finset.range i, p ^ (i - j - 1) * q ^ j) ≤
            q ^ i / (q - p) :=
        sum_range_separated_geometric_convolution_le p q hp' hpq i
      calc
        _ ≤ ∑ j ∈ Finset.range i, p ^ (i - j - 1) *
              (M * loadingTransverseRate N ^ j * G k +
                (s * M * B0 / (q - loadingTransverseRate N)) *
                  Zm * q ^ j) := hterm
        _ = M * G k *
              (∑ j ∈ Finset.range i,
                p ^ (i - j - 1) * loadingTransverseRate N ^ j) +
            (s * M * B0 / (q - loadingTransverseRate N)) * Zm *
              (∑ j ∈ Finset.range i,
                p ^ (i - j - 1) * q ^ j) := by
          simp only [mul_add, Finset.sum_add_distrib]
          rw [Finset.mul_sum, Finset.mul_sum]
          congr 1 <;> apply Finset.sum_congr rfl <;> intro j hj <;> ring
        _ ≤ M * G k * (q ^ i / (q - loadingTransverseRate N)) +
            (s * M * B0 / (q - loadingTransverseRate N)) * Zm *
              (q ^ i / (q - p)) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hhom (mul_nonneg hM0 (hG k)))
            (mul_le_mul_of_nonneg_left hfeedback
              (mul_nonneg
                (div_nonneg (mul_nonneg (mul_nonneg hs.le hM0) hB0)
                  hgap.le) hZm0))
    have hpqi : p ^ i ≤ q ^ i := pow_le_pow_left₀ hp' hpq.le _
    have hqpow : 0 < q ^ i := pow_pos hq' _
    have habs : |z (k + i)| ≤
        ((|z k| + s ^ 2 * Lq * M /
            (q - loadingTransverseRate N) * G k) +
          (4 * s ^ 2 * Lq * M * B0 /
            (gainFloor N * (q - loadingTransverseRate N))) * Zm) *
          q ^ i := by
      calc
        |z (k + i)| ≤ p ^ i * |z k| +
            (s ^ 2 * Lq) *
              (M * G k * (q ^ i / (q - loadingTransverseRate N)) +
                (s * M * B0 / (q - loadingTransverseRate N)) * Zm *
                  (q ^ i / (q - p))) :=
          hraw.trans (add_le_add le_rfl
            (mul_le_mul_of_nonneg_left hsum
              (mul_nonneg (sq_nonneg s) hLq)))
        _ ≤ q ^ i * |z k| +
            (s ^ 2 * Lq) *
              (M * G k * (q ^ i / (q - loadingTransverseRate N)) +
                (s * M * B0 / (q - loadingTransverseRate N)) * Zm *
                  (q ^ i / (q - p))) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right hpqi (abs_nonneg _)) le_rfl
        _ = ((|z k| + s ^ 2 * Lq * M /
              (q - loadingTransverseRate N) * G k) +
            (4 * s ^ 2 * Lq * M * B0 /
              (gainFloor N * (q - loadingTransverseRate N))) * Zm) *
            q ^ i := by
          have hqp : q - p = s * gainFloor N / 4 := by
            dsimp [q, p]
            ring
          rw [hqp]
          field_simp [hs.ne', hg.ne', hgap.ne']
          ring
    have hdiv := (div_le_iff₀ hqpow).2 habs
    simpa [u] using hdiv
  let A : ℝ := |z k| + s ^ 2 * Lq * M /
    (q - loadingTransverseRate N) * G k
  let theta : ℝ := 4 * s ^ 2 * Lq * M * B0 /
    (gainFloor N * (q - loadingTransverseRate N))
  have hA : 0 ≤ A := by
    dsimp [A]
    exact add_nonneg (abs_nonneg _)
      (mul_nonneg
        (div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg s) hLq) hM0)
          hgap.le) (hG k))
  have htheta : 0 ≤ theta := by
    dsimp [theta]
    exact div_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg s)) hLq) hM0) hB0)
      (mul_nonneg hg.le hgap.le)
  have hthetaHalf' : theta ≤ 1 / 2 := by
    simpa [theta, q] using hthetaHalf
  have hslowAbs : |z (k + m)| ≤ 2 * A * q ^ m := by
    apply actual_quadratic_Zmax_absorption z k m q A theta hq' hA
      htheta hthetaHalf'
    dsimp only
    simpa [u, A, theta] using hpoint
  have hfastFinal := hfast q hq' hrateq' hfastCap z F k m
    hFcenter hFzero hFstep hS
  have hmaxAbs : Zm ≤ 2 * A := by
    apply range_image_max_le_two_mul_of_pointwise_self_half
      u A theta m hA htheta hthetaHalf'
    · intro i hi
      exact div_nonneg (abs_nonneg _) (pow_nonneg hq'.le _)
    · simpa [u, A, theta] using hpoint
  have hcoef : 0 ≤ s * M * B0 / (q - loadingTransverseRate N) := by
    exact div_nonneg (mul_nonneg (mul_nonneg hs.le hM0) hB0) hgap.le
  refine ⟨hslowAbs, ?_⟩
  change G (k + m) ≤
    M * loadingTransverseRate N ^ m * G k +
      (s * M * B0 / (q - loadingTransverseRate N)) * (2 * A) * q ^ m
  calc
    G (k + m) ≤ M * loadingTransverseRate N ^ m * G k +
        (s * M * B0 / (q - loadingTransverseRate N)) * Zm * q ^ m := by
      simpa [G, u, Zm] using hfastFinal
    _ ≤ M * loadingTransverseRate N ^ m * G k +
        (s * M * B0 / (q - loadingTransverseRate N)) * (2 * A) * q ^ m := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hmaxAbs hcoef)
          (pow_nonneg hq'.le m))

/-- The preceding `Z_m` theorem specialized to a genuine noiseless corrected
equation-(47) trajectory.  Its slow premise is supplied by
`actual_quadratic_slow_one_step_majorant`, and its fast premise is the exact
carrier-preserving recurrence, so the resulting pair is ready for the
equation-(48) comparison. -/
theorem actual_quadratic_noiseless_equation47_decay
    (N : NetworkSetup n) (M s : ℝ)
    (hM : 1 ≤ M) (hs : 0 < s) (hs1 : s ≤ 1)
    (Aq Lq K0 J0 B0 : ℝ)
    (hAq : 0 ≤ Aq) (hLq : 0 ≤ Lq) (hK0 : 0 ≤ K0)
    (hJ0 : 0 ≤ J0) (hB0 : 0 ≤ B0)
    (hK : ∀ (t : ℕ) (E K : Fin n → ℝ),
      dotProduct (absoluteProbability N t) E = 0 →
      (∑ i, K i) = 0 →
      |actualQuadraticCorrectedLift N t (E, K)| ≤
        K0 * (nodeSupNorm E + nodeL1Norm K))
    (hJ : ∀ (t : ℕ) (E K : Fin n → ℝ),
      nodeSupNorm (loadingFastPerturbationInput N t E K).1 +
          nodeL1Norm (loadingFastPerturbationInput N t E K).2 ≤
        J0 * (nodeSupNorm E + nodeL1Norm K))
    (hB : ∀ (t : ℕ) (z : ℝ),
      nodeSupNorm (loadingFastCenterInput N t z).1 +
          nodeL1Norm (loadingFastCenterInput N t z).2 ≤ B0 * |z|)
    (hmajor : ∀ (u : ℝ), 0 ≤ u → u ≤ 1 → ∀ (t : ℕ)
      (F : (Fin n → ℝ) × (Fin n → ℝ)),
      dotProduct (absoluteProbability N t) F.1 = 0 →
      (∑ i, F.2 i) = 0 →
      (∀ z : ℝ,
        |actualQuadraticCorrectedLift N (t + 1)
            (loadingFastCenterInput N t z)| ≤ Aq * |z|) ∧
      |-gain N t * actualQuadraticCorrectedLift N t F +
          actualQuadraticCorrectedLift N (t + 1)
            (loadingFastPerturbationInput N t F.1 F.2) +
          u * actualQuadraticCorrectedLift N (t + 1)
            (loadingFastCenterInput N t
              (actualQuadraticCorrectedLift N t F))| ≤
        Lq * (nodeSupNorm F.1 + nodeL1Norm F.2))
    (htriangular : ∀ (k t : ℕ), k ≤ t → ∀ (E K : Fin n → ℝ),
      dotProduct (absoluteProbability N k) E = 0 →
      (∑ i, K i) = 0 →
      nodeSupNorm (forwardProduct N.rowMix t k *ᵥ E) +
          nodeL1Norm
            (forwardProduct N.colMix t k *ᵥ K +
              ∑ q ∈ Finset.Ico k t,
                forwardProduct N.colMix t (q + 1) *ᵥ
                  ((N.colMix q - 1) *ᵥ
                    (forwardProduct N.rowMix q k *ᵥ E))) ≤
        M * loadingFastRate N ^ (t - k) *
          (nodeSupNorm E + nodeL1Norm K)) :
    ∀ (hsn : s * (n : ℝ) ≤ 1 / 4)
        (hsAq : s * Aq ≤ gainFloor N / 2)
        (hfastCap : loadingFastRate N +
          M * (s * J0 + s ^ 2 * B0 * K0) ≤ loadingTransverseRate N)
        (hp : 0 ≤ 1 - s * gainFloor N / 2)
        (hq : 0 < 1 - gainFloor N * s / 4)
        (hrateq : loadingTransverseRate N <
          1 - gainFloor N * s / 4)
        (hg : 0 < gainFloor N)
        (hthetaHalf :
          4 * s ^ 2 * Lq * M * B0 /
              (gainFloor N *
                ((1 - gainFloor N * s / 4) -
                  loadingTransverseRate N)) ≤ 1 / 2)
        (X U : ℕ → Fin n → ℝ) (k m : ℕ),
        (∀ r, (∑ q, U r q) = 0) →
        (∀ t, k ≤ t → X (t + 1) = fun q =>
          (N.rowMix t *ᵥ X t) q - s * X t q - s * U t q) →
        (∀ t, k ≤ t → U (t + 1) = fun q =>
          (N.colMix t *ᵥ U t) q +
            ((N.colMix t - 1) *ᵥ X t) q) →
        let xi := loadingSlowCenter N X
        let F := loadingFastCoordinates N X U
        let zq : ℕ → ℝ := fun r =>
          xi r - s * actualQuadraticCorrectedLift N r (F r)
        let q := 1 - gainFloor N * s / 4
        let G : ℕ → ℝ := fun t =>
          nodeSupNorm (F t).1 + nodeL1Norm (F t).2
        let A := |zq k| + s ^ 2 * Lq * M /
          (q - loadingTransverseRate N) * G k
        |zq (k + m)| ≤ 2 * A * q ^ m ∧
          G (k + m) ≤
            M * loadingTransverseRate N ^ m * G k +
              (s * M * B0 / (q - loadingTransverseRate N)) *
                (2 * A) * q ^ m := by
  have hslowOne := actual_quadratic_slow_one_step_majorant
    N Aq Lq hAq hLq hmajor
  have hdecay := actual_quadratic_slow_fast_Zmax_decay
    N M s Lq hM hs hLq K0 J0 B0 hK0 hJ0 hB0 hK hJ hB htriangular
  intro hsn hsAq hfastCap hp hq hrateq hg hthetaHalf
    X U k m hUzero hXrec hUrec
  dsimp only
  let e : ℕ → Fin n → ℝ := fun _ _ => 0
  let xi := loadingSlowCenter N X
  let F := loadingFastCoordinates N X U
  let zq : ℕ → ℝ := fun r =>
    xi r - s * actualQuadraticCorrectedLift N r (F r)
  have hXrec0 (t : ℕ) (hkt : k ≤ t) : X (t + 1) = fun q =>
      (N.rowMix t *ᵥ X t) q - s * X t q - s * U t q - s * e t q := by
    simpa [e] using hXrec t hkt
  have hUrec0 (t : ℕ) (hkt : k ≤ t) : U (t + 1) = fun q =>
      (N.colMix t *ᵥ U t) q + ((N.colMix t - 1) *ᵥ X t) q +
        ((N.colMix t - 1) *ᵥ e t) q := by
    rw [hUrec t hkt]
    funext q
    simp [e, Matrix.mulVec, dotProduct]
  have hcoord (t : ℕ) (hkt : k ≤ t) :
      (dotProduct (absoluteProbability N t) (F t).1 = 0 ∧
        (∑ q, (F t).2 q) = 0) ∧
      zq (t + 1) =
        (1 - s * gain N t) * zq t + s ^ 2 *
          (-gain N t * actualQuadraticCorrectedLift N t (F t) +
            actualQuadraticCorrectedLift N (t + 1)
              (loadingFastPerturbationInput N t (F t).1 (F t).2) +
            actualQuadraticCorrectedLift N (t + 1)
              (loadingFastCenterInput N t (zq t)) +
            s * actualQuadraticCorrectedLift N (t + 1)
              (loadingFastCenterInput N t
                (actualQuadraticCorrectedLift N t (F t)))) -
          s * dotProduct (influenceRow N t) (e t) + s ^ 2 *
            actualQuadraticCorrectedLift N (t + 1)
              (loadingFastPerturbationInput N t (e t) 0) ∧
      F (t + 1) =
        loadingFastStep N t (F t) -
          loadingFastScale s
            (loadingFastPerturbationInput N t (F t).1 (F t).2) -
          loadingFastScale s (loadingFastCenterInput N t (zq t)) -
          loadingFastScale s
            (loadingFastScale s
              (loadingFastCenterInput N t
                (actualQuadraticCorrectedLift N t (F t)))) +
          (0, (N.colMix t - 1) *ᵥ e t) -
          loadingFastScale s
            (loadingFastPerturbationInput N t (e t) 0) := by
    simpa [xi, F, zq] using
      (actual_quadratic_corrected_slow_fast_recurrence
        N s X U e t hUzero (hXrec0 t hkt) (hUrec0 t hkt))
  have hFstep : ∀ t, k ≤ t →
      F (t + 1) = actualQuadraticHomogeneousFastStep N s t (F t) -
        loadingFastScale s (loadingFastCenterInput N t (zq t)) := by
    intro t hkt
    have hf := (hcoord t hkt).2.2
    rw [hf]
    apply Prod.ext <;> funext a <;>
      simp [actualQuadraticHomogeneousFastStep, e,
        loadingFastPerturbationInput, loadingFastScale,
        dotProduct, Matrix.mulVec] <;> ring
  have hslowStep : ∀ t, k ≤ t →
      |zq (t + 1)| ≤
        (1 - s * gainFloor N / 2) * |zq t| +
          s ^ 2 * Lq *
            (nodeSupNorm (F t).1 + nodeL1Norm (F t).2) := by
    intro t hkt
    simpa [xi, F, zq] using
      (hslowOne s hs.le hs1 hsn hsAq X U t hUzero
        (hXrec t hkt) (hUrec t hkt))
  simpa [xi, F, zq] using
    (hdecay hfastCap hp hq hrateq hg hthetaHalf zq F k m
      (hcoord k le_rfl).1.1 (hcoord k le_rfl).1.2 hFstep hslowStep)

/-- One positive network-only cap satisfying the simultaneous supplemental
conditions used by the corrected slow/fast response. -/
theorem actual_quadratic_response_cap_spec
    (N : NetworkSetup n) (M K0 J0 B0 Aq Lq : ℝ)
    (hM : 1 ≤ M) (hK0 : 0 ≤ K0) (hJ0 : 0 ≤ J0)
    (hB0 : 0 ≤ B0) (hAq : 0 ≤ Aq) (hLq : 0 ≤ Lq) :
    ∃ sResp : ℝ, 0 < sResp ∧ ∀ s : ℝ, 0 < s → s ≤ sResp →
      s ≤ 1 ∧
      loadingFastRate N + M * (s * J0 + s ^ 2 * B0 * K0) ≤
        loadingTransverseRate N ∧
      s * (n : ℝ) ≤ 1 / 4 ∧
      s ^ 2 * Aq ≤ 1 / 4 ∧
      s * Aq ≤ gainFloor N / 2 ∧
      0 ≤ 1 - s * gainFloor N / 2 ∧
      0 < 1 - gainFloor N * s / 4 ∧
      (1 - loadingTransverseRate N) / 2 ≤
        (1 - gainFloor N * s / 4) - loadingTransverseRate N ∧
      4 * s ^ 2 * Lq * M * B0 /
          (gainFloor N *
            ((1 - gainFloor N * s / 4) -
              loadingTransverseRate N)) ≤ 1 / 2 := by
  have hg : 0 < gainFloor N :=
    (uniform_mixing_and_influence N).2.2.2.2.2.2.2.1
  have hfast1 : loadingFastRate N < 1 := by
    unfold loadingFastRate loadingTriangularRate
    linarith [mixingRate_lt_one N]
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr N.hn
  have hfastGap : 0 < loadingTransverseRate N - loadingFastRate N := by
    unfold loadingTransverseRate
    linarith
  have htrans0 : 0 ≤ loadingTransverseRate N := by
    unfold loadingTransverseRate loadingFastRate loadingTriangularRate
    linarith [mixingRate_nonneg N]
  have htrans1 : loadingTransverseRate N < 1 := by
    unfold loadingTransverseRate
    linarith
  let cfast := (loadingTransverseRate N - loadingFastRate N) /
    (M * (J0 + B0 * K0) + 1)
  let cn := 1 / (4 * (n : ℝ))
  let cAq2 := 1 / (4 * (Aq + 1))
  let cAq := gainFloor N / (2 * (Aq + 1))
  let csep := (1 - loadingTransverseRate N) /
    (2 * (gainFloor N + 1))
  let cfeed := gainFloor N * (1 - loadingTransverseRate N) /
    (16 * (Lq * M * B0 + 1))
  let sResp := min 1
    (min cfast (min cn (min cAq2 (min cAq (min csep cfeed)))))
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM
  have hdenFast : 0 < M * (J0 + B0 * K0) + 1 := by positivity
  have hdenAq : 0 < Aq + 1 := by linarith
  have hdenSep : 0 < gainFloor N + 1 := by linarith
  have hdenFeed : 0 < Lq * M * B0 + 1 := by positivity
  have hcfast : 0 < cfast := by
    dsimp [cfast]
    exact div_pos hfastGap hdenFast
  have hcn : 0 < cn := by dsimp [cn]; positivity
  have hcAq2 : 0 < cAq2 := by dsimp [cAq2]; positivity
  have hcAq : 0 < cAq := by dsimp [cAq]; positivity
  have hcsep : 0 < csep := by
    dsimp [csep]
    exact div_pos (sub_pos.mpr htrans1)
      (mul_pos (by norm_num) hdenSep)
  have hcfeed : 0 < cfeed := by
    dsimp [cfeed]
    exact div_pos (mul_pos hg (sub_pos.mpr htrans1))
      (mul_pos (by norm_num) hdenFeed)
  have hsResp : 0 < sResp := by
    dsimp [sResp]
    exact lt_min (by norm_num)
      (lt_min hcfast (lt_min hcn
        (lt_min hcAq2 (lt_min hcAq (lt_min hcsep hcfeed)))))
  refine ⟨sResp, hsResp, ?_⟩
  intro s hs hsCap
  have hsAll := hsCap
  simp only [sResp, le_min_iff] at hsAll
  rcases hsAll with
    ⟨hs1, hsFastCap, hsnCap, hsAq2Cap, hsAqCap, hsSepCap, hsFeedCap⟩
  have hfastBudget : s * (M * (J0 + B0 * K0) + 1) ≤
      loadingTransverseRate N - loadingFastRate N := by
    exact (le_div_iff₀ hdenFast).mp (by simpa [cfast] using hsFastCap)
  have hs_sq_le : s ^ 2 ≤ s := by nlinarith
  have hperturb : M * (s * J0 + s ^ 2 * B0 * K0) ≤
      loadingTransverseRate N - loadingFastRate N := by
    have hBK : 0 ≤ B0 * K0 := mul_nonneg hB0 hK0
    have hsqBK : s ^ 2 * (B0 * K0) ≤ s * (B0 * K0) :=
      mul_le_mul_of_nonneg_right hs_sq_le hBK
    have hinside : s * J0 + s ^ 2 * B0 * K0 ≤
        s * (J0 + B0 * K0) := by nlinarith
    have hscaled := mul_le_mul_of_nonneg_left hinside hM0
    nlinarith
  have hfastCap : loadingFastRate N +
      M * (s * J0 + s ^ 2 * B0 * K0) ≤ loadingTransverseRate N := by
    linarith
  have hnBudget : s * (4 * (n : ℝ)) ≤ 1 := by
    exact (le_div_iff₀ (by positivity : 0 < 4 * (n : ℝ))).mp
      (by simpa [cn] using hsnCap)
  have hsn : s * (n : ℝ) ≤ 1 / 4 := by nlinarith
  have hAq2Budget : s * (4 * (Aq + 1)) ≤ 1 := by
    exact (le_div_iff₀ (by positivity : 0 < 4 * (Aq + 1))).mp
      (by simpa [cAq2] using hsAq2Cap)
  have hsAqQuarter : s * Aq ≤ 1 / 4 := by nlinarith
  have hs2Aq : s ^ 2 * Aq ≤ 1 / 4 := by
    have := mul_le_mul_of_nonneg_right hs_sq_le hAq
    nlinarith
  have hAqBudget : s * (2 * (Aq + 1)) ≤ gainFloor N := by
    exact (le_div_iff₀ (by positivity : 0 < 2 * (Aq + 1))).mp
      (by simpa [cAq] using hsAqCap)
  have hsAq : s * Aq ≤ gainFloor N / 2 := by nlinarith
  have hgain_le_n : gainFloor N ≤ (n : ℝ) :=
    (gainFloor_le_gain N 0).trans (gain_le_n N 0)
  have hsg : s * gainFloor N ≤ 1 / 4 := by
    have := mul_le_mul_of_nonneg_left hgain_le_n hs.le
    linarith
  have hp : 0 ≤ 1 - s * gainFloor N / 2 := by nlinarith
  have hq : 0 < 1 - gainFloor N * s / 4 := by nlinarith
  have hsepBudget : s * (2 * (gainFloor N + 1)) ≤
      1 - loadingTransverseRate N := by
    exact (le_div_iff₀ (by positivity : 0 < 2 * (gainFloor N + 1))).mp
      (by simpa [csep] using hsSepCap)
  have hsep : (1 - loadingTransverseRate N) / 2 ≤
      (1 - gainFloor N * s / 4) - loadingTransverseRate N := by
    nlinarith
  have hdenTheta : 0 < gainFloor N *
      ((1 - gainFloor N * s / 4) - loadingTransverseRate N) := by
    exact mul_pos hg (lt_of_lt_of_le (by nlinarith [htrans1]) hsep)
  have hfeedBudget : s * (16 * (Lq * M * B0 + 1)) ≤
      gainFloor N * (1 - loadingTransverseRate N) := by
    exact (le_div_iff₀ (by positivity :
      0 < 16 * (Lq * M * B0 + 1))).mp
      (by simpa [cfeed] using hsFeedCap)
  have hfeedNumerator : 4 * s ^ 2 * Lq * M * B0 ≤
      gainFloor N * (1 - loadingTransverseRate N) / 4 := by
    have hC : 0 ≤ Lq * M * B0 := by positivity
    have hs2C : s ^ 2 * (Lq * M * B0) ≤ s * (Lq * M * B0) :=
      mul_le_mul_of_nonneg_right hs_sq_le hC
    nlinarith
  have htheta : 4 * s ^ 2 * Lq * M * B0 /
        (gainFloor N *
          ((1 - gainFloor N * s / 4) - loadingTransverseRate N)) ≤
      1 / 2 := by
    apply (div_le_iff₀ hdenTheta).2
    have hdenLower : gainFloor N * (1 - loadingTransverseRate N) / 2 ≤
        gainFloor N *
          ((1 - gainFloor N * s / 4) - loadingTransverseRate N) := by
      calc
        gainFloor N * (1 - loadingTransverseRate N) / 2 =
            gainFloor N * ((1 - loadingTransverseRate N) / 2) := by ring
        _ ≤ gainFloor N *
            ((1 - gainFloor N * s / 4) - loadingTransverseRate N) :=
          mul_le_mul_of_nonneg_left hsep hg.le
    nlinarith
  exact ⟨hs1, hfastCap, hsn, hs2Aq, hsAq, hp, hq, hsep, htheta⟩

/-- Exact scalar comparison scaffold for step 15: subtract the finite gain
product from a forced nonautonomous recurrence and unroll the residual. -/
theorem gain_product_error_geometric_unroll
    (gain z R : ℕ → ℝ) (s p : ℝ) (k m : ℕ)
    (hp : 0 ≤ p)
    (hcoef : ∀ t, k ≤ t → |1 - s * gain t| ≤ p)
    (hrec : ∀ t, k ≤ t →
      z (t + 1) = (1 - s * gain t) * z t + s ^ 2 * R t) :
    |z (k + m) -
        (∏ r ∈ Finset.Ico k (k + m), (1 - s * gain r)) * z k| ≤
      s ^ 2 * ∑ i ∈ Finset.range m,
        p ^ (m - i - 1) * |R (k + i)| := by
  let P : ℕ → ℝ := fun t =>
    ∏ r ∈ Finset.Ico k t, (1 - s * gain r)
  let d : ℕ → ℝ := fun t => z t - P t * z k
  have hd0 : d k = 0 := by simp [d, P]
  have hdstep : ∀ t, k ≤ t →
      |d (t + 1)| ≤ p * |d t| + s ^ 2 * |R t| := by
    intro t hkt
    have hPsucc : P (t + 1) = P t * (1 - s * gain t) := by
      dsimp [P]
      rw [Finset.prod_Ico_succ_top hkt]
    have hdrec : d (t + 1) =
        (1 - s * gain t) * d t + s ^ 2 * R t := by
      dsimp [d]
      rw [hrec t hkt, hPsucc]
      ring
    rw [hdrec]
    calc
      |(1 - s * gain t) * d t + s ^ 2 * R t| ≤
          |(1 - s * gain t) * d t| + |s ^ 2 * R t| := abs_add_le _ _
      _ = |1 - s * gain t| * |d t| + s ^ 2 * |R t| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg s)]
      _ ≤ p * |d t| + s ^ 2 * |R t| :=
        add_le_add
          (mul_le_mul_of_nonneg_right (hcoef t hkt) (abs_nonneg _)) le_rfl
  have hunroll := abs_slow_recurrence_geometric_unroll
    d (fun t => |R t|) k p (s ^ 2) hp (sq_nonneg s)
      (fun t => abs_nonneg (R t)) hdstep m
  simp only [hd0, abs_zero, mul_zero, zero_add] at hunroll
  simpa [d, P] using hunroll

/-- The two separated convolutions left after the gain-product subtraction:
one slow residual at rate `q`, and one fast residual at rate `r`. -/
theorem two_rate_product_residual_convolution_le
    (p q r a b A G0 : ℝ) (m : ℕ)
    (hp : 0 ≤ p) (hpq : p < q) (hr : 0 ≤ r) (hrq : r < q)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : 0 ≤ A) (hG0 : 0 ≤ G0) :
    (∑ i ∈ Finset.range m,
      p ^ (m - i - 1) * (a * A * q ^ i + b * G0 * r ^ i)) ≤
        (a * A / (q - p) + b * G0 / (q - r)) * q ^ m := by
  have hq0 : 0 ≤ q := le_trans hp hpq.le
  have hslow := sum_range_separated_geometric_convolution_le
    p q hp hpq m
  have hfast :
      (∑ i ∈ Finset.range m,
        p ^ (m - i - 1) * r ^ i) ≤ q ^ m / (q - r) := by
    calc
      _ ≤ ∑ i ∈ Finset.range m,
          q ^ (m - i - 1) * r ^ i := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ hp hpq.le _) (pow_nonneg hr _)
      _ = ∑ i ∈ Finset.range m,
          r ^ (m - i - 1) * q ^ i :=
        sum_range_geometric_convolution_comm r q m
      _ ≤ q ^ m / (q - r) :=
        sum_range_separated_geometric_convolution_le r q hr hrq m
  calc
    (∑ i ∈ Finset.range m,
      p ^ (m - i - 1) * (a * A * q ^ i + b * G0 * r ^ i)) =
        a * A * (∑ i ∈ Finset.range m,
          p ^ (m - i - 1) * q ^ i) +
        b * G0 * (∑ i ∈ Finset.range m,
          p ^ (m - i - 1) * r ^ i) := by
      simp only [mul_add, Finset.sum_add_distrib]
      rw [Finset.mul_sum, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring
    _ ≤ a * A * (q ^ m / (q - p)) +
        b * G0 * (q ^ m / (q - r)) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hslow (mul_nonneg ha hA))
        (mul_le_mul_of_nonneg_left hfast (mul_nonneg hb hG0))
    _ = (a * A / (q - p) + b * G0 / (q - r)) * q ^ m := by
      ring

/-- The scalar normalization after the two-rate convolution in equation (47).
The slow gap contributes one factor of `s`, while the fixed fast gap absorbs
the fast residual without making the comparison constant stepsize-dependent. -/
theorem actual_quadratic_gain_product_coefficient_absorption
    (s g df Aq Lq Cz Cf M aA G z q p r : ℝ)
    (hs : 0 < s) (hs1 : s ≤ 1) (hg : 0 < g) (hdf : 0 < df)
    (hAq : 0 ≤ Aq) (hLq : 0 ≤ Lq) (hCz : 0 ≤ Cz)
    (hCf : 0 ≤ Cf) (hM : 0 ≤ M) (hG : 0 ≤ G)
    (hslowGap : q - p = 3 * s * g / 4)
    (hfastGap : df ≤ q - r)
    (haA : aA ≤ (Aq * Cz + Lq * Cf * s) * (|z| + s ^ 2 * G)) :
    s ^ 2 * (aA / (q - p) + Lq * M * G / (q - r)) ≤
      (4 * (Aq * Cz + Lq * Cf) / (3 * g) + Lq * M / df) *
        (s * |z| + s ^ 2 * G) := by
  have hs0 : 0 ≤ s := hs.le
  have hW : 0 ≤ |z| + s ^ 2 * G :=
    add_nonneg (abs_nonneg z) (mul_nonneg (sq_nonneg s) hG)
  have hK : 0 ≤ Aq * Cz + Lq * Cf :=
    add_nonneg (mul_nonneg hAq hCz) (mul_nonneg hLq hCf)
  have hcoeff : Aq * Cz + Lq * Cf * s ≤ Aq * Cz + Lq * Cf := by
    have hLCf : 0 ≤ Lq * Cf := mul_nonneg hLq hCf
    nlinarith
  have haAK : aA ≤ (Aq * Cz + Lq * Cf) * (|z| + s ^ 2 * G) :=
    haA.trans (mul_le_mul_of_nonneg_right hcoeff hW)
  have hslowDen : 0 < q - p := by
    rw [hslowGap]
    positivity
  have hfastDen : 0 < q - r := lt_of_lt_of_le hdf hfastGap
  have hscaledW : s * (|z| + s ^ 2 * G) ≤ s * |z| + s ^ 2 * G := by
    have hs2G : 0 ≤ s ^ 2 * G := mul_nonneg (sq_nonneg s) hG
    nlinarith
  have hslow :
      s ^ 2 * (aA / (q - p)) ≤
        (4 * (Aq * Cz + Lq * Cf) / (3 * g)) *
          (s * |z| + s ^ 2 * G) := by
    calc
      s ^ 2 * (aA / (q - p)) ≤
          s ^ 2 * (((Aq * Cz + Lq * Cf) * (|z| + s ^ 2 * G)) /
            (q - p)) := by
        exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right haAK hslowDen.le) (sq_nonneg s)
      _ = (4 * (Aq * Cz + Lq * Cf) / (3 * g)) *
          (s * (|z| + s ^ 2 * G)) := by
        rw [hslowGap]
        field_simp [hs.ne', hg.ne']
        <;> ring
      _ ≤ (4 * (Aq * Cz + Lq * Cf) / (3 * g)) *
          (s * |z| + s ^ 2 * G) := by
        exact mul_le_mul_of_nonneg_left hscaledW (by positivity)
  have hfastQuot : Lq * M * G / (q - r) ≤ Lq * M * G / df := by
    apply (div_le_div_iff₀ hfastDen hdf).2
    exact mul_le_mul_of_nonneg_left hfastGap
      (mul_nonneg (mul_nonneg hLq hM) hG)
  have hfast :
      s ^ 2 * (Lq * M * G / (q - r)) ≤
        (Lq * M / df) * (s ^ 2 * G) := by
    calc
      s ^ 2 * (Lq * M * G / (q - r)) ≤
          s ^ 2 * (Lq * M * G / df) :=
        mul_le_mul_of_nonneg_left hfastQuot (sq_nonneg s)
      _ = (Lq * M / df) * (s ^ 2 * G) := by ring
  have hfastCoeff : 0 ≤ Lq * M / df := by positivity
  have hfastCarrier : s ^ 2 * G ≤ s * |z| + s ^ 2 * G := by
    exact le_add_of_nonneg_left (mul_nonneg hs0 (abs_nonneg z))
  calc
    s ^ 2 * (aA / (q - p) + Lq * M * G / (q - r)) =
        s ^ 2 * (aA / (q - p)) +
          s ^ 2 * (Lq * M * G / (q - r)) := by ring
    _ ≤ (4 * (Aq * Cz + Lq * Cf) / (3 * g)) *
          (s * |z| + s ^ 2 * G) +
        (Lq * M / df) * (s ^ 2 * G) := add_le_add hslow hfast
    _ ≤ (4 * (Aq * Cz + Lq * Cf) / (3 * g)) *
          (s * |z| + s ^ 2 * G) +
        (Lq * M / df) * (s * |z| + s ^ 2 * G) :=
      add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hfastCarrier hfastCoeff)
    _ = (4 * (Aq * Cz + Lq * Cf) / (3 * g) + Lq * M / df) *
          (s * |z| + s ^ 2 * G) := by ring

/-- Finite-window variation of constants for the scalar node-state recurrence
used in the equation-(48) row-disagreement transport. -/
theorem actual_quadratic_affine_window_unroll
    (A : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (z b : ℕ → Fin n → ℝ) (start m : ℕ)
    (hz : ∀ i < m,
      z (start + i + 1) = A (start + i) *ᵥ z (start + i) + b (start + i)) :
    z (start + m) =
      (FiniteNetwork.consecutiveProduct A start m) *ᵥ z start +
        ∑ i ∈ Finset.range m,
          (FiniteNetwork.consecutiveProduct A (start + i + 1) (m - i - 1)) *ᵥ
            b (start + i) := by
  classical
  induction m with
  | zero => simp
  | succ m ih =>
      have hzlast := hz m (Nat.lt_succ_self m)
      have ih' := ih (fun i hi => hz i (Nat.lt_succ_of_lt hi))
      rw [show start + (m + 1) = start + m + 1 by omega, hzlast, ih']
      rw [Matrix.mulVec_add, Matrix.mulVec_sum,
        Finset.sum_range_succ, FiniteNetwork.consecutiveProduct_succ,
        Matrix.mulVec_mulVec]
      have hterm : ∀ i ∈ Finset.range m,
          A (start + m) *ᵥ
              ((FiniteNetwork.consecutiveProduct A (start + i + 1)
                (m - i - 1)) *ᵥ b (start + i)) =
            (FiniteNetwork.consecutiveProduct A (start + i + 1)
              (m + 1 - i - 1)) *ᵥ b (start + i) := by
        intro i hi
        have him : i < m := Finset.mem_range.mp hi
        rw [show m + 1 - i - 1 = (m - i - 1) + 1 by omega,
          FiniteNetwork.consecutiveProduct_succ, Matrix.mulVec_mulVec]
        congr 2
        apply congrArg A
        rw [Nat.sub_sub]
        omega
      have hsum :
          ∑ i ∈ Finset.range m,
              A (start + m) *ᵥ
                ((FiniteNetwork.consecutiveProduct A (start + i + 1)
                  (m - i - 1)) *ᵥ b (start + i)) =
            ∑ i ∈ Finset.range m,
              (FiniteNetwork.consecutiveProduct A (start + i + 1)
                (m + 1 - i - 1)) *ᵥ b (start + i) := by
        exact Finset.sum_congr rfl hterm
      rw [hsum]
      simp
      abel

/-- Row-disagreement variation of constants with the exact arbitrary-window
row-product rate.  This is the analytic transport used after equation (47). -/
theorem actual_quadratic_row_disagreement_geometric_convolution
    (N : NetworkSetup n) (s : ℝ) (X Y : ℕ → Fin n → ℝ) (k m : ℕ)
    (hs : 0 ≤ s)
    (hrec : ∀ t, k ≤ t →
      X (t + 1) = N.rowMix t *ᵥ X t - s • Y t) :
    nodeL2Norm (disagreement (X (k + m))) ≤
      rowMixingConstant N * mixingRate N ^ m *
          nodeL2Norm (disagreement (X k)) +
        rowMixingConstant N * s *
          ∑ i ∈ Finset.range m,
            mixingRate N ^ (m - i - 1) *
              nodeL2Norm (disagreement (Y (k + i))) := by
  classical
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp N.hn
  let b : ℕ → Fin n → ℝ := fun t => (-s) • Y t
  have hraw := actual_quadratic_affine_window_unroll
    N.rowMix X b k m (by
      intro i hi
      rw [hrec (k + i) (by omega)]
      simp [b, sub_eq_add_neg])
  have hcons (x : Fin n → ℝ) :
      FiniteNetwork.consensusError x = disagreement x := by
    funext i
    simp [FiniteNetwork.consensusError_apply, FiniteNetwork.meanState,
      SOptLib.finiteUniformAverage_def, disagreement]
  have hconsAdd (x y : Fin n → ℝ) :
      FiniteNetwork.consensusError (x + y) =
        FiniteNetwork.consensusError x + FiniteNetwork.consensusError y := by
    funext i
    simp only [FiniteNetwork.consensusError_apply, Pi.add_apply,
      FiniteNetwork.meanState, SOptLib.finiteUniformAverage_def,
      Finset.sum_add_distrib, smul_add]
    abel
  have hconsSmul (c : ℝ) (x : Fin n → ℝ) :
      FiniteNetwork.consensusError (c • x) =
        c • FiniteNetwork.consensusError x := by
    funext i
    simp only [FiniteNetwork.consensusError_apply, Pi.smul_apply,
      FiniteNetwork.meanState, SOptLib.finiteUniformAverage_def,
      Finset.smul_sum, smul_sub]
    apply congrArg (fun z => c * x i - z)
    apply Finset.sum_congr rfl
    intro j hj
    rw [smul_smul, smul_smul, mul_comm]
  have hconsSum (f : ℕ → Fin n → ℝ) (S : Finset ℕ) :
      FiniteNetwork.consensusError (∑ i ∈ S, f i) =
        ∑ i ∈ S, FiniteNetwork.consensusError (f i) := by
    induction S using Finset.induction_on with
    | empty =>
        funext i
        simp [FiniteNetwork.consensusError_apply, FiniteNetwork.meanState,
          SOptLib.finiteUniformAverage_def]
    | @insert i S hi ih =>
        simp only [Finset.sum_insert hi, hconsAdd, ih]
  have hdecomp :
      disagreement (X (k + m)) =
        disagreement
            ((FiniteNetwork.consecutiveProduct N.rowMix k m) *ᵥ X k) +
          ∑ i ∈ Finset.range m,
            (-s) • disagreement
              ((FiniteNetwork.consecutiveProduct N.rowMix (k + i + 1)
                (m - i - 1)) *ᵥ Y (k + i)) := by
    rw [← hcons, hraw, hconsAdd, hconsSum]
    apply congrArg₂ (· + ·)
    · rw [hcons]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [Matrix.mulVec_smul, hconsSmul, hcons]
  have hnorm (x : Fin n → ℝ) :
      nodeL2Norm x = ‖(WithLp.toLp 2 x : PiLp 2 (fun _ : Fin n => ℝ))‖ := by
    simp [PiLp.norm_eq_of_L2, nodeL2Norm, Real.norm_eq_abs, sq_abs]
  have hnodeAdd (x y : Fin n → ℝ) :
      nodeL2Norm (x + y) ≤ nodeL2Norm x + nodeL2Norm y := by
    rw [hnorm, hnorm, hnorm, WithLp.toLp_add]
    exact norm_add_le _ _
  have hnodeSum (f : ℕ → Fin n → ℝ) (S : Finset ℕ) :
      nodeL2Norm (∑ i ∈ S, f i) ≤ ∑ i ∈ S, nodeL2Norm (f i) := by
    rw [hnorm, WithLp.toLp_sum]
    calc
      ‖∑ i ∈ S, (WithLp.toLp 2 (f i) : PiLp 2 (fun _ : Fin n => ℝ))‖ ≤
          ∑ i ∈ S, ‖(WithLp.toLp 2 (f i) : PiLp 2 (fun _ : Fin n => ℝ))‖ :=
        norm_sum_le _ _
      _ = ∑ i ∈ S, nodeL2Norm (f i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hnorm]
  have hnodeSmul (c : ℝ) (x : Fin n → ℝ) :
      nodeL2Norm (c • x) = |c| * nodeL2Norm x := by
    rw [hnorm, hnorm, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]
  have hinitial :
      nodeL2Norm (disagreement
          ((FiniteNetwork.consecutiveProduct N.rowMix k m) *ᵥ X k)) ≤
        rowMixingConstant N * mixingRate N ^ m *
          nodeL2Norm (disagreement (X k)) := by
    have h := rowMix_disagreement_nodeL2_geometric N (k + m) k
      (by omega) (X k)
    simpa [forwardProduct] using h
  have hterm : ∀ i ∈ Finset.range m,
      nodeL2Norm ((-s) • disagreement
          ((FiniteNetwork.consecutiveProduct N.rowMix (k + i + 1)
            (m - i - 1)) *ᵥ Y (k + i))) ≤
        s * (rowMixingConstant N * mixingRate N ^ (m - i - 1) *
          nodeL2Norm (disagreement (Y (k + i)))) := by
    intro i hi
    have him : i < m := Finset.mem_range.mp hi
    have h := rowMix_disagreement_nodeL2_geometric N (k + m) (k + i + 1)
      (by omega) (Y (k + i))
    have hdiff : k + m - (k + i + 1) = m - i - 1 := by omega
    rw [hnodeSmul, abs_neg, abs_of_nonneg hs]
    apply mul_le_mul_of_nonneg_left _ hs
    simpa [forwardProduct, hdiff] using h
  rw [hdecomp]
  calc
    nodeL2Norm
        (disagreement
            ((FiniteNetwork.consecutiveProduct N.rowMix k m) *ᵥ X k) +
          ∑ i ∈ Finset.range m,
            (-s) • disagreement
              ((FiniteNetwork.consecutiveProduct N.rowMix (k + i + 1)
                (m - i - 1)) *ᵥ Y (k + i))) ≤
      nodeL2Norm (disagreement
          ((FiniteNetwork.consecutiveProduct N.rowMix k m) *ᵥ X k)) +
        nodeL2Norm (∑ i ∈ Finset.range m,
          (-s) • disagreement
            ((FiniteNetwork.consecutiveProduct N.rowMix (k + i + 1)
              (m - i - 1)) *ᵥ Y (k + i))) := hnodeAdd _ _
    _ ≤ nodeL2Norm (disagreement
          ((FiniteNetwork.consecutiveProduct N.rowMix k m) *ᵥ X k)) +
        ∑ i ∈ Finset.range m,
          nodeL2Norm ((-s) • disagreement
            ((FiniteNetwork.consecutiveProduct N.rowMix (k + i + 1)
              (m - i - 1)) *ᵥ Y (k + i))) :=
      add_le_add le_rfl (hnodeSum _ _)
    _ ≤ rowMixingConstant N * mixingRate N ^ m *
          nodeL2Norm (disagreement (X k)) +
        ∑ i ∈ Finset.range m,
          s * (rowMixingConstant N * mixingRate N ^ (m - i - 1) *
            nodeL2Norm (disagreement (Y (k + i)))) :=
      add_le_add hinitial (Finset.sum_le_sum hterm)
    _ = rowMixingConstant N * mixingRate N ^ m *
          nodeL2Norm (disagreement (X k)) +
        rowMixingConstant N * s *
          ∑ i ∈ Finset.range m,
            mixingRate N ^ (m - i - 1) *
              nodeL2Norm (disagreement (Y (k + i))) := by
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- The row-disagreement forcing `X_t+U_t` is controlled by the corrected
slow coordinate and the equation-(47) fast gauge. -/
theorem actual_quadratic_row_forcing_disagreement_le
    (N : NetworkSetup n) (s K0 : ℝ) (X U : ℕ → Fin n → ℝ) (t : ℕ)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hK0 : 0 ≤ K0)
    (hUzero : (∑ q, U t q) = 0)
    (hK : ∀ (r : ℕ) (E K : Fin n → ℝ),
      dotProduct (absoluteProbability N r) E = 0 →
      (∑ i, K i) = 0 →
      |actualQuadraticCorrectedLift N r (E, K)| ≤
        K0 * (nodeSupNorm E + nodeL1Norm K)) :
    let xi := loadingSlowCenter N X
    let F := loadingFastCoordinates N X U
    let zq := xi t - s * actualQuadraticCorrectedLift N t (F t)
    let G := nodeSupNorm (F t).1 + nodeL1Norm (F t).2
    nodeL2Norm (disagreement (fun q => X t q + U t q)) ≤
      (n : ℝ) ^ 2 * |zq| +
        ((n : ℝ) + (n : ℝ) ^ 2 * K0) * G := by
  dsimp only
  let xi := loadingSlowCenter N X
  let F := loadingFastCoordinates N X U
  let zq : ℝ := xi t - s * actualQuadraticCorrectedLift N t (F t)
  let G : ℝ := nodeSupNorm (F t).1 + nodeL1Norm (F t).2
  let y : Fin n → ℝ := fun q => X t q + U t q
  have hpiSum : ∑ q, absoluteProbability N t q = 1 :=
    (absoluteProbability_spec N).2.1 t
  have hcenter : dotProduct (absoluteProbability N t) (F t).1 = 0 := by
    simp only [F, loadingFastCoordinates, xi, loadingSlowCenter]
    unfold dotProduct
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hpiSum, one_mul, sub_self]
  have hmass : ∑ q, (pushMass N t q - 1) = 0 := by
    rw [Finset.sum_sub_distrib, pushMass_sum_eq_n]
    simp
  have htracker : (∑ q, (F t).2 q) = 0 := by
    simp only [F, loadingFastCoordinates]
    rw [Finset.sum_sub_distrib, hUzero, ← Finset.sum_mul, hmass,
      zero_mul, sub_zero]
  have hG : 0 ≤ G := by
    dsimp [G]
    exact add_nonneg (nodeSupNorm_nonneg N (F t).1)
      (Finset.sum_nonneg fun i _ => abs_nonneg ((F t).2 i))
  have hlift := hK t (F t).1 (F t).2 hcenter htracker
  have hxiEq : xi t = zq + s * actualQuadraticCorrectedLift N t (F t) := by
    dsimp [zq]
    ring
  have hxi : |xi t| ≤ |zq| + s * K0 * G := by
    rw [hxiEq]
    calc
      |zq + s * actualQuadraticCorrectedLift N t (F t)| ≤
          |zq| + |s * actualQuadraticCorrectedLift N t (F t)| :=
        abs_add_le _ _
      _ = |zq| + s * |actualQuadraticCorrectedLift N t (F t)| := by
        rw [abs_mul, abs_of_nonneg hs]
      _ ≤ |zq| + s * (K0 * G) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (by simpa [G] using hlift) hs)
      _ = |zq| + s * K0 * G := by ring
  have hpushLe (q : Fin n) : pushMass N t q ≤ (n : ℝ) := by
    calc
      pushMass N t q ≤ ∑ j, pushMass N t j :=
        Finset.single_le_sum (fun j _ => pushMass_nonneg N t j)
          (Finset.mem_univ q)
      _ = (n : ℝ) := pushMass_sum_eq_n N t
  have hy (q : Fin n) :
      y q = (F t).1 q + (F t).2 q + pushMass N t q * xi t := by
    dsimp [y, F, loadingFastCoordinates]
    ring
  have hpoint (q : Fin n) :
      |y q| ≤ G + (n : ℝ) * (|zq| + s * K0 * G) := by
    rw [hy]
    calc
      |(F t).1 q + (F t).2 q + pushMass N t q * xi t| ≤
          |(F t).1 q| + |(F t).2 q| +
            |pushMass N t q * xi t| := by
        linarith [abs_add_le ((F t).1 q) ((F t).2 q),
          abs_add_le ((F t).1 q + (F t).2 q)
            (pushMass N t q * xi t)]
      _ = |(F t).1 q| + |(F t).2 q| +
          pushMass N t q * |xi t| := by
        rw [abs_mul, abs_of_nonneg (pushMass_nonneg N t q)]
      _ ≤ nodeSupNorm (F t).1 + nodeL1Norm (F t).2 +
          (n : ℝ) * |xi t| := by
        have hKcoord : |(F t).2 q| ≤ nodeL1Norm (F t).2 := by
          unfold nodeL1Norm
          exact Finset.single_le_sum (fun i _ => abs_nonneg ((F t).2 i))
            (Finset.mem_univ q)
        exact add_le_add
          (add_le_add (abs_le_nodeSupNorm (F t).1 q) hKcoord)
          (mul_le_mul (hpushLe q) le_rfl (abs_nonneg _)
            (Nat.cast_nonneg n))
      _ ≤ G + (n : ℝ) * (|zq| + s * K0 * G) := by
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hxi
          (Nat.cast_nonneg n))
  have hyL1 : nodeL1Norm y ≤
      (n : ℝ) * (G + (n : ℝ) * (|zq| + s * K0 * G)) := by
    unfold nodeL1Norm
    calc
      (∑ q, |y q|) ≤ ∑ _q : Fin n,
          (G + (n : ℝ) * (|zq| + s * K0 * G)) :=
        Finset.sum_le_sum fun q _ => hpoint q
      _ = (n : ℝ) * (G + (n : ℝ) * (|zq| + s * K0 * G)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
  have hcarrier :
      (n : ℝ) * (G + (n : ℝ) * (|zq| + s * K0 * G)) ≤
        (n : ℝ) ^ 2 * |zq| +
          ((n : ℝ) + (n : ℝ) ^ 2 * K0) * G := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hsK0G : s * (K0 * G) ≤ K0 * G :=
      by simpa using mul_le_mul_of_nonneg_right hs1 (mul_nonneg hK0 hG)
    nlinarith [abs_nonneg zq]
  calc
    nodeL2Norm (disagreement (fun q => X t q + U t q)) =
        nodeL2Norm (disagreement y) := by rfl
    _ ≤ nodeL2Norm y := disagreement_nodeL2_le N y
    _ ≤ nodeL1Norm y := nodeL2Norm_le_nodeL1Norm y
    _ ≤ (n : ℝ) * (G + (n : ℝ) * (|zq| + s * K0 * G)) := hyL1
    _ ≤ (n : ℝ) ^ 2 * |zq| +
        ((n : ℝ) + (n : ℝ) ^ 2 * K0) * G := hcarrier

/-- Exact actual-output transport: the arithmetic mean differs from the
corrected slow coordinate only through the corrected fast lift and arithmetic
row disagreement. -/
theorem actual_quadratic_arithmetic_output_error_le
    (N : NetworkSetup n) (s K0 : ℝ) (X U : ℕ → Fin n → ℝ) (t : ℕ)
    (hs : 0 ≤ s)
    (hUzero : (∑ q, U t q) = 0)
    (hK : ∀ (r : ℕ) (E K : Fin n → ℝ),
      dotProduct (absoluteProbability N r) E = 0 →
      (∑ i, K i) = 0 →
      |actualQuadraticCorrectedLift N r (E, K)| ≤
        K0 * (nodeSupNorm E + nodeL1Norm K)) :
    let xi := loadingSlowCenter N X
    let F := loadingFastCoordinates N X U
    let zq := xi t - s * actualQuadraticCorrectedLift N t (F t)
    let G := nodeSupNorm (F t).1 + nodeL1Norm (F t).2
    |(n : ℝ)⁻¹ * ∑ j, X t j - zq| ≤
      s * K0 * G + nodeL2Norm (disagreement (X t)) := by
  dsimp only
  let xi := loadingSlowCenter N X
  let F := loadingFastCoordinates N X U
  let zq : ℝ := xi t - s * actualQuadraticCorrectedLift N t (F t)
  let G : ℝ := nodeSupNorm (F t).1 + nodeL1Norm (F t).2
  have hpiNonneg : ∀ q, 0 ≤ absoluteProbability N t q :=
    (absoluteProbability_spec N).1 t
  have hpiSum : ∑ q, absoluteProbability N t q = 1 :=
    (absoluteProbability_spec N).2.1 t
  have hcenter : dotProduct (absoluteProbability N t) (F t).1 = 0 := by
    simp only [F, loadingFastCoordinates, xi, loadingSlowCenter]
    unfold dotProduct
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hpiSum, one_mul, sub_self]
  have hmass : ∑ q, (pushMass N t q - 1) = 0 := by
    rw [Finset.sum_sub_distrib, pushMass_sum_eq_n]
    simp
  have htracker : (∑ q, (F t).2 q) = 0 := by
    simp only [F, loadingFastCoordinates]
    rw [Finset.sum_sub_distrib, hUzero, ← Finset.sum_mul, hmass,
      zero_mul, sub_zero]
  have hlift := hK t (F t).1 (F t).2 hcenter htracker
  have hmeanIdentity :
      (n : ℝ)⁻¹ * ∑ j, X t j - xi t =
        -dotProduct (absoluteProbability N t) (disagreement (X t)) := by
    unfold xi loadingSlowCenter dotProduct disagreement
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hpiSum, one_mul]
    ring
  have hweighted :
      |dotProduct (absoluteProbability N t) (disagreement (X t))| ≤
        nodeL2Norm (disagreement (X t)) := by
    unfold dotProduct
    calc
      |∑ q, absoluteProbability N t q * disagreement (X t) q| ≤
          ∑ q, |absoluteProbability N t q * disagreement (X t) q| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ q, absoluteProbability N t q * |disagreement (X t) q| := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [abs_mul, abs_of_nonneg (hpiNonneg q)]
      _ ≤ ∑ q, absoluteProbability N t q *
          nodeL2Norm (disagreement (X t)) :=
        Finset.sum_le_sum fun q _ =>
          mul_le_mul_of_nonneg_left
            (abs_le_nodeL2Norm (disagreement (X t)) q) (hpiNonneg q)
      _ = nodeL2Norm (disagreement (X t)) := by
        rw [← Finset.sum_mul, hpiSum, one_mul]
  have houtIdentity :
      (n : ℝ)⁻¹ * ∑ j, X t j - zq =
        ((n : ℝ)⁻¹ * ∑ j, X t j - xi t) +
          s * actualQuadraticCorrectedLift N t (F t) := by
    dsimp [zq]
    ring
  rw [houtIdentity]
  calc
    |(n : ℝ)⁻¹ * ∑ j, X t j - xi t +
        s * actualQuadraticCorrectedLift N t (F t)| ≤
      |(n : ℝ)⁻¹ * ∑ j, X t j - xi t| +
        |s * actualQuadraticCorrectedLift N t (F t)| := abs_add_le _ _
    _ = |dotProduct (absoluteProbability N t) (disagreement (X t))| +
        s * |actualQuadraticCorrectedLift N t (F t)| := by
      rw [hmeanIdentity, abs_neg, abs_mul, abs_of_nonneg hs]
    _ ≤ nodeL2Norm (disagreement (X t)) + s * (K0 * G) :=
      add_le_add hweighted (mul_le_mul_of_nonneg_left
        (by simpa [G] using hlift) hs)
    _ = s * K0 * G + nodeL2Norm (disagreement (X t)) := by ring

/-- One network-only choice of every equation-(47) majorant, followed by a
single response cap and uniform noiseless decay for all smaller stepsizes. -/
theorem actual_quadratic_noiseless_decay_uniform_in_stepsize
    (N : NetworkSetup n) :
    ∃ M K0 J0 B0 Aq Lq sResp : ℝ,
      1 ≤ M ∧ 0 ≤ K0 ∧ 0 ≤ J0 ∧ 0 ≤ B0 ∧
      0 ≤ Aq ∧ 0 ≤ Lq ∧ 0 < sResp ∧
      (∀ (t : ℕ) (E K : Fin n → ℝ),
        dotProduct (absoluteProbability N t) E = 0 →
        (∑ i, K i) = 0 →
        |actualQuadraticCorrectedLift N t (E, K)| ≤
          K0 * (nodeSupNorm E + nodeL1Norm K)) ∧
      ∀ (s : ℝ), 0 < s → s ≤ sResp →
        (s ≤ 1 ∧
        loadingFastRate N + M * (s * J0 + s ^ 2 * B0 * K0) ≤
          loadingTransverseRate N ∧
        s * (n : ℝ) ≤ 1 / 4 ∧
        s ^ 2 * Aq ≤ 1 / 4 ∧
        s * Aq ≤ gainFloor N / 2 ∧
        0 ≤ 1 - s * gainFloor N / 2 ∧
        0 < 1 - gainFloor N * s / 4 ∧
        (1 - loadingTransverseRate N) / 2 ≤
          (1 - gainFloor N * s / 4) - loadingTransverseRate N ∧
        4 * s ^ 2 * Lq * M * B0 /
            (gainFloor N *
              ((1 - gainFloor N * s / 4) -
                loadingTransverseRate N)) ≤ 1 / 2) ∧
        ∀ (X U : ℕ → Fin n → ℝ) (k m : ℕ),
          (∀ r, (∑ q, U r q) = 0) →
          (∀ t, k ≤ t → X (t + 1) = fun q =>
            (N.rowMix t *ᵥ X t) q - s * X t q - s * U t q) →
          (∀ t, k ≤ t → U (t + 1) = fun q =>
            (N.colMix t *ᵥ U t) q +
              ((N.colMix t - 1) *ᵥ X t) q) →
          let xi := loadingSlowCenter N X
          let F := loadingFastCoordinates N X U
          let zq : ℕ → ℝ := fun r =>
            xi r - s * actualQuadraticCorrectedLift N r (F r)
          let q := 1 - gainFloor N * s / 4
          let G : ℕ → ℝ := fun t =>
            nodeSupNorm (F t).1 + nodeL1Norm (F t).2
          let A := |zq k| + s ^ 2 * Lq * M /
            (q - loadingTransverseRate N) * G k
          let p := 1 - s * gainFloor N
          let C := s * M * B0 / (q - loadingTransverseRate N)
          let a := 2 * Aq + 2 * Lq * C
          let b := Lq * M
          (|zq (k + m)| ≤ 2 * A * q ^ m ∧
              G (k + m) ≤
                M * loadingTransverseRate N ^ m * G k +
                  (s * M * B0 / (q - loadingTransverseRate N)) *
                    (2 * A) * q ^ m) ∧
            |zq (k + m) -
                (∏ r ∈ Finset.Ico k (k + m),
                  (1 - s * gain N r)) * zq k| ≤
              s ^ 2 *
                (a * A / (q - p) +
                  b * G k / (q - loadingTransverseRate N)) * q ^ m := by
  obtain ⟨Mtri, _hMtriBase, _hMtri0, htriangular⟩ :=
    exists_loading_triangular_product_constant N
  let M : ℝ := max 1 Mtri
  have hM : 1 ≤ M := le_max_left _ _
  have hMtri_le : Mtri ≤ M := le_max_right _ _
  have hr0 : 0 ≤ loadingFastRate N := by
    unfold loadingFastRate loadingTriangularRate
    linarith [mixingRate_nonneg N]
  have htriangularM : ∀ (k t : ℕ), k ≤ t → ∀ (E K : Fin n → ℝ),
      dotProduct (absoluteProbability N k) E = 0 →
      (∑ i, K i) = 0 →
      nodeSupNorm (forwardProduct N.rowMix t k *ᵥ E) +
          nodeL1Norm
            (forwardProduct N.colMix t k *ᵥ K +
              ∑ q ∈ Finset.Ico k t,
                forwardProduct N.colMix t (q + 1) *ᵥ
                  ((N.colMix q - 1) *ᵥ
                    (forwardProduct N.rowMix q k *ᵥ E))) ≤
        M * loadingFastRate N ^ (t - k) *
          (nodeSupNorm E + nodeL1Norm K) := by
    intro k t hkt E K hE hK
    have hraw := htriangular k t hkt E K hE hK
    have hp : 0 ≤ loadingFastRate N ^ (t - k) := pow_nonneg hr0 _
    have hG : 0 ≤ nodeSupNorm E + nodeL1Norm K :=
      add_nonneg (nodeSupNorm_nonneg N E)
        (Finset.sum_nonneg fun i _ => abs_nonneg (K i))
    exact hraw.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hMtri_le hp) hG)
  obtain ⟨K0, J0, B0, hK0, hJ0, hB0, hK, hJ, hB⟩ :=
    actual_quadratic_equation47_operator_majorants N
  obtain ⟨Aq, Lq, hAq, hLq, hmajor⟩ :=
    actual_quadratic_equation47_slow_coefficient_majorants
      N K0 J0 B0 hK0 hJ0 hB0 hK hJ hB
  obtain ⟨sResp, hsResp, hcaps⟩ :=
    actual_quadratic_response_cap_spec
      N M K0 J0 B0 Aq Lq hM hK0 hJ0 hB0 hAq hLq
  refine ⟨M, K0, J0, B0, Aq, Lq, sResp, hM, hK0, hJ0, hB0,
    hAq, hLq, hsResp, hK, ?_⟩
  intro s hs hsCap
  have hc := hcaps s hs hsCap
  refine ⟨hc, ?_⟩
  intro X U k m hUzero hXrec hUrec
  have hg : 0 < gainFloor N :=
    (uniform_mixing_and_influence N).2.2.2.2.2.2.2.1
  have htrans1 : loadingTransverseRate N < 1 := by
    unfold loadingTransverseRate loadingFastRate loadingTriangularRate
    linarith [mixingRate_lt_one N]
  have hrateq : loadingTransverseRate N <
      1 - gainFloor N * s / 4 := by
    have hgap : 0 < (1 - loadingTransverseRate N) / 2 := by linarith
    linarith [hc.2.2.2.2.2.2.2.1]
  have hdecay := actual_quadratic_noiseless_equation47_decay
    N M s hM hs hc.1 Aq Lq K0 J0 B0 hAq hLq hK0 hJ0 hB0
      hK hJ hB hmajor htriangularM
      hc.2.2.1 hc.2.2.2.2.1 hc.2.1 hc.2.2.2.2.2.1
      hc.2.2.2.2.2.2.1 hrateq hg hc.2.2.2.2.2.2.2.2
      X U k m hUzero hXrec hUrec
  dsimp only
  let e : ℕ → Fin n → ℝ := fun _ _ => 0
  let xi := loadingSlowCenter N X
  let F := loadingFastCoordinates N X U
  let zq : ℕ → ℝ := fun r =>
    xi r - s * actualQuadraticCorrectedLift N r (F r)
  let G : ℕ → ℝ := fun t =>
    nodeSupNorm (F t).1 + nodeL1Norm (F t).2
  let R : ℕ → ℝ := fun t =>
    -gain N t * actualQuadraticCorrectedLift N t (F t) +
      actualQuadraticCorrectedLift N (t + 1)
        (loadingFastPerturbationInput N t (F t).1 (F t).2) +
      actualQuadraticCorrectedLift N (t + 1)
        (loadingFastCenterInput N t (zq t)) +
      s * actualQuadraticCorrectedLift N (t + 1)
        (loadingFastCenterInput N t
          (actualQuadraticCorrectedLift N t (F t)))
  have hXrec0 (t : ℕ) (hkt : k ≤ t) : X (t + 1) = fun q =>
      (N.rowMix t *ᵥ X t) q - s * X t q - s * U t q - s * e t q := by
    simpa [e] using hXrec t hkt
  have hUrec0 (t : ℕ) (hkt : k ≤ t) : U (t + 1) = fun q =>
      (N.colMix t *ᵥ U t) q + ((N.colMix t - 1) *ᵥ X t) q +
        ((N.colMix t - 1) *ᵥ e t) q := by
    rw [hUrec t hkt]
    funext q
    simp [e, Matrix.mulVec, dotProduct]
  have hslow (t : ℕ) (hkt : k ≤ t) :=
    actualQuadratic_corrected_slow_recurrence
      N s X U e t hUzero (hXrec0 t hkt) (hUrec0 t hkt)
  have hliftZero (t : ℕ) :
      actualQuadraticCorrectedLift N (t + 1)
        (loadingFastPerturbationInput N t (e t) 0) = 0 := by
    have hzero := actualQuadraticCorrectedLift_scale N (t + 1) 0
      ((0 : Fin n → ℝ), (0 : Fin n → ℝ))
    simpa [e, loadingFastPerturbationInput, loadingFastScale, dotProduct]
      using hzero
  have hrec : ∀ t, k ≤ t →
      zq (t + 1) = (1 - s * gain N t) * zq t + s ^ 2 * R t := by
    intro t hkt
    have ht := (hslow t hkt).2
    rw [hliftZero t, mul_zero, add_zero] at ht
    simpa [xi, F, zq, R, e] using ht
  have hR : ∀ t, k ≤ t →
      |R t| ≤ Aq * |zq t| + Lq * G t := by
    intro t hkt
    have hm := hmajor s hs.le hc.1 t (F t)
      (hslow t hkt).1.1 (hslow t hkt).1.2
    have hsplit : R t =
        (-gain N t * actualQuadraticCorrectedLift N t (F t) +
          actualQuadraticCorrectedLift N (t + 1)
            (loadingFastPerturbationInput N t (F t).1 (F t).2) +
          s * actualQuadraticCorrectedLift N (t + 1)
            (loadingFastCenterInput N t
              (actualQuadraticCorrectedLift N t (F t)))) +
        actualQuadraticCorrectedLift N (t + 1)
          (loadingFastCenterInput N t (zq t)) := by
      dsimp [R]
      ring
    rw [hsplit]
    calc
      _ ≤ |-gain N t * actualQuadraticCorrectedLift N t (F t) +
              actualQuadraticCorrectedLift N (t + 1)
                (loadingFastPerturbationInput N t (F t).1 (F t).2) +
              s * actualQuadraticCorrectedLift N (t + 1)
                (loadingFastCenterInput N t
                  (actualQuadraticCorrectedLift N t (F t)))| +
            |actualQuadraticCorrectedLift N (t + 1)
              (loadingFastCenterInput N t (zq t))| := abs_add_le _ _
      _ ≤ Lq * G t + Aq * |zq t| := by
        exact add_le_add (by simpa [G] using hm.2) (hm.1 (zq t))
      _ = Aq * |zq t| + Lq * G t := by ring
  have hgain0 (t : ℕ) : 0 ≤ gain N t := by
    unfold gain dotProduct
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg ((absoluteProbability_spec N).1 (t + 1) i)
        (pushMass_nonneg N t i)
  have hp : 0 ≤ 1 - s * gainFloor N := by
    have hgf_le_n : gainFloor N ≤ (n : ℝ) :=
      (gainFloor_le_gain N 0).trans (gain_le_n N 0)
    have := mul_le_mul_of_nonneg_left hgf_le_n hs.le
    nlinarith [hc.2.2.1]
  have hcoef : ∀ t, k ≤ t →
      |1 - s * gain N t| ≤ 1 - s * gainFloor N := by
    intro t hkt
    have hgainN := gain_le_n N t
    have hnonneg : 0 ≤ 1 - s * gain N t := by
      have := mul_le_mul_of_nonneg_left hgainN hs.le
      nlinarith [hc.2.2.1]
    rw [abs_of_nonneg hnonneg]
    have hfloor := gainFloor_le_gain N t
    nlinarith [mul_le_mul_of_nonneg_left hfloor hs.le]
  have hunroll := gain_product_error_geometric_unroll
    (gain N) zq R s (1 - s * gainFloor N) k m hp hcoef hrec
  let q : ℝ := 1 - gainFloor N * s / 4
  let p : ℝ := 1 - s * gainFloor N
  let A : ℝ := |zq k| + s ^ 2 * Lq * M /
    (q - loadingTransverseRate N) * G k
  let C : ℝ := s * M * B0 / (q - loadingTransverseRate N)
  let a : ℝ := 2 * Aq + 2 * Lq * C
  let b : ℝ := Lq * M
  have hgap : 0 < q - loadingTransverseRate N := by
    dsimp [q]
    exact sub_pos.mpr hrateq
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM
  have hG0 : 0 ≤ G k := by
    dsimp [G]
    exact add_nonneg (nodeSupNorm_nonneg N (F k).1)
      (Finset.sum_nonneg fun i _ => abs_nonneg ((F k).2 i))
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact add_nonneg (abs_nonneg _)
      (mul_nonneg
        (div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg s) hLq) hM0)
          hgap.le) hG0)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg (mul_nonneg (mul_nonneg hs.le hM0) hB0) hgap.le
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hpq : p < q := by
    dsimp [p, q]
    nlinarith [mul_pos hs hg]
  have hfast0 : 0 ≤ loadingTransverseRate N := by
    unfold loadingTransverseRate loadingFastRate loadingTriangularRate
    linarith [mixingRate_nonneg N]
  have hdecayAt (i : ℕ) :
      |zq (k + i)| ≤ 2 * A * q ^ i ∧
      G (k + i) ≤
        M * loadingTransverseRate N ^ i * G k + C * (2 * A) * q ^ i := by
    have hi := actual_quadratic_noiseless_equation47_decay
      N M s hM hs hc.1 Aq Lq K0 J0 B0 hAq hLq hK0 hJ0 hB0
        hK hJ hB hmajor htriangularM
        hc.2.2.1 hc.2.2.2.2.1 hc.2.1 hc.2.2.2.2.2.1
        hc.2.2.2.2.2.2.1 hrateq hg hc.2.2.2.2.2.2.2.2
        X U k i hUzero hXrec hUrec
    simpa [xi, F, zq, G, q, A, C] using hi
  have hpoint (i : ℕ) :
      Aq * |zq (k + i)| + Lq * G (k + i) ≤
        a * A * q ^ i + b * G k * loadingTransverseRate N ^ i := by
    have hi := hdecayAt i
    calc
      Aq * |zq (k + i)| + Lq * G (k + i) ≤
          Aq * (2 * A * q ^ i) +
            Lq * (M * loadingTransverseRate N ^ i * G k +
              C * (2 * A) * q ^ i) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hi.1 hAq)
          (mul_le_mul_of_nonneg_left hi.2 hLq)
      _ = a * A * q ^ i + b * G k * loadingTransverseRate N ^ i := by
        dsimp [a, b]
        ring
  have hsum :
      (∑ i ∈ Finset.range m,
        p ^ (m - i - 1) *
          (Aq * |zq (k + i)| + Lq * G (k + i))) ≤
      (a * A / (q - p) +
          b * G k / (q - loadingTransverseRate N)) * q ^ m := by
    calc
      _ ≤ ∑ i ∈ Finset.range m,
          p ^ (m - i - 1) *
            (a * A * q ^ i + b * G k * loadingTransverseRate N ^ i) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hpoint i) (pow_nonneg hp _)
      _ ≤ (a * A / (q - p) +
          b * G k / (q - loadingTransverseRate N)) * q ^ m :=
        two_rate_product_residual_convolution_le
          p q (loadingTransverseRate N) a b A (G k) m
            hp hpq hfast0 hrateq ha0 hb0 hA0 hG0
  refine ⟨by simpa [xi, F, zq, G] using hdecay, ?_⟩
  calc
    |zq (k + m) -
        (∏ r ∈ Finset.Ico k (k + m), (1 - s * gain N r)) * zq k| ≤
        s ^ 2 * ∑ i ∈ Finset.range m,
          (1 - s * gainFloor N) ^ (m - i - 1) * |R (k + i)| := hunroll
    _ ≤ s ^ 2 * ∑ i ∈ Finset.range m,
          (1 - s * gainFloor N) ^ (m - i - 1) *
            (Aq * |zq (k + i)| + Lq * G (k + i)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg s)
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hR (k + i) (by omega))
        (pow_nonneg hp _)
    _ ≤ s ^ 2 *
        (a * A / (q - p) +
          b * G k / (q - loadingTransverseRate N)) * q ^ m := by
      simpa [p, mul_assoc] using
        (mul_le_mul_of_nonneg_left hsum (sq_nonneg s))
    _ = s ^ 2 *
        ((2 * Aq + 2 * Lq *
            (s * M * B0 /
              ((1 - gainFloor N * s / 4) - loadingTransverseRate N))) *
            (|zq k| + s ^ 2 * Lq * M /
              ((1 - gainFloor N * s / 4) - loadingTransverseRate N) * G k) /
            ((1 - gainFloor N * s / 4) - (1 - s * gainFloor N)) +
          (Lq * M) * G k /
            ((1 - gainFloor N * s / 4) - loadingTransverseRate N)) *
          (1 - gainFloor N * s / 4) ^ m := by
      rfl

set_option maxHeartbeats 3000000

/-- Source-normalized equation-(47) estimates with all comparison constants
chosen before the stepsize.  In particular, the final estimate has neither of
the two convolution denominators left in its conclusion. -/
theorem actual_quadratic_gain_product_comparison_uniform
    (N : NetworkSetup n) :
    ∃ M K0 J0 B0 Aq Lq Cz Cf Cd CEf CEs Co Cof sResp : ℝ,
      1 ≤ M ∧ 0 ≤ K0 ∧ 0 ≤ J0 ∧ 0 ≤ B0 ∧
      0 ≤ Aq ∧ 0 ≤ Lq ∧ 0 ≤ Cz ∧ 0 ≤ Cf ∧ 0 ≤ Cd ∧
      0 ≤ CEf ∧ 0 ≤ CEs ∧ 0 ≤ Co ∧ 0 ≤ Cof ∧ 0 < sResp ∧
      ∀ (s : ℝ), 0 < s → s ≤ sResp →
        (s ≤ 1 ∧
        loadingFastRate N + M * (s * J0 + s ^ 2 * B0 * K0) ≤
          loadingTransverseRate N ∧
        s * (n : ℝ) ≤ 1 / 4 ∧
        s ^ 2 * Aq ≤ 1 / 4 ∧
        s * Aq ≤ gainFloor N / 2 ∧
        0 ≤ 1 - s * gainFloor N / 2 ∧
        0 < 1 - gainFloor N * s / 4 ∧
        (1 - loadingTransverseRate N) / 2 ≤
          (1 - gainFloor N * s / 4) - loadingTransverseRate N ∧
        4 * s ^ 2 * Lq * M * B0 /
            (gainFloor N *
              ((1 - gainFloor N * s / 4) -
                loadingTransverseRate N)) ≤ 1 / 2) ∧
        ∀ (X U : ℕ → Fin n → ℝ) (k m : ℕ),
          (∀ r, (∑ q, U r q) = 0) →
          (∀ t, k ≤ t → X (t + 1) = fun q =>
            (N.rowMix t *ᵥ X t) q - s * X t q - s * U t q) →
          (∀ t, k ≤ t → U (t + 1) = fun q =>
            (N.colMix t *ᵥ U t) q +
              ((N.colMix t - 1) *ᵥ X t) q) →
          let xi := loadingSlowCenter N X
          let F := loadingFastCoordinates N X U
          let zq : ℕ → ℝ := fun r =>
            xi r - s * actualQuadraticCorrectedLift N r (F r)
          let q := 1 - gainFloor N * s / 4
          let G : ℕ → ℝ := fun t =>
            nodeSupNorm (F t).1 + nodeL1Norm (F t).2
          let W := |zq k| + s ^ 2 * G k
          (((|zq (k + m)| ≤ Cz * W * q ^ m ∧
              G (k + m) ≤
                M * loadingTransverseRate N ^ m * G k +
                  Cf * s * W * q ^ m) ∧
            |zq (k + m) -
                (∏ r ∈ Finset.Ico k (k + m),
                  (1 - s * gain N r)) * zq k| ≤
              Cd * (s * |zq k| + s ^ 2 * G k) * q ^ m) ∧
            nodeL2Norm (disagreement (X (k + m))) ≤
              rowMixingConstant N * mixingRate N ^ m *
                  nodeL2Norm (disagreement (X k)) +
                CEf * s * loadingTransverseRate N ^ m * G k +
                CEs * s * W * q ^ m) ∧
            |(n : ℝ)⁻¹ * ∑ j, X (k + m) j -
                (∏ r ∈ Finset.Ico k (k + m),
                  (1 - s * gain N r)) * zq k| ≤
              rowMixingConstant N * mixingRate N ^ m *
                  nodeL2Norm (disagreement (X k)) +
                Cof * s * loadingTransverseRate N ^ m * G k +
                Co * (s * |zq k| + s ^ 2 * G k) * q ^ m := by
  rcases actual_quadratic_noiseless_decay_uniform_in_stepsize N with
    ⟨M, K0, J0, B0, Aq, Lq, sResp, hM, hK0, hJ0, hB0,
      hAq, hLq, hsResp, hK, hpack⟩
  let df : ℝ := (1 - loadingTransverseRate N) / 2
  let Cz : ℝ := 2 * (1 + Lq * M / df)
  let Cf : ℝ := M * B0 * Cz / df
  let Cd : ℝ :=
    4 * (Aq * Cz + Lq * Cf) / (3 * gainFloor N) + Lq * M / df
  let CYz : ℝ := (n : ℝ) ^ 2
  let CYG : ℝ := (n : ℝ) + (n : ℝ) ^ 2 * K0
  let Arow : ℝ := CYz * Cz + CYG * Cf
  let Brow : ℝ := CYG * M
  let CEf : ℝ := rowMixingConstant N * Brow /
    (loadingTransverseRate N - mixingRate N)
  let CEs : ℝ := rowMixingConstant N * Arow / df
  let Co : ℝ := Cd + K0 * Cf + CEs
  let Cof : ℝ := K0 * M + CEf
  have htrans1 : loadingTransverseRate N < 1 := by
    unfold loadingTransverseRate loadingFastRate loadingTriangularRate
    linarith [mixingRate_lt_one N]
  have hdf : 0 < df := by dsimp [df]; linarith
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM
  have hCz : 0 ≤ Cz := by
    dsimp [Cz]
    positivity
  have hCf : 0 ≤ Cf := by
    dsimp [Cf]
    positivity
  have hg : 0 < gainFloor N :=
    (uniform_mixing_and_influence N).2.2.2.2.2.2.2.1
  have hCd : 0 ≤ Cd := by
    dsimp [Cd]
    positivity
  have hrhoFast : mixingRate N < loadingTransverseRate N := by
    unfold loadingTransverseRate loadingFastRate loadingTriangularRate
    linarith [mixingRate_lt_one N]
  have hrowC : 0 ≤ rowMixingConstant N := by
    unfold rowMixingConstant
    exact div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (blockContraction_pos N).le
  have hCYz : 0 ≤ CYz := by dsimp [CYz]; positivity
  have hCYG : 0 ≤ CYG := by dsimp [CYG]; positivity
  have hArow : 0 ≤ Arow := by dsimp [Arow]; positivity
  have hBrow : 0 ≤ Brow := by dsimp [Brow]; positivity
  have hCEf : 0 ≤ CEf := by
    dsimp [CEf]
    exact div_nonneg (mul_nonneg hrowC hBrow) (sub_nonneg.mpr hrhoFast.le)
  have hCEs : 0 ≤ CEs := by
    dsimp [CEs]
    exact div_nonneg (mul_nonneg hrowC hArow) hdf.le
  have hCo : 0 ≤ Co := by dsimp [Co]; positivity
  have hCof : 0 ≤ Cof := by dsimp [Cof]; positivity
  refine ⟨M, K0, J0, B0, Aq, Lq, Cz, Cf, Cd, CEf, CEs, Co, Cof, sResp,
    hM, hK0, hJ0, hB0, hAq, hLq, hCz, hCf, hCd, hCEf, hCEs,
    hCo, hCof, hsResp, ?_⟩
  intro s hs hsCap
  have hsPack := hpack s hs hsCap
  refine ⟨hsPack.1, ?_⟩
  intro X U k m hUzero hXrec hUrec
  have htraj := hsPack.2 X U k m hUzero hXrec hUrec
  dsimp only at htraj ⊢
  let xi := loadingSlowCenter N X
  let F := loadingFastCoordinates N X U
  let zq : ℕ → ℝ := fun r =>
    xi r - s * actualQuadraticCorrectedLift N r (F r)
  let q : ℝ := 1 - gainFloor N * s / 4
  let G : ℕ → ℝ := fun t =>
    nodeSupNorm (F t).1 + nodeL1Norm (F t).2
  let W : ℝ := |zq k| + s ^ 2 * G k
  let A : ℝ := |zq k| + s ^ 2 * Lq * M /
    (q - loadingTransverseRate N) * G k
  let p : ℝ := 1 - s * gainFloor N
  let C : ℝ := s * M * B0 / (q - loadingTransverseRate N)
  let a : ℝ := 2 * Aq + 2 * Lq * C
  let b : ℝ := Lq * M
  have htraj' :
      (|zq (k + m)| ≤ 2 * A * q ^ m ∧
          G (k + m) ≤
            M * loadingTransverseRate N ^ m * G k +
              C * (2 * A) * q ^ m) ∧
        |zq (k + m) -
            (∏ r ∈ Finset.Ico k (k + m),
              (1 - s * gain N r)) * zq k| ≤
          s ^ 2 *
            (a * A / (q - p) +
              b * G k / (q - loadingTransverseRate N)) * q ^ m := by
    simpa [xi, F, zq, q, G, A, p, C, a, b] using htraj
  rcases hsPack.1 with
    ⟨hs1, _hfastCap, _hsn, _hsAq2, _hsAq, _hp, hq, hfastGap, _htheta⟩
  have hq0 : 0 ≤ q := by simpa [q] using hq.le
  have hG : 0 ≤ G k := by
    dsimp [G]
    exact add_nonneg (nodeSupNorm_nonneg N (F k).1)
      (Finset.sum_nonneg fun i _ => abs_nonneg ((F k).2 i))
  have hW : 0 ≤ W := by
    dsimp [W]
    exact add_nonneg (abs_nonneg _) (mul_nonneg (sq_nonneg s) hG)
  have hfastDen : 0 < q - loadingTransverseRate N := by
    exact lt_of_lt_of_le hdf (by simpa [df, q] using hfastGap)
  have hfastQuot : Lq * M / (q - loadingTransverseRate N) ≤ Lq * M / df := by
    apply (div_le_div_iff₀ hfastDen hdf).2
    exact mul_le_mul_of_nonneg_left (by simpa [df, q] using hfastGap)
      (mul_nonneg hLq hM0)
  have hA0 : 0 ≤ A := by
    dsimp [A]
    positivity
  have hAmajor : A ≤ (1 + Lq * M / df) * W := by
    have hterm := mul_le_mul_of_nonneg_right hfastQuot
      (mul_nonneg (sq_nonneg s) hG)
    have hLMdf : 0 ≤ Lq * M / df := by positivity
    calc
      A = |zq k| + (Lq * M / (q - loadingTransverseRate N)) *
          (s ^ 2 * G k) := by dsimp [A]; ring
      _ ≤ |zq k| + (Lq * M / df) * (s ^ 2 * G k) :=
        add_le_add le_rfl hterm
      _ ≤ (1 + Lq * M / df) * W := by
        dsimp [W]
        nlinarith [abs_nonneg (zq k), mul_nonneg (sq_nonneg s) hG,
          mul_nonneg hLMdf (abs_nonneg (zq k))]
  have htwoA : 2 * A ≤ Cz * W := by
    dsimp [Cz]
    nlinarith
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hCmajor : C ≤ s * M * B0 / df := by
    dsimp [C]
    have hnum : 0 ≤ s * M * B0 := by positivity
    apply (div_le_div_iff₀ hfastDen hdf).2
    exact mul_le_mul_of_nonneg_left (by simpa [df, q] using hfastGap) hnum
  have hCAmajor : C * (2 * A) ≤ Cf * s * W := by
    calc
      C * (2 * A) ≤ (s * M * B0 / df) * (Cz * W) :=
        mul_le_mul hCmajor htwoA (by positivity) (by positivity)
      _ = Cf * s * W := by
        dsimp [Cf]
        ring
  have haAmajor : a * A ≤
      (Aq * Cz + Lq * Cf * s) * W := by
    calc
      a * A = Aq * (2 * A) + Lq * (C * (2 * A)) := by
        dsimp [a]
        ring
      _ ≤ Aq * (Cz * W) + Lq * (Cf * s * W) :=
        add_le_add (mul_le_mul_of_nonneg_left htwoA hAq)
          (mul_le_mul_of_nonneg_left hCAmajor hLq)
      _ = (Aq * Cz + Lq * Cf * s) * W := by ring
  have hnormAt (i : ℕ) :
      |zq (k + i)| ≤ Cz * W * q ^ i ∧
        G (k + i) ≤
          M * loadingTransverseRate N ^ i * G k + Cf * s * W * q ^ i := by
    have hi := hsPack.2 X U k i hUzero hXrec hUrec
    dsimp only at hi
    have hiSlow : |zq (k + i)| ≤ 2 * A * q ^ i := by
      simpa [xi, F, zq, q, G, A, p, C, a, b] using hi.1.1
    have hiFast : G (k + i) ≤
        M * loadingTransverseRate N ^ i * G k + C * (2 * A) * q ^ i := by
      simpa [xi, F, zq, q, G, A, p, C, a, b] using hi.1.2
    exact ⟨hiSlow.trans
        (mul_le_mul_of_nonneg_right htwoA (pow_nonneg hq0 i)),
      hiFast.trans (add_le_add le_rfl
        (mul_le_mul_of_nonneg_right hCAmajor (pow_nonneg hq0 i)))⟩
  have habsorb := actual_quadratic_gain_product_coefficient_absorption
    s (gainFloor N) df Aq Lq Cz Cf M (a * A) (G k) (zq k)
      q p (loadingTransverseRate N) hs hs1 hg hdf hAq hLq hCz hCf
      hM0 hG (by dsimp [q, p]; ring)
      (by simpa [df, q] using hfastGap) (by simpa [W] using haAmajor)
  have hslowNorm := (hnormAt m).1
  have hfastNorm := (hnormAt m).2
  have hcompare :
      |zq (k + m) -
          (∏ r ∈ Finset.Ico k (k + m), (1 - s * gain N r)) * zq k| ≤
        Cd * (s * |zq k| + s ^ 2 * G k) * q ^ m := by
    calc
      |zq (k + m) -
          (∏ r ∈ Finset.Ico k (k + m), (1 - s * gain N r)) * zq k| ≤
        s ^ 2 *
          (a * A / (q - p) +
            b * G k / (q - loadingTransverseRate N)) * q ^ m := htraj'.2
      _ ≤ Cd * (s * |zq k| + s ^ 2 * G k) * q ^ m := by
        dsimp [b, Cd]
        exact mul_le_mul_of_nonneg_right habsorb (pow_nonneg hq0 m)
  have hrowBound :
      nodeL2Norm (disagreement (X (k + m))) ≤
        rowMixingConstant N * mixingRate N ^ m *
            nodeL2Norm (disagreement (X k)) +
          CEf * s * loadingTransverseRate N ^ m * G k +
          CEs * s * W * q ^ m := by
    let Y : ℕ → Fin n → ℝ := fun t q => X t q + U t q
    have hXrow : ∀ t, k ≤ t →
        X (t + 1) = N.rowMix t *ᵥ X t - s • Y t := by
      intro t hkt
      rw [hXrec t hkt]
      funext j
      simp [Y, Pi.sub_apply]
      ring
    have hrowRaw := actual_quadratic_row_disagreement_geometric_convolution
      N s X Y k m hs.le hXrow
    have hforceAt (i : ℕ) :
        nodeL2Norm (disagreement (Y (k + i))) ≤
          CYz * |zq (k + i)| + CYG * G (k + i) := by
      have hi := actual_quadratic_row_forcing_disagreement_le
        N s K0 X U (k + i) hs.le hs1 hK0 (hUzero (k + i)) hK
      simpa [Y, xi, F, zq, G, CYz, CYG] using hi
    have hcoeff : CYz * Cz + CYG * Cf * s ≤ Arow := by
      dsimp [Arow]
      have hCYGCf : 0 ≤ CYG * Cf := mul_nonneg hCYG hCf
      nlinarith
    have hforceDecay (i : ℕ) :
        nodeL2Norm (disagreement (Y (k + i))) ≤
          Arow * W * q ^ i +
            Brow * G k * loadingTransverseRate N ^ i := by
      have hi := hnormAt i
      calc
        nodeL2Norm (disagreement (Y (k + i))) ≤
            CYz * |zq (k + i)| + CYG * G (k + i) := hforceAt i
        _ ≤ CYz * (Cz * W * q ^ i) +
            CYG * (M * loadingTransverseRate N ^ i * G k +
              Cf * s * W * q ^ i) :=
          add_le_add (mul_le_mul_of_nonneg_left hi.1 hCYz)
            (mul_le_mul_of_nonneg_left hi.2 hCYG)
        _ = (CYz * Cz + CYG * Cf * s) * W * q ^ i +
            Brow * G k * loadingTransverseRate N ^ i := by
          dsimp [Brow]
          ring
        _ ≤ Arow * W * q ^ i +
            Brow * G k * loadingTransverseRate N ^ i := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hcoeff hW) (pow_nonneg hq0 i)) le_rfl
    have hrho0 : 0 ≤ mixingRate N := mixingRate_nonneg N
    have hrf0 : 0 ≤ loadingTransverseRate N := by
      unfold loadingTransverseRate loadingFastRate loadingTriangularRate
      linarith [mixingRate_nonneg N]
    have hrhoq : mixingRate N < q := hrhoFast.trans
      (by exact sub_pos.mp hfastDen)
    have hqrhoGap : df ≤ q - mixingRate N := by
      have := hfastGap
      dsimp [df, q] at this ⊢
      linarith
    have hslowConv := sum_range_separated_geometric_convolution_le
      (mixingRate N) q hrho0 hrhoq m
    have hfastConv := sum_range_separated_geometric_convolution_le
      (mixingRate N) (loadingTransverseRate N) hrho0 hrhoFast m
    have hqrhoPos : 0 < q - mixingRate N := sub_pos.mpr hrhoq
    have hrhoFastPos : 0 < loadingTransverseRate N - mixingRate N :=
      sub_pos.mpr hrhoFast
    have hslowDen :
        q ^ m / (q - mixingRate N) ≤ q ^ m / df := by
      apply (div_le_div_iff₀ hqrhoPos hdf).2
      exact mul_le_mul_of_nonneg_left hqrhoGap (pow_nonneg hq0 m)
    have hsum :
        (∑ i ∈ Finset.range m,
          mixingRate N ^ (m - i - 1) *
            nodeL2Norm (disagreement (Y (k + i)))) ≤
          Arow * W * (q ^ m / df) +
            Brow * G k *
              (loadingTransverseRate N ^ m /
                (loadingTransverseRate N - mixingRate N)) := by
      calc
        _ ≤ ∑ i ∈ Finset.range m,
            mixingRate N ^ (m - i - 1) *
              (Arow * W * q ^ i +
                Brow * G k * loadingTransverseRate N ^ i) := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left (hforceDecay i)
            (pow_nonneg hrho0 _)
        _ = Arow * W *
              (∑ i ∈ Finset.range m,
                mixingRate N ^ (m - i - 1) * q ^ i) +
            Brow * G k *
              (∑ i ∈ Finset.range m,
                mixingRate N ^ (m - i - 1) *
                  loadingTransverseRate N ^ i) := by
          simp only [mul_add, Finset.sum_add_distrib]
          rw [Finset.mul_sum, Finset.mul_sum]
          congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring
        _ ≤ Arow * W * (q ^ m / (q - mixingRate N)) +
            Brow * G k *
              (loadingTransverseRate N ^ m /
                (loadingTransverseRate N - mixingRate N)) :=
          add_le_add
            (mul_le_mul_of_nonneg_left hslowConv (mul_nonneg hArow hW))
            (mul_le_mul_of_nonneg_left hfastConv
              (mul_nonneg hBrow hG))
        _ ≤ Arow * W * (q ^ m / df) +
            Brow * G k *
              (loadingTransverseRate N ^ m /
                (loadingTransverseRate N - mixingRate N)) :=
          add_le_add
            (mul_le_mul_of_nonneg_left hslowDen (mul_nonneg hArow hW)) le_rfl
    calc
      nodeL2Norm (disagreement (X (k + m))) ≤
          rowMixingConstant N * mixingRate N ^ m *
              nodeL2Norm (disagreement (X k)) +
            rowMixingConstant N * s *
              ∑ i ∈ Finset.range m,
                mixingRate N ^ (m - i - 1) *
                  nodeL2Norm (disagreement (Y (k + i))) := hrowRaw
      _ ≤ rowMixingConstant N * mixingRate N ^ m *
              nodeL2Norm (disagreement (X k)) +
            rowMixingConstant N * s *
              (Arow * W * (q ^ m / df) +
                Brow * G k *
                  (loadingTransverseRate N ^ m /
                    (loadingTransverseRate N - mixingRate N))) := by
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hsum (mul_nonneg hrowC hs.le))
      _ = rowMixingConstant N * mixingRate N ^ m *
              nodeL2Norm (disagreement (X k)) +
            CEf * s * loadingTransverseRate N ^ m * G k +
            CEs * s * W * q ^ m := by
        dsimp [CEf, CEs]
        ring
  have houtLocal :
      |(n : ℝ)⁻¹ * ∑ j, X (k + m) j - zq (k + m)| ≤
        s * K0 * G (k + m) +
          nodeL2Norm (disagreement (X (k + m))) := by
    have h := actual_quadratic_arithmetic_output_error_le
      N s K0 X U (k + m) hs.le (hUzero (k + m)) hK
    simpa [xi, F, zq, G] using h
  let carrier : ℝ := s * |zq k| + s ^ 2 * G k
  have hcarrier : 0 ≤ carrier := by
    dsimp [carrier]
    positivity
  have hs2le : s ^ 2 ≤ s := by nlinarith [sq_nonneg s]
  have hs2one : s ^ 2 ≤ 1 := by nlinarith [sq_nonneg s]
  have hsw : s * W ≤ carrier := by
    have htail : s * (s ^ 2 * G k) ≤ s ^ 2 * G k := by
      have := mul_le_mul_of_nonneg_right hs1
        (mul_nonneg (sq_nonneg s) hG)
      simpa using this
    calc
      s * W = s * |zq k| + s * (s ^ 2 * G k) := by dsimp [W]; ring
      _ ≤ s * |zq k| + s ^ 2 * G k := add_le_add le_rfl htail
      _ = carrier := by rfl
  have hs2w : s ^ 2 * W ≤ carrier := by
    have hhead : s ^ 2 * |zq k| ≤ s * |zq k| :=
      mul_le_mul_of_nonneg_right hs2le (abs_nonneg (zq k))
    have htail : s ^ 2 * (s ^ 2 * G k) ≤ s ^ 2 * G k := by
      have := mul_le_mul_of_nonneg_right hs2one
        (mul_nonneg (sq_nonneg s) hG)
      simpa using this
    calc
      s ^ 2 * W = s ^ 2 * |zq k| + s ^ 2 * (s ^ 2 * G k) := by
        dsimp [W]
        ring
      _ ≤ s * |zq k| + s ^ 2 * G k := add_le_add hhead htail
      _ = carrier := by rfl
  have hslowLift :
      s * K0 * (Cf * s * W * q ^ m) ≤
        K0 * Cf * carrier * q ^ m := by
    calc
      s * K0 * (Cf * s * W * q ^ m) =
          K0 * Cf * (s ^ 2 * W) * q ^ m := by ring
      _ ≤ K0 * Cf * carrier * q ^ m :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hs2w (mul_nonneg hK0 hCf))
          (pow_nonneg hq0 m)
  have hrowSlow : CEs * s * W * q ^ m ≤
      CEs * carrier * q ^ m := by
    calc
      CEs * s * W * q ^ m = CEs * (s * W) * q ^ m := by ring
      _ ≤ CEs * carrier * q ^ m :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsw hCEs) (pow_nonneg hq0 m)
  have hfastLift :
      s * K0 * (M * loadingTransverseRate N ^ m * G k) =
        K0 * M * s * loadingTransverseRate N ^ m * G k := by ring
  have houtput :
      |(n : ℝ)⁻¹ * ∑ j, X (k + m) j -
          (∏ r ∈ Finset.Ico k (k + m),
            (1 - s * gain N r)) * zq k| ≤
        rowMixingConstant N * mixingRate N ^ m *
            nodeL2Norm (disagreement (X k)) +
          Cof * s * loadingTransverseRate N ^ m * G k +
          Co * carrier * q ^ m := by
    calc
      |(n : ℝ)⁻¹ * ∑ j, X (k + m) j -
          (∏ r ∈ Finset.Ico k (k + m),
            (1 - s * gain N r)) * zq k| ≤
        |(n : ℝ)⁻¹ * ∑ j, X (k + m) j - zq (k + m)| +
          |zq (k + m) -
            (∏ r ∈ Finset.Ico k (k + m),
              (1 - s * gain N r)) * zq k| := by
        convert abs_add_le
          ((n : ℝ)⁻¹ * ∑ j, X (k + m) j - zq (k + m))
          (zq (k + m) -
            (∏ r ∈ Finset.Ico k (k + m),
              (1 - s * gain N r)) * zq k) using 1 <;> ring
      _ ≤ (s * K0 * G (k + m) +
            nodeL2Norm (disagreement (X (k + m)))) +
          Cd * carrier * q ^ m := by
        exact add_le_add houtLocal (by simpa [carrier] using hcompare)
      _ ≤ (s * K0 *
              (M * loadingTransverseRate N ^ m * G k +
                Cf * s * W * q ^ m) +
            (rowMixingConstant N * mixingRate N ^ m *
                nodeL2Norm (disagreement (X k)) +
              CEf * s * loadingTransverseRate N ^ m * G k +
              CEs * s * W * q ^ m)) +
          Cd * carrier * q ^ m := by
        exact add_le_add
          (add_le_add
            (mul_le_mul_of_nonneg_left hfastNorm (mul_nonneg hs.le hK0))
            hrowBound) le_rfl
      _ ≤ rowMixingConstant N * mixingRate N ^ m *
              nodeL2Norm (disagreement (X k)) +
            Cof * s * loadingTransverseRate N ^ m * G k +
            Co * carrier * q ^ m := by
        rw [mul_add, hfastLift]
        calc
          _ = rowMixingConstant N * mixingRate N ^ m *
                  nodeL2Norm (disagreement (X k)) +
                Cof * s * loadingTransverseRate N ^ m * G k +
                (s * K0 * (Cf * s * W * q ^ m) +
                  CEs * s * W * q ^ m + Cd * carrier * q ^ m) := by
            dsimp [Cof]
            ring
          _ ≤ rowMixingConstant N * mixingRate N ^ m *
                  nodeL2Norm (disagreement (X k)) +
                Cof * s * loadingTransverseRate N ^ m * G k +
                (K0 * Cf * carrier * q ^ m +
                  CEs * carrier * q ^ m + Cd * carrier * q ^ m) := by
            apply add_le_add le_rfl
            exact add_le_add (add_le_add hslowLift hrowSlow) le_rfl
          _ = rowMixingConstant N * mixingRate N ^ m *
                  nodeL2Norm (disagreement (X k)) +
                Cof * s * loadingTransverseRate N ^ m * G k +
                Co * carrier * q ^ m := by
            dsimp [Co]
            ring
  exact ⟨⟨⟨⟨hslowNorm, hfastNorm⟩, hcompare⟩, hrowBound⟩,
    by simpa [carrier] using houtput⟩

set_option maxHeartbeats 1000000

/-- The source single-noise pulse evaluated at its first successor.  The
constants are chosen before the stepsize and pulse time.  Besides the three
initial bounds used in equation (48), the conclusion records that the literal
equation-(46) trajectory is noiseless after the pulse. -/
theorem actual_quadratic_single_impulse_initial_bounds
    (N : NetworkSetup n) :
    ∃ K0 J0 B0 Nf Cc : ℝ,
      0 ≤ K0 ∧ 0 ≤ J0 ∧ 0 ≤ B0 ∧ 0 ≤ Nf ∧ 0 ≤ Cc ∧
      (∀ (t : ℕ) (E K : Fin n → ℝ),
        dotProduct (absoluteProbability N t) E = 0 →
        (∑ i, K i) = 0 →
        |actualQuadraticCorrectedLift N t (E, K)| ≤
          K0 * (nodeSupNorm E + nodeL1Norm K)) ∧
      ∀ (s : ℝ), 0 < s → s ≤ 1 → ∀ (j : ℕ) (i : Fin n)
        (X U : ℕ → Fin n → ℝ),
        let e : ℕ → Fin n → ℝ := fun t q =>
          if t = j then if q = i then 1 else 0 else 0
        (∀ r, (∑ q, U r q) = 0) → X j = 0 → U j = 0 →
        (∀ t, X (t + 1) = fun q =>
          (N.rowMix t *ᵥ X t) q - s * X t q - s * U t q - s * e t q) →
        (∀ t, U (t + 1) = fun q =>
          (N.colMix t *ᵥ U t) q + ((N.colMix t - 1) *ᵥ X t) q +
            ((N.colMix t - 1) *ᵥ e t) q) →
        let k := j + 1
        let xi := loadingSlowCenter N X
        let F := loadingFastCoordinates N X U
        let zq : ℕ → ℝ := fun r =>
          xi r - s * actualQuadraticCorrectedLift N r (F r)
        nodeSupNorm (F k).1 + nodeL1Norm (F k).2 ≤ Nf ∧
        nodeL2Norm (disagreement (X k)) ≤ 2 * s ∧
        |zq k + s * influenceRow N j i| ≤ s ^ 2 * Cc ∧
        (∀ t, k ≤ t →
          X (t + 1) = fun q =>
            (N.rowMix t *ᵥ X t) q - s * X t q - s * U t q) ∧
        (∀ t, k ≤ t →
          U (t + 1) = fun q =>
            (N.colMix t *ᵥ U t) q + ((N.colMix t - 1) *ᵥ X t) q) := by
  classical
  obtain ⟨K0, J0, B0, hK0, hJ0, hB0, hK, hJ, _hB⟩ :=
    actual_quadratic_equation47_operator_majorants N
  let Nf : ℝ := 2 + J0
  let Cc : ℝ := K0 * J0
  refine ⟨K0, J0, B0, Nf, Cc, hK0, hJ0, hB0, ?_, ?_, hK, ?_⟩
  · dsimp [Nf]
    linarith
  · dsimp [Cc]
    positivity
  · intro s hs hs1 j i X U
    dsimp only
    intro hUzero hXj hUj hXrec hUrec
    let e : ℕ → Fin n → ℝ := fun t q =>
      if t = j then if q = i then 1 else 0 else 0
    let delta : Fin n → ℝ := fun q => if q = i then 1 else 0
    let k := j + 1
    let xi := loadingSlowCenter N X
    let F := loadingFastCoordinates N X U
    let zq : ℕ → ℝ := fun r =>
      xi r - s * actualQuadraticCorrectedLift N r (F r)
    have hej : e j = delta := by
      funext q
      simp [e, delta]
    have heTail (t : ℕ) (hkt : k ≤ t) : e t = 0 := by
      have htj : t ≠ j := by
        dsimp [k] at hkt
        omega
      funext q
      simp [e, htj]
    have hxiJ : xi j = 0 := by
      simp [xi, loadingSlowCenter, hXj, dotProduct]
    have hFj : F j = (0, 0) := by
      apply Prod.ext <;> funext q
      · change X j q - xi j = 0
        rw [hxiJ, hXj]
        simp
      · change U j q - (pushMass N j q - 1) * xi j = 0
        rw [hxiJ, hUj]
        simp
    have hliftZero (r : ℕ) :
        actualQuadraticCorrectedLift N r
            ((0 : Fin n → ℝ), (0 : Fin n → ℝ)) = 0 := by
      have hzero := actualQuadraticCorrectedLift_scale N r 0
        ((0 : Fin n → ℝ), (0 : Fin n → ℝ))
      simpa [loadingFastScale] using hzero
    have hzqJ : zq j = 0 := by
      simp [zq, hxiJ, hFj, hliftZero]
    have hcoord := actual_quadratic_corrected_slow_fast_recurrence
      N s X U e j hUzero
        (by simpa [e] using hXrec j) (by simpa [e] using hUrec j)
    have hdeltaSup : nodeSupNorm delta = 1 := by
      letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp N.hn
      unfold nodeSupNorm
      apply le_antisymm
      · apply ciSup_le
        intro q
        by_cases hqi : q = i <;> simp [delta, hqi]
      · have hi : |delta i| ≤ ⨆ q, |delta q| :=
          le_ciSup (Finite.bddAbove_range (fun q : Fin n => |delta q|)) i
        simpa [delta] using hi
    have hdeltaL1 : nodeL1Norm delta = 1 := by
      unfold nodeL1Norm delta
      simp_rw [abs_ite, abs_one, abs_zero]
      simp
    have hdeltaL2 : nodeL2Norm delta ≤ 1 := by
      exact (nodeL2Norm_le_nodeL1Norm delta).trans_eq hdeltaL1
    have hXk : X k = fun q => -s * delta q := by
      rw [show k = j + 1 by rfl, hXrec j]
      funext q
      rw [hXj, hUj]
      simp only [Pi.zero_apply, Matrix.mulVec_zero, zero_sub, mul_zero,
        sub_zero, hej]
      by_cases hqi : q = i <;> simp [delta, hqi]
    have hEk : nodeL2Norm (disagreement (X k)) ≤ 2 * s := by
      calc
        nodeL2Norm (disagreement (X k)) ≤ nodeL2Norm (X k) :=
          disagreement_nodeL2_le N (X k)
        _ ≤ nodeL1Norm (X k) := nodeL2Norm_le_nodeL1Norm (X k)
        _ = s := by
          rw [hXk]
          simp only [nodeL1Norm, abs_mul, abs_neg, abs_of_pos hs]
          rw [← Finset.mul_sum, show (∑ q, |delta q|) = 1 by
            simpa [nodeL1Norm] using hdeltaL1]
          ring
        _ ≤ 2 * s := by linarith
    let N0 : (Fin n → ℝ) × (Fin n → ℝ) :=
      (0, (N.colMix j - 1) *ᵥ delta)
    let N1 := loadingFastPerturbationInput N j delta 0
    have hfastStepZero : loadingFastStep N j
        ((0 : Fin n → ℝ), (0 : Fin n → ℝ)) = (0, 0) := by
      apply Prod.ext <;> funext q <;>
        simp [loadingFastStep, Matrix.mulVec, dotProduct]
    have hperturbZero : loadingFastPerturbationInput N j
        (0 : Fin n → ℝ) 0 = (0, 0) := by
      apply Prod.ext <;> funext q <;>
        simp [loadingFastPerturbationInput, dotProduct]
    have hcenterZero : loadingFastCenterInput N j 0 =
        ((0 : Fin n → ℝ), (0 : Fin n → ℝ)) := by
      apply Prod.ext <;> funext q <;>
        simp [loadingFastCenterInput]
    have hFk : F k = N0 - loadingFastScale s N1 := by
      have hf := hcoord.2.2
      have hFjRaw : loadingFastCoordinates N X U j = (0, 0) := by
        simpa [F] using hFj
      have hzqJRaw :
          (fun r => loadingSlowCenter N X r -
            s * actualQuadraticCorrectedLift N r
              (loadingFastCoordinates N X U r)) j = 0 := by
        simpa [zq, xi, F] using hzqJ
      change loadingFastCoordinates N X U (j + 1) =
        N0 - loadingFastScale s N1
      rw [hf, hFjRaw, hzqJRaw, hfastStepZero, hperturbZero,
        hcenterZero, hliftZero, hcenterZero, hej]
      apply Prod.ext <;> funext q <;> simp [N0, N1, loadingFastScale]
    have hN0 : nodeSupNorm N0.1 + nodeL1Norm N0.2 ≤ 2 := by
      have hcol := (columnInnovation_norms_le_two N j i).1
      have hcolEq : (N.colMix j - 1) *ᵥ delta =
          (columnInnovation N j i).1 := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec]
        funext q
        simp [delta, Matrix.mulVec, dotProduct, columnInnovation]
      simpa [N0, hcolEq, nodeSupNorm, nodeL1Norm] using hcol
    have hN1 : nodeSupNorm N1.1 + nodeL1Norm N1.2 ≤ J0 := by
      have hj := hJ j delta 0
      have hzeroL1 : nodeL1Norm (0 : Fin n → ℝ) = 0 := by
        simp [nodeL1Norm]
      simpa [N1, hdeltaSup, hzeroL1] using hj
    have hFkGauge : nodeSupNorm (F k).1 + nodeL1Norm (F k).2 ≤ Nf := by
      have hadd := loadingFastGauge_add_le N N0
        (loadingFastScale (-s) N1)
      have hscale := loadingFastScale_gauge_le_abs N (-s) N1
      rw [hFk]
      have hsub : N0 - loadingFastScale s N1 =
          N0 + loadingFastScale (-s) N1 := by
        apply Prod.ext <;> funext q <;> simp [loadingFastScale] <;> ring
      rw [hsub]
      calc
        nodeSupNorm (N0 + loadingFastScale (-s) N1).1 +
            nodeL1Norm (N0 + loadingFastScale (-s) N1).2 ≤
            (nodeSupNorm N0.1 + nodeL1Norm N0.2) +
              (nodeSupNorm (loadingFastScale (-s) N1).1 +
                nodeL1Norm (loadingFastScale (-s) N1).2) := hadd
        _ ≤ 2 + s * J0 := by
          have hsabs : |-s| = s := by rw [abs_neg, abs_of_pos hs]
          rw [hsabs] at hscale
          exact add_le_add hN0 (hscale.trans
            (mul_le_mul_of_nonneg_left hN1 hs.le))
        _ ≤ Nf := by
          dsimp [Nf]
          nlinarith
    have hN1carrier := loadingFastPerturbationInput_spec N j delta 0
    have hN1Lift :
        |actualQuadraticCorrectedLift N (j + 1) N1| ≤ K0 * J0 := by
      have hk := hK (j + 1) N1.1 N1.2 hN1carrier.1 hN1carrier.2.1
      exact hk.trans (mul_le_mul_of_nonneg_left hN1 hK0)
    have hzqPulse :
        zq k = -s * influenceRow N j i +
          s ^ 2 * actualQuadraticCorrectedLift N (j + 1) N1 := by
      have hz := hcoord.2.1
      have hFjRaw : loadingFastCoordinates N X U j = (0, 0) := by
        simpa [F] using hFj
      have hzqJRaw :
          (fun r => loadingSlowCenter N X r -
            s * actualQuadraticCorrectedLift N r
              (loadingFastCoordinates N X U r)) j = 0 := by
        simpa [zq, xi, F] using hzqJ
      change (fun r => loadingSlowCenter N X r -
        s * actualQuadraticCorrectedLift N r
          (loadingFastCoordinates N X U r)) (j + 1) =
        -s * influenceRow N j i +
          s ^ 2 * actualQuadraticCorrectedLift N (j + 1) N1
      rw [hz, hzqJRaw, hFjRaw, hej]
      have hdot : dotProduct (influenceRow N j) delta =
          influenceRow N j i := by simp [dotProduct, delta]
      rw [hperturbZero, hcenterZero, hliftZero, hcenterZero, hliftZero,
        hdot]
      simp [N1]
    have hzqBound : |zq k + s * influenceRow N j i| ≤ s ^ 2 * Cc := by
      rw [hzqPulse]
      have hs2 := mul_le_mul_of_nonneg_left hN1Lift (sq_nonneg s)
      rw [show -s * influenceRow N j i +
          s ^ 2 * actualQuadraticCorrectedLift N (j + 1) N1 +
          s * influenceRow N j i =
          s ^ 2 * actualQuadraticCorrectedLift N (j + 1) N1 by ring,
        abs_mul, abs_of_nonneg (sq_nonneg s)]
      simpa [Cc, mul_assoc] using hs2
    have hXtail : ∀ t, k ≤ t →
        X (t + 1) = fun q =>
          (N.rowMix t *ᵥ X t) q - s * X t q - s * U t q := by
      intro t hkt
      rw [hXrec t]
      have htj : t ≠ j := by
        dsimp [k] at hkt
        omega
      funext q
      simp [htj]
    have hUtail : ∀ t, k ≤ t →
        U (t + 1) = fun q =>
          (N.colMix t *ᵥ U t) q + ((N.colMix t - 1) *ᵥ X t) q := by
      intro t hkt
      rw [hUrec t]
      have htj : t ≠ j := by
        dsimp [k] at hkt
        omega
      funext q
      simp [htj, Matrix.mulVec, dotProduct]
    exact ⟨hFkGauge, hEk, hzqBound, hXtail, hUtail⟩

/-- The stochastic half of equation (48), for a literal unit pulse in the
equation-(46) input.  The fast `s * r_f^m` contribution is retained. -/
theorem actual_quadratic_equation48_impulse_response
    (N : NetworkSetup n) :
    ∃ Cr sResp : ℝ, 0 ≤ Cr ∧ 0 < sResp ∧
      ∀ (s : ℝ), 0 < s → s ≤ sResp → ∀ (j : ℕ) (i : Fin n)
        (X U : ℕ → Fin n → ℝ),
        let e : ℕ → Fin n → ℝ := fun t q =>
          if t = j then if q = i then 1 else 0 else 0
        (∀ r, (∑ q, U r q) = 0) → X j = 0 → U j = 0 →
        (∀ t, X (t + 1) = fun q =>
          (N.rowMix t *ᵥ X t) q - s * X t q - s * U t q - s * e t q) →
        (∀ t, U (t + 1) = fun q =>
          (N.colMix t *ᵥ U t) q + ((N.colMix t - 1) *ᵥ X t) q +
            ((N.colMix t - 1) *ᵥ e t) q) →
        ∀ m : ℕ,
          |(n : ℝ)⁻¹ * ∑ q, X (j + 1 + m) q +
              s * influenceRow N j i *
                (∏ r ∈ Finset.Ico (j + 1) (j + 1 + m),
                  (1 - s * gain N r))| ≤
            Cr * (s ^ 2 * (1 - gainFloor N * s / 4) ^ m +
              s * loadingTransverseRate N ^ m) := by
  classical
  rcases actual_quadratic_gain_product_comparison_uniform N with
    ⟨M, K0, J0, B0, Aq, Lq, Cz, Cf, Cd, CEf, CEs, Co, Cof, sResp,
      hM, hK0, hJ0, hB0, hAq, hLq, hCz, hCf, hCd, hCEf, hCEs,
      hCo, hCof, hsResp, hpack⟩
  rcases actual_quadratic_single_impulse_initial_bounds N with
    ⟨Kp, Jp, Bp, Nf, Cc, hKp, hJp, hBp, hNf, hCc, _hKpulse, hpulse⟩
  let Cr : ℝ := 2 * rowMixingConstant N + Cof * Nf +
    Co * (influenceRowBound N + Cc + Nf) + Cc
  have hrowC : 0 ≤ rowMixingConstant N := by
    unfold rowMixingConstant
    exact div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (blockContraction_pos N).le
  have hBstar : 0 ≤ influenceRowBound N := by
    have hnorm : 0 ≤ nodeL2Norm (influenceRow N 0) := by
      unfold nodeL2Norm
      exact Real.sqrt_nonneg _
    exact hnorm.trans (influenceRow_nodeL2_le N 0)
  have hCr : 0 ≤ Cr := by
    dsimp [Cr]
    positivity
  refine ⟨Cr, sResp, hCr, hsResp, ?_⟩
  intro s hs hsCap j i X U
  dsimp only
  intro hUzero hXj hUj hXrec hUrec m
  have hcaps := (hpack s hs hsCap).1
  have hs1 : s ≤ 1 := hcaps.1
  have hinit := hpulse s hs hs1 j i X U hUzero hXj hUj
    (by simpa using hXrec) (by simpa using hUrec)
  dsimp only at hinit
  let k := j + 1
  let xi := loadingSlowCenter N X
  let F := loadingFastCoordinates N X U
  let zq : ℕ → ℝ := fun r =>
    xi r - s * actualQuadraticCorrectedLift N r (F r)
  let qslow : ℝ := 1 - gainFloor N * s / 4
  let G : ℕ → ℝ := fun t =>
    nodeSupNorm (F t).1 + nodeL1Norm (F t).2
  let P : ℝ := ∏ r ∈ Finset.Ico k (k + m), (1 - s * gain N r)
  have hcompare := (hpack s hs hsCap).2 X U k m hUzero
    hinit.2.2.2.1 hinit.2.2.2.2
  have hout :
      |(n : ℝ)⁻¹ * ∑ a, X (k + m) a - P * zq k| ≤
        rowMixingConstant N * mixingRate N ^ m *
            nodeL2Norm (disagreement (X k)) +
          Cof * s * loadingTransverseRate N ^ m * G k +
          Co * (s * |zq k| + s ^ 2 * G k) * qslow ^ m := by
    simpa [k, xi, F, zq, qslow, G, P] using hcompare.2
  have hbi : |influenceRow N j i| ≤ influenceRowBound N :=
    (abs_le_nodeL2Norm (influenceRow N j) i).trans
      (influenceRow_nodeL2_le N j)
  have hzq : |zq k| ≤ s * (influenceRowBound N + Cc) := by
    have hsplit : zq k = (zq k + s * influenceRow N j i) -
        s * influenceRow N j i := by ring
    rw [hsplit]
    calc
      |zq k + s * influenceRow N j i - s * influenceRow N j i| ≤
          |zq k + s * influenceRow N j i| +
            |s * influenceRow N j i| := abs_sub _ _
      _ ≤ s ^ 2 * Cc + s * influenceRowBound N := by
        rw [abs_mul, abs_of_pos hs]
        exact add_le_add hinit.2.2.1
          (mul_le_mul_of_nonneg_left hbi hs.le)
      _ ≤ s * (influenceRowBound N + Cc) := by
        have hs2 : s ^ 2 ≤ s := by nlinarith [sq_nonneg s]
        have hmul : s ^ 2 * Cc ≤ s * Cc :=
          mul_le_mul_of_nonneg_right hs2 hCc
        nlinarith
  have hcarrier : s * |zq k| + s ^ 2 * G k ≤
      s ^ 2 * (influenceRowBound N + Cc + Nf) := by
    calc
      s * |zq k| + s ^ 2 * G k ≤
          s * (s * (influenceRowBound N + Cc)) + s ^ 2 * Nf :=
        add_le_add (mul_le_mul_of_nonneg_left hzq hs.le)
          (mul_le_mul_of_nonneg_left hinit.1 (sq_nonneg s))
      _ = s ^ 2 * (influenceRowBound N + Cc + Nf) := by ring
  have hrhoFast : mixingRate N ≤ loadingTransverseRate N := by
    unfold loadingTransverseRate loadingFastRate loadingTriangularRate
    linarith [mixingRate_lt_one N]
  have hrho0 : 0 ≤ mixingRate N := mixingRate_nonneg N
  have hfast0 : 0 ≤ loadingTransverseRate N := by
    unfold loadingTransverseRate loadingFastRate loadingTriangularRate
    linarith [mixingRate_nonneg N]
  have hrhoPow : mixingRate N ^ m ≤ loadingTransverseRate N ^ m :=
    pow_le_pow_left₀ hrho0 hrhoFast m
  have hq0 : 0 ≤ qslow := by simpa [qslow] using hcaps.2.2.2.2.2.2.1.le
  have hgf0 : 0 ≤ gainFloor N :=
    (uniform_mixing_and_influence N).2.2.2.2.2.2.2.1.le
  have hfactor (r : ℕ) :
      |1 - s * gain N r| ≤ qslow := by
    have hgainN := gain_le_n N r
    have hnonneg : 0 ≤ 1 - s * gain N r := by
      have hscaled := mul_le_mul_of_nonneg_left hgainN hs.le
      nlinarith [hcaps.2.2.1]
    rw [abs_of_nonneg hnonneg]
    have hfloor := gainFloor_le_gain N r
    have hscaled := mul_le_mul_of_nonneg_left hfloor hs.le
    dsimp [qslow]
    nlinarith [mul_nonneg hs.le hgf0]
  have habsProd (S : Finset ℕ) (f : ℕ → ℝ) :
      |∏ r ∈ S, f r| = ∏ r ∈ S, |f r| := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a S ha ih => simp [Finset.prod_insert, ha, abs_mul, ih]
  have hP : |P| ≤ qslow ^ m := by
    dsimp [P]
    rw [habsProd]
    calc
      (∏ r ∈ Finset.Ico k (k + m), |1 - s * gain N r|) ≤
          ∏ _r ∈ Finset.Ico k (k + m), qslow := by
        exact Finset.prod_le_prod
          (fun r _ => abs_nonneg (1 - s * gain N r))
          fun r _ => hfactor r
      _ = qslow ^ m := by simp
  have hfastPow0 : 0 ≤ loadingTransverseRate N ^ m := pow_nonneg hfast0 m
  have hslowPow0 : 0 ≤ qslow ^ m := pow_nonneg hq0 m
  calc
    |(n : ℝ)⁻¹ * ∑ a, X (j + 1 + m) a +
        s * influenceRow N j i *
          (∏ r ∈ Finset.Ico (j + 1) (j + 1 + m),
            (1 - s * gain N r))| =
      |((n : ℝ)⁻¹ * ∑ a, X (k + m) a - P * zq k) +
        P * (zq k + s * influenceRow N j i)| := by
          congr 1
          dsimp [k, P]
          ring
    _ ≤ |(n : ℝ)⁻¹ * ∑ a, X (k + m) a - P * zq k| +
        |P * (zq k + s * influenceRow N j i)| := abs_add_le _ _
    _ ≤ (rowMixingConstant N * mixingRate N ^ m * (2 * s) +
          Cof * s * loadingTransverseRate N ^ m * Nf +
          Co * (s ^ 2 * (influenceRowBound N + Cc + Nf)) * qslow ^ m) +
        qslow ^ m * (s ^ 2 * Cc) := by
      apply add_le_add
      · exact hout.trans (add_le_add
          (add_le_add
            (mul_le_mul_of_nonneg_left hinit.2.1
              (mul_nonneg hrowC (pow_nonneg hrho0 m)))
            (mul_le_mul_of_nonneg_left hinit.1
              (mul_nonneg (mul_nonneg hCof hs.le)
                (pow_nonneg (by
                  unfold loadingTransverseRate
                  positivity) m))))
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcarrier hCo) hslowPow0))
      · rw [abs_mul]
        calc
          |P| * |zq k + s * influenceRow N j i| ≤
              qslow ^ m * |zq k + s * influenceRow N j i| :=
            mul_le_mul_of_nonneg_right hP (abs_nonneg _)
          _ ≤ qslow ^ m * (s ^ 2 * Cc) :=
            mul_le_mul_of_nonneg_left hinit.2.2.1 hslowPow0
    _ ≤ Cr * (s ^ 2 * qslow ^ m + s * loadingTransverseRate N ^ m) := by
      dsimp [Cr]
      have hslowCoeff : 0 ≤ influenceRowBound N + Cc + Nf := by positivity
      have hfastCoeff : 0 ≤ Cof * Nf := mul_nonneg hCof hNf
      have hmixTerm :
          (2 * rowMixingConstant N) * (s * mixingRate N ^ m) ≤
            (2 * rowMixingConstant N) *
              (s * loadingTransverseRate N ^ m) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hrhoPow hs.le)
          (mul_nonneg (by norm_num) hrowC)
      calc
        _ ≤ (2 * rowMixingConstant N + Cof * Nf) *
                (s * loadingTransverseRate N ^ m) +
              (Co * (influenceRowBound N + Cc + Nf) + Cc) *
                (s ^ 2 * qslow ^ m) := by
          calc
            _ = ((2 * rowMixingConstant N) * (s * mixingRate N ^ m) +
                  (Cof * Nf) * (s * loadingTransverseRate N ^ m)) +
                ((Co * (influenceRowBound N + Cc + Nf)) *
                    (s ^ 2 * qslow ^ m) + Cc * (s ^ 2 * qslow ^ m)) := by
              ring
            _ ≤ ((2 * rowMixingConstant N) *
                    (s * loadingTransverseRate N ^ m) +
                  (Cof * Nf) * (s * loadingTransverseRate N ^ m)) +
                ((Co * (influenceRowBound N + Cc + Nf)) *
                    (s ^ 2 * qslow ^ m) + Cc * (s ^ 2 * qslow ^ m)) :=
              add_le_add (add_le_add hmixTerm le_rfl) le_rfl
            _ = _ := by ring
        _ ≤ (2 * rowMixingConstant N + Cof * Nf +
              Co * (influenceRowBound N + Cc + Nf) + Cc) *
              (s ^ 2 * qslow ^ m + s * loadingTransverseRate N ^ m) := by
          have hA : 0 ≤ 2 * rowMixingConstant N + Cof * Nf := by positivity
          have hB : 0 ≤ Co * (influenceRowBound N + Cc + Nf) + Cc := by
            positivity
          nlinarith [mul_nonneg (mul_nonneg (sq_nonneg s) hslowPow0) hA,
            mul_nonneg (mul_nonneg hs.le hfastPow0) hB]
    _ = Cr * (s ^ 2 * (1 - gainFloor N * s / 4) ^ m +
        s * loadingTransverseRate N ^ m) := by rfl

/-- The deterministic half of equation (48): from the true consensus initial
state, the actual arithmetic output is uniformly close to the finite gain
product.  Both constants are selected before the stepsize. -/
theorem actual_quadratic_equation48_deterministic_signal
    (N : NetworkSetup n) :
    ∃ Ca sResp : ℝ, 0 ≤ Ca ∧ 0 < sResp ∧
      ∀ (s : ℝ), 0 < s → s ≤ sResp →
        ∀ (X U : ℕ → Fin n → ℝ) (m : ℕ),
          X 0 = 1 → U 0 = 0 →
          (∀ r, (∑ q, U r q) = 0) →
          (∀ t, X (t + 1) = fun q =>
            (N.rowMix t *ᵥ X t) q - s * X t q - s * U t q) →
          (∀ t, U (t + 1) = fun q =>
            (N.colMix t *ᵥ U t) q +
              ((N.colMix t - 1) *ᵥ X t) q) →
          |(n : ℝ)⁻¹ * ∑ j, X m j -
              (∏ r ∈ Finset.Ico 0 m, (1 - s * gain N r))| ≤
            Ca * s * (1 - gainFloor N * s / 4) ^ m := by
  rcases actual_quadratic_gain_product_comparison_uniform N with
    ⟨M, K0, J0, B0, Aq, Lq, Cz, Cf, Cd, CEf, CEs, Co, Cof, sResp,
      hM, hK0, hJ0, hB0, hAq, hLq, hCz, hCf, hCd, hCEf, hCEs,
      hCo, hCof, hsResp, hpack⟩
  refine ⟨Co, sResp, hCo, hsResp, ?_⟩
  intro s hs hsCap X U m hX0 hU0 hUzero hXrec hUrec
  have hres := (hpack s hs hsCap).2 X U 0 m hUzero
    (fun t _ => hXrec t) (fun t _ => hUrec t)
  dsimp only at hres
  have hout := hres.2
  have hpiSum : ∑ q, absoluteProbability N 0 q = 1 :=
    (absoluteProbability_spec N).2.1 0
  have hxi0 : loadingSlowCenter N X 0 = 1 := by
    rw [loadingSlowCenter, hX0]
    unfold dotProduct
    simpa using hpiSum
  have hF0 : loadingFastCoordinates N X U 0 = (0, 0) := by
    apply Prod.ext <;> funext q <;>
      simp [loadingFastCoordinates, hxi0, hX0, hU0]
  have hlift0 : actualQuadraticCorrectedLift N 0
      ((0 : Fin n → ℝ), (0 : Fin n → ℝ)) = 0 := by
    have h := actualQuadraticCorrectedLift_scale N 0 0
      (0 : (Fin n → ℝ) × (Fin n → ℝ))
    simpa [loadingFastScale] using h
  have hz0 : loadingSlowCenter N X 0 -
      s * actualQuadraticCorrectedLift N 0
        (loadingFastCoordinates N X U 0) = 1 := by
    rw [hxi0, hF0, hlift0]
    ring
  have hG0 : nodeSupNorm (loadingFastCoordinates N X U 0).1 +
      nodeL1Norm (loadingFastCoordinates N X U 0).2 = 0 := by
    rw [hF0]
    simp [nodeSupNorm, nodeL1Norm]
  have hE0 : nodeL2Norm (disagreement (X 0)) = 0 := by
    rw [hX0]
    simp [nodeL2Norm, disagreement, Nat.ne_of_gt N.hn]
  simpa [hz0, hG0, hE0] using hout

/-- On the uniform response cap, every finite nonautonomous gain product is
dominated by the source slow rate `q_s = 1-gs/4`. -/
theorem actual_quadratic_gain_product_abs_le_slow_rate
    (N : NetworkSetup n) (s : ℝ) (k m : ℕ)
    (hs : 0 < s) (hsn : s * (n : ℝ) ≤ 1 / 4) :
    |∏ r ∈ Finset.Ico k (k + m), (1 - s * gain N r)| ≤
      (1 - gainFloor N * s / 4) ^ m := by
  have hgf0 : 0 ≤ gainFloor N :=
    (uniform_mixing_and_influence N).2.2.2.2.2.2.2.1.le
  have hq0 : 0 ≤ 1 - gainFloor N * s / 4 := by
    have hgf_le_n : gainFloor N ≤ (n : ℝ) :=
      (gainFloor_le_gain N 0).trans (gain_le_n N 0)
    have hscaled := mul_le_mul_of_nonneg_left hgf_le_n hs.le
    nlinarith
  have hfactor (r : ℕ) :
      |1 - s * gain N r| ≤ 1 - gainFloor N * s / 4 := by
    have hgainN := gain_le_n N r
    have hnonneg : 0 ≤ 1 - s * gain N r := by
      have hscaled := mul_le_mul_of_nonneg_left hgainN hs.le
      nlinarith
    rw [abs_of_nonneg hnonneg]
    have hfloor := gainFloor_le_gain N r
    have hscaled := mul_le_mul_of_nonneg_left hfloor hs.le
    nlinarith [mul_nonneg hs.le hgf0]
  have habsProd (S : Finset ℕ) (f : ℕ → ℝ) :
      |∏ r ∈ S, f r| = ∏ r ∈ S, |f r| := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a S ha ih => simp [Finset.prod_insert, ha, abs_mul, ih]
  rw [habsProd]
  calc
    (∏ r ∈ Finset.Ico k (k + m), |1 - s * gain N r|) ≤
        ∏ _r ∈ Finset.Ico k (k + m),
          (1 - gainFloor N * s / 4) := by
      exact Finset.prod_le_prod
        (fun r _ => abs_nonneg (1 - s * gain N r))
        fun r hr => hfactor r
    _ = (1 - gainFloor N * s / 4) ^ m := by simp

/-- Finite pathwise superposition for the scalar equation-(46) system.  The
homogeneous response and every summand are genuine trajectories of the same
time-varying system; the latter is driven by a literal node-time unit pulse. -/
theorem actual_quadratic_pathwise_superposition
    (N : NetworkSetup n) (s x0 : ℝ)
    (X U e Xsig Usig : ℕ → Fin n → ℝ)
    (Xpulse Upulse : ℕ → Fin n → ℕ → Fin n → ℝ)
    (hX0 : X 0 = fun _ => x0) (hU0 : U 0 = 0)
    (hXsig0 : Xsig 0 = 1) (hUsig0 : Usig 0 = 0)
    (hXrec : ∀ t, X (t + 1) = fun q =>
      (N.rowMix t *ᵥ X t) q - s * X t q - s * U t q - s * e t q)
    (hUrec : ∀ t, U (t + 1) = fun q =>
      (N.colMix t *ᵥ U t) q + ((N.colMix t - 1) *ᵥ X t) q +
        ((N.colMix t - 1) *ᵥ e t) q)
    (hXsigRec : ∀ t, Xsig (t + 1) = fun q =>
      (N.rowMix t *ᵥ Xsig t) q - s * Xsig t q - s * Usig t q)
    (hUsigRec : ∀ t, Usig (t + 1) = fun q =>
      (N.colMix t *ᵥ Usig t) q + ((N.colMix t - 1) *ᵥ Xsig t) q)
    (hXpulse0 : ∀ j i, Xpulse j i j = 0)
    (hUpulse0 : ∀ j i, Upulse j i j = 0)
    (hXpulseRec : ∀ j i t, Xpulse j i (t + 1) = fun q =>
      (N.rowMix t *ᵥ Xpulse j i t) q - s * Xpulse j i t q -
        s * Upulse j i t q -
        s * (if t = j then if q = i then 1 else 0 else 0))
    (hUpulseRec : ∀ j i t, Upulse j i (t + 1) = fun q =>
      (N.colMix t *ᵥ Upulse j i t) q +
        ((N.colMix t - 1) *ᵥ Xpulse j i t) q +
        ((N.colMix t - 1) *ᵥ
          (fun q => if t = j then if q = i then 1 else 0 else 0)) q) :
    ∀ t,
      X t = x0 • Xsig t +
          ∑ j ∈ Finset.range t, ∑ i, e j i • Xpulse j i t ∧
      U t = x0 • Usig t +
          ∑ j ∈ Finset.range t, ∑ i, e j i • Upulse j i t := by
  classical
  intro t
  induction t with
  | zero =>
      rw [hX0, hU0, hXsig0, hUsig0]
      constructor <;> funext q <;> simp
  | succ t ih =>
      rcases ih with ⟨ihX, ihU⟩
      let SX : Fin n → ℝ :=
        ∑ j ∈ Finset.range t, ∑ i, e j i • Xpulse j i t
      let SU : Fin n → ℝ :=
        ∑ j ∈ Finset.range t, ∑ i, e j i • Upulse j i t
      have hXold :
          (∑ j ∈ Finset.range t, ∑ i, e j i • Xpulse j i (t + 1)) =
            fun q => (N.rowMix t *ᵥ SX) q - s * SX q - s * SU q := by
        calc
          (∑ j ∈ Finset.range t, ∑ i,
              e j i • Xpulse j i (t + 1)) =
              ∑ j ∈ Finset.range t, ∑ i, e j i •
                (fun q => (N.rowMix t *ᵥ Xpulse j i t) q -
                  s * Xpulse j i t q - s * Upulse j i t q) := by
            apply Finset.sum_congr rfl
            intro j hj
            apply Finset.sum_congr rfl
            intro i hi
            rw [hXpulseRec j i t]
            simp [ne_of_gt (Finset.mem_range.mp hj)]
          _ = fun q => (N.rowMix t *ᵥ SX) q - s * SX q - s * SU q := by
            funext q
            have hscaleX :
                (∑ j ∈ Finset.range t, ∑ i,
                  e j i • (s * Xpulse j i t q)) =
                  s * ∑ j ∈ Finset.range t, ∑ i,
                    e j i • Xpulse j i t q := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j hj
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              simp only [smul_eq_mul]
              ring
            have hscaleU :
                (∑ j ∈ Finset.range t, ∑ i,
                  e j i • (s * Upulse j i t q)) =
                  s * ∑ j ∈ Finset.range t, ∑ i,
                    e j i • Upulse j i t q := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j hj
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              simp only [smul_eq_mul]
              ring
            simp only [SX, SU, Matrix.mulVec_sum, Matrix.mulVec_smul,
              Pi.smul_apply, Finset.smul_sum, Finset.sum_sub_distrib,
              Finset.sum_apply, smul_sub]
            rw [hscaleX, hscaleU]
      have hUold :
          (∑ j ∈ Finset.range t, ∑ i, e j i • Upulse j i (t + 1)) =
            fun q => (N.colMix t *ᵥ SU) q +
              ((N.colMix t - 1) *ᵥ SX) q := by
        calc
          (∑ j ∈ Finset.range t, ∑ i,
              e j i • Upulse j i (t + 1)) =
              ∑ j ∈ Finset.range t, ∑ i, e j i •
                (fun q => (N.colMix t *ᵥ Upulse j i t) q +
                  ((N.colMix t - 1) *ᵥ Xpulse j i t) q) := by
            apply Finset.sum_congr rfl
            intro j hj
            apply Finset.sum_congr rfl
            intro i hi
            rw [hUpulseRec j i t]
            simp [ne_of_gt (Finset.mem_range.mp hj), Matrix.mulVec]
          _ = fun q => (N.colMix t *ᵥ SU) q +
              ((N.colMix t - 1) *ᵥ SX) q := by
            funext q
            simp only [SX, SU, Matrix.mulVec_sum, Matrix.mulVec_smul,
              Pi.smul_apply, Finset.smul_sum, Finset.sum_add_distrib,
              Finset.sum_apply, smul_add]
      have hXnew :
          (∑ i, e t i • Xpulse t i (t + 1)) = fun q => -s * e t q := by
        funext q
        simp [hXpulseRec, hXpulse0, hUpulse0, Matrix.mulVec]
        ring
      have hUnew :
          (∑ i, e t i • Upulse t i (t + 1)) =
            fun q => ((N.colMix t - 1) *ᵥ e t) q := by
        funext q
        simp [hUpulseRec, hXpulse0, hUpulse0, Matrix.mulVec, dotProduct,
          Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      constructor
      · rw [hXrec t, hXsigRec t, Finset.sum_range_succ, hXold, hXnew]
        rw [ihX, ihU]
        change (fun q =>
          (N.rowMix t *ᵥ (x0 • Xsig t + SX)) q -
            s * (x0 • Xsig t + SX) q -
            s * (x0 • Usig t + SU) q - s * e t q) = _
        rw [Matrix.mulVec_add, Matrix.mulVec_smul]
        funext q
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      · rw [hUrec t, hUsigRec t, Finset.sum_range_succ, hUold, hUnew]
        rw [ihX, ihU]
        change (fun q =>
          (N.colMix t *ᵥ (x0 • Usig t + SU)) q +
            ((N.colMix t - 1) *ᵥ (x0 • Xsig t + SX)) q +
            ((N.colMix t - 1) *ᵥ e t) q) = _
        rw [Matrix.mulVec_add, Matrix.mulVec_smul,
          Matrix.mulVec_add, Matrix.mulVec_smul]
        funext q
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring

/-- Canonical scalar equation-(46) trajectory with constant initial primal
coordinate and an arbitrary deterministic input table. -/
def actualQuadraticScalarTrajectory
    (N : NetworkSetup n) (s x0 : ℝ) (e : ℕ → Fin n → ℝ) :
    ℕ → (Fin n → ℝ) × (Fin n → ℝ)
  | 0 => (fun _ => x0, 0)
  | t + 1 =>
      let Z := actualQuadraticScalarTrajectory N s x0 e t
      (fun q => (N.rowMix t *ᵥ Z.1) q - s * Z.1 q - s * Z.2 q - s * e t q,
       fun q => (N.colMix t *ᵥ Z.2) q + ((N.colMix t - 1) *ᵥ Z.1) q +
         ((N.colMix t - 1) *ᵥ e t) q)

/-- A canonical unit-pulse trajectory is exactly zero through its pulse time;
the pulse enters the transition from `j` to `j+1`. -/
theorem actualQuadraticScalarTrajectory_zero_before_pulse
    (N : NetworkSetup n) (s : ℝ) (j : ℕ) (i : Fin n) (t : ℕ)
    (ht : t ≤ j) :
    actualQuadraticScalarTrajectory N s 0
        (fun r q => if r = j then if q = i then 1 else 0 else 0) t =
      (0, 0) := by
  induction t with
  | zero =>
      rfl
  | succ t ih =>
      have htj : t < j := Nat.lt_of_succ_le ht
      rw [actualQuadraticScalarTrajectory]
      rw [ih (Nat.le_of_lt htj)]
      apply Prod.ext <;> funext q <;>
        simp [ne_of_lt htj, Matrix.mulVec]

/-- Equation (52)'s one-step calculation: at the first time after a unit
pulse, its arithmetic primal response is exactly `-s/n`, independently of
all mixing and stability properties. -/
theorem actualQuadraticScalarTrajectory_newest_pulse_mean
    (N : NetworkSetup n) (s : ℝ) (j : ℕ) (i : Fin n) :
    (n : ℝ)⁻¹ * ∑ q,
        (actualQuadraticScalarTrajectory N s 0
          (fun r q => if r = j then if q = i then 1 else 0 else 0)
          (j + 1)).1 q = -s / (n : ℝ) := by
  rw [actualQuadraticScalarTrajectory]
  rw [actualQuadraticScalarTrajectory_zero_before_pulse N s j i j le_rfl]
  simp only [Prod.fst_zero, Prod.snd_zero]
  simp [Matrix.mulVec, N.hn, div_eq_mul_inv]
  ring

/-- The variance-energy form of equation (52), obtained by retaining only
the newest pulse `j=t-1` at every positive time. -/
theorem actual_quadratic_newest_noise_variance_lower
    (N : NetworkSetup n) (s : ℝ) (T : PositiveHorizon) :
    (((T.1 - 1 : ℕ) : ℝ) * s ^ 2) / (n : ℝ) ≤
      ∑ t ∈ Finset.range T.1, ∑ j ∈ Finset.range t, ∑ i,
        ((n : ℝ)⁻¹ * ∑ q,
          (actualQuadraticScalarTrajectory N s 0
            (fun r q => if r = j then if q = i then 1 else 0 else 0)
            t).1 q) ^ 2 := by
  classical
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr N.hn
  have htime (t : ℕ) (ht : t ∈ Finset.Ico 1 T.1) :
      s ^ 2 / (n : ℝ) ≤
        ∑ j ∈ Finset.range t, ∑ i,
          ((n : ℝ)⁻¹ * ∑ q,
            (actualQuadraticScalarTrajectory N s 0
              (fun r q => if r = j then if q = i then 1 else 0 else 0)
              t).1 q) ^ 2 := by
    have htpos : 0 < t := (Finset.mem_Ico.mp ht).1
    have hpred : t - 1 ∈ Finset.range t :=
      Finset.mem_range.mpr (Nat.sub_lt htpos (by omega))
    have hsucc : t - 1 + 1 = t := Nat.sub_add_cancel htpos
    have hnew (i : Fin n) :
        (n : ℝ)⁻¹ * ∑ q,
            (actualQuadraticScalarTrajectory N s 0
              (fun r q => if r = t - 1 then if q = i then 1 else 0 else 0)
              t).1 q = -s / (n : ℝ) := by
      rw [← hsucc]
      exact actualQuadraticScalarTrajectory_newest_pulse_mean N s (t - 1) i
    calc
      s ^ 2 / (n : ℝ) = ∑ i : Fin n, (-s / (n : ℝ)) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        field_simp [hn.ne']
      _ = ∑ i,
          ((n : ℝ)⁻¹ * ∑ q,
            (actualQuadraticScalarTrajectory N s 0
              (fun r q => if r = t - 1 then if q = i then 1 else 0 else 0)
              t).1 q) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [hnew i]
      _ ≤ ∑ j ∈ Finset.range t, ∑ i,
          ((n : ℝ)⁻¹ * ∑ q,
            (actualQuadraticScalarTrajectory N s 0
              (fun r q => if r = j then if q = i then 1 else 0 else 0)
              t).1 q) ^ 2 := by
        exact Finset.single_le_sum
          (s := Finset.range t)
          (f := fun j => ∑ i,
            ((n : ℝ)⁻¹ * ∑ q,
              (actualQuadraticScalarTrajectory N s 0
                (fun r q => if r = j then if q = i then 1 else 0 else 0)
                t).1 q) ^ 2)
          (fun j hj => Finset.sum_nonneg fun i hi => sq_nonneg _) hpred
  calc
    (((T.1 - 1 : ℕ) : ℝ) * s ^ 2) / (n : ℝ) =
        ∑ _t ∈ Finset.Ico 1 T.1, s ^ 2 / (n : ℝ) := by
      simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      ring
    _ ≤ ∑ t ∈ Finset.Ico 1 T.1, ∑ j ∈ Finset.range t, ∑ i,
          ((n : ℝ)⁻¹ * ∑ q,
            (actualQuadraticScalarTrajectory N s 0
              (fun r q => if r = j then if q = i then 1 else 0 else 0)
              t).1 q) ^ 2 := Finset.sum_le_sum htime
    _ ≤ ∑ t ∈ Finset.range T.1, ∑ j ∈ Finset.range t, ∑ i,
          ((n : ℝ)⁻¹ * ∑ q,
            (actualQuadraticScalarTrajectory N s 0
              (fun r q => if r = j then if q = i then 1 else 0 else 0)
              t).1 q) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro t ht
        exact Finset.mem_range.mpr (Finset.mem_Ico.mp ht).2
      · intro t htT ht
        exact Finset.sum_nonneg fun j hj =>
          Finset.sum_nonneg fun i hi => sq_nonneg _

/-- The tracker-residual component of every canonical equation-(46)
trajectory has zero total mass.  Column stochasticity kills both innovation
terms and preserves the preceding tracker mass. -/
theorem actualQuadraticScalarTrajectory_tracker_sum_eq_zero
    (N : NetworkSetup n) (s x0 : ℝ) (e : ℕ → Fin n → ℝ) :
    ∀ t, ∑ q, (actualQuadraticScalarTrajectory N s x0 e t).2 q = 0 := by
  intro t
  induction t with
  | zero => simp [actualQuadraticScalarTrajectory]
  | succ t ih =>
      rw [actualQuadraticScalarTrajectory]
      dsimp only
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      rw [Matrix.sum_mulVec_of_mem_colStochastic (N.col_stochastic t)]
      simp only [Matrix.sub_mulVec, Matrix.one_mulVec,
        Pi.sub_apply, Finset.sum_sub_distrib]
      rw [Matrix.sum_mulVec_of_mem_colStochastic (N.col_stochastic t)]
      rw [Matrix.sum_mulVec_of_mem_colStochastic (N.col_stochastic t)]
      rw [ih]
      ring

/-- The canonical homogeneous and literal unit-pulse responses give the
finite Duhamel expansion of every scalar equation-(46) trajectory. -/
theorem actual_quadratic_canonical_pathwise_superposition
    (N : NetworkSetup n) (s x0 : ℝ)
    (X U e : ℕ → Fin n → ℝ)
    (hX0 : X 0 = fun _ => x0) (hU0 : U 0 = 0)
    (hXrec : ∀ t, X (t + 1) = fun q =>
      (N.rowMix t *ᵥ X t) q - s * X t q - s * U t q - s * e t q)
    (hUrec : ∀ t, U (t + 1) = fun q =>
      (N.colMix t *ᵥ U t) q + ((N.colMix t - 1) *ᵥ X t) q +
        ((N.colMix t - 1) *ᵥ e t) q) :
    let signal := actualQuadraticScalarTrajectory N s 1 (fun _ _ => 0)
    let pulse := fun (j : ℕ) (i : Fin n) =>
      actualQuadraticScalarTrajectory N s 0
        (fun r q => if r = j then if q = i then 1 else 0 else 0)
    ∀ t,
      X t = x0 • (signal t).1 +
          ∑ j ∈ Finset.range t, ∑ i, e j i • (pulse j i t).1 ∧
      U t = x0 • (signal t).2 +
          ∑ j ∈ Finset.range t, ∑ i, e j i • (pulse j i t).2 := by
  dsimp only
  apply actual_quadratic_pathwise_superposition N s x0 X U e
    (fun t => (actualQuadraticScalarTrajectory N s 1 (fun _ _ => 0) t).1)
    (fun t => (actualQuadraticScalarTrajectory N s 1 (fun _ _ => 0) t).2)
    (fun j i t =>
      (actualQuadraticScalarTrajectory N s 0
        (fun r q => if r = j then if q = i then 1 else 0 else 0) t).1)
    (fun j i t =>
      (actualQuadraticScalarTrajectory N s 0
        (fun r q => if r = j then if q = i then 1 else 0 else 0) t).2)
    hX0 hU0
  · rfl
  · rfl
  · exact hXrec
  · exact hUrec
  · intro t
    rw [actualQuadraticScalarTrajectory]
    funext q
    simp [Matrix.mulVec]
  · intro t
    rw [actualQuadraticScalarTrajectory]
    funext q
    simp [Matrix.mulVec]
  · intro j i
    exact congrArg Prod.fst
      (actualQuadraticScalarTrajectory_zero_before_pulse N s j i j le_rfl)
  · intro j i
    exact congrArg Prod.snd
      (actualQuadraticScalarTrajectory_zero_before_pulse N s j i j le_rfl)
  · intro j i t
    rfl
  · intro j i t
    rfl

/-- Specialization of the canonical scalar superposition to the genuine
`Point 1` equation-(46) recurrence. -/
theorem actual_quadratic_point_pathwise_superposition
    (N : NetworkSetup n) (s x0 : ℝ)
    (XV UV eV : ℕ → NodeTable n 1)
    (hX0 : ∀ i, XV 0 i (0 : Fin 1) = x0) (hUV0 : UV 0 = 0)
    (hstep : ∀ t,
      XV (t + 1) =
          leftAct (N.rowMix t - s • 1) (XV t) - s • UV t - s • eV t ∧
      UV (t + 1) =
          leftAct (N.colMix t - 1) (XV t) +
            leftAct (N.colMix t) (UV t) +
            leftAct (N.colMix t - 1) (eV t)) :
    let X : ℕ → Fin n → ℝ := fun r i => XV r i (0 : Fin 1)
    let U : ℕ → Fin n → ℝ := fun r i => UV r i (0 : Fin 1)
    let e : ℕ → Fin n → ℝ := fun r i => eV r i (0 : Fin 1)
    let signal := actualQuadraticScalarTrajectory N s 1 (fun _ _ => 0)
    let pulse := fun (j : ℕ) (i : Fin n) =>
      actualQuadraticScalarTrajectory N s 0
        (fun r q => if r = j then if q = i then 1 else 0 else 0)
    ∀ t,
      X t = x0 • (signal t).1 +
          ∑ j ∈ Finset.range t, ∑ i, e j i • (pulse j i t).1 ∧
      U t = x0 • (signal t).2 +
          ∑ j ∈ Finset.range t, ∑ i, e j i • (pulse j i t).2 := by
  classical
  dsimp only
  let X : ℕ → Fin n → ℝ := fun r i => XV r i (0 : Fin 1)
  let U : ℕ → Fin n → ℝ := fun r i => UV r i (0 : Fin 1)
  let e : ℕ → Fin n → ℝ := fun r i => eV r i (0 : Fin 1)
  have hXscalar0 : X 0 = fun _ => x0 := by
    funext i
    exact hX0 i
  have hUscalar0 : U 0 = 0 := by
    have hcoord := congrArg
      (fun Z : NodeTable n 1 => fun i => Z i (0 : Fin 1)) hUV0
    simpa [U] using hcoord
  have hXrec (t : ℕ) : X (t + 1) = fun q =>
      (N.rowMix t *ᵥ X t) q - s * X t q - s * U t q - s * e t q := by
    funext q
    have hq := congrFun (hstep t).1 q
    have hc := congrArg (fun z : Point 1 => z (0 : Fin 1)) hq
    simp [X, U, e, leftAct, Matrix.smulVec_apply,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      Finset.sum_sub_distrib, Finset.smul_sum, smul_smul] at hc
    simp only [X, U, e]
    rw [hc]
    simp [X, U, e, Matrix.mulVec, dotProduct, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, Finset.sum_sub_distrib,
      sub_mul]
  have hUrec (t : ℕ) : U (t + 1) = fun q =>
      (N.colMix t *ᵥ U t) q + ((N.colMix t - 1) *ᵥ X t) q +
        ((N.colMix t - 1) *ᵥ e t) q := by
    funext q
    have hq := congrFun (hstep t).2 q
    have hc := congrArg (fun z : Point 1 => z (0 : Fin 1)) hq
    simp [X, U, e, leftAct, Matrix.smulVec_apply,
      Matrix.sub_apply, Matrix.one_apply, Finset.sum_sub_distrib,
      Finset.sum_add_distrib] at hc
    simp only [X, U, e]
    rw [hc]
    simp [X, U, e, Matrix.mulVec, dotProduct, Matrix.sub_apply,
      Matrix.one_apply, Finset.sum_sub_distrib, sub_mul]
    ring
  exact actual_quadratic_canonical_pathwise_superposition
    N s x0 X U e hXscalar0 hUscalar0 hXrec hUrec

/-- The legal homogeneous quadratic witness together with its exact scaled
Push--Pull state recursion (46).  The lower-left block is literally
`C_t - I`; in particular the tracker residual has not been zeroed or replaced
by a scalar proxy. -/
theorem actual_quadratic_iid_instance_spec
    (N : NetworkSetup n) (L Δ sigma H : ℝ)
    (hL : 0 < L) (hΔ : 0 < Δ) (hsigma : 0 < sigma) (hH : 0 ≤ H) :
    ∃ (atom : Fin 3 → ℝ) (nu : Measure (Fin 3))
        (phi : ℕ → Fin n → Fin 3 → Point 1)
        (S : Setup n 1 (SOptLib.miniBatchSamplePath n (Fin 3)))
        (hfinite : InFiniteHeterogeneityLayer S),
      let I : FiniteInstance n :=
        { d := 1
          Ω := SOptLib.miniBatchSamplePath n (Fin 3)
          setup := S
          finite_layer := hfinite }
      IsProbabilityMeasure nu ∧
      Integrable atom nu ∧
      (∫ a, atom a ∂nu) = 0 ∧
      (∫ a, ‖atom a‖ ^ 2 ∂nu) = sigma ^ 2 ∧
      (∀ G : ℝ → ℝ, G 0 = 0 → G (-sigma) = G sigma →
        (∫ a, G (atom a) ∂nu) = G sigma) ∧
      (∀ t i a, phi t i a = PiLp.single 2 (0 : Fin 1) (atom a)) ∧
      S.probability = SOptLib.iidMiniBatchSampleLaw n nu ∧
      (∀ t omega i, S.noise t omega i = phi t i (omega t i)) ∧
      S.initialPoint (0 : Fin 1) = Real.sqrt (2 * Δ / L) ∧
      I ∈ fixedInstanceClass N L Δ sigma H ∧
      initialHeterogeneitySq S = 0 ∧
      (∀ i z, gradient (S.localObjective i) z = L • z) ∧
      (∀ t (z : Point 1),
        leftAct (N.rowMix t) (fun _ : Fin n => z) = fun _ => z) ∧
      (∀ t (Z : NodeTable n 1),
        ∑ i, leftAct (N.colMix t) Z i = ∑ i, Z i) ∧
      ∀ (alpha : ℝ)
          (omega : SOptLib.miniBatchSamplePath n (Fin 3)),
        let s := dimensionlessStepsize L alpha
        let X : ℕ → NodeTable n 1 := fun r => primal S omega alpha r
        let e : ℕ → NodeTable n 1 := fun r => L⁻¹ • S.noise r omega
        let U : ℕ → NodeTable n 1 :=
          fun r => L⁻¹ • tracker S omega alpha r - X r - e r
        U 0 = 0 ∧
        ∀ t,
          X (t + 1) =
              leftAct (N.rowMix t - s • 1) (X t) - s • U t - s • e t ∧
          U (t + 1) =
              leftAct (N.colMix t - 1) (X t) +
                leftAct (N.colMix t) (U t) +
                leftAct (N.colMix t - 1) (e t) := by
  classical
  obtain ⟨hobjective, hobjNonneg, hobjInf, hobjGap, hobjGrad⟩ :=
    actualQuadraticObjective_spec L Δ hL hΔ
  obtain ⟨atom, nu, phi, hnu, hatomInt, hcenter, hsecond, heven,
      hphi, hcentered, hsecondMoment, hindependent⟩ :=
    actualQuadraticNoise_spec n sigma hsigma
  letI : IsProbabilityMeasure nu := hnu
  let F : Point 1 → ℝ := fun x => (L / 2) * ‖x‖ ^ 2
  let x0 : Point 1 :=
    WithLp.toLp 2 (fun _ : Fin 1 => Real.sqrt (2 * Δ / L))
  let Omega := SOptLib.miniBatchSamplePath n (Fin 3)
  let noise : ℕ → Omega → NodeTable n 1 :=
    fun t omega i => phi t i (omega t i)
  let probability : Measure Omega := SOptLib.iidMiniBatchSampleLaw n nu
  have hprobability : IsProbabilityMeasure probability := by
    dsimp [probability]
    infer_instance
  let S : Setup n 1 Omega :=
    { network := N
      hd := by norm_num
      L := L
      Δ := Δ
      σ := sigma
      H := H
      hL := hL
      hΔ := hΔ
      hσ := hsigma.le
      hH := hH
      localObjective := fun _ => F
      initialPoint := x0
      noise := noise
      probability := probability
      is_probability := hprobability
      local_smooth := fun _ => hobjective
      average_lower_bounded := by
        refine ⟨0, ?_⟩
        rintro _ ⟨z, rfl⟩
        simpa [F, Nat.ne_of_gt N.hn] using hobjNonneg z
      exact_initial_gap := by
        simpa [F, x0, Nat.ne_of_gt N.hn] using hobjGap
      noise_centered := by
        simpa [noise, probability, Omega] using hcentered
      noise_second_moment := by
        simpa [noise, probability, Omega] using hsecondMoment
      node_conditional_independence := by
        simpa [noise, probability, Omega] using hindependent }
  have haverage : averageObjective S = F := by
    funext z
    simp [averageObjective, S, Nat.ne_of_gt N.hn]
  have hgradient : ∀ i z, gradient (S.localObjective i) z = L • z := by
    intro i z
    simpa [S, F] using hobjGrad z
  have hheterogeneity : initialHeterogeneitySq S = 0 := by
    unfold initialHeterogeneitySq
    simp only [S, haverage, sub_self, norm_zero, zero_pow, Nat.ofNat_pos,
      Finset.sum_const_zero, mul_zero]
    simp
  have hfinite : InFiniteHeterogeneityLayer S := by
    unfold InFiniteHeterogeneityLayer
    rw [hheterogeneity]
    exact sq_nonneg H
  let I : FiniteInstance n :=
    { d := 1
      Ω := Omega
      setup := S
      finite_layer := hfinite }
  have hfixed : I ∈ fixedInstanceClass N L Δ sigma H := by
    simp [fixedInstanceClass, I, S, FiniteInstance.network,
      FiniteInstance.lipschitz, FiniteInstance.gap, FiniteInstance.noiseScale,
      FiniteInstance.heterogeneityScale]
  have hrowConstant : ∀ t (z : Point 1),
      leftAct (N.rowMix t) (fun _ : Fin n => z) = fun _ => z := by
    intro t z
    funext i
    unfold leftAct Matrix.smulVec
    rw [← Finset.sum_smul]
    rw [Matrix.sum_row_of_mem_rowStochastic (N.row_stochastic t) i]
    simp
  have hcolSum : ∀ t (Z : NodeTable n 1),
      ∑ i, leftAct (N.colMix t) Z i = ∑ i, Z i := by
    intro t Z
    exact Matrix.sum_smulVec_of_mem_colStochastic Z (N.col_stochastic t)
  refine ⟨atom, nu, phi, S, hfinite, ?_, hatomInt, hcenter, hsecond,
    heven, hphi, ?_, ?_, ?_, hfixed, hheterogeneity, hgradient,
    hrowConstant, hcolSum, ?_⟩
  · exact hnu
  · rfl
  · intro t omega i
    rfl
  · simp [S, x0]
  · intro alpha omega
    let s := dimensionlessStepsize L alpha
    let X : ℕ → NodeTable n 1 := fun r => primal S omega alpha r
    let e : ℕ → NodeTable n 1 := fun r => L⁻¹ • S.noise r omega
    let U : ℕ → NodeTable n 1 :=
      fun r => L⁻¹ • tracker S omega alpha r - X r - e r
    have hsampled (r : ℕ) :
        sampledOracle S omega alpha r = L • (X r + e r) := by
      funext i
      rw [sampledOracle_eq_gradient_add_noise]
      rw [hgradient]
      simp only [X, e, Pi.add_apply, Pi.smul_apply, smul_add, smul_smul]
      field_simp [hL.ne']
      simp
    have htrackerAs (r : ℕ) :
        tracker S omega alpha r = L • (U r + X r + e r) := by
      dsimp only [U]
      simp only [smul_add, smul_sub, smul_smul]
      simp [hL.ne']
      module
    have hleftAdd (A : NetworkMatrix n) (V W : NodeTable n 1) :
        leftAct A (V + W) = leftAct A V + leftAct A W := by
      funext i
      simp [leftAct, Matrix.smulVec_apply, smul_add,
        Finset.sum_add_distrib]
    have hleftSmul (A : NetworkMatrix n) (c : ℝ) (V : NodeTable n 1) :
        leftAct A (c • V) = c • leftAct A V := by
      funext i
      simp [leftAct, Matrix.smulVec_apply, Finset.smul_sum, smul_smul,
        mul_comm]
    have hsubOne (A : NetworkMatrix n) (V : NodeTable n 1) :
        leftAct (A - 1) V = leftAct A V - V := by
      exact Matrix.sub_one_smulVec A V
    have hsubScalarOne (A : NetworkMatrix n) (c : ℝ)
        (V : NodeTable n 1) :
        leftAct (A - c • 1) V = leftAct A V - c • V := by
      funext i
      simp [leftAct, Matrix.smulVec_apply, Matrix.sub_apply,
        Matrix.smul_apply, sub_smul, Finset.sum_sub_distrib,
        Finset.smul_sum, smul_smul, Matrix.one_apply]
    have hUzero : U 0 = 0 := by
      rw [show U 0 = L⁻¹ • tracker S omega alpha 0 - X 0 - e 0 by rfl,
        tracker_zero, hsampled]
      simp only [smul_add, smul_smul]
      field_simp [hL.ne']
      simp
    refine ⟨hUzero, ?_⟩
    intro t
    change
      X (t + 1) =
          leftAct (N.rowMix t - s • 1) (X t) - s • U t - s • e t ∧
        U (t + 1) =
          leftAct (N.colMix t - 1) (X t) +
            leftAct (N.colMix t) (U t) +
            leftAct (N.colMix t - 1) (e t)
    constructor
    · change primal S omega alpha (t + 1) =
          leftAct (N.rowMix t - s • 1) (X t) - s • U t - s • e t
      rw [primal_succ]
      rw [hsubScalarOne, htrackerAs]
      dsimp only [s, dimensionlessStepsize]
      simp only [smul_add, smul_smul]
      module
    · change
        L⁻¹ • tracker S omega alpha (t + 1) - X (t + 1) - e (t + 1) =
          leftAct (N.colMix t - 1) (X t) +
            leftAct (N.colMix t) (U t) +
            leftAct (N.colMix t - 1) (e t)
      rw [tracker_succ, hsampled (t + 1), hsampled t]
      rw [htrackerAs]
      rw [hleftSmul, hleftAdd, hleftAdd]
      rw [hsubOne, hsubOne]
      simp only [smul_add, smul_sub, smul_smul]
      simp [hL.ne']
      module

/-- Pathwise equation-(49) input expansion for the legal iid quadratic
witness.  The stochastic coefficient is the source-normalized amplitude
`atom / L`, while the response is the literal unit pulse used in (48). -/
theorem actual_quadratic_iid_pathwise_superposition
    (N : NetworkSetup n) (L x0 : ℝ) (atom : Fin 3 → ℝ)
    (phi : ℕ → Fin n → Fin 3 → Point 1)
    (S : Setup n 1 (SOptLib.miniBatchSamplePath n (Fin 3)))
    (hphi : ∀ t i a, phi t i a = PiLp.single 2 (0 : Fin 1) (atom a))
    (hnoise : ∀ t omega i, S.noise t omega i = phi t i (omega t i))
    (hx0 : S.initialPoint (0 : Fin 1) = x0)
    (alpha : ℝ) (omega : SOptLib.miniBatchSamplePath n (Fin 3))
    (hrec :
      let s := dimensionlessStepsize L alpha
      let XV : ℕ → NodeTable n 1 := fun r => primal S omega alpha r
      let eV : ℕ → NodeTable n 1 := fun r => L⁻¹ • S.noise r omega
      let UV : ℕ → NodeTable n 1 :=
        fun r => L⁻¹ • tracker S omega alpha r - XV r - eV r
      UV 0 = 0 ∧
      ∀ t,
        XV (t + 1) =
            leftAct (N.rowMix t - s • 1) (XV t) - s • UV t - s • eV t ∧
        UV (t + 1) =
            leftAct (N.colMix t - 1) (XV t) +
              leftAct (N.colMix t) (UV t) +
              leftAct (N.colMix t - 1) (eV t)) :
    let s := dimensionlessStepsize L alpha
    let XV : ℕ → NodeTable n 1 := fun r => primal S omega alpha r
    let eV : ℕ → NodeTable n 1 := fun r => L⁻¹ • S.noise r omega
    let UV : ℕ → NodeTable n 1 :=
      fun r => L⁻¹ • tracker S omega alpha r - XV r - eV r
    let signal := actualQuadraticScalarTrajectory N s 1 (fun _ _ => 0)
    let pulse := fun (j : ℕ) (i : Fin n) =>
      actualQuadraticScalarTrajectory N s 0
        (fun r q => if r = j then if q = i then 1 else 0 else 0)
    ∀ t,
      (fun i => XV t i (0 : Fin 1)) = x0 • (signal t).1 +
          ∑ j ∈ Finset.range t, ∑ i,
            (atom (omega j i) / L) • (pulse j i t).1 ∧
      (fun i => UV t i (0 : Fin 1)) = x0 • (signal t).2 +
          ∑ j ∈ Finset.range t, ∑ i,
            (atom (omega j i) / L) • (pulse j i t).2 := by
  classical
  dsimp only
  let s := dimensionlessStepsize L alpha
  let XV : ℕ → NodeTable n 1 := fun r => primal S omega alpha r
  let eV : ℕ → NodeTable n 1 := fun r => L⁻¹ • S.noise r omega
  let UV : ℕ → NodeTable n 1 :=
    fun r => L⁻¹ • tracker S omega alpha r - XV r - eV r
  have hXV0 : ∀ i, XV 0 i (0 : Fin 1) = x0 := by
    intro i
    dsimp only [XV]
    rw [primal_zero]
    exact hx0
  have heV (t : ℕ) (i : Fin n) :
      eV t i (0 : Fin 1) = atom (omega t i) / L := by
    dsimp only [eV]
    change (L⁻¹ • S.noise t omega i) (0 : Fin 1) = _
    rw [hnoise t omega i, hphi t i (omega t i)]
    simp [div_eq_mul_inv, mul_comm]
  have hsuper := actual_quadratic_point_pathwise_superposition
    N s x0 XV UV eV hXV0 hrec.1 hrec.2
  dsimp only at hsuper
  intro t
  simpa only [heV] using hsuper t

/-- Exact centered covariance of two canonical iid time-node coordinates.
This is the probabilistic diagonalization input in source equation (49). -/
theorem actual_quadratic_iid_atom_cross_moment
    (n : ℕ) (atom : Fin 3 → ℝ) (nu : Measure (Fin 3)) (sigma : ℝ)
    (hnu : IsProbabilityMeasure nu)
    (hcenter : (∫ a, atom a ∂nu) = 0)
    (hsecond : (∫ a, ‖atom a‖ ^ 2 ∂nu) = sigma ^ 2) :
    ∀ p q : ℕ × Fin n,
      (∫ omega : SOptLib.miniBatchSamplePath n (Fin 3),
          atom (omega p.1 p.2) * atom (omega q.1 q.2)
        ∂SOptLib.iidMiniBatchSampleLaw n nu) =
        if p = q then sigma ^ 2 else 0 := by
  classical
  letI : IsProbabilityMeasure nu := hnu
  let Omega := SOptLib.miniBatchSamplePath n (Fin 3)
  let P : Measure Omega := SOptLib.iidMiniBatchSampleLaw n nu
  let xi : (ℕ × Fin n) → Omega → Fin 3 :=
    fun r omega => omega r.1 r.2
  have hxiMeas (r : ℕ × Fin n) : Measurable (xi r) := by
    exact (measurable_pi_apply r.2).comp (measurable_pi_apply r.1)
  have hmap (r : ℕ × Fin n) : Measure.map (xi r) P = nu := by
    simpa [P, xi, Omega] using
      (SOptLib.iidMiniBatchSampleLaw_map_eval n nu r.1 r.2)
  have hmean (r : ℕ × Fin n) :
      (∫ omega : Omega, atom (xi r omega) ∂P) = 0 := by
    calc
      (∫ omega : Omega, atom (xi r omega) ∂P) = ∫ a, atom a ∂nu := by
        simpa [Function.comp_def] using
          (integral_comp_eq_integral_of_map_eq
            (hxiMeas r).aemeasurable
            (by rw [hmap r]; exact (measurable_of_finite atom).aestronglyMeasurable)
            (hmap r))
      _ = 0 := hcenter
  have hdiag (r : ℕ × Fin n) :
      (∫ omega : Omega, atom (xi r omega) ^ 2 ∂P) = sigma ^ 2 := by
    calc
      (∫ omega : Omega, atom (xi r omega) ^ 2 ∂P) =
          ∫ a, atom a ^ 2 ∂nu := by
        simpa [Function.comp_def] using
          (integral_comp_eq_integral_of_map_eq
            (hxiMeas r).aemeasurable
            (by
              rw [hmap r]
              exact (measurable_of_finite (fun a => atom a ^ 2)).aestronglyMeasurable)
            (hmap r))
      _ = sigma ^ 2 := by
        simpa [Real.norm_eq_abs, sq_abs] using hsecond
  intro p q
  by_cases hpq : p = q
  · subst q
    simp only [if_pos rfl]
    simpa [P, xi, Omega, pow_two] using hdiag p
  · have hindep : ProbabilityTheory.IndepFun (xi p) (xi q) P :=
      (SOptLib.iidMiniBatchSampleLaw_iIndepFun_eval n nu).indepFun hpq
    have hfactor :
        (∫ omega : Omega, atom (xi p omega) * atom (xi q omega) ∂P) =
          (∫ omega : Omega, atom (xi p omega) ∂P) *
            ∫ omega : Omega, atom (xi q omega) ∂P := by
      simpa [Function.comp_def] using
        (hindep.integral_fun_comp_mul_comp
          (hxiMeas p).aemeasurable (hxiMeas q).aemeasurable
          (by rw [hmap p]; exact (measurable_of_finite atom).aestronglyMeasurable)
          (by rw [hmap q]; exact (measurable_of_finite atom).aestronglyMeasurable))
    rw [if_neg hpq]
    change (∫ omega : Omega,
      atom (xi p omega) * atom (xi q omega) ∂P) = 0
    rw [hfactor, hmean p, hmean q, zero_mul]

/-- Finite covariance diagonalization for the canonical iid atom field. -/
theorem actual_quadratic_iid_weighted_sum_second_moment
    (n : ℕ) (atom : Fin 3 → ℝ) (nu : Measure (Fin 3)) (sigma : ℝ)
    (hnu : IsProbabilityMeasure nu)
    (hcenter : (∫ a, atom a ∂nu) = 0)
    (hsecond : (∫ a, ‖atom a‖ ^ 2 ∂nu) = sigma ^ 2)
    (s : Finset (ℕ × Fin n)) (c : (ℕ × Fin n) → ℝ) :
    (∫ omega : SOptLib.miniBatchSamplePath n (Fin 3),
        (∑ p ∈ s, c p * atom (omega p.1 p.2)) ^ 2
      ∂SOptLib.iidMiniBatchSampleLaw n nu) =
      ∑ p ∈ s, c p ^ 2 * sigma ^ 2 := by
  classical
  letI : IsProbabilityMeasure nu := hnu
  let Omega := SOptLib.miniBatchSamplePath n (Fin 3)
  let P : Measure Omega := SOptLib.iidMiniBatchSampleLaw n nu
  let Z : (ℕ × Fin n) → Omega → ℝ :=
    fun p omega => atom (omega p.1 p.2)
  have hevalMeas (p : ℕ × Fin n) :
      Measurable (fun omega : Omega => omega p.1 p.2) :=
    (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  have hmap (p : ℕ × Fin n) :
      Measure.map (fun omega : Omega => omega p.1 p.2) P = nu := by
    simpa [P, Omega] using
      (SOptLib.iidMiniBatchSampleLaw_map_eval n nu p.1 p.2)
  have hmeas (p : ℕ × Fin n) : AEStronglyMeasurable (Z p) P := by
    exact ((measurable_of_finite atom).comp (hevalMeas p)).aestronglyMeasurable
  have hL2 (p : ℕ × Fin n) :
      Integrable (fun omega => ‖Z p omega‖ ^ 2) P := by
    have hmapped : Integrable (fun a => ‖atom a‖ ^ 2)
        (Measure.map (fun omega : Omega => omega p.1 p.2) P) := by
      rw [hmap p]
      exact Integrable.of_finite
    simpa [Z, Function.comp_def] using hmapped.comp_measurable (hevalMeas p)
  have hdiag (p : ℕ × Fin n) :
      (∫ omega, ‖Z p omega‖ ^ 2 ∂P) = sigma ^ 2 := by
    calc
      (∫ omega, ‖Z p omega‖ ^ 2 ∂P) =
          ∫ a, ‖atom a‖ ^ 2 ∂nu := by
        change (∫ omega : Omega,
          (fun a => ‖atom a‖ ^ 2) ((fun z : Omega => z p.1 p.2) omega) ∂P) = _
        exact integral_comp_eq_integral_of_map_eq
          (hevalMeas p).aemeasurable
          (by rw [hmap p]; exact
            (measurable_of_finite (fun a => ‖atom a‖ ^ 2)).aestronglyMeasurable)
          (hmap p)
      _ = sigma ^ 2 := hsecond
  have hcross (p q : ℕ × Fin n) (hpq : p ≠ q) :
      (∫ omega, ⟪Z p omega, Z q omega⟫_ℝ ∂P) = 0 := by
    have hmoment := actual_quadratic_iid_atom_cross_moment
      n atom nu sigma hnu hcenter hsecond p q
    rw [if_neg hpq] at hmoment
    have hintegrand :
        (fun omega : Omega => ⟪Z p omega, Z q omega⟫_ℝ) =
      fun omega => Z p omega * Z q omega := by
      funext omega
      calc
        ⟪Z p omega, Z q omega⟫_ℝ =
            ⟪Z p omega • (1 : ℝ), Z q omega • (1 : ℝ)⟫_ℝ := by
              simp
        _ = Z p omega * Z q omega * ⟪(1 : ℝ), (1 : ℝ)⟫_ℝ := by
              rw [real_inner_smul_left, real_inner_smul_right]
              ring
        _ = Z p omega * Z q omega := by
              rw [real_inner_self_eq_norm_sq]
              norm_num
    rw [hintegrand]
    simpa [P, Omega, Z] using hmoment
  have hraw := integral_norm_sq_finset_weighted_sum_eq_sum_sq_mul_of_cross_zero
    P s c Z (fun _ => sigma ^ 2)
    (fun p hp => hmeas p) (fun p hp => hL2 p)
    (fun p hp q hq hpq => hcross p q hpq)
    (fun p hp => hdiag p)
  simpa [P, Omega, Z, Real.norm_eq_abs, sq_abs, smul_eq_mul] using hraw

/-- Exact second moment of a deterministic signal plus a finite centered iid
atom response.  In particular, the deterministic/noise cross term vanishes. -/
theorem actual_quadratic_iid_affine_weighted_sum_second_moment
    (n : ℕ) (atom : Fin 3 → ℝ) (nu : Measure (Fin 3)) (sigma : ℝ)
    (hnu : IsProbabilityMeasure nu) (hatomInt : Integrable atom nu)
    (hcenter : (∫ a, atom a ∂nu) = 0)
    (hsecond : (∫ a, ‖atom a‖ ^ 2 ∂nu) = sigma ^ 2)
    (s : Finset (ℕ × Fin n)) (c : (ℕ × Fin n) → ℝ) (d : ℝ) :
    (∫ omega : SOptLib.miniBatchSamplePath n (Fin 3),
        (d + ∑ p ∈ s, c p * atom (omega p.1 p.2)) ^ 2
      ∂SOptLib.iidMiniBatchSampleLaw n nu) =
      d ^ 2 + ∑ p ∈ s, c p ^ 2 * sigma ^ 2 := by
  classical
  letI : IsProbabilityMeasure nu := hnu
  let Omega := SOptLib.miniBatchSamplePath n (Fin 3)
  let P : Measure Omega := SOptLib.iidMiniBatchSampleLaw n nu
  let Z : Omega → ℝ := fun omega =>
    ∑ p ∈ s, c p * atom (omega p.1 p.2)
  have hevalMeas (p : ℕ × Fin n) :
      Measurable (fun omega : Omega => omega p.1 p.2) :=
    (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  have hmap (p : ℕ × Fin n) :
      Measure.map (fun omega : Omega => omega p.1 p.2) P = nu := by
    simpa [P, Omega] using
      (SOptLib.iidMiniBatchSampleLaw_map_eval n nu p.1 p.2)
  have hcoordInt (p : ℕ × Fin n) :
      Integrable (fun omega : Omega => atom (omega p.1 p.2)) P := by
    have hmapped : Integrable atom
        (Measure.map (fun omega : Omega => omega p.1 p.2) P) := by
      rw [hmap p]
      exact hatomInt
    simpa [Function.comp_def] using hmapped.comp_measurable (hevalMeas p)
  have hcoordSqInt (p : ℕ × Fin n) :
      Integrable (fun omega : Omega => ‖atom (omega p.1 p.2)‖ ^ 2) P := by
    have hmapped : Integrable (fun a => ‖atom a‖ ^ 2)
        (Measure.map (fun omega : Omega => omega p.1 p.2) P) := by
      rw [hmap p]
      exact Integrable.of_finite
    simpa [Function.comp_def] using hmapped.comp_measurable (hevalMeas p)
  have hZmeas : AEStronglyMeasurable Z P := by
    have heq : Z = ∑ p ∈ s,
        (fun omega : Omega => c p * atom (omega p.1 p.2)) := by
      funext omega
      simp only [Z, Finset.sum_apply]
    rw [heq]
    exact Finset.aestronglyMeasurable_sum s fun p hp =>
      (hcoordInt p).aestronglyMeasurable.const_mul (c p)
  have hZmem : MemLp Z 2 P := by
    apply memLp_finset_sum s
    intro p hp
    have hpMem : MemLp (fun omega : Omega => atom (omega p.1 p.2)) 2 P :=
      (memLp_two_iff_integrable_sq_norm (hcoordInt p).aestronglyMeasurable).2
        (hcoordSqInt p)
    simpa [Z, smul_eq_mul] using hpMem.const_smul (c p)
  have hZsq : Integrable (fun omega => ‖Z omega‖ ^ 2) P :=
    (memLp_two_iff_integrable_sq_norm hZmeas).1 hZmem
  have hcoordMean (p : ℕ × Fin n) :
      (∫ omega : Omega, atom (omega p.1 p.2) ∂P) = 0 := by
    calc
      (∫ omega : Omega, atom (omega p.1 p.2) ∂P) = ∫ a, atom a ∂nu := by
        simpa [Function.comp_def] using
          (integral_comp_eq_integral_of_map_eq
            (hevalMeas p).aemeasurable
            (by rw [hmap p]; exact hatomInt.aestronglyMeasurable)
            (hmap p))
      _ = 0 := hcenter
  have hZmean : (∫ omega, Z omega ∂P) = 0 := by
    dsimp only [Z]
    rw [integral_finset_sum _ fun p hp => (hcoordInt p).const_mul (c p)]
    apply Finset.sum_eq_zero
    intro p hp
    rw [integral_const_mul, hcoordMean p, mul_zero]
  let u : Omega → ℝ := fun _ => d
  have huSq : Integrable (fun omega => ‖u omega‖ ^ 2) P := by
    simpa [u] using
      (integrable_const (μ := P) (‖d‖ ^ 2) :
        Integrable (fun _ : Omega => ‖d‖ ^ 2) P)
  have huMeas : AEStronglyMeasurable u P :=
    (measurable_const.aestronglyMeasurable)
  have hcrossInt : Integrable (fun omega => ⟪u omega, Z omega⟫_ℝ) P :=
    integrable_inner_of_integrable_sq_norm huMeas hZmeas huSq hZsq
  have hinnerPoint : (fun omega => ⟪u omega, Z omega⟫_ℝ) =
      fun omega => d * Z omega := by
    funext omega
    calc
      ⟪u omega, Z omega⟫_ℝ =
          ⟪d • (1 : ℝ), Z omega • (1 : ℝ)⟫_ℝ := by simp [u]
      _ = d * Z omega * ⟪(1 : ℝ), (1 : ℝ)⟫_ℝ := by
        rw [real_inner_smul_left, real_inner_smul_right]
        ring
      _ = d * Z omega := by
        rw [real_inner_self_eq_norm_sq]
        norm_num
  have hcrossZero : (∫ omega, ⟪u omega, Z omega⟫_ℝ ∂P) = 0 := by
    rw [hinnerPoint, integral_const_mul, hZmean, mul_zero]
  have hraw := integral_norm_sq_smul_add_smul_eq_of_integral_inner_eq_zero
    P u Z 1 1 huSq hZsq hcrossInt hcrossZero
  have hnoise := actual_quadratic_iid_weighted_sum_second_moment
    n atom nu sigma hnu hcenter hsecond s c
  dsimp [u, Z, P, Omega] at hraw
  simp only [one_smul, one_pow, one_mul] at hraw
  simp [Real.norm_eq_abs, sq_abs] at hraw
  have hnoise' := hnoise
  simp only [SOptLib.iidMiniBatchSampleLaw_def] at hnoise'
  rw [hnoise'] at hraw
  exact hraw

/-- Source equation (49), before summing over output times: the exact expected
quadratic output energy is the homogeneous signal energy plus the diagonal
iid pulse-response energy. -/
theorem actual_quadratic_equation49_iid_output_energy
    (N : NetworkSetup n) (L x0 sigma : ℝ) (atom : Fin 3 → ℝ)
    (nu : Measure (Fin 3))
    (phi : ℕ → Fin n → Fin 3 → Point 1)
    (S : Setup n 1 (SOptLib.miniBatchSamplePath n (Fin 3)))
    (hL : 0 < L) (hnu : IsProbabilityMeasure nu)
    (hatomInt : Integrable atom nu)
    (hcenter : (∫ a, atom a ∂nu) = 0)
    (hsecond : (∫ a, ‖atom a‖ ^ 2 ∂nu) = sigma ^ 2)
    (hphi : ∀ t i a, phi t i a = PiLp.single 2 (0 : Fin 1) (atom a))
    (hprob : S.probability = SOptLib.iidMiniBatchSampleLaw n nu)
    (hnoise : ∀ t omega i, S.noise t omega i = phi t i (omega t i))
    (hx0 : S.initialPoint (0 : Fin 1) = x0)
    (hgrad : ∀ i z, gradient (S.localObjective i) z = L • z)
    (alpha : ℝ)
    (hrec : ∀ omega : SOptLib.miniBatchSamplePath n (Fin 3),
      let s := dimensionlessStepsize L alpha
      let XV : ℕ → NodeTable n 1 := fun r => primal S omega alpha r
      let eV : ℕ → NodeTable n 1 := fun r => L⁻¹ • S.noise r omega
      let UV : ℕ → NodeTable n 1 :=
        fun r => L⁻¹ • tracker S omega alpha r - XV r - eV r
      UV 0 = 0 ∧
      ∀ t,
        XV (t + 1) =
            leftAct (N.rowMix t - s • 1) (XV t) - s • UV t - s • eV t ∧
        UV (t + 1) =
            leftAct (N.colMix t - 1) (XV t) +
              leftAct (N.colMix t) (UV t) +
              leftAct (N.colMix t - 1) (eV t)) :
    let s := dimensionlessStepsize L alpha
    let signal := actualQuadraticScalarTrajectory N s 1 (fun _ _ => 0)
    let pulse := fun (j : ℕ) (i : Fin n) =>
      actualQuadraticScalarTrajectory N s 0
        (fun r q => if r = j then if q = i then 1 else 0 else 0)
    let a : ℕ → ℝ := fun t => (n : ℝ)⁻¹ * ∑ q, (signal t).1 q
    let r : ℕ → ℕ → Fin n → ℝ := fun t j i =>
      (n : ℝ)⁻¹ * ∑ q, (pulse j i t).1 q
    ∀ t,
      SOptLib.expectation S.probability (stationarityIntegrand S alpha t) =
        (L * x0 * a t) ^ 2 +
          sigma ^ 2 * ∑ j ∈ Finset.range t, ∑ i, (r t j i) ^ 2 := by
  classical
  dsimp only
  let sdim := dimensionlessStepsize L alpha
  let signal := actualQuadraticScalarTrajectory N sdim 1 (fun _ _ => 0)
  let pulse := fun (j : ℕ) (i : Fin n) =>
    actualQuadraticScalarTrajectory N sdim 0
      (fun r q => if r = j then if q = i then 1 else 0 else 0)
  let a : ℕ → ℝ := fun t => (n : ℝ)⁻¹ * ∑ q, (signal t).1 q
  let r : ℕ → ℕ → Fin n → ℝ := fun t j i =>
    (n : ℝ)⁻¹ * ∑ q, (pulse j i t).1 q
  have havgGrad (z : Point 1) : gradient (averageObjective S) z = L • z := by
    have havg := SOptLib.finiteAverageObjective_hasGradientAt
      S.localObjective (fun i x => gradient (S.localObjective i) x) z
      (fun i => ((S.local_smooth i).1 _).hasGradientAt)
    calc
      gradient (averageObjective S) z =
          (n : ℝ)⁻¹ • ∑ i, gradient (S.localObjective i) z := by
        simpa only [averageObjective, Fintype.card_fin] using havg.gradient
      _ = L • z := by
        simp only [hgrad, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
        have hn : (n : ℝ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.ne_of_gt N.hn)
        have hc : (n : ℝ)⁻¹ * ((n : ℝ) * L) = L := by
          field_simp
        rw [hc]
  intro t
  have hmean (omega : SOptLib.miniBatchSamplePath n (Fin 3)) :
      (arithmeticMean S omega alpha t) (0 : Fin 1) =
        x0 * a t + ∑ j ∈ Finset.range t, ∑ i,
          (atom (omega j i) / L) * r t j i := by
    have hsuper := actual_quadratic_iid_pathwise_superposition
      N L x0 atom phi S hphi hnoise hx0 alpha omega (hrec omega) t
    have hsum := congrArg
      (fun f : Fin n → ℝ => (n : ℝ)⁻¹ * ∑ q, f q) hsuper.1
    calc
      (arithmeticMean S omega alpha t) (0 : Fin 1) =
          (n : ℝ)⁻¹ * ∑ q,
            (primal S omega alpha t q) (0 : Fin 1) := by
        unfold arithmeticMean
        change (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) 0)
            ((n : ℝ)⁻¹ • ∑ q, primal S omega alpha t q) = _
        rw [map_smul, map_sum]
        simp only [PiLp.proj_apply, smul_eq_mul]
      _ =
          (n : ℝ)⁻¹ * ∑ q,
            (x0 • (signal t).1 +
              ∑ j ∈ Finset.range t, ∑ i,
                (atom (omega j i) / L) • (pulse j i t).1) q := hsum
      _ = x0 * a t + ∑ j ∈ Finset.range t, ∑ i,
          (atom (omega j i) / L) * r t j i := by
        have hcomm :
            ∑ q, ∑ j ∈ Finset.range t, ∑ i,
                (atom (omega j i) / L) * (pulse j i t).1 q =
              ∑ j ∈ Finset.range t, ∑ i,
                (atom (omega j i) / L) * ∑ q, (pulse j i t).1 q := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          Finset.sum_add_distrib, Finset.sum_apply]
        dsimp only [a, r]
        rw [hcomm]
        rw [mul_add]
        apply congrArg₂ (fun u v : ℝ => u + v)
        · rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q hq
          ring
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
  have hintegrand (omega : SOptLib.miniBatchSamplePath n (Fin 3)) :
      stationarityIntegrand S alpha t omega =
        (L * x0 * a t +
          ∑ j ∈ Finset.range t, ∑ i,
            r t j i * atom (omega j i)) ^ 2 := by
    unfold stationarityIntegrand
    rw [havgGrad]
    have hnorm (z : Point 1) : ‖z‖ ^ 2 = (z (0 : Fin 1)) ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      simp [Real.norm_eq_abs, sq_abs]
    rw [hnorm]
    change (L * (arithmeticMean S omega alpha t) (0 : Fin 1)) ^ 2 = _
    rw [hmean omega]
    have hscale :
        L * (∑ j ∈ Finset.range t, ∑ i,
          atom (omega j i) / L * r t j i) =
          ∑ j ∈ Finset.range t, ∑ i,
            r t j i * atom (omega j i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      field_simp [hL.ne']
    change (L * (x0 * a t + ∑ j ∈ Finset.range t, ∑ i,
      atom (omega j i) / L * r t j i)) ^ 2 = _
    rw [mul_add, hscale]
    ring
  unfold SOptLib.expectation
  rw [hprob]
  calc
    (∫ omega, stationarityIntegrand S alpha t omega
        ∂SOptLib.iidMiniBatchSampleLaw n nu) =
        ∫ omega,
          (L * x0 * a t +
            ∑ j ∈ Finset.range t, ∑ i,
              r t j i * atom (omega j i)) ^ 2
          ∂SOptLib.iidMiniBatchSampleLaw n nu := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hintegrand
    _ = (L * x0 * a t) ^ 2 +
          sigma ^ 2 * ∑ j ∈ Finset.range t, ∑ i, (r t j i) ^ 2 := by
      have hcov := actual_quadratic_iid_affine_weighted_sum_second_moment
        n atom nu sigma hnu hatomInt hcenter hsecond
        ((Finset.range t).product (Finset.univ : Finset (Fin n)))
        (fun p => r t p.1 p.2) (L * x0 * a t)
      have hprodAtom (omega : SOptLib.miniBatchSamplePath n (Fin 3)) :
          ∑ p ∈ (Finset.range t).product (Finset.univ : Finset (Fin n)),
              r t p.1 p.2 * atom (omega p.1 p.2) =
            ∑ j ∈ Finset.range t, ∑ i,
              r t j i * atom (omega j i) := by
        exact Finset.sum_product _ _ _
      have hprodSq :
          ∑ p ∈ (Finset.range t).product (Finset.univ : Finset (Fin n)),
              (r t p.1 p.2) ^ 2 * sigma ^ 2 =
            ∑ j ∈ Finset.range t, ∑ i,
              (r t j i) ^ 2 * sigma ^ 2 := by
        exact Finset.sum_product _ _ _
      calc
        ∫ omega,
            (L * x0 * a t + ∑ j ∈ Finset.range t, ∑ i,
              r t j i * atom (omega j i)) ^ 2
            ∂SOptLib.iidMiniBatchSampleLaw n nu =
            ∫ omega,
              (L * x0 * a t +
                ∑ p ∈ (Finset.range t).product
                    (Finset.univ : Finset (Fin n)),
                  r t p.1 p.2 * atom (omega p.1 p.2)) ^ 2
              ∂SOptLib.iidMiniBatchSampleLaw n nu := by
          apply integral_congr_ae
          apply Filter.Eventually.of_forall
          intro omega
          change
            (L * x0 * a t + ∑ j ∈ Finset.range t, ∑ i,
              r t j i * atom (omega j i)) ^ 2 =
            (L * x0 * a t +
              ∑ p ∈ (Finset.range t).product
                  (Finset.univ : Finset (Fin n)),
                r t p.1 p.2 * atom (omega p.1 p.2)) ^ 2
          rw [hprodAtom]
        _ =
            (L * x0 * a t) ^ 2 +
              ∑ p ∈ (Finset.range t).product
                  (Finset.univ : Finset (Fin n)),
                (r t p.1 p.2) ^ 2 * sigma ^ 2 := hcov
        _ = (L * x0 * a t) ^ 2 +
              ∑ j ∈ Finset.range t, ∑ i,
                (r t j i) ^ 2 * sigma ^ 2 := by rw [hprodSq]
        _ = (L * x0 * a t) ^ 2 +
              sigma ^ 2 * ∑ j ∈ Finset.range t, ∑ i,
                (r t j i) ^ 2 := by
          apply congrArg (fun z => (L * x0 * a t) ^ 2 + z)
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring

/-- Source equation (49): after summing the exact iid output energy over the
horizon, the quadratic witness cost splits into its deterministic signal and
diagonal pulse-response energies. -/
theorem actual_quadratic_equation49_iid_cost_identity
    (N : NetworkSetup n) (L Δ sigma : ℝ)
    (atom : Fin 3 → ℝ) (nu : Measure (Fin 3))
    (phi : ℕ → Fin n → Fin 3 → Point 1)
    (S : Setup n 1 (SOptLib.miniBatchSamplePath n (Fin 3)))
    (hfinite : InFiniteHeterogeneityLayer S)
    (hL : 0 < L) (hΔ : 0 < Δ)
    (hnu : IsProbabilityMeasure nu) (hatomInt : Integrable atom nu)
    (hcenter : (∫ a, atom a ∂nu) = 0)
    (hsecond : (∫ a, ‖atom a‖ ^ 2 ∂nu) = sigma ^ 2)
    (hphi : ∀ t i a, phi t i a = PiLp.single 2 (0 : Fin 1) (atom a))
    (hprob : S.probability = SOptLib.iidMiniBatchSampleLaw n nu)
    (hnoise : ∀ t omega i, S.noise t omega i = phi t i (omega t i))
    (hx0 : S.initialPoint (0 : Fin 1) = Real.sqrt (2 * Δ / L))
    (hgrad : ∀ i z, gradient (S.localObjective i) z = L • z)
    (alpha : ℝ)
    (hrec : ∀ omega : SOptLib.miniBatchSamplePath n (Fin 3),
      let s := dimensionlessStepsize L alpha
      let XV : ℕ → NodeTable n 1 := fun r => primal S omega alpha r
      let eV : ℕ → NodeTable n 1 := fun r => L⁻¹ • S.noise r omega
      let UV : ℕ → NodeTable n 1 :=
        fun r => L⁻¹ • tracker S omega alpha r - XV r - eV r
      UV 0 = 0 ∧
      ∀ t,
        XV (t + 1) =
            leftAct (N.rowMix t - s • 1) (XV t) - s • UV t - s • eV t ∧
        UV (t + 1) =
            leftAct (N.colMix t - 1) (XV t) +
              leftAct (N.colMix t) (UV t) +
              leftAct (N.colMix t - 1) (eV t))
    (T : PositiveHorizon) :
    let I : FiniteInstance n :=
      { d := 1
        Ω := SOptLib.miniBatchSamplePath n (Fin 3)
        setup := S
        finite_layer := hfinite }
    let s := dimensionlessStepsize L alpha
    let signal := actualQuadraticScalarTrajectory N s 1 (fun _ _ => 0)
    let pulse := fun (j : ℕ) (i : Fin n) =>
      actualQuadraticScalarTrajectory N s 0
        (fun r q => if r = j then if q = i then 1 else 0 else 0)
    let Dact := ∑ t ∈ Finset.range T.1,
      ((n : ℝ)⁻¹ * ∑ q, (signal t).1 q) ^ 2
    let Vact := ∑ t ∈ Finset.range T.1, ∑ j ∈ Finset.range t, ∑ i,
      ((n : ℝ)⁻¹ * ∑ q, (pulse j i t).1 q) ^ 2
    (T.1 : ℝ) * FiniteInstance.cost I alpha T =
      2 * ADelta L Δ * Dact + sigma ^ 2 * Vact := by
  classical
  dsimp only
  have hpoint := actual_quadratic_equation49_iid_output_energy
    N L (Real.sqrt (2 * Δ / L)) sigma atom nu phi S hL hnu
    hatomInt hcenter hsecond hphi hprob hnoise hx0 hgrad alpha hrec
  have hTne : (T.1 : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt T.2)
  have hrad : 0 ≤ 2 * Δ / L := by positivity
  have hxscale : (L * Real.sqrt (2 * Δ / L)) ^ 2 =
      2 * ADelta L Δ := by
    rw [mul_pow, Real.sq_sqrt hrad]
    unfold ADelta
    field_simp [hL.ne']
  unfold FiniteInstance.cost stationarityError
  change (T.1 : ℝ) * ((T.1 : ℝ)⁻¹ *
      ∑ t ∈ Finset.range T.1,
        SOptLib.expectation S.probability
          (stationarityIntegrand S alpha t)) = _
  rw [← mul_assoc, mul_inv_cancel₀ hTne, one_mul]
  calc
    ∑ t ∈ Finset.range T.1,
        SOptLib.expectation S.probability (stationarityIntegrand S alpha t) =
        ∑ t ∈ Finset.range T.1,
          ((L * Real.sqrt (2 * Δ / L)) ^ 2 *
              ((n : ℝ)⁻¹ * ∑ q,
                (actualQuadraticScalarTrajectory N
                  (dimensionlessStepsize L alpha) 1 (fun _ _ => 0) t).1 q) ^ 2 +
            sigma ^ 2 * ∑ j ∈ Finset.range t, ∑ i,
              ((n : ℝ)⁻¹ * ∑ q,
                (actualQuadraticScalarTrajectory N
                  (dimensionlessStepsize L alpha) 0
                    (fun r q => if r = j then if q = i then 1 else 0 else 0)
                  t).1 q) ^ 2) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [hpoint t]
      ring
    _ = 2 * ADelta L Δ *
          ∑ t ∈ Finset.range T.1,
            ((n : ℝ)⁻¹ * ∑ q,
              (actualQuadraticScalarTrajectory N
                (dimensionlessStepsize L alpha) 1 (fun _ _ => 0) t).1 q) ^ 2 +
        sigma ^ 2 *
          ∑ t ∈ Finset.range T.1, ∑ j ∈ Finset.range t, ∑ i,
            ((n : ℝ)⁻¹ * ∑ q,
              (actualQuadraticScalarTrajectory N
                (dimensionlessStepsize L alpha) 0
                  (fun r q => if r = j then if q = i then 1 else 0 else 0)
                t).1 q) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, hxscale]

/-- The deterministic equation-(50) comparison: a response within a scaled
slow geometric envelope of a reference response has uniformly comparable
finite square energy. -/
theorem actual_quadratic_signal_energy_comparison
    (g C s : ℝ) (T : ℕ) (a p : ℕ → ℝ)
    (hg : 0 < g) (hC : 0 ≤ C) (hs : 0 < s)
    (hs_one : s ≤ 1) (hgs : g * s ≤ 1)
    (hp : ∀ t ∈ Finset.range T,
      |p t| ≤ (1 - g * s / 4) ^ t)
    (ha : ∀ t ∈ Finset.range T,
      |a t - p t| ≤ C * s * (1 - g * s / 4) ^ t) :
    |∑ t ∈ Finset.range T, (a t) ^ 2 -
        ∑ t ∈ Finset.range T, (p t) ^ 2| ≤
      (8 * C + 4 * C ^ 2) / g := by
  let q : ℝ := 1 - g * s / 4
  have hgs_pos : 0 < g * s := mul_pos hg hs
  have hq0 : 0 ≤ q := by
    dsimp [q]
    nlinarith
  have hq1 : q < 1 := by
    dsimp [q]
    nlinarith
  have hq2 : q ^ 2 < 1 := by
    nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq1.le)]
  have hden : g * s / 4 ≤ 1 - q ^ 2 := by
    dsimp [q]
    nlinarith [mul_nonneg (sub_nonneg.mpr hgs) hgs_pos.le]
  have hden_pos : 0 < 1 - q ^ 2 := sub_pos.mpr hq2
  have hsmall_pos : 0 < g * s / 4 := by positivity
  have hinv : 1 / (1 - q ^ 2) ≤ 4 / (g * s) := by
    calc
      1 / (1 - q ^ 2) ≤ 1 / (g * s / 4) :=
        one_div_le_one_div_of_le hsmall_pos hden
      _ = 4 / (g * s) := by field_simp
  cases T with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, sub_zero, abs_zero]
      exact div_nonneg
        (add_nonneg (mul_nonneg (by norm_num) hC)
          (mul_nonneg (by norm_num) (sq_nonneg C))) hg.le
  | succ N =>
      have hgeom :
          ∑ t ∈ Finset.range (N + 1), (q ^ t) ^ 2 ≤
            1 / (1 - q ^ 2) := by
        simpa using
          (finite_geometric_sq_response_sum_le
            (M := (1 : ℝ)) (r := q) (x := (1 : ℝ)) hq2 N)
      have hpoint (t : ℕ) (ht : t ∈ Finset.range (N + 1)) :
          |(a t) ^ 2 - (p t) ^ 2| ≤
            (2 * C * s + C ^ 2 * s ^ 2) * (q ^ t) ^ 2 := by
        have hqt0 : 0 ≤ q ^ t := pow_nonneg hq0 t
        have henv0 : 0 ≤ C * s * q ^ t := by positivity
        have ha' : |a t - p t| ≤ C * s * q ^ t := by
          simpa [q] using ha t ht
        have hp' : |p t| ≤ q ^ t := by
          simpa [q] using hp t ht
        have hplus : |a t + p t| ≤ C * s * q ^ t + 2 * q ^ t := by
          calc
            |a t + p t| = |(a t - p t) + 2 * p t| := by ring_nf
            _ ≤ |a t - p t| + |2 * p t| := abs_add_le _ _
            _ = |a t - p t| + 2 * |p t| := by simp [abs_mul]
            _ ≤ C * s * q ^ t + 2 * q ^ t := by
              exact add_le_add ha'
                (mul_le_mul_of_nonneg_left hp' (by norm_num))
        calc
          |(a t) ^ 2 - (p t) ^ 2| =
              |a t - p t| * |a t + p t| := by
            rw [← abs_mul]
            congr 1
            ring
          _ ≤ (C * s * q ^ t) * (C * s * q ^ t + 2 * q ^ t) :=
            mul_le_mul ha' hplus (abs_nonneg _) henv0
          _ = (2 * C * s + C ^ 2 * s ^ 2) * (q ^ t) ^ 2 := by ring
      have hcoef0 : 0 ≤ 2 * C * s + C ^ 2 * s ^ 2 := by positivity
      calc
        |∑ t ∈ Finset.range (N + 1), (a t) ^ 2 -
            ∑ t ∈ Finset.range (N + 1), (p t) ^ 2| ≤
            ∑ t ∈ Finset.range (N + 1),
              |(a t) ^ 2 - (p t) ^ 2| := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ t ∈ Finset.range (N + 1),
              (2 * C * s + C ^ 2 * s ^ 2) * (q ^ t) ^ 2 :=
          Finset.sum_le_sum hpoint
        _ = (2 * C * s + C ^ 2 * s ^ 2) *
              ∑ t ∈ Finset.range (N + 1), (q ^ t) ^ 2 := by
          rw [Finset.mul_sum]
        _ ≤ (2 * C * s + C ^ 2 * s ^ 2) *
              (1 / (1 - q ^ 2)) :=
          mul_le_mul_of_nonneg_left hgeom hcoef0
        _ ≤ (2 * C * s + C ^ 2 * s ^ 2) * (4 / (g * s)) :=
          mul_le_mul_of_nonneg_left hinv hcoef0
        _ = (8 * C + 4 * C ^ 2 * s) / g := by
          field_simp [hg.ne', hs.ne']
          ring
        _ ≤ (8 * C + 4 * C ^ 2) / g := by
          apply (div_le_div_iff_of_pos_right hg).2
          nlinarith [mul_nonneg (sq_nonneg C) (sub_nonneg.mpr hs_one)]

/-- A finite gain product retains its first-order mass while its accumulated
`s*n` budget is at most one. -/
theorem actual_quadratic_gain_product_ge_linear
    (N : NetworkSetup n) (s : ℝ) (k t : ℕ) (hs : 0 < s)
    (hbudget : (t : ℝ) * (s * (n : ℝ)) ≤ 1) :
    1 - (t : ℝ) * (s * (n : ℝ)) ≤
      ∏ r ∈ Finset.Ico k (k + t), (1 - s * gain N r) := by
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr N.hn
  have hx0 : 0 ≤ s * (n : ℝ) := mul_nonneg hs.le hn.le
  induction t with
  | zero => simp
  | succ t ih =>
      have htbudget : (t : ℝ) * (s * (n : ℝ)) ≤ 1 := by
        have htcast : (t : ℝ) ≤ (t + 1 : ℕ) := by norm_num
        exact (mul_le_mul_of_nonneg_right htcast hx0).trans hbudget
      have hsn : s * (n : ℝ) ≤ 1 := by
        have hone : (1 : ℝ) ≤ (t + 1 : ℕ) := by norm_num
        have := mul_le_mul_of_nonneg_right hone hx0
        nlinarith
      have hfactor : 1 - s * (n : ℝ) ≤ 1 - s * gain N (k + t) := by
        have hscaled := mul_le_mul_of_nonneg_left (gain_le_n N (k + t)) hs.le
        linarith
      have ih' := ih htbudget
      have hfactor0 : 0 ≤ 1 - s * (n : ℝ) := by linarith
      have hprev0 : 0 ≤ ∏ r ∈ Finset.Ico k (k + t), (1 - s * gain N r) :=
        (sub_nonneg.mpr htbudget).trans ih'
      have hmul :
          (1 - (t : ℝ) * (s * (n : ℝ))) *
              (1 - s * (n : ℝ)) ≤
            (∏ r ∈ Finset.Ico k (k + t), (1 - s * gain N r)) *
              (1 - s * gain N (k + t)) :=
        mul_le_mul ih' hfactor hfactor0 hprev0
      rw [show k + (t + 1) = k + t + 1 by omega,
        Finset.prod_Ico_succ_top (by omega)]
      calc
        1 - ((t + 1 : ℕ) : ℝ) * (s * (n : ℝ)) ≤
            (1 - (t : ℝ) * (s * (n : ℝ))) *
              (1 - s * (n : ℝ)) := by
          norm_num at hbudget ⊢
          nlinarith [mul_nonneg (Nat.cast_nonneg t)
            (sq_nonneg (s * (n : ℝ)))]
        _ ≤ _ := hmul

/-- The complete variance transition in equation (51): retain the newest
`m` impulses, apply the interval energy estimate (6), and absorb the
actual-to-proxy error from equation (50). -/
theorem actual_quadratic_equation51_variance_floor
    (N : NetworkSetup n) (s : ℝ) (T m : ℕ) (V Cvar : ℝ)
    (hs : 0 < s)
    (hmThreshold : influenceEnergyWindowThreshold N ≤ m)
    (hmLower : (8 * (n : ℝ) * s)⁻¹ ≤ (m : ℝ))
    (hmBudget : (m : ℝ) * (s * (n : ℝ)) ≤ 1 / 4)
    (h2m : 2 * m ≤ T)
    (hCvar : Cvar * s ≤ gainFloor N ^ 2 / (256 * (n : ℝ) ^ 2))
    (hcomparison :
      |V - s ^ 2 * ∑ t ∈ Finset.range T, ∑ j ∈ Finset.range t, ∑ i,
        (influenceRow N j i *
          (∏ r ∈ Finset.Ico (j + 1) t, (1 - s * gain N r))) ^ 2| ≤
        Cvar * s ^ 2 * (T : ℝ)) :
    gainFloor N ^ 2 * s / (256 * (n : ℝ) ^ 2) ≤ V / (T : ℝ) := by
  classical
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr N.hn
  have hsn0 : 0 ≤ s * (n : ℝ) := by positivity
  have hproduct (t j : ℕ) (hj : j ∈ Finset.Ico (t - m) t) :
      (1 / 2 : ℝ) ≤
        (∏ r ∈ Finset.Ico (j + 1) t, (1 - s * gain N r)) ^ 2 := by
    have hjt : j < t := (Finset.mem_Ico.mp hj).2
    let d := t - (j + 1)
    have hdle : d ≤ m := by
      dsimp [d]
      have hjlow := (Finset.mem_Ico.mp hj).1
      omega
    have hend : j + 1 + d = t := by
      dsimp [d]
      omega
    have hdbudget : (d : ℝ) * (s * (n : ℝ)) ≤ 1 / 4 := by
      have hdcast : (d : ℝ) ≤ (m : ℝ) := by exact_mod_cast hdle
      exact (mul_le_mul_of_nonneg_right hdcast hsn0).trans hmBudget
    have hlin := actual_quadratic_gain_product_ge_linear N s (j + 1) d hs
      (hdbudget.trans (by norm_num))
    rw [hend] at hlin
    have hthree : (3 / 4 : ℝ) ≤
        ∏ r ∈ Finset.Ico (j + 1) t, (1 - s * gain N r) := by
      nlinarith
    nlinarith [sq_nonneg
      ((∏ r ∈ Finset.Ico (j + 1) t, (1 - s * gain N r)) - 3 / 4)]
  have htime (t : ℕ) (ht : t ∈ Finset.Ico m T) :
      (m : ℝ) * gainFloor N ^ 2 / (8 * (n : ℝ)) ≤
        ∑ j ∈ Finset.range t, ∑ i,
          (influenceRow N j i *
            (∏ r ∈ Finset.Ico (j + 1) t, (1 - s * gain N r))) ^ 2 := by
    have hmt : m ≤ t := (Finset.mem_Ico.mp ht).1
    have hend : t - m + m = t := by omega
    have henergy := window_influence_energy_lower N (t - m) m hmThreshold
    rw [hend] at henergy
    have hweighted :
        (1 / 2 : ℝ) * ∑ j ∈ Finset.Ico (t - m) t, influenceEnergy N j ≤
          ∑ j ∈ Finset.Ico (t - m) t, ∑ i,
            (influenceRow N j i *
              (∏ r ∈ Finset.Ico (j + 1) t, (1 - s * gain N r))) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      unfold influenceEnergy
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      calc
        (1 / 2 : ℝ) * influenceRow N j i ^ 2 ≤
            (∏ r ∈ Finset.Ico (j + 1) t,
              (1 - s * gain N r)) ^ 2 * influenceRow N j i ^ 2 :=
          mul_le_mul_of_nonneg_right (hproduct t j hj) (sq_nonneg _)
        _ = (influenceRow N j i *
              (∏ r ∈ Finset.Ico (j + 1) t,
                (1 - s * gain N r))) ^ 2 := by ring
    calc
      (m : ℝ) * gainFloor N ^ 2 / (8 * (n : ℝ)) =
          (1 / 2 : ℝ) *
            ((m : ℝ) * gainFloor N ^ 2 / (4 * (n : ℝ))) := by ring
      _ ≤ (1 / 2 : ℝ) *
            ∑ j ∈ Finset.Ico (t - m) t, influenceEnergy N j :=
        mul_le_mul_of_nonneg_left henergy (by norm_num)
      _ ≤ ∑ j ∈ Finset.Ico (t - m) t, ∑ i,
            (influenceRow N j i *
              (∏ r ∈ Finset.Ico (j + 1) t,
                (1 - s * gain N r))) ^ 2 := hweighted
      _ ≤ ∑ j ∈ Finset.range t, ∑ i,
            (influenceRow N j i *
              (∏ r ∈ Finset.Ico (j + 1) t,
                (1 - s * gain N r))) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          exact Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2
        · intro j hj _
          exact Finset.sum_nonneg fun i hi => sq_nonneg _
  have hproxy :
      ((T - m : ℕ) : ℝ) *
          ((m : ℝ) * gainFloor N ^ 2 / (8 * (n : ℝ))) ≤
        ∑ t ∈ Finset.range T, ∑ j ∈ Finset.range t, ∑ i,
          (influenceRow N j i *
            (∏ r ∈ Finset.Ico (j + 1) t, (1 - s * gain N r))) ^ 2 := by
    calc
      ((T - m : ℕ) : ℝ) *
          ((m : ℝ) * gainFloor N ^ 2 / (8 * (n : ℝ))) =
          ∑ _t ∈ Finset.Ico m T,
            ((m : ℝ) * gainFloor N ^ 2 / (8 * (n : ℝ))) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ t ∈ Finset.Ico m T, ∑ j ∈ Finset.range t, ∑ i,
            (influenceRow N j i *
              (∏ r ∈ Finset.Ico (j + 1) t,
                (1 - s * gain N r))) ^ 2 :=
        Finset.sum_le_sum htime
      _ ≤ ∑ t ∈ Finset.range T, ∑ j ∈ Finset.range t, ∑ i,
            (influenceRow N j i *
              (∏ r ∈ Finset.Ico (j + 1) t,
                (1 - s * gain N r))) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro t ht
          exact Finset.mem_range.mpr (Finset.mem_Ico.mp ht).2
        · intro t ht _
          exact Finset.sum_nonneg fun j hj =>
            Finset.sum_nonneg fun i hi => sq_nonneg _
  have hmpos : 0 < (m : ℝ) :=
    lt_of_lt_of_le (inv_pos.mpr (by positivity : 0 < 8 * (n : ℝ) * s)) hmLower
  have hmposNat : 0 < m := by exact_mod_cast hmpos
  have hTposNat : 0 < T := by omega
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast hTposNat
  have hmT : m ≤ T := by omega
  have htail : (T : ℝ) / 2 ≤ ((T - m : ℕ) : ℝ) := by
    rw [Nat.cast_sub hmT]
    have h2m' : 2 * (m : ℝ) ≤ (T : ℝ) := by exact_mod_cast h2m
    linarith
  have hproxy' :
      (T : ℝ) * gainFloor N ^ 2 /
          (128 * (n : ℝ) ^ 2 * s) ≤
        ∑ t ∈ Finset.range T, ∑ j ∈ Finset.range t, ∑ i,
          (influenceRow N j i *
            (∏ r ∈ Finset.Ico (j + 1) t, (1 - s * gain N r))) ^ 2 := by
    calc
      (T : ℝ) * gainFloor N ^ 2 /
          (128 * (n : ℝ) ^ 2 * s) =
          ((T : ℝ) / 2) * (8 * (n : ℝ) * s)⁻¹ *
            (gainFloor N ^ 2 / (8 * (n : ℝ))) := by
        field_simp [hn.ne', hs.ne']
        ring
      _ ≤ ((T - m : ℕ) : ℝ) * (m : ℝ) *
            (gainFloor N ^ 2 / (8 * (n : ℝ))) := by
        gcongr
      _ = ((T - m : ℕ) : ℝ) *
            ((m : ℝ) * gainFloor N ^ 2 / (8 * (n : ℝ))) := by ring
      _ ≤ _ := hproxy
  have hproxyNorm :
      gainFloor N ^ 2 * s / (128 * (n : ℝ) ^ 2) ≤
        s ^ 2 * (∑ t ∈ Finset.range T, ∑ j ∈ Finset.range t, ∑ i,
          (influenceRow N j i *
            (∏ r ∈ Finset.Ico (j + 1) t, (1 - s * gain N r))) ^ 2) /
          (T : ℝ) := by
    apply (le_div_iff₀ hTpos).2
    calc
      gainFloor N ^ 2 * s / (128 * (n : ℝ) ^ 2) * (T : ℝ) =
          s ^ 2 * ((T : ℝ) * gainFloor N ^ 2 /
            (128 * (n : ℝ) ^ 2 * s)) := by
        field_simp [hs.ne']
      _ ≤ s ^ 2 * (∑ t ∈ Finset.range T, ∑ j ∈ Finset.range t, ∑ i,
          (influenceRow N j i *
            (∏ r ∈ Finset.Ico (j + 1) t, (1 - s * gain N r))) ^ 2) :=
        mul_le_mul_of_nonneg_left hproxy' (sq_nonneg s)
  have hproxyTotal := (le_div_iff₀ hTpos).mp hproxyNorm
  have habsorb :
      Cvar * s ^ 2 ≤ gainFloor N ^ 2 * s / (256 * (n : ℝ) ^ 2) := by
    calc
      Cvar * s ^ 2 = (Cvar * s) * s := by ring
      _ ≤ (gainFloor N ^ 2 / (256 * (n : ℝ) ^ 2)) * s :=
        mul_le_mul_of_nonneg_right hCvar hs.le
      _ = gainFloor N ^ 2 * s / (256 * (n : ℝ) ^ 2) := by ring
  have herror := mul_le_mul_of_nonneg_right habsorb hTpos.le
  have hlower := (abs_le.mp hcomparison).1
  apply (le_div_iff₀ hTpos).2
  have hdouble :
      gainFloor N ^ 2 * s / (128 * (n : ℝ) ^ 2) =
        2 * (gainFloor N ^ 2 * s / (256 * (n : ℝ) ^ 2)) := by ring
  have hgap :
      gainFloor N ^ 2 * s / (256 * (n : ℝ) ^ 2) * (T : ℝ) ≤
        gainFloor N ^ 2 * s / (128 * (n : ℝ) ^ 2) * (T : ℝ) -
          Cvar * s ^ 2 * (T : ℝ) := by
    rw [hdouble]
    nlinarith
  have hactual :
      s ^ 2 * (∑ t ∈ Finset.range T, ∑ j ∈ Finset.range t, ∑ i,
        (influenceRow N j i *
          (∏ r ∈ Finset.Ico (j + 1) t, (1 - s * gain N r))) ^ 2) -
        Cvar * s ^ 2 * (T : ℝ) ≤ V := by
    linarith
  calc
    gainFloor N ^ 2 * s / (256 * (n : ℝ) ^ 2) * (T : ℝ) ≤
        gainFloor N ^ 2 * s / (128 * (n : ℝ) ^ 2) * (T : ℝ) -
          Cvar * s ^ 2 * (T : ℝ) := hgap
    _ ≤ s ^ 2 * (∑ t ∈ Finset.range T, ∑ j ∈ Finset.range t, ∑ i,
          (influenceRow N j i *
            (∏ r ∈ Finset.Ico (j + 1) t, (1 - s * gain N r))) ^ 2) -
          Cvar * s ^ 2 * (T : ℝ) := sub_le_sub_right hproxyTotal _
    _ ≤ V := hactual

/-- The one-pulse square-energy estimate behind the stochastic half of
equation (50).  In particular, the fast geometric response is retained. -/
theorem two_rate_impulse_square_energy_error_le
    (g B C s rf : ℝ) (T : ℕ) (a p : ℕ → ℝ) (h : ℝ)
    (hg : 0 < g) (hB : 0 ≤ B) (hC : 0 ≤ C) (hs : 0 < s)
    (hs_one : s ≤ 1) (hgs : g * s ≤ 1)
    (hrf0 : 0 ≤ rf) (hrf1 : rf < 1) (hh : |h| ≤ B)
    (hp : ∀ m ∈ Finset.range T, |p m| ≤ (1 - g * s / 4) ^ m)
    (ha : ∀ m ∈ Finset.range T,
      |a m - (-s * h * p m)| ≤
        C * (s ^ 2 * (1 - g * s / 4) ^ m + s * rf ^ m)) :
    |∑ m ∈ Finset.range T, (a m) ^ 2 -
        ∑ m ∈ Finset.range T, (-s * h * p m) ^ 2| ≤
      (8 * B * C / g + 2 * B * C / (1 - rf) +
          8 * C ^ 2 / g + 2 * C ^ 2 / (1 - rf ^ 2)) * s ^ 2 := by
  let q : ℝ := 1 - g * s / 4
  have hgs_pos : 0 < g * s := mul_pos hg hs
  have hq0 : 0 ≤ q := by
    dsimp [q]
    nlinarith
  have hq1 : q < 1 := by
    dsimp [q]
    nlinarith
  have hq2 : q ^ 2 < 1 := by
    nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq1.le)]
  have hrf2 : rf ^ 2 < 1 := by
    nlinarith [mul_nonneg hrf0 (sub_nonneg.mpr hrf1.le)]
  have hden : g * s / 4 ≤ 1 - q ^ 2 := by
    dsimp [q]
    nlinarith [mul_nonneg (sub_nonneg.mpr hgs) hgs_pos.le]
  have hsmall_pos : 0 < g * s / 4 := by positivity
  have hinv : 1 / (1 - q ^ 2) ≤ 4 / (g * s) := by
    calc
      1 / (1 - q ^ 2) ≤ 1 / (g * s / 4) :=
        one_div_le_one_div_of_le hsmall_pos hden
      _ = 4 / (g * s) := by field_simp
  cases T with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, sub_zero, abs_zero]
      have hrfden : 0 ≤ 1 - rf := sub_nonneg.mpr hrf1.le
      have hrf2den : 0 ≤ 1 - rf ^ 2 := sub_nonneg.mpr hrf2.le
      exact mul_nonneg
        (add_nonneg
          (add_nonneg
            (add_nonneg (div_nonneg (by positivity) hg.le)
              (div_nonneg (by positivity) hrfden))
            (div_nonneg (by positivity) hg.le))
          (div_nonneg (by positivity) hrf2den))
        (sq_nonneg s)
  | succ N =>
      have hqsum :
          ∑ m ∈ Finset.range (N + 1), (q ^ m) ^ 2 ≤
            4 / (g * s) := by
        calc
          _ ≤ 1 / (1 - q ^ 2) := by
            simpa using
              (finite_geometric_sq_response_sum_le
                (M := (1 : ℝ)) (r := q) (x := (1 : ℝ)) hq2 N)
          _ ≤ _ := hinv
      have hrfsqsum :
          ∑ m ∈ Finset.range (N + 1), (rf ^ m) ^ 2 ≤
            1 / (1 - rf ^ 2) := by
        simpa using
          (finite_geometric_sq_response_sum_le
            (M := (1 : ℝ)) (r := rf) (x := (1 : ℝ)) hrf2 N)
      have hrfsum :
          ∑ m ∈ Finset.range (N + 1), rf ^ m ≤
            1 / (1 - rf) := by
        have h := geom_sum_Ico_le_of_lt_one
          (x := rf) (m := 0) (n := N + 1) hrf0 hrf1
        rw [← Finset.range_eq_Ico] at h
        simpa using h
      have hqrf (m : ℕ) : (q * rf) ^ m ≤ rf ^ m := by
        rw [mul_pow]
        exact mul_le_of_le_one_left (pow_nonneg hrf0 m)
          (pow_le_one₀ hq0 hq1.le)
      have hqrfsum :
          ∑ m ∈ Finset.range (N + 1), (q * rf) ^ m ≤
            1 / (1 - rf) :=
        (Finset.sum_le_sum fun m _ => hqrf m).trans hrfsum
      have hpoint (m : ℕ) (hm : m ∈ Finset.range (N + 1)) :
          |(a m) ^ 2 - (-s * h * p m) ^ 2| ≤
            2 * B * C *
                (s ^ 3 * (q ^ m) ^ 2 + s ^ 2 * (q * rf) ^ m) +
              2 * C ^ 2 *
                (s ^ 4 * (q ^ m) ^ 2 + s ^ 2 * (rf ^ m) ^ 2) := by
        let b : ℝ := -s * h * p m
        let E : ℝ := C * (s ^ 2 * q ^ m + s * rf ^ m)
        let F : ℝ := s * B * q ^ m
        have hqm0 : 0 ≤ q ^ m := pow_nonneg hq0 m
        have hrm0 : 0 ≤ rf ^ m := pow_nonneg hrf0 m
        have hE0 : 0 ≤ E := by dsimp [E]; positivity
        have hF0 : 0 ≤ F := by dsimp [F]; positivity
        have he : |a m - b| ≤ E := by
          dsimp [b, E]
          simpa [q] using ha m hm
        have hb : |b| ≤ F := by
          dsimp [b, F]
          rw [abs_mul, abs_mul, abs_neg, abs_of_pos hs]
          have hhp : |h| * |p m| ≤ B * q ^ m :=
            mul_le_mul hh (by simpa [q] using hp m hm)
              (abs_nonneg _) hB
          calc
            s * |h| * |p m| = s * (|h| * |p m|) := by ring
            _ ≤ s * (B * q ^ m) :=
              mul_le_mul_of_nonneg_left hhp hs.le
            _ = s * B * q ^ m := by ring
        have hplus : |a m + b| ≤ E + 2 * F := by
          calc
            |a m + b| = |(a m - b) + 2 * b| := by ring_nf
            _ ≤ |a m - b| + |2 * b| := abs_add_le _ _
            _ = |a m - b| + 2 * |b| := by simp [abs_mul]
            _ ≤ E + 2 * F := by
              exact add_le_add he
                (mul_le_mul_of_nonneg_left hb (by norm_num))
        have hbasic : |(a m) ^ 2 - b ^ 2| ≤ E * (E + 2 * F) := by
          calc
            |(a m) ^ 2 - b ^ 2| = |a m - b| * |a m + b| := by
              rw [← abs_mul]
              congr 1
              ring
            _ ≤ E * (E + 2 * F) :=
              mul_le_mul he hplus (abs_nonneg _) hE0
        dsimp [b] at hbasic ⊢
        dsimp [E, F] at hbasic
        have hpow : (q * rf) ^ m = q ^ m * rf ^ m := mul_pow q rf m
        calc
          _ ≤ C * (s ^ 2 * q ^ m + s * rf ^ m) *
                (C * (s ^ 2 * q ^ m + s * rf ^ m) +
                  2 * (s * B * q ^ m)) := hbasic
          _ ≤ 2 * B * C *
                  (s ^ 3 * (q ^ m) ^ 2 + s ^ 2 * (q * rf) ^ m) +
                2 * C ^ 2 *
                  (s ^ 4 * (q ^ m) ^ 2 + s ^ 2 * (rf ^ m) ^ 2) := by
            rw [hpow]
            nlinarith [mul_nonneg (sq_nonneg C)
              (sq_nonneg (s ^ 2 * q ^ m - s * rf ^ m))]
      have hsumPoint :
          |∑ m ∈ Finset.range (N + 1), (a m) ^ 2 -
              ∑ m ∈ Finset.range (N + 1), (-s * h * p m) ^ 2| ≤
            ∑ m ∈ Finset.range (N + 1),
              (2 * B * C *
                  (s ^ 3 * (q ^ m) ^ 2 + s ^ 2 * (q * rf) ^ m) +
                2 * C ^ 2 *
                  (s ^ 4 * (q ^ m) ^ 2 + s ^ 2 * (rf ^ m) ^ 2)) := by
        calc
          _ ≤ ∑ m ∈ Finset.range (N + 1),
                |(a m) ^ 2 - (-s * h * p m) ^ 2| := by
            rw [← Finset.sum_sub_distrib]
            exact Finset.abs_sum_le_sum_abs _ _
          _ ≤ _ := Finset.sum_le_sum hpoint
      have hsumExpand :
          ∑ m ∈ Finset.range (N + 1),
              (2 * B * C *
                  (s ^ 3 * (q ^ m) ^ 2 + s ^ 2 * (q * rf) ^ m) +
                2 * C ^ 2 *
                  (s ^ 4 * (q ^ m) ^ 2 + s ^ 2 * (rf ^ m) ^ 2)) =
            (2 * B * C * s ^ 3) *
                ∑ m ∈ Finset.range (N + 1), (q ^ m) ^ 2 +
              (2 * B * C * s ^ 2) *
                ∑ m ∈ Finset.range (N + 1), (q * rf) ^ m +
              (2 * C ^ 2 * s ^ 4) *
                ∑ m ∈ Finset.range (N + 1), (q ^ m) ^ 2 +
              (2 * C ^ 2 * s ^ 2) *
                ∑ m ∈ Finset.range (N + 1), (rf ^ m) ^ 2 := by
        calc
          _ = ∑ m ∈ Finset.range (N + 1),
                (((2 * B * C * s ^ 3) * (q ^ m) ^ 2 +
                    (2 * B * C * s ^ 2) * (q * rf) ^ m) +
                  ((2 * C ^ 2 * s ^ 4) * (q ^ m) ^ 2 +
                    (2 * C ^ 2 * s ^ 2) * (rf ^ m) ^ 2)) := by
            apply Finset.sum_congr rfl
            intro m hm
            ring
          _ = _ := by
            simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
            ring
      rw [hsumExpand] at hsumPoint
      have hA0 : 0 ≤ 2 * B * C * s ^ 3 := by positivity
      have hD0 : 0 ≤ 2 * B * C * s ^ 2 := by positivity
      have hE0 : 0 ≤ 2 * C ^ 2 * s ^ 4 := by positivity
      have hF0 : 0 ≤ 2 * C ^ 2 * s ^ 2 := by positivity
      have hsumA := mul_le_mul_of_nonneg_left hqsum hA0
      have hsumD := mul_le_mul_of_nonneg_left hqrfsum hD0
      have hsumE := mul_le_mul_of_nonneg_left hqsum hE0
      have hsumF := mul_le_mul_of_nonneg_left hrfsqsum hF0
      calc
        _ ≤ (2 * B * C * s ^ 3) * (4 / (g * s)) +
              (2 * B * C * s ^ 2) * (1 / (1 - rf)) +
              (2 * C ^ 2 * s ^ 4) * (4 / (g * s)) +
              (2 * C ^ 2 * s ^ 2) * (1 / (1 - rf ^ 2)) :=
          hsumPoint.trans (by nlinarith)
        _ = (8 * B * C / g) * s ^ 2 +
              (2 * B * C / (1 - rf)) * s ^ 2 +
              (8 * C ^ 2 / g) * s ^ 3 +
              (2 * C ^ 2 / (1 - rf ^ 2)) * s ^ 2 := by
          field_simp [hg.ne', hs.ne']
          ring
        _ ≤ (8 * B * C / g) * s ^ 2 +
              (2 * B * C / (1 - rf)) * s ^ 2 +
              (8 * C ^ 2 / g) * s ^ 2 +
              (2 * C ^ 2 / (1 - rf ^ 2)) * s ^ 2 := by
          have hs3 : s ^ 3 ≤ s ^ 2 := by
            nlinarith [mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hs_one)]
          have hcoef : 0 ≤ 8 * C ^ 2 / g := div_nonneg (by positivity) hg.le
          nlinarith [mul_le_mul_of_nonneg_left hs3 hcoef]
        _ = (8 * B * C / g + 2 * B * C / (1 - rf) +
              8 * C ^ 2 / g + 2 * C ^ 2 / (1 - rf ^ 2)) * s ^ 2 := by
          ring

/-- Triangular horizon aggregation for per-impulse energy comparisons. -/
theorem triangular_square_energy_difference_le
    {ι : Type*} [Fintype ι]
    (T : ℕ) (A B : ℕ → ι → ℕ → ℝ) (E : ℝ)
    (hE : 0 ≤ E)
    (hper : ∀ j ∈ Finset.range T, ∀ i,
      |∑ m ∈ Finset.range (T - 1 - j), A j i m -
          ∑ m ∈ Finset.range (T - 1 - j), B j i m| ≤ E) :
    |∑ t ∈ Finset.range T, ∑ j ∈ Finset.range t, ∑ i, A j i (t - 1 - j) -
        ∑ t ∈ Finset.range T, ∑ j ∈ Finset.range t, ∑ i, B j i (t - 1 - j)| ≤
      (T : ℝ) * (Fintype.card ι : ℝ) * E := by
  cases T with
  | zero => simp
  | succ K =>
      have hdiagA :
          ∑ t ∈ Finset.range (K + 1),
              ∑ j ∈ Finset.range t, ∑ i, A j i (t - 1 - j) =
            ∑ j ∈ Finset.range K,
              ∑ m ∈ Finset.range (K - j), ∑ i, A j i m := by
        simpa [Finset.sum_range_succ'] using
          (Finset.sum_range_diag_flip K (fun j m => ∑ i, A j i m))
      have hdiagB :
          ∑ t ∈ Finset.range (K + 1),
              ∑ j ∈ Finset.range t, ∑ i, B j i (t - 1 - j) =
            ∑ j ∈ Finset.range K,
              ∑ m ∈ Finset.range (K - j), ∑ i, B j i m := by
        simpa [Finset.sum_range_succ'] using
          (Finset.sum_range_diag_flip K (fun j m => ∑ i, B j i m))
      rw [hdiagA, hdiagB]
      have hrearrange :
          (∑ j ∈ Finset.range K,
                ∑ m ∈ Finset.range (K - j), ∑ i, A j i m) -
              (∑ j ∈ Finset.range K,
                ∑ m ∈ Finset.range (K - j), ∑ i, B j i m) =
            ∑ j ∈ Finset.range K, ∑ i,
              ((∑ m ∈ Finset.range (K - j), A j i m) -
                ∑ m ∈ Finset.range (K - j), B j i m) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        have hcommA :
            (∑ m ∈ Finset.range (K - j), ∑ i, A j i m) =
              ∑ i, ∑ m ∈ Finset.range (K - j), A j i m :=
          Finset.sum_comm
        have hcommB :
            (∑ m ∈ Finset.range (K - j), ∑ i, B j i m) =
              ∑ i, ∑ m ∈ Finset.range (K - j), B j i m :=
          Finset.sum_comm
        calc
          (∑ m ∈ Finset.range (K - j), ∑ i, A j i m) -
              ∑ m ∈ Finset.range (K - j), ∑ i, B j i m =
              (∑ i, ∑ m ∈ Finset.range (K - j), A j i m) -
                ∑ i, ∑ m ∈ Finset.range (K - j), B j i m := by
            rw [hcommA, hcommB]
          _ = ∑ i,
              ((∑ m ∈ Finset.range (K - j), A j i m) -
                ∑ m ∈ Finset.range (K - j), B j i m) := by
            rw [Finset.sum_sub_distrib]
      rw [hrearrange]
      calc
        |∑ j ∈ Finset.range K, ∑ i,
            ((∑ m ∈ Finset.range (K - j), A j i m) -
              ∑ m ∈ Finset.range (K - j), B j i m)| ≤
            ∑ j ∈ Finset.range K, ∑ i,
              |(∑ m ∈ Finset.range (K - j), A j i m) -
                ∑ m ∈ Finset.range (K - j), B j i m| := by
          calc
            _ ≤ ∑ j ∈ Finset.range K,
                |∑ i,
                  ((∑ m ∈ Finset.range (K - j), A j i m) -
                    ∑ m ∈ Finset.range (K - j), B j i m)| :=
              Finset.abs_sum_le_sum_abs _ _
            _ ≤ _ := by
              apply Finset.sum_le_sum
              intro j hj
              exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ Finset.range K, ∑ _i : ι, E := by
          apply Finset.sum_le_sum
          intro j hj
          apply Finset.sum_le_sum
          intro i hi
          simpa using hper j (Finset.mem_range.mpr
            ((Finset.mem_range.mp hj).trans (Nat.lt_succ_self K))) i
        _ ≤ ((K + 1 : ℕ) : ℝ) * (Fintype.card ι : ℝ) * E := by
          simp only [Finset.sum_const, Finset.card_univ, Finset.card_range,
            nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
          have hcard : 0 ≤ (Fintype.card ι : ℝ) := by positivity
          nlinarith

/-- Declaration-order-local form of the scalar window budget used by the
equations-(52)--(56) comparator trial.  The public theorem with the same
mathematical statement is retained below with the effective-node API. -/
theorem actual_quadratic_windowLength_le_budget_div_gainFloor
    (N : NetworkSetup n) (T t : ℕ) (s : ℝ) (hs : 0 < s) :
    (windowLength N T t s : ℝ) ≤ epsilon / (s * gainFloor N) := by
  classical
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr N.hn
  have hmu : 0 < mixingMinorization N := by
    unfold mixingMinorization
    split_ifs
    · exact pow_pos ((lt_min_iff).2 ⟨N.ha, by norm_num⟩) _
    · norm_num
  have hg : 0 < gainFloor N :=
    (mul_pos hn hmu).trans_le (gainFloor_ge_n_mul_mixingMinorization N)
  have hR : 0 ≤ epsilon / (s * gainFloor N) :=
    div_nonneg (by norm_num [epsilon]) (mul_pos hs hg).le
  unfold windowLength
  by_cases htT : t < T
  · rw [if_pos htT]
    have hsup :
        ((Finset.Icc t T).sup fun P =>
          (Finset.Icc (P + 1) T).sup fun Q =>
            if s * ∑ r ∈ Finset.Ico P Q, gain N r ≤ epsilon
            then Q - P else 0 : ℕ) ≤
          (Nat.floor (epsilon / (s * gainFloor N)) : ℕ) := by
      apply Finset.sup_le
      intro P hP
      apply Finset.sup_le
      intro Q hQ
      split_ifs with hbudget
      · have hPQ : P ≤ Q := by
          simp only [Finset.mem_Icc] at hQ
          omega
        have hgain_sum :
            ((Q - P : ℕ) : ℝ) * gainFloor N ≤
              ∑ r ∈ Finset.Ico P Q, gain N r := by
          calc
            ((Q - P : ℕ) : ℝ) * gainFloor N =
                ∑ r ∈ Finset.Ico P Q, gainFloor N := by simp [hPQ]
            _ ≤ ∑ r ∈ Finset.Ico P Q, gain N r :=
              Finset.sum_le_sum fun r _ => gainFloor_le_gain N r
        have hsum_budget :
            (∑ r ∈ Finset.Ico P Q, gain N r) ≤ epsilon / s :=
          (le_div_iff₀ hs).2 (by simpa [mul_comm] using hbudget)
        apply Nat.le_floor
        calc
          ((Q - P : ℕ) : ℝ) ≤ (epsilon / s) / gainFloor N :=
            (le_div_iff₀ hg).2 (hgain_sum.trans hsum_budget)
          _ = epsilon / (s * gainFloor N) := by ring
      · exact Nat.zero_le _
    have hcast :
        (((Finset.Icc t T).sup fun P =>
          (Finset.Icc (P + 1) T).sup fun Q =>
            if s * ∑ r ∈ Finset.Ico P Q, gain N r ≤ epsilon
            then Q - P else 0 : ℕ) : ℝ) ≤
          (Nat.floor (epsilon / (s * gainFloor N)) : ℕ) := by
      exact_mod_cast hsup
    exact hcast.trans (Nat.floor_le hR)
  · rw [if_neg htT]
    norm_num
    exact hR

/-- The source comparator trial used before the cost dichotomy in (53).
At the admissible trial `s=T⁻¹ᵗ²`, the window budget and the uniform
row-energy bound give exactly `M₀ᶜᵒˢᵗ/√T`. -/
theorem actual_quadratic_comparator_trial_upper
    (N : NetworkSetup n) (L Δ σ : ℝ)
    (hL : 0 < L) (hΔ : 0 < Δ) (T : PositiveHorizon)
    (hlarge : (64 * n : ℕ) ^ 2 ≤ T.1) :
    comparator N L Δ σ T ≤
      ((ADelta L Δ + σ ^ 2 * influenceRowBound N ^ 2 / 2) /
        gainFloor N) / Real.sqrt T.1 := by
  classical
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr N.hn
  have hT : (0 : ℝ) < T.1 := Nat.cast_pos.mpr T.2
  have hA : 0 < ADelta L Δ := by
    unfold ADelta
    exact mul_pos hL hΔ
  have hg : 0 < gainFloor N :=
    (uniform_mixing_and_influence N).2.2.2.2.2.2.2.1
  have hB : 0 ≤ influenceRowBound N := by
    have hnorm : 0 ≤ nodeL2Norm (influenceRow N 0) := by
      unfold nodeL2Norm
      exact Real.sqrt_nonneg _
    exact hnorm.trans (influenceRow_nodeL2_le N 0)
  have hsqrt : 0 < Real.sqrt T.1 := Real.sqrt_pos.2 hT
  have hsqrt_sq : (Real.sqrt T.1) ^ 2 = (T.1 : ℝ) :=
    Real.sq_sqrt hT.le
  have h64n : (64 : ℝ) * n ≤ Real.sqrt T.1 := by
    have hcast : ((64 * n : ℕ) ^ 2 : ℝ) ≤ (T.1 : ℝ) := by
      exact_mod_cast hlarge
    have hnonneg : 0 ≤ (64 : ℝ) * n := by positivity
    apply (sq_le_sq₀ hnonneg hsqrt.le).mp
    simpa [hsqrt_sq] using hcast
  let sT : AdmissibleDimensionlessStepsize n :=
    ⟨(Real.sqrt T.1)⁻¹, inv_pos.mpr hsqrt, by
      simpa [one_div] using
        (one_div_le_one_div_of_le (mul_pos (by norm_num) hn) h64n)⟩
  have hsT : 0 < sT.1 := sT.2.1
  have hsT_eq : sT.1 = (Real.sqrt T.1)⁻¹ := rfl
  have hwindow (t : ℕ) :
      (windowLength N T.1 t sT.1 : ℝ) ≤
        epsilon * Real.sqrt T.1 / gainFloor N := by
    calc
      (windowLength N T.1 t sT.1 : ℝ) ≤
          epsilon / (sT.1 * gainFloor N) :=
        actual_quadratic_windowLength_le_budget_div_gainFloor
          N T.1 t sT.1 hsT
      _ = epsilon * Real.sqrt T.1 / gainFloor N := by
        rw [hsT_eq]
        field_simp [ne_of_gt hsqrt, ne_of_gt hg]
  have henergy (j : ℕ) :
      influenceEnergy N j ≤ influenceRowBound N ^ 2 := by
    have hnormsq : nodeL2Norm (influenceRow N j) ^ 2 =
        influenceEnergy N j := by
      unfold nodeL2Norm influenceEnergy
      rw [Real.sq_sqrt]
      exact Finset.sum_nonneg fun i _ => sq_nonneg (influenceRow N j i)
    have hnorm_nonneg : 0 ≤ nodeL2Norm (influenceRow N j) := by
      unfold nodeL2Norm
      exact Real.sqrt_nonneg _
    rw [← hnormsq]
    nlinarith [influenceRow_nodeL2_le N j]
  have hwindow_nonneg (t : ℕ) :
      0 ≤ (windowLength N T.1 t sT.1 : ℝ) := Nat.cast_nonneg _
  have hsum : windowInfluenceSum N T.1 sT.1 ≤
      (T.1 : ℝ) * influenceRowBound N ^ 2 *
        (epsilon * Real.sqrt T.1 / gainFloor N) := by
    unfold windowInfluenceSum
    calc
      (∑ j ∈ Finset.range T.1,
          influenceEnergy N j * windowLength N T.1 (j + 1) sT.1) ≤
          ∑ _j ∈ Finset.range T.1,
            influenceRowBound N ^ 2 *
              (epsilon * Real.sqrt T.1 / gainFloor N) := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul (henergy j) (hwindow (j + 1))
          (hwindow_nonneg (j + 1)) (sq_nonneg _)
      _ = (T.1 : ℝ) * influenceRowBound N ^ 2 *
          (epsilon * Real.sqrt T.1 / gainFloor N) := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
  have hnum : comparatorNumerator N L Δ σ T sT ≤
      epsilon * Real.sqrt T.1 / gainFloor N *
        (ADelta L Δ + σ ^ 2 * influenceRowBound N ^ 2 / 2) := by
    unfold comparatorNumerator
    have hnoise :
        (σ ^ 2 / 2) * sT.1 ^ 2 * windowInfluenceSum N T.1 sT.1 ≤
          epsilon * Real.sqrt T.1 / gainFloor N *
            (σ ^ 2 * influenceRowBound N ^ 2 / 2) := by
      have hcoeff : 0 ≤ (σ ^ 2 / 2) * sT.1 ^ 2 := by positivity
      calc
        (σ ^ 2 / 2) * sT.1 ^ 2 * windowInfluenceSum N T.1 sT.1 ≤
            (σ ^ 2 / 2) * sT.1 ^ 2 *
              ((T.1 : ℝ) * influenceRowBound N ^ 2 *
                (epsilon * Real.sqrt T.1 / gainFloor N)) :=
          mul_le_mul_of_nonneg_left hsum hcoeff
        _ = epsilon * Real.sqrt T.1 / gainFloor N *
              (σ ^ 2 * influenceRowBound N ^ 2 / 2) := by
          rw [hsT_eq]
          field_simp [ne_of_gt hsqrt, ne_of_gt hg]
          rw [hsqrt_sq]
    calc
      ADelta L Δ * windowLength N T.1 0 sT.1 +
          (σ ^ 2 / 2) * sT.1 ^ 2 * windowInfluenceSum N T.1 sT.1 ≤
        ADelta L Δ * (epsilon * Real.sqrt T.1 / gainFloor N) +
          epsilon * Real.sqrt T.1 / gainFloor N *
            (σ ^ 2 * influenceRowBound N ^ 2 / 2) :=
        add_le_add (mul_le_mul_of_nonneg_left (hwindow 0) hA.le) hnoise
      _ = epsilon * Real.sqrt T.1 / gainFloor N *
          (ADelta L Δ + σ ^ 2 * influenceRowBound N ^ 2 / 2) := by ring
  have hAt : comparatorAt N L Δ σ T sT ≤
      ((ADelta L Δ + σ ^ 2 * influenceRowBound N ^ 2 / 2) /
        gainFloor N) / Real.sqrt T.1 := by
    unfold comparatorAt
    rw [div_le_iff₀ (mul_pos (by norm_num [epsilon]) hT)]
    calc
      comparatorNumerator N L Δ σ T sT ≤
          epsilon * Real.sqrt T.1 / gainFloor N *
            (ADelta L Δ + σ ^ 2 * influenceRowBound N ^ 2 / 2) := hnum
      _ = ((ADelta L Δ + σ ^ 2 * influenceRowBound N ^ 2 / 2) /
            gainFloor N) / Real.sqrt T.1 * (epsilon * T.1) := by
        field_simp [ne_of_gt hsqrt, ne_of_gt hg]
        rw [hsqrt_sq]
  have hrange_bdd : BddBelow (Set.range fun s : AdmissibleDimensionlessStepsize n =>
      comparatorAt N L Δ σ T s) := by
    refine ⟨0, ?_⟩
    rintro y ⟨u, rfl⟩
    have henergy_nonneg : 0 ≤ windowInfluenceSum N T.1 u.1 := by
      unfold windowInfluenceSum influenceEnergy
      exact Finset.sum_nonneg fun j _ =>
        mul_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)
          (Nat.cast_nonneg _)
    unfold comparatorAt comparatorNumerator
    exact div_nonneg
      (add_nonneg (mul_nonneg hA.le (Nat.cast_nonneg _))
        (mul_nonneg (by positivity) henergy_nonneg))
      (mul_pos (by norm_num [epsilon]) hT).le
  unfold comparator
  exact (csInf_le hrange_bdd ⟨sT, rfl⟩).trans hAt

/-- Equation (54)'s logarithmic delay estimate, derived from the literal
ceiling definition in equation (35). -/
theorem loadingDelay_le_affine_log_inv
    (N : NetworkSetup n) (s : ℝ) (hs : 0 < s) (hsOne : s ≤ 1) :
    (loadingDelay N s : ℝ) ≤
      5 + 2 * Real.log (loadingConstant N) /
          Real.log (1 / loadingRate N) +
        6 / Real.log (1 / loadingRate N) * Real.log (1 / s) := by
  obtain ⟨_hρpos, _hρlt, _hflat, _hfast, _htrans, hKone,
      _hKflat, _hKtri, hell⟩ := loading_constants_spec N
  have hKpos : 0 < loadingConstant N :=
    lt_of_lt_of_le zero_lt_one hKone
  have hs3pos : 0 < s ^ 3 := pow_pos hs _
  have hinvs : 1 ≤ 1 / s := (le_div_iff₀ hs).2 (by simpa using hsOne)
  have hloginvs : 0 ≤ Real.log (1 / s) := Real.log_nonneg hinvs
  have hlogK : 0 ≤ Real.log (loadingConstant N) := Real.log_nonneg hKone
  let R : ℝ := Real.log (loadingConstant N / s ^ 3) /
    Real.log (1 / loadingRate N)
  have hlog_formula :
      Real.log (loadingConstant N / s ^ 3) =
        Real.log (loadingConstant N) + 3 * Real.log (1 / s) := by
    rw [Real.log_div (ne_of_gt hKpos) (ne_of_gt hs3pos), Real.log_pow,
      Real.log_div (by norm_num) (ne_of_gt hs)]
    simp only [Real.log_one, zero_sub]
    ring
  have hR : 0 ≤ R := by
    dsimp [R]
    rw [hlog_formula]
    exact div_nonneg (add_nonneg hlogK (mul_nonneg (by norm_num) hloginvs)) hell.le
  have hceil : ((Nat.ceil R : ℕ) : ℝ) ≤ R + 1 :=
    (Nat.ceil_lt_add_one hR).le
  have hhalf : (loadingHalfDelay N s : ℝ) ≤ R + 1 := by
    unfold loadingHalfDelay
    rw [Nat.cast_max]
    apply max_le
    · norm_num
      exact hR
    · exact hceil
  unfold loadingDelay
  push_cast
  dsimp [R] at hhalf ⊢
  rw [hlog_formula] at hhalf
  have hellne : Real.log (1 / loadingRate N) ≠ 0 := ne_of_gt hell
  field_simp [hellne] at hhalf ⊢
  nlinarith

/-- Equations (54)--(55), at the exact interface needed by the storage
construction: one horizon threshold works for every stepsize in the localized
`T⁻¹ᐟ²` interval. -/
theorem equation54_uniform_storage_loss_and_onset
    (N : NetworkSetup n) (L Δ σ cQ CQ sLoad : ℝ)
    (hL : 0 < L) (hΔ : 0 < Δ) (hcQ : 0 < cQ) (hCQ : 0 < CQ)
    (hsLoad : 0 < sLoad) :
    ∃ T₀ : ℕ, ∀ T : PositiveHorizon, T₀ ≤ T.1 →
      ∀ s : ℝ, 0 < s →
        cQ / Real.sqrt T.1 ≤ s → s ≤ CQ / Real.sqrt T.1 →
        s ≤ sLoad ∧
          σ ^ 2 *
            (influenceRowBound N ^ 2 * s ^ 2 *
                (loadingDelay N s - 1) + n * s ^ 4 * T.1) ≤
            48 * ADelta L Δ := by
  have hA : 0 < ADelta L Δ := by
    unfold ADelta
    exact mul_pos hL hΔ
  obtain ⟨_hρpos, _hρlt, _hflat, _hfast, _htrans, hKone,
      _hKflat, _hKtri, hell⟩ := loading_constants_spec N
  have hlogK : 0 ≤ Real.log (loadingConstant N) := Real.log_nonneg hKone
  let c₀ : ℝ := 5 + 2 * Real.log (loadingConstant N) /
    Real.log (1 / loadingRate N)
  let c₁ : ℝ := 6 / Real.log (1 / loadingRate N)
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  have hc₁ : 0 < c₁ := by dsimp [c₁]; positivity
  let D₁ : ℝ := σ ^ 2 * influenceRowBound N ^ 2 * c₁ * CQ
  let D₂ : ℝ := σ ^ 2 *
    (influenceRowBound N ^ 2 * c₀ * CQ ^ 2 + (n : ℝ) * CQ ^ 4)
  have hinvT : Filter.Tendsto (fun k : ℕ => ((k : ℝ))⁻¹)
      Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hinvSqrt : Filter.Tendsto (fun k : ℕ => (Real.sqrt (k : ℝ))⁻¹)
      Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hvanish : Filter.Tendsto
      (fun k : ℕ => D₁ * (Real.sqrt (k : ℝ))⁻¹ + D₂ * ((k : ℝ))⁻¹)
      Filter.atTop (nhds 0) := by
    simpa using (hinvSqrt.const_mul D₁).add (hinvT.const_mul D₂)
  have heventLoss : ∀ᶠ k : ℕ in Filter.atTop,
      D₁ * (Real.sqrt (k : ℝ))⁻¹ + D₂ * ((k : ℝ))⁻¹ <
        48 * ADelta L Δ :=
    (tendsto_order.1 hvanish).2 _ (by positivity)
  have hsqrtTop : Filter.Tendsto (fun k : ℕ => Real.sqrt (k : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have heventLoad : ∀ᶠ k : ℕ in Filter.atTop,
      max (CQ / sLoad) CQ ≤ Real.sqrt (k : ℝ) :=
    (Filter.tendsto_atTop.1 hsqrtTop) _
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.1 (heventLoss.and heventLoad)
  refine ⟨T₀, ?_⟩
  intro T hTlarge s hs _hsLower hsUpper
  have hT₀both := hT₀ T.1 hTlarge
  have hT₀loss := hT₀both.1
  have hT₀load := hT₀both.2
  have hT : (0 : ℝ) < T.1 := Nat.cast_pos.mpr T.2
  have hsqrt : 0 < Real.sqrt T.1 := Real.sqrt_pos.2 hT
  have hsqrtSq : (Real.sqrt T.1) ^ 2 = (T.1 : ℝ) :=
    Real.sq_sqrt hT.le
  have hsroot : s * Real.sqrt T.1 ≤ CQ := by
    have hsUpper' := hsUpper
    rw [le_div_iff₀ hsqrt] at hsUpper'
    exact hsUpper'
  have hsLoadUse : s ≤ sLoad := by
    have hroot : CQ / sLoad ≤ Real.sqrt T.1 :=
      (le_max_left _ _).trans hT₀load
    have hCQroot : CQ ≤ sLoad * Real.sqrt T.1 := by
      calc
        CQ = (CQ / sLoad) * sLoad := by field_simp [ne_of_gt hsLoad]
        _ ≤ Real.sqrt T.1 * sLoad :=
          mul_le_mul_of_nonneg_right hroot hsLoad.le
        _ = sLoad * Real.sqrt T.1 := by ring
    exact hsUpper.trans ((div_le_iff₀ hsqrt).2 hCQroot)
  have hsOne : s ≤ 1 := by
    have hroot : CQ ≤ Real.sqrt T.1 :=
      (le_max_right (CQ / sLoad) CQ).trans hT₀load
    exact hsUpper.trans ((div_le_iff₀ hsqrt).2 (by simpa using hroot))
  have hdelay0 := loadingDelay_le_affine_log_inv N s hs hsOne
  have hlogInv : Real.log (1 / s) ≤ 1 / s := by
    linarith [Real.log_le_sub_one_of_pos (one_div_pos.mpr hs)]
  have hdelay : (loadingDelay N s : ℝ) ≤ c₀ + c₁ / s := by
    change (loadingDelay N s : ℝ) ≤ c₀ + c₁ * Real.log (1 / s) at hdelay0
    have hmul := mul_le_mul_of_nonneg_left hlogInv hc₁.le
    calc
      (loadingDelay N s : ℝ) ≤ c₀ + c₁ * Real.log (1 / s) := hdelay0
      _ ≤ c₀ + c₁ * (1 / s) := add_le_add_right hmul c₀
      _ = c₀ + c₁ / s := by ring
  have hdelaySub : (loadingDelay N s : ℝ) - 1 ≤ c₀ + c₁ / s := by
    linarith
  have hsSqT : s ^ 2 * (T.1 : ℝ) ≤ CQ ^ 2 := by
    have hsquares := mul_self_le_mul_self
      (mul_nonneg hs.le hsqrt.le) hsroot
    calc
      s ^ 2 * (T.1 : ℝ) = (s * Real.sqrt T.1) ^ 2 := by
        conv_lhs => rw [← hsqrtSq]
        ring
      _ ≤ CQ ^ 2 := by simpa [pow_two] using hsquares
  have hsSq : s ^ 2 ≤ CQ ^ 2 / (T.1 : ℝ) :=
    (le_div_iff₀ hT).2 (by simpa [mul_comm] using hsSqT)
  have hsFourthT : s ^ 4 * (T.1 : ℝ) ≤ CQ ^ 4 / (T.1 : ℝ) := by
    calc
      s ^ 4 * (T.1 : ℝ) = s ^ 2 * (s ^ 2 * (T.1 : ℝ)) := by ring
      _ ≤ s ^ 2 * CQ ^ 2 :=
        mul_le_mul_of_nonneg_left hsSqT (sq_nonneg s)
      _ ≤ (CQ ^ 2 / (T.1 : ℝ)) * CQ ^ 2 :=
        mul_le_mul_of_nonneg_right hsSq (sq_nonneg CQ)
      _ = CQ ^ 4 / (T.1 : ℝ) := by ring
  have hdelayScaled :
      s ^ 2 * ((loadingDelay N s : ℝ) - 1) ≤
        c₀ * CQ ^ 2 / (T.1 : ℝ) + c₁ * CQ / Real.sqrt T.1 := by
    have hmul := mul_le_mul_of_nonneg_left hdelaySub (sq_nonneg s)
    have hsLinear : s ≤ CQ / Real.sqrt T.1 := hsUpper
    have hc0mul := mul_le_mul_of_nonneg_left hsSq hc₀.le
    have hc1mul := mul_le_mul_of_nonneg_left hsLinear hc₁.le
    have hsne : s ≠ 0 := ne_of_gt hs
    calc
      s ^ 2 * ((loadingDelay N s : ℝ) - 1) ≤
          s ^ 2 * (c₀ + c₁ / s) := hmul
      _ = c₀ * s ^ 2 + c₁ * s := by field_simp [hsne]
      _ ≤ c₀ * (CQ ^ 2 / (T.1 : ℝ)) +
          c₁ * (CQ / Real.sqrt T.1) := add_le_add hc0mul hc1mul
      _ = c₀ * CQ ^ 2 / (T.1 : ℝ) +
          c₁ * CQ / Real.sqrt T.1 := by ring
  have hBsq : 0 ≤ influenceRowBound N ^ 2 := sq_nonneg _
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hinside :
      influenceRowBound N ^ 2 * s ^ 2 *
            ((loadingDelay N s : ℝ) - 1) +
          (n : ℝ) * s ^ 4 * T.1 ≤
        influenceRowBound N ^ 2 *
            (c₀ * CQ ^ 2 / T.1 + c₁ * CQ / Real.sqrt T.1) +
          (n : ℝ) * (CQ ^ 4 / T.1) :=
    add_le_add
      (by simpa [mul_assoc] using
        (mul_le_mul_of_nonneg_left hdelayScaled hBsq))
      (by simpa [mul_assoc] using
        (mul_le_mul_of_nonneg_left hsFourthT hn))
  have hbound :
      σ ^ 2 *
          (influenceRowBound N ^ 2 * s ^ 2 *
              ((loadingDelay N s : ℝ) - 1) +
            (n : ℝ) * s ^ 4 * T.1) ≤
        D₁ / Real.sqrt T.1 + D₂ / T.1 := by
    calc
      _ ≤ σ ^ 2 *
          (influenceRowBound N ^ 2 *
              (c₀ * CQ ^ 2 / T.1 + c₁ * CQ / Real.sqrt T.1) +
            (n : ℝ) * (CQ ^ 4 / T.1)) :=
        mul_le_mul_of_nonneg_left hinside (sq_nonneg σ)
      _ = D₁ / Real.sqrt T.1 + D₂ / T.1 := by
        dsimp [D₁, D₂]
        ring
  refine ⟨hsLoadUse, hbound.trans ?_⟩
  simpa [div_eq_mul_inv] using hT₀loss.le

/-- Equation (53) as a scalar response lemma.  The onset is uniform in the
actual response energies: equation (52) first enters the fixed response cap,
then the signal and variance parts of equation (51) give the two sides of the
localized `T⁻¹/²` interval. -/
theorem actual_quadratic_equation53_low_cost_localization
    (n : ℕ) (A M sigma g Csig sResp : ℝ)
    (hn : 0 < n) (hA : 0 < A) (hM : 0 < M) (hsigma : 0 < sigma)
    (hg : 0 < g) (hCsig : 0 ≤ Csig) (hsResp : 0 < sResp) :
    ∃ T53 : ℕ, ∀ T : ℕ, T53 ≤ T → 0 < T →
      ∀ s D V Q : ℝ, 0 < s → 0 ≤ D → 0 ≤ V →
        (T : ℝ) * Q = 2 * A * D + sigma ^ 2 * V →
        (((T - 1 : ℕ) : ℝ) * s ^ 2) / (n : ℝ) ≤ V →
        (s ≤ sResp → D ≥ (1 / 2 : ℝ) * min (T : ℝ)
              ((4 * (n : ℝ) * s)⁻¹) - Csig) →
        (s ≤ sResp →
          2 * Nat.floor ((4 * (n : ℝ) * s)⁻¹) ≤ T →
          g ^ 2 * s / (256 * (n : ℝ) ^ 2) ≤ V / (T : ℝ)) →
        Q ≤ M / Real.sqrt T →
        A / (8 * (n : ℝ) * M) / Real.sqrt T ≤ s ∧
          s ≤ (256 * (n : ℝ) ^ 2 * M / (sigma ^ 2 * g ^ 2)) /
            Real.sqrt T := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsqrtTop : Filter.Tendsto (fun k : ℕ => Real.sqrt (k : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinvSqrt : Filter.Tendsto
      (fun k : ℕ => (Real.sqrt (k : ℝ))⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hsqrtTop
  let Kcap : ℝ := 2 * (n : ℝ) * M / sigma ^ 2
  have hcapTendsto : Filter.Tendsto
      (fun k : ℕ => Kcap / Real.sqrt (k : ℝ)) Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hinvSqrt.const_mul Kcap
  have heventCap : ∀ᶠ k : ℕ in Filter.atTop,
      Kcap / Real.sqrt (k : ℝ) < sResp ^ 2 :=
    (tendsto_order.1 hcapTendsto).2 _ (sq_pos_of_pos hsResp)
  have heventRootOne : ∀ᶠ k : ℕ in Filter.atTop,
      4 * M / A ≤ Real.sqrt (k : ℝ) :=
    (Filter.tendsto_atTop.1 hsqrtTop) _
  have heventRootTwo : ∀ᶠ k : ℕ in Filter.atTop,
      2 * A * Csig / M ≤ Real.sqrt (k : ℝ) :=
    (Filter.tendsto_atTop.1 hsqrtTop) _
  have heventTwo : ∀ᶠ k : ℕ in Filter.atTop, 2 ≤ k :=
    Filter.eventually_atTop.2 ⟨2, fun _ hk => hk⟩
  obtain ⟨T53, hT53⟩ := Filter.eventually_atTop.1
    (heventCap.and (heventRootOne.and (heventRootTwo.and heventTwo)))
  refine ⟨T53, ?_⟩
  intro T hT53large hTpos s D V Q hs hD hV hcost hNewest hSignal hVariance hLow
  have hconditions := hT53 T hT53large
  have hcapOnset : Kcap / Real.sqrt (T : ℝ) ≤ sResp ^ 2 :=
    hconditions.1.le
  have hrootOne : 4 * M / A ≤ Real.sqrt (T : ℝ) := hconditions.2.1
  have hrootTwo : 2 * A * Csig / M ≤ Real.sqrt (T : ℝ) :=
    hconditions.2.2.1
  have hTtwo : 2 ≤ T := hconditions.2.2.2
  have ht : (0 : ℝ) < T := Nat.cast_pos.mpr hTpos
  have hsqrt : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.2 ht
  have hsqrtSq : (Real.sqrt (T : ℝ)) ^ 2 = (T : ℝ) :=
    Real.sq_sqrt ht.le
  have hTsub : (((T - 1 : ℕ) : ℝ)) = (T : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ T)]
    norm_num
  have hhalf : (T : ℝ) / 2 ≤ ((T - 1 : ℕ) : ℝ) := by
    rw [hTsub]
    have hTtwoR : (2 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hTtwo
    linarith
  have hnoiseCost : sigma ^ 2 * V ≤ (T : ℝ) * Q := by
    rw [hcost]
    exact le_add_of_nonneg_left (mul_nonneg (mul_nonneg (by positivity) hA.le) hD)
  have hscaledLow : (T : ℝ) * Q ≤ M * Real.sqrt (T : ℝ) := by
    calc
      (T : ℝ) * Q ≤ (T : ℝ) * (M / Real.sqrt (T : ℝ)) :=
        mul_le_mul_of_nonneg_left hLow ht.le
      _ = M * Real.sqrt (T : ℝ) := by
        field_simp [hsqrt.ne']
        nlinarith [hsqrtSq]
  have hnewestMul : ((T - 1 : ℕ) : ℝ) * s ^ 2 ≤ (n : ℝ) * V :=
    by simpa [mul_comm] using (div_le_iff₀ hnR).mp hNewest
  have hhalfNewest : (T : ℝ) / 2 * s ^ 2 ≤ (n : ℝ) * V :=
    (mul_le_mul_of_nonneg_right hhalf (sq_nonneg s)).trans hnewestMul
  have hnoiseNewest :
      sigma ^ 2 * ((T : ℝ) / 2 * s ^ 2) ≤
        (n : ℝ) * (M * Real.sqrt (T : ℝ)) := by
    calc
      sigma ^ 2 * ((T : ℝ) / 2 * s ^ 2) ≤
          sigma ^ 2 * ((n : ℝ) * V) :=
        mul_le_mul_of_nonneg_left hhalfNewest (sq_nonneg sigma)
      _ = (n : ℝ) * (sigma ^ 2 * V) := by ring
      _ ≤ (n : ℝ) * ((T : ℝ) * Q) :=
        mul_le_mul_of_nonneg_left hnoiseCost hnR.le
      _ ≤ (n : ℝ) * (M * Real.sqrt (T : ℝ)) :=
        mul_le_mul_of_nonneg_left hscaledLow hnR.le
  have hsSqBound : s ^ 2 ≤ Kcap / Real.sqrt (T : ℝ) := by
    have hcancel : sigma ^ 2 * s ^ 2 * Real.sqrt (T : ℝ) / 2 ≤
        (n : ℝ) * M := by
      apply le_of_mul_le_mul_right ?_ hsqrt
      calc
        (sigma ^ 2 * s ^ 2 * Real.sqrt (T : ℝ) / 2) *
            Real.sqrt (T : ℝ) =
            sigma ^ 2 * ((T : ℝ) / 2 * s ^ 2) := by
          calc
            _ = sigma ^ 2 * s ^ 2 * (Real.sqrt (T : ℝ)) ^ 2 / 2 := by ring
            _ = _ := by rw [hsqrtSq]; ring
        _ ≤ (n : ℝ) * (M * Real.sqrt (T : ℝ)) := hnoiseNewest
        _ = ((n : ℝ) * M) * Real.sqrt (T : ℝ) := by ring
    rw [le_div_iff₀ hsqrt, le_div_iff₀ (sq_pos_of_pos hsigma)]
    nlinarith
  have hsCap : s ≤ sResp := by
    have hsSqResp : s ^ 2 ≤ sResp ^ 2 := hsSqBound.trans hcapOnset
    nlinarith [sq_nonneg (s - sResp)]
  have hsignalCost : 2 * A * D ≤ (T : ℝ) * Q := by
    rw [hcost]
    exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg sigma) hV)
  have hminBound :
      A * min (T : ℝ) ((4 * (n : ℝ) * s)⁻¹) ≤
        2 * M * Real.sqrt (T : ℝ) := by
    have hSignalUse := hSignal hsCap
    have hresidual : 2 * A * Csig ≤ M * Real.sqrt (T : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hrootTwo hM.le
      field_simp [hM.ne'] at hmul
      nlinarith
    nlinarith
  let x : ℝ := (4 * (n : ℝ) * s)⁻¹
  have hx : 0 < x := by dsimp [x]; positivity
  have hxT : x ≤ (T : ℝ) := by
    by_contra hnot
    have hTlt : (T : ℝ) < x := lt_of_not_ge hnot
    have hminEq : min (T : ℝ) x = (T : ℝ) := min_eq_left hTlt.le
    have hrootMul : 4 * M ≤ A * Real.sqrt (T : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hrootOne hA.le
      field_simp [hA.ne'] at hmul
      nlinarith
    dsimp [x] at hTlt hminEq
    rw [hminEq] at hminBound
    nlinarith [hsqrtSq]
  have hxBound : x ≤ 2 * M * Real.sqrt (T : ℝ) / A := by
    have hminEq : min (T : ℝ) x = x := min_eq_right hxT
    dsimp [x] at hminEq ⊢
    rw [hminEq] at hminBound
    exact (le_div_iff₀ hA).2 (by simpa [mul_comm] using hminBound)
  have hsLower : A / (8 * (n : ℝ) * M) / Real.sqrt (T : ℝ) ≤ s := by
    have hden : 0 < 4 * (n : ℝ) * s := by positivity
    have hcrossRaw := mul_le_mul_of_nonneg_right hxBound hden.le
    have hcross : 1 ≤ (2 * M * Real.sqrt (T : ℝ) / A) *
        (4 * (n : ℝ) * s) := by
      calc
        1 = x * (4 * (n : ℝ) * s) := by
          dsimp [x]
          field_simp [hden.ne']
        _ ≤ _ := hcrossRaw
    rw [div_le_iff₀ hsqrt, div_le_iff₀ (by positivity : 0 < 8 * (n : ℝ) * M)]
    have hcrossA := mul_le_mul_of_nonneg_left hcross hA.le
    field_simp [hA.ne'] at hcrossA
    nlinarith
  have h2m : 2 * Nat.floor ((4 * (n : ℝ) * s)⁻¹) ≤ T := by
    have hfloorX : ((Nat.floor x : ℕ) : ℝ) ≤ x := Nat.floor_le hx.le
    have hfloorBound : ((Nat.floor x : ℕ) : ℝ) ≤
        2 * M * Real.sqrt (T : ℝ) / A := hfloorX.trans hxBound
    have hrootMul : 4 * M ≤ A * Real.sqrt (T : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hrootOne hA.le
      field_simp [hA.ne'] at hmul
      nlinarith
    have hfloorTwice : 2 * ((Nat.floor x : ℕ) : ℝ) ≤
        4 * M * Real.sqrt (T : ℝ) / A := by
      apply (le_div_iff₀ hA).2
      have hfloorA := mul_le_mul_of_nonneg_left hfloorBound hA.le
      field_simp [hA.ne'] at hfloorA
      nlinarith
    have hrootSquare : 4 * M * Real.sqrt (T : ℝ) / A ≤
        (Real.sqrt (T : ℝ)) ^ 2 := by
      apply (div_le_iff₀ hA).2
      have hmul := mul_le_mul_of_nonneg_right hrootMul hsqrt.le
      nlinarith
    have hreal : ((2 * Nat.floor x : ℕ) : ℝ) ≤ (T : ℝ) := by
      norm_num
      rw [← hsqrtSq]
      exact hfloorTwice.trans hrootSquare
    have hnat : 2 * Nat.floor x ≤ T := by exact_mod_cast hreal
    simpa [x] using hnat
  have hvarianceUse := hVariance hsCap h2m
  have hvarianceScaled :
      g ^ 2 * s * (T : ℝ) ≤ 256 * (n : ℝ) ^ 2 * V := by
    have h := (le_div_iff₀ ht).mp hvarianceUse
    have hdenVar : 0 < 256 * (n : ℝ) ^ 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left h hdenVar.le
    calc
      g ^ 2 * s * (T : ℝ) =
          (256 * (n : ℝ) ^ 2) *
            (g ^ 2 * s / (256 * (n : ℝ) ^ 2) * (T : ℝ)) := by
        field_simp [hdenVar.ne']
      _ ≤ (256 * (n : ℝ) ^ 2) * V := hmul
  have hupperCore :
      sigma ^ 2 * g ^ 2 * s * Real.sqrt (T : ℝ) ≤
        256 * (n : ℝ) ^ 2 * M := by
    have hmul := mul_le_mul_of_nonneg_left hvarianceScaled (sq_nonneg sigma)
    have hnoiseUpper : sigma ^ 2 * V ≤ M * Real.sqrt (T : ℝ) :=
      hnoiseCost.trans hscaledLow
    have hmulNoise := mul_le_mul_of_nonneg_left hnoiseUpper
      (by positivity : 0 ≤ 256 * (n : ℝ) ^ 2)
    apply le_of_mul_le_mul_right ?_ hsqrt
    calc
      (sigma ^ 2 * g ^ 2 * s * Real.sqrt (T : ℝ)) *
          Real.sqrt (T : ℝ) =
          sigma ^ 2 * (g ^ 2 * s * (T : ℝ)) := by
        calc
          _ = sigma ^ 2 * g ^ 2 * s * (Real.sqrt (T : ℝ)) ^ 2 := by ring
          _ = _ := by rw [hsqrtSq]; ring
      _ ≤ sigma ^ 2 * (256 * (n : ℝ) ^ 2 * V) := hmul
      _ = 256 * (n : ℝ) ^ 2 * (sigma ^ 2 * V) := by ring
      _ ≤ 256 * (n : ℝ) ^ 2 * (M * Real.sqrt (T : ℝ)) := hmulNoise
      _ = (256 * (n : ℝ) ^ 2 * M) * Real.sqrt (T : ℝ) := by ring
  refine ⟨hsLower, ?_⟩
  rw [le_div_iff₀ hsqrt,
    le_div_iff₀ (mul_pos (sq_pos_of_pos hsigma) (sq_pos_of_pos hg))]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hupperCore

/-- Literal minimax risk. Book `#/algorithm_spec/parameters/0/math`:
“`R_T=\inf_{\alpha>0}\sup_{I\in C_H}T^{-1}\sum_{t<T}{\mathbb E}\|\nabla f(\bar x_t)\|^2`”.
`ENNReal` retains the source's possible infinite value. -/
def minimaxRisk (C : Set (FiniteInstance n)) (T : PositiveHorizon) : ENNReal :=
  ⨅ α : {a : ℝ // 0 < a},
    ⨆ I : C, ENNReal.ofReal (FiniteInstance.cost I.1 α.1 T)

set_option maxHeartbeats 4000000 in
/-- Equation (56), including the paper's non-exchanged quantifier order:
for every horizon and every positive stepsize there is a (possibly
`T,α`-dependent) hard instance in the same fixed class. -/
theorem actual_quadratic_response_all_stepsizes
    (N : NetworkSetup n) (L Δ σ : ℝ)
    (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 < σ) :
    ∃ Tminus : ℕ, ∀ H : ℝ, 0 ≤ H →
      ∀ T : PositiveHorizon, Tminus ≤ T.1 → ∀ α : ℝ, 0 < α →
      ∃ I ∈ fixedInstanceClass N L Δ σ H,
        ENNReal.ofReal (comparator N L Δ σ T / 6400) ≤
          ENNReal.ofReal (FiniteInstance.cost I α T) := by
  obtain ⟨sLoad, hsLoad, hsLoadCap, hStorageUniform⟩ :=
    storage_instance_lower_bound_uniform_in_H N L Δ σ hL hΔ hσ
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr N.hn
  have hg : 0 < gainFloor N :=
    (uniform_mixing_and_influence N).2.2.2.2.2.2.2.1
  have hA : 0 < ADelta L Δ := by unfold ADelta; positivity
  let M₀ : ℝ :=
    (ADelta L Δ + σ ^ 2 * influenceRowBound N ^ 2 / 2) / gainFloor N
  have hM₀ : 0 < M₀ := by
    dsimp [M₀]
    apply div_pos
    · exact add_pos_of_pos_of_nonneg
        (by unfold ADelta; positivity) (by positivity)
    · exact hg
  let cQ : ℝ := ADelta L Δ / (8 * (n : ℝ) * M₀)
  let CQ : ℝ := 256 * (n : ℝ) ^ 2 * M₀ /
    (σ ^ 2 * gainFloor N ^ 2)
  have hcQ : 0 < cQ := by
    dsimp [cQ]
    exact div_pos hA (by positivity)
  have hCQ : 0 < CQ := by dsimp [CQ]; positivity
  rcases actual_quadratic_equation48_deterministic_signal N with
    ⟨Ca, sSignal, hCa, hsSignal, hSignal⟩
  rcases actual_quadratic_equation48_impulse_response N with
    ⟨Cr, sPulse, hCr, hsPulse, hPulse⟩
  let Csig : ℝ := (8 * Ca + 4 * Ca ^ 2) / gainFloor N
  have hCsig : 0 ≤ Csig := by dsimp [Csig]; positivity
  let Cvar : ℝ :=
    (n : ℝ) *
      (8 * influenceRowBound N * Cr / gainFloor N +
        2 * influenceRowBound N * Cr /
          (1 - loadingTransverseRate N) +
        8 * Cr ^ 2 / gainFloor N +
        2 * Cr ^ 2 / (1 - loadingTransverseRate N ^ 2))
  have hrf0 : 0 ≤ loadingTransverseRate N := by
    unfold loadingTransverseRate loadingFastRate loadingTriangularRate
    linarith [mixingRate_nonneg N]
  have hrf1 : loadingTransverseRate N < 1 := by
    unfold loadingTransverseRate loadingFastRate loadingTriangularRate
    linarith [mixingRate_lt_one N]
  have hrowBound : 0 ≤ influenceRowBound N := by
    have hnorm : 0 ≤ nodeL2Norm (influenceRow N 0) := by
      unfold nodeL2Norm
      exact Real.sqrt_nonneg _
    exact hnorm.trans (influenceRow_nodeL2_le N 0)
  have hCvar : 0 ≤ Cvar := by
    have hden1 : 0 ≤ 1 - loadingTransverseRate N := sub_nonneg.mpr hrf1.le
    have hden2 : 0 ≤ 1 - loadingTransverseRate N ^ 2 := by
      nlinarith [mul_nonneg hrf0 (sub_nonneg.mpr hrf1.le)]
    dsimp [Cvar]
    positivity
  let sVariance : ℝ :=
    min sPulse (min 1
      (min (1 / (8 * (n : ℝ)))
        (min (1 / (4 * (n : ℝ) *
          ((influenceEnergyWindowThreshold N + 1 : ℕ) : ℝ)))
          (gainFloor N ^ 2 /
            (256 * (n : ℝ) ^ 2 * (Cvar + 1))))))
  have hsVariance : 0 < sVariance := by
    have hthreshold :
        0 < ((influenceEnergyWindowThreshold N + 1 : ℕ) : ℝ) := by positivity
    dsimp [sVariance]
    positivity
  let sResp : ℝ :=
    min sSignal (min sVariance (min 1 (1 / (4 * (n : ℝ)))))
  have hsResp : 0 < sResp := by dsimp [sResp]; positivity
  obtain ⟨T₅₃, hT₅₃⟩ := actual_quadratic_equation53_low_cost_localization
    n (ADelta L Δ) M₀ σ (gainFloor N) Csig sResp N.hn hA hM₀ hσ hg
      hCsig hsResp
  obtain ⟨T₅₄, hT₅₄⟩ := equation54_uniform_storage_loss_and_onset
    N L Δ σ cQ CQ sLoad hL hΔ hcQ hCQ hsLoad
  let Tminus : ℕ := max ((64 * n) ^ 2) (max T₅₃ T₅₄)
  refine ⟨Tminus, ?_⟩
  intro H hH T hT alpha halpha
  have hlarge : (64 * n : ℕ) ^ 2 ≤ T.1 :=
    (le_max_left _ _).trans hT
  have hT53 : T₅₃ ≤ T.1 :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hT)
  have hT54 : T₅₄ ≤ T.1 :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hT)
  have hComparatorTrial :
      comparator N L Δ σ T ≤ M₀ / Real.sqrt T.1 := by
    simpa [M₀] using
      actual_quadratic_comparator_trial_upper N L Δ σ hL hΔ T hlarge
  have hStorageForH := hStorageUniform H hH
  rcases actual_quadratic_iid_instance_spec N L Δ σ H hL hΔ hσ hH with
    ⟨atom, nu, phi, S, hfinite, hnu, hatomInt, hcenter, hsecond,
      heven, hphi, hprob, hnoise, hx0, hI, hheterogeneity, hgrad,
      hrow, hcol, hrec⟩
  let I : FiniteInstance n :=
    { d := 1
      Ω := SOptLib.miniBatchSamplePath n (Fin 3)
      setup := S
      finite_layer := hfinite }
  have h49 := actual_quadratic_equation49_iid_cost_identity
    N L Δ σ atom nu phi S hfinite hL hΔ hnu hatomInt hcenter hsecond
    hphi hprob hnoise hx0 hgrad alpha (hrec alpha) T
  dsimp only at h49
  let s := dimensionlessStepsize L alpha
  let signal := actualQuadraticScalarTrajectory N s 1 (fun _ _ => 0)
  let pulse := fun (j : ℕ) (i : Fin n) =>
    actualQuadraticScalarTrajectory N s 0
      (fun r q => if r = j then if q = i then 1 else 0 else 0)
  have hs : 0 < s := by
    dsimp [s, dimensionlessStepsize]
    positivity
  have hStorageForLocalized
      (hsLower : cQ / Real.sqrt T.1 ≤ s)
      (hsUpper : s ≤ CQ / Real.sqrt T.1) :
      ∃ J ∈ fixedInstanceClass N L Δ σ H,
        ENNReal.ofReal (comparator N L Δ σ T / 6400) ≤
          ENNReal.ofReal (FiniteInstance.cost J alpha T) := by
    have h54 := hT₅₄ T hT54 s hs hsLower hsUpper
    let sAdm : AdmissibleDimensionlessStepsize n :=
      ⟨s, hs, h54.1.trans hsLoadCap⟩
    rcases hStorageForH T sAdm h54.1 with
      ⟨J, hJ, _hzero, _h42, _h44, h45⟩
    refine ⟨J, hJ, ?_⟩
    have hsdiv : s / L = alpha := by
      dsimp [s, dimensionlessStepsize]
      field_simp [ne_of_gt hL]
    have hcost := h45 h54.2
    have hcomp : comparator N L Δ σ T ≤ comparatorAt N L Δ σ T sAdm := by
      have hrange_bdd : BddBelow
          (Set.range fun u : AdmissibleDimensionlessStepsize n =>
            comparatorAt N L Δ σ T u) := by
        refine ⟨0, ?_⟩
        rintro y ⟨u, rfl⟩
        have henergy_nonneg : 0 ≤ windowInfluenceSum N T.1 u.1 := by
          unfold windowInfluenceSum influenceEnergy
          exact Finset.sum_nonneg fun j _ =>
            mul_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)
              (Nat.cast_nonneg _)
        unfold comparatorAt comparatorNumerator
        exact div_nonneg
          (add_nonneg (mul_nonneg hA.le (Nat.cast_nonneg _))
            (mul_nonneg (by positivity) henergy_nonneg))
          (mul_pos (by norm_num [epsilon])
            (Nat.cast_pos.mpr T.2)).le
      unfold comparator
      exact csInf_le hrange_bdd ⟨sAdm, rfl⟩
    have hcompdiv : comparator N L Δ σ T / 6400 ≤
        comparatorAt N L Δ σ T sAdm / 6400 :=
      div_le_div_of_nonneg_right hcomp (by norm_num)
    exact (ENNReal.ofReal_le_ofReal hcompdiv).trans (by
      simpa [sAdm, hsdiv] using hcost)
  have hNewestVariance52 :
      (((T.1 - 1 : ℕ) : ℝ) * s ^ 2) / (n : ℝ) ≤
        ∑ t ∈ Finset.range T.1, ∑ j ∈ Finset.range t, ∑ i,
          ((n : ℝ)⁻¹ * ∑ q, (pulse j i t).1 q) ^ 2 := by
    simpa [pulse] using actual_quadratic_newest_noise_variance_lower N s T
  have hsignal48 (hsCap : s ≤ sSignal) (m : ℕ) :
      |(n : ℝ)⁻¹ * ∑ q, (signal m).1 q -
          (∏ r ∈ Finset.Ico 0 m, (1 - s * gain N r))| ≤
        Ca * s * (1 - gainFloor N * s / 4) ^ m := by
    apply hSignal s hs hsCap
      (fun t => (signal t).1) (fun t => (signal t).2) m
    · rfl
    · rfl
    · intro t
      exact actualQuadraticScalarTrajectory_tracker_sum_eq_zero
        N s 1 (fun _ _ => 0) t
    · intro t
      dsimp [signal]
      rw [actualQuadraticScalarTrajectory]
      funext q
      simp [Matrix.mulVec]
    · intro t
      dsimp [signal]
      rw [actualQuadraticScalarTrajectory]
      funext q
      simp [Matrix.mulVec]
  have hpulse48 (hsCap : s ≤ sPulse) (j : ℕ) (i : Fin n) (m : ℕ) :
      |(n : ℝ)⁻¹ * ∑ q, (pulse j i (j + 1 + m)).1 q +
          s * influenceRow N j i *
            (∏ r ∈ Finset.Ico (j + 1) (j + 1 + m),
              (1 - s * gain N r))| ≤
        Cr * (s ^ 2 * (1 - gainFloor N * s / 4) ^ m +
          s * loadingTransverseRate N ^ m) := by
    apply hPulse s hs hsCap j i
      (fun t => (pulse j i t).1) (fun t => (pulse j i t).2)
    · intro t
      exact actualQuadraticScalarTrajectory_tracker_sum_eq_zero
        N s 0 (fun r q => if r = j then if q = i then 1 else 0 else 0) t
    · exact congrArg Prod.fst
        (actualQuadraticScalarTrajectory_zero_before_pulse N s j i j le_rfl)
    · exact congrArg Prod.snd
        (actualQuadraticScalarTrajectory_zero_before_pulse N s j i j le_rfl)
    · intro t
      rfl
    · intro t
      rfl
  have hD50 (hsCap : s ≤ sSignal) (hsOne : s ≤ 1)
      (hsn : s * (n : ℝ) ≤ 1 / 4) :
      |∑ t ∈ Finset.range T.1,
          ((n : ℝ)⁻¹ * ∑ q, (signal t).1 q) ^ 2 -
        ∑ t ∈ Finset.range T.1,
          (∏ r ∈ Finset.Ico 0 t, (1 - s * gain N r)) ^ 2| ≤
        (8 * Ca + 4 * Ca ^ 2) / gainFloor N := by
    have hgf : 0 < gainFloor N :=
      (uniform_mixing_and_influence N).2.2.2.2.2.2.2.1
    have hgf_le_n : gainFloor N ≤ (n : ℝ) :=
      (gainFloor_le_gain N 0).trans (gain_le_n N 0)
    have hgfs : gainFloor N * s ≤ 1 := by
      have hscaled := mul_le_mul_of_nonneg_right hgf_le_n hs.le
      nlinarith
    apply actual_quadratic_signal_energy_comparison
      (gainFloor N) Ca s T.1
      (fun t => (n : ℝ)⁻¹ * ∑ q, (signal t).1 q)
      (fun t => ∏ r ∈ Finset.Ico 0 t, (1 - s * gain N r))
      hgf hCa hs hsOne hgfs
    · intro t ht
      simpa using
        (actual_quadratic_gain_product_abs_le_slow_rate N s 0 t hs hsn)
    · intro t ht
      exact hsignal48 hsCap t
  have hV50 (hsCap : s ≤ sPulse) (hsOne : s ≤ 1)
      (hsn : s * (n : ℝ) ≤ 1 / 4) :
      |∑ t ∈ Finset.range T.1, ∑ j ∈ Finset.range t, ∑ i,
          ((n : ℝ)⁻¹ * ∑ q, (pulse j i t).1 q) ^ 2 -
        s ^ 2 * ∑ t ∈ Finset.range T.1, ∑ j ∈ Finset.range t, ∑ i,
          (influenceRow N j i *
            (∏ r ∈ Finset.Ico (j + 1) t, (1 - s * gain N r))) ^ 2| ≤
        ((n : ℝ) *
          (8 * influenceRowBound N * Cr / gainFloor N +
            2 * influenceRowBound N * Cr /
              (1 - loadingTransverseRate N) +
            8 * Cr ^ 2 / gainFloor N +
            2 * Cr ^ 2 / (1 - loadingTransverseRate N ^ 2))) *
          s ^ 2 * (T.1 : ℝ) := by
    let Kvar : ℝ :=
      8 * influenceRowBound N * Cr / gainFloor N +
        2 * influenceRowBound N * Cr / (1 - loadingTransverseRate N) +
        8 * Cr ^ 2 / gainFloor N +
        2 * Cr ^ 2 / (1 - loadingTransverseRate N ^ 2)
    have hgf : 0 < gainFloor N :=
      (uniform_mixing_and_influence N).2.2.2.2.2.2.2.1
    have hgf_le_n : gainFloor N ≤ (n : ℝ) :=
      (gainFloor_le_gain N 0).trans (gain_le_n N 0)
    have hgfs : gainFloor N * s ≤ 1 := by
      have hscaled := mul_le_mul_of_nonneg_right hgf_le_n hs.le
      nlinarith
    have hB : 0 ≤ influenceRowBound N := by
      have hnorm : 0 ≤ nodeL2Norm (influenceRow N 0) := by
        unfold nodeL2Norm
        exact Real.sqrt_nonneg _
      exact hnorm.trans (influenceRow_nodeL2_le N 0)
    have hrf0 : 0 ≤ loadingTransverseRate N := by
      unfold loadingTransverseRate loadingFastRate loadingTriangularRate
      linarith [mixingRate_nonneg N]
    have hrf1 : loadingTransverseRate N < 1 := by
      unfold loadingTransverseRate loadingFastRate loadingTriangularRate
      linarith [mixingRate_lt_one N]
    have hKvar : 0 ≤ Kvar := by
      dsimp [Kvar]
      have hden1 : 0 ≤ 1 - loadingTransverseRate N :=
        sub_nonneg.mpr hrf1.le
      have hden2 : 0 ≤ 1 - loadingTransverseRate N ^ 2 := by
        have hsq : loadingTransverseRate N ^ 2 ≤ 1 := by
          nlinarith [mul_nonneg hrf0 (sub_nonneg.mpr hrf1.le)]
        linarith
      exact add_nonneg
        (add_nonneg
          (add_nonneg (div_nonneg (by positivity) hgf.le)
            (div_nonneg (by positivity) hden1))
          (div_nonneg (by positivity) hgf.le))
        (div_nonneg (by positivity) hden2)
    have hper (j : ℕ) (hj : j ∈ Finset.range T.1) (i : Fin n) :
        |∑ m ∈ Finset.range (T.1 - 1 - j),
            ((n : ℝ)⁻¹ * ∑ q, (pulse j i (j + 1 + m)).1 q) ^ 2 -
          ∑ m ∈ Finset.range (T.1 - 1 - j),
            (-s * influenceRow N j i *
              (∏ r ∈ Finset.Ico (j + 1) (j + 1 + m),
                (1 - s * gain N r))) ^ 2| ≤ Kvar * s ^ 2 := by
      have hrow : |influenceRow N j i| ≤ influenceRowBound N :=
        (abs_le_nodeL2Norm (influenceRow N j) i).trans
          (influenceRow_nodeL2_le N j)
      apply two_rate_impulse_square_energy_error_le
        (gainFloor N) (influenceRowBound N) Cr s
        (loadingTransverseRate N) (T.1 - 1 - j)
        (fun m => (n : ℝ)⁻¹ * ∑ q, (pulse j i (j + 1 + m)).1 q)
        (fun m => ∏ r ∈ Finset.Ico (j + 1) (j + 1 + m),
          (1 - s * gain N r))
        (influenceRow N j i) hgf hB hCr hs hsOne hgfs hrf0 hrf1 hrow
      · intro m hm
        simpa using
          (actual_quadratic_gain_product_abs_le_slow_rate
            N s (j + 1) m hs hsn)
      · intro m hm
        simpa [sub_neg_eq_add] using hpulse48 hsCap j i m
    let A : ℕ → Fin n → ℕ → ℝ := fun j i m =>
      ((n : ℝ)⁻¹ * ∑ q, (pulse j i (j + 1 + m)).1 q) ^ 2
    let B : ℕ → Fin n → ℕ → ℝ := fun j i m =>
      (-s * influenceRow N j i *
        (∏ r ∈ Finset.Ico (j + 1) (j + 1 + m),
          (1 - s * gain N r))) ^ 2
    have htri := triangular_square_energy_difference_le
      T.1 A B (Kvar * s ^ 2) (mul_nonneg hKvar (sq_nonneg s))
      (fun j hj i => by simpa [A, B] using hper j hj i)
    have hAtri :
        (∑ t ∈ Finset.range T.1, ∑ j ∈ Finset.range t, ∑ i,
          A j i (t - 1 - j)) =
        ∑ t ∈ Finset.range T.1, ∑ j ∈ Finset.range t, ∑ i,
          ((n : ℝ)⁻¹ * ∑ q, (pulse j i t).1 q) ^ 2 := by
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro j hj
      have hjt : j < t := Finset.mem_range.mp hj
      have heq : j + 1 + (t - 1 - j) = t := by omega
      simp only [A, heq]
    have hBtri :
        (∑ t ∈ Finset.range T.1, ∑ j ∈ Finset.range t, ∑ i,
          B j i (t - 1 - j)) =
        ∑ t ∈ Finset.range T.1, ∑ j ∈ Finset.range t, ∑ i,
          (-s * influenceRow N j i *
            (∏ r ∈ Finset.Ico (j + 1) t, (1 - s * gain N r))) ^ 2 := by
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro j hj
      have hjt : j < t := Finset.mem_range.mp hj
      have heq : j + 1 + (t - 1 - j) = t := by omega
      simp only [B, heq]
    rw [hAtri, hBtri] at htri
    have hfactor :
        (∑ t ∈ Finset.range T.1, ∑ j ∈ Finset.range t, ∑ i,
          (-s * influenceRow N j i *
            (∏ r ∈ Finset.Ico (j + 1) t, (1 - s * gain N r))) ^ 2) =
        s ^ 2 * ∑ t ∈ Finset.range T.1, ∑ j ∈ Finset.range t, ∑ i,
          (influenceRow N j i *
            (∏ r ∈ Finset.Ico (j + 1) t, (1 - s * gain N r))) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hfactor] at htri
    dsimp [Kvar] at htri ⊢
    simp only [Fintype.card_fin] at htri
    convert htri using 1 <;> ring
  have hSignal51 (hsCap : s ≤ sSignal) (hsOne : s ≤ 1)
      (hsn : s * (n : ℝ) ≤ 1 / 4)
      (k : ℕ) (hkT : k ≤ T.1)
      (hkbudget : ((k - 1 : ℕ) : ℝ) * (s * (n : ℝ)) ≤ 1 / 4) :
      ∑ t ∈ Finset.range T.1,
          ((n : ℝ)⁻¹ * ∑ q, (signal t).1 q) ^ 2 ≥
        (k : ℝ) / 2 - (8 * Ca + 4 * Ca ^ 2) / gainFloor N := by
    have hcomp := hD50 hsCap hsOne hsn
    have hterm (t : ℕ) (ht : t ∈ Finset.range k) :
        (1 / 2 : ℝ) ≤
          (∏ r ∈ Finset.Ico 0 t, (1 - s * gain N r)) ^ 2 := by
      have htkNat : t ≤ k - 1 := Nat.le_sub_one_of_lt (Finset.mem_range.mp ht)
      have htk : (t : ℝ) ≤ (k - 1 : ℕ) := by exact_mod_cast htkNat
      have htb : (t : ℝ) * (s * (n : ℝ)) ≤ 1 / 4 :=
        (mul_le_mul_of_nonneg_right htk (by positivity)).trans hkbudget
      have hlin := actual_quadratic_gain_product_ge_linear N s 0 t hs
        (htb.trans (by norm_num))
      simp only [zero_add] at hlin
      have hthree : (3 / 4 : ℝ) ≤
          ∏ r ∈ Finset.Ico 0 t, (1 - s * gain N r) := by
        nlinarith
      nlinarith [sq_nonneg
        ((∏ r ∈ Finset.Ico 0 t, (1 - s * gain N r)) - 3 / 4)]
    have hproxy : (k : ℝ) / 2 ≤
        ∑ t ∈ Finset.range T.1,
          (∏ r ∈ Finset.Ico 0 t, (1 - s * gain N r)) ^ 2 := by
      calc
        (k : ℝ) / 2 = ∑ _t ∈ Finset.range k, (1 / 2 : ℝ) := by
          simp [Finset.sum_const, nsmul_eq_mul]
          ring
        _ ≤ ∑ t ∈ Finset.range k,
            (∏ r ∈ Finset.Ico 0 t, (1 - s * gain N r)) ^ 2 :=
          Finset.sum_le_sum hterm
        _ ≤ ∑ t ∈ Finset.range T.1,
            (∏ r ∈ Finset.Ico 0 t, (1 - s * gain N r)) ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hkT)
          intro t htT htk
          exact sq_nonneg _
    have hlow := (abs_le.mp hcomp).1
    nlinarith
  have hSignal51Min (hsCap : s ≤ sSignal) (hsOne : s ≤ 1)
      (hsn : s * (n : ℝ) ≤ 1 / 4) :
      ∑ t ∈ Finset.range T.1,
          ((n : ℝ)⁻¹ * ∑ q, (signal t).1 q) ^ 2 ≥
        (1 / 2 : ℝ) * min (T.1 : ℝ)
            ((4 * (n : ℝ) * s)⁻¹) -
          (8 * Ca + 4 * Ca ^ 2) / gainFloor N := by
    let x : ℝ := (4 * (n : ℝ) * s)⁻¹
    let m : ℕ := Nat.floor x
    let k : ℕ := min T.1 (m + 1)
    have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr N.hn
    have hx : 0 < x := by dsimp [x]; positivity
    have hmle : (m : ℝ) ≤ x := by
      dsimp [m]
      exact Nat.floor_le hx.le
    have hxlt : x < (m : ℝ) + 1 := by
      dsimp [m]
      simpa using Nat.lt_floor_add_one x
    have hkT : k ≤ T.1 := by dsimp [k]; exact min_le_left _ _
    have hkpred : k - 1 ≤ m := by
      dsimp [k]
      omega
    have hkbudget : ((k - 1 : ℕ) : ℝ) * (s * (n : ℝ)) ≤ 1 / 4 := by
      have hkcast : ((k - 1 : ℕ) : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast hkpred
      have hknx : ((k - 1 : ℕ) : ℝ) ≤ x := hkcast.trans hmle
      have hmul := mul_le_mul_of_nonneg_right hknx (by positivity : 0 ≤ s * (n : ℝ))
      have hxmul : x * (s * (n : ℝ)) = 1 / 4 := by
        dsimp [x]
        field_simp [hs.ne', hn.ne']
      rwa [hxmul] at hmul
    have hkreal : min (T.1 : ℝ) x ≤ (k : ℝ) := by
      by_cases hcase : T.1 ≤ m + 1
      · have hk : k = T.1 := by dsimp [k]; exact Nat.min_eq_left hcase
        rw [hk]
        exact min_le_left _ _
      · have hmT : m + 1 ≤ T.1 := Nat.le_of_not_ge hcase
        have hk : k = m + 1 := by dsimp [k]; exact Nat.min_eq_right hmT
        rw [hk]
        have hxcast : x ≤ ((m + 1 : ℕ) : ℝ) := by
          norm_num
          exact hxlt.le
        exact (min_le_right (T.1 : ℝ) x).trans hxcast
    have hbase := hSignal51 hsCap hsOne hsn k hkT hkbudget
    dsimp [x] at hkreal
    nlinarith
  have hVariance51 (hsCap : s ≤ sVariance)
      (h2m : 2 * Nat.floor ((4 * (n : ℝ) * s)⁻¹) ≤ T.1) :
      gainFloor N ^ 2 * s / (256 * (n : ℝ) ^ 2) ≤
        (∑ t ∈ Finset.range T.1, ∑ j ∈ Finset.range t, ∑ i,
          ((n : ℝ)⁻¹ * ∑ q, (pulse j i t).1 q) ^ 2) / (T.1 : ℝ) := by
    let m : ℕ := Nat.floor ((4 * (n : ℝ) * s)⁻¹)
    have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr N.hn
    have hsPulseCap : s ≤ sPulse := hsCap.trans (min_le_left _ _)
    have hsRest : s ≤ min 1
        (min (1 / (8 * (n : ℝ)))
          (min (1 / (4 * (n : ℝ) *
            ((influenceEnergyWindowThreshold N + 1 : ℕ) : ℝ)))
            (gainFloor N ^ 2 /
              (256 * (n : ℝ) ^ 2 * (Cvar + 1))))) :=
      hsCap.trans (min_le_right _ _)
    have hsOne : s ≤ 1 := hsRest.trans (min_le_left _ _)
    have hsRest2 : s ≤ min (1 / (8 * (n : ℝ)))
        (min (1 / (4 * (n : ℝ) *
          ((influenceEnergyWindowThreshold N + 1 : ℕ) : ℝ)))
          (gainFloor N ^ 2 /
            (256 * (n : ℝ) ^ 2 * (Cvar + 1)))) :=
      hsRest.trans (min_le_right _ _)
    have hsEight : s ≤ 1 / (8 * (n : ℝ)) :=
      hsRest2.trans (min_le_left _ _)
    have hsRest3 : s ≤ min (1 / (4 * (n : ℝ) *
        ((influenceEnergyWindowThreshold N + 1 : ℕ) : ℝ)))
        (gainFloor N ^ 2 /
          (256 * (n : ℝ) ^ 2 * (Cvar + 1))) :=
      hsRest2.trans (min_le_right _ _)
    have hsThreshold : s ≤ 1 / (4 * (n : ℝ) *
        ((influenceEnergyWindowThreshold N + 1 : ℕ) : ℝ)) :=
      hsRest3.trans (min_le_left _ _)
    have hsAbsorb : s ≤ gainFloor N ^ 2 /
        (256 * (n : ℝ) ^ 2 * (Cvar + 1)) :=
      hsRest3.trans (min_le_right _ _)
    have hsnEight : s * (n : ℝ) ≤ 1 / 8 := by
      have h := (le_div_iff₀ (by positivity : 0 < 8 * (n : ℝ))).mp hsEight
      nlinarith
    have hsnQuarter : s * (n : ℝ) ≤ 1 / 4 := hsnEight.trans (by norm_num)
    let x : ℝ := (4 * (n : ℝ) * s)⁻¹
    have hx : 0 < x := by dsimp [x]; positivity
    have hmle : (m : ℝ) ≤ x := by
      dsimp [m, x]
      exact Nat.floor_le hx.le
    have hmBudget : (m : ℝ) * (s * (n : ℝ)) ≤ 1 / 4 := by
      have hmul := mul_le_mul_of_nonneg_right hmle (by positivity : 0 ≤ s * (n : ℝ))
      have hxmul : x * (s * (n : ℝ)) = 1 / 4 := by
        dsimp [x]
        field_simp [hs.ne', hn.ne']
      rwa [hxmul] at hmul
    have hthresholdReal :
        (influenceEnergyWindowThreshold N : ℝ) ≤ x := by
      have hthresholdPos :
          0 < ((influenceEnergyWindowThreshold N + 1 : ℕ) : ℝ) := by positivity
      have hcap := (le_div_iff₀
        (mul_pos (by positivity : 0 < 4 * (n : ℝ)) hthresholdPos)).mp
          hsThreshold
      dsimp [x]
      rw [inv_eq_one_div, le_div_iff₀ (by positivity : 0 < 4 * (n : ℝ) * s)]
      calc
        (influenceEnergyWindowThreshold N : ℝ) *
            (4 * (n : ℝ) * s) ≤
          ((influenceEnergyWindowThreshold N + 1 : ℕ) : ℝ) *
            (4 * (n : ℝ) * s) := by
          apply mul_le_mul_of_nonneg_right
          · norm_num
          · positivity
        _ = s * (4 * (n : ℝ) *
            ((influenceEnergyWindowThreshold N + 1 : ℕ) : ℝ)) := by ring
        _ ≤ 1 := hcap
    have hmThreshold : influenceEnergyWindowThreshold N ≤ m := by
      dsimp [m]
      exact Nat.le_floor hthresholdReal
    have hxTwo : 2 ≤ x := by
      dsimp [x]
      rw [inv_eq_one_div, le_div_iff₀ (by positivity : 0 < 4 * (n : ℝ) * s)]
      nlinarith
    have hxlt : x < (m : ℝ) + 1 := by
      dsimp [m, x]
      simpa using Nat.lt_floor_add_one ((4 * (n : ℝ) * s)⁻¹)
    have hmLower : (8 * (n : ℝ) * s)⁻¹ ≤ (m : ℝ) := by
      have hinv : (8 * (n : ℝ) * s)⁻¹ = x / 2 := by
        dsimp [x]
        field_simp [hs.ne', hn.ne']
        ring
      rw [hinv]
      nlinarith
    have hCvarAbsorb :
        Cvar * s ≤ gainFloor N ^ 2 / (256 * (n : ℝ) ^ 2) := by
      have hsAbsorb' : s ≤
          (gainFloor N ^ 2 / (256 * (n : ℝ) ^ 2)) / (Cvar + 1) := by
        calc
          s ≤ gainFloor N ^ 2 /
              (256 * (n : ℝ) ^ 2 * (Cvar + 1)) := hsAbsorb
          _ = (gainFloor N ^ 2 / (256 * (n : ℝ) ^ 2)) /
              (Cvar + 1) := (div_div _ _ _).symm
      have hcap := (le_div_iff₀ (by positivity : 0 < Cvar + 1)).mp hsAbsorb'
      have hmul : Cvar * s ≤ (Cvar + 1) * s := by nlinarith
      calc
        Cvar * s ≤ (Cvar + 1) * s := hmul
        _ = s * (Cvar + 1) := by ring
        _ ≤ gainFloor N ^ 2 / (256 * (n : ℝ) ^ 2) := by
          simpa [div_eq_mul_inv, mul_assoc] using hcap
    have hcompare := hV50 hsPulseCap hsOne hsnQuarter
    apply actual_quadratic_equation51_variance_floor
      N s T.1 m
      (∑ t ∈ Finset.range T.1, ∑ j ∈ Finset.range t, ∑ i,
        ((n : ℝ)⁻¹ * ∑ q, (pulse j i t).1 q) ^ 2)
      Cvar hs hmThreshold hmLower hmBudget
    · simpa [m] using h2m
    · exact hCvarAbsorb
    · simpa [Cvar] using hcompare
  have hDact : 0 ≤ ∑ t ∈ Finset.range T.1,
      ((n : ℝ)⁻¹ * ∑ q, (signal t).1 q) ^ 2 :=
    Finset.sum_nonneg fun t _ => sq_nonneg _
  have hVact : 0 ≤ ∑ t ∈ Finset.range T.1,
      ∑ j ∈ Finset.range t, ∑ i,
        ((n : ℝ)⁻¹ * ∑ q, (pulse j i t).1 q) ^ 2 :=
    Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun i _ => sq_nonneg _
  by_cases hhigh : M₀ / Real.sqrt T.1 < FiniteInstance.cost I alpha T
  · refine ⟨I, ?_, ENNReal.ofReal_le_ofReal ?_⟩
    · simpa [I] using hI
    · have hcompDiv : comparator N L Δ σ T / 6400 ≤
          M₀ / Real.sqrt T.1 := by
        by_cases hcompNonneg : 0 ≤ comparator N L Δ σ T
        · calc
            comparator N L Δ σ T / 6400 ≤ comparator N L Δ σ T := by
              nlinarith
            _ ≤ M₀ / Real.sqrt T.1 := hComparatorTrial
        · have hcompNeg : comparator N L Δ σ T ≤ 0 := le_of_not_ge hcompNonneg
          exact (div_nonpos_of_nonpos_of_nonneg hcompNeg (by norm_num)).trans
            (by positivity)
      exact hcompDiv.trans hhigh.le
  · have hLow : FiniteInstance.cost I alpha T ≤ M₀ / Real.sqrt T.1 :=
      le_of_not_gt hhigh
    have hlocalized := hT₅₃ T.1 hT53 T.2 s
      (∑ t ∈ Finset.range T.1,
        ((n : ℝ)⁻¹ * ∑ q, (signal t).1 q) ^ 2)
      (∑ t ∈ Finset.range T.1, ∑ j ∈ Finset.range t, ∑ i,
        ((n : ℝ)⁻¹ * ∑ q, (pulse j i t).1 q) ^ 2)
      (FiniteInstance.cost I alpha T) hs hDact hVact h49 hNewestVariance52
      (by
        intro hsRespCap
        have hsSignalCap : s ≤ sSignal :=
          hsRespCap.trans (min_le_left _ _)
        have hsTail : s ≤ min sVariance (min 1 (1 / (4 * (n : ℝ)))) :=
          hsRespCap.trans (min_le_right _ _)
        have hsOne : s ≤ 1 :=
          (hsTail.trans (min_le_right _ _)).trans (min_le_left _ _)
        have hsQuarter : s ≤ 1 / (4 * (n : ℝ)) :=
          (hsTail.trans (min_le_right _ _)).trans (min_le_right _ _)
        have hsn : s * (n : ℝ) ≤ 1 / 4 := by
          have h := (le_div_iff₀ (by positivity : 0 < 4 * (n : ℝ))).mp
            hsQuarter
          nlinarith
        simpa [Csig] using hSignal51Min hsSignalCap hsOne hsn)
      (by
        intro hsRespCap h2m
        have hsVarianceCap : s ≤ sVariance :=
          (hsRespCap.trans (min_le_right _ _)).trans (min_le_left _ _)
        exact hVariance51 hsVarianceCap h2m)
      hLow
    have hsLower : cQ / Real.sqrt T.1 ≤ s := by
      simpa [cQ] using hlocalized.1
    have hsUpper : s ≤ CQ / Real.sqrt T.1 := by
      simpa [CQ] using hlocalized.2
    exact hStorageForLocalized hsLower hsUpper

/-! ## Effective nodes, periodic specialization, and source endpoints -/

def centralizedStochasticScale (n : ℕ) (L Δ σ : ℝ) (T : PositiveHorizon) : ℝ :=
  σ * Real.sqrt (ADelta L Δ / (n * T.1))

/-- `M_0^{cost}`. Book `#/key_lemmas/2/proof/16/math`:
“`M_0^{cost}={A_\Delta+\sigma^2B_*^2/2\over g}`”. -/
def comparatorLocalizationBaseCost
    (N : NetworkSetup n) (L Δ σ : ℝ) : ℝ :=
  (ADelta L Δ + σ ^ 2 * influenceRowBound N ^ 2 / 2) / gainFloor N

/-- `M_B=M_0^{cost}+A_Δ`. Book `#/key_lemmas/2/proof/16/math`:
“`M_B=M_0^{cost}+A_\Delta`”. -/
def comparatorLocalizationBudget
    (N : NetworkSetup n) (L Δ σ : ℝ) : ℝ :=
  comparatorLocalizationBaseCost N L Δ σ + ADelta L Δ

/-- The lower competing-step coefficient `c_B=A_Δ/(2nM_B)`. Book
`#/key_lemmas/2/proof/18/math`:
“`c_B/\sqrt T\le s\le C_B/\sqrt T`”, with `c_B` defined in
`#/key_lemmas/2/proof/16/math` as “`c_B={A_\Delta\over2nM_B}`”. -/
def comparatorStepLowerConstant
    (N : NetworkSetup n) (L Δ σ : ℝ) : ℝ :=
  ADelta L Δ / (2 * n * comparatorLocalizationBudget N L Δ σ)

/-- The upper competing-step coefficient `C_B=32n²M_B/(σ²g²)`. Book
`#/key_lemmas/2/proof/18/math`:
“`c_B/\sqrt T\le s\le C_B/\sqrt T`”, with `C_B` defined in
`#/key_lemmas/2/proof/16/math` as
“`C_B={32n^2M_B\over\sigma^2g^2}`”. -/
def comparatorStepUpperConstant
    (N : NetworkSetup n) (L Δ σ : ℝ) : ℝ :=
  32 * n ^ 2 * comparatorLocalizationBudget N L Δ σ /
    (σ ^ 2 * gainFloor N ^ 2)

/-- A candidate is “competing” exactly in the sense used in (19): its
explicit comparator is at most `M_B/√T`. -/
def IsCompetingStepsize (N : NetworkSetup n) (L Δ σ : ℝ)
    (T : PositiveHorizon) (s : AdmissibleDimensionlessStepsize n) : Prop :=
  comparatorAt N L Δ σ T s ≤
    comparatorLocalizationBudget N L Δ σ / Real.sqrt T.1

/-- Future-window lengths can only decrease when the starting time moves
forward.  This is the monotonicity used in the summation-by-parts step of
equation (59). -/
theorem windowLength_antitone
    (N : NetworkSetup n) (T : ℕ) (s : ℝ) {t u : ℕ} (htu : t ≤ u) :
    windowLength N T u s ≤ windowLength N T t s := by
  classical
  unfold windowLength
  by_cases huT : u < T
  · have htT : t < T := lt_of_le_of_lt htu huT
    rw [if_pos huT, if_pos htT]
    apply Finset.sup_le
    intro P hP
    have hP' : P ∈ Finset.Icc t T := by
      simp only [Finset.mem_Icc] at hP ⊢
      exact ⟨htu.trans hP.1, hP.2⟩
    exact Finset.le_sup (s := Finset.Icc t T)
      (f := fun P =>
        (Finset.Icc (P + 1) T).sup fun Q =>
          if s * ∑ r ∈ Finset.Ico P Q, gain N r ≤ epsilon
          then Q - P else 0) hP'
  · rw [if_neg huT]
    exact Nat.zero_le _

/-- Any admissible future window has length at most its scalar budget divided
by the uniform gain floor. -/
theorem windowLength_le_budget_div_gainFloor
    (N : NetworkSetup n) (T t : ℕ) (s : ℝ) (hs : 0 < s) :
    (windowLength N T t s : ℝ) ≤ epsilon / (s * gainFloor N) := by
  exact actual_quadratic_windowLength_le_budget_div_gainFloor N T t s hs

/-- Abel summation for nonincreasing nonnegative weights: a discrete
coboundary has no more than two initial weights' worth of endpoint error. -/
theorem abs_sum_range_weight_mul_coboundary_le
    (w c : ℕ → ℝ) (T : ℕ) (C : ℝ)
    (hw_nonneg : ∀ t, 0 ≤ w t)
    (hw_anti : ∀ t, w (t + 1) ≤ w t)
    (hC : 0 ≤ C) (hc : ∀ t, |c t| ≤ C) :
    |∑ t ∈ Finset.range T, w t * (c t - c (t + 1))| ≤
      2 * w 0 * C := by
  classical
  by_cases hT : T = 0
  · subst T
    simp only [Finset.range_zero, Finset.sum_empty, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (hw_nonneg 0)) hC
  · obtain ⟨U, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hT
    have habel_all : ∀ V : ℕ,
        (∑ t ∈ Finset.range (V + 1), w t * (c t - c (t + 1))) =
          w 0 * c 0 - w V * c (V + 1) +
            ∑ t ∈ Finset.range V, (w (t + 1) - w t) * c (t + 1) := by
      intro V
      induction V with
      | zero => simp; ring
      | succ V ih =>
          conv_lhs => rw [Finset.sum_range_succ, ih]
          conv_rhs => rw [Finset.sum_range_succ]
          ring
    have habel := habel_all U
    rw [habel]
    have hvariation :
        ∑ t ∈ Finset.range U, |(w (t + 1) - w t) * c (t + 1)| ≤
          (w 0 - w U) * C := by
      calc
        ∑ t ∈ Finset.range U, |(w (t + 1) - w t) * c (t + 1)| =
            ∑ t ∈ Finset.range U,
              (w t - w (t + 1)) * |c (t + 1)| := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr (hw_anti t)),
            neg_sub]
        _ ≤ ∑ t ∈ Finset.range U, (w t - w (t + 1)) * C := by
          apply Finset.sum_le_sum
          intro t ht
          exact mul_le_mul_of_nonneg_left (hc (t + 1))
            (sub_nonneg.mpr (hw_anti t))
        _ = (w 0 - w U) * C := by
          rw [← Finset.sum_mul]
          congr 1
          simpa using (Finset.sum_range_sub' w U)
    calc
      |w 0 * c 0 - w U * c (U + 1) +
          ∑ t ∈ Finset.range U, (w (t + 1) - w t) * c (t + 1)| ≤
          |w 0 * c 0| + |w U * c (U + 1)| +
            ∑ t ∈ Finset.range U,
              |(w (t + 1) - w t) * c (t + 1)| := by
        calc
          |w 0 * c 0 - w U * c (U + 1) +
              ∑ t ∈ Finset.range U,
                (w (t + 1) - w t) * c (t + 1)| ≤
              |w 0 * c 0 - w U * c (U + 1)| +
                |∑ t ∈ Finset.range U,
                  (w (t + 1) - w t) * c (t + 1)| := abs_add_le _ _
          _ ≤ (|w 0 * c 0| + |w U * c (U + 1)|) +
                ∑ t ∈ Finset.range U,
                  |(w (t + 1) - w t) * c (t + 1)| := by
            exact add_le_add (abs_sub _ _) (Finset.abs_sum_le_sum_abs _ _)
          _ = |w 0 * c 0| + |w U * c (U + 1)| +
                ∑ t ∈ Finset.range U,
                  |(w (t + 1) - w t) * c (t + 1)| := by ring
      _ ≤ w 0 * C + w U * C + (w 0 - w U) * C := by
        exact add_le_add
          (add_le_add
            (by simpa [abs_mul, abs_of_nonneg (hw_nonneg 0)] using
              mul_le_mul_of_nonneg_left (hc 0) (hw_nonneg 0))
            (by simpa [abs_mul, abs_of_nonneg (hw_nonneg U)] using
              mul_le_mul_of_nonneg_left (hc (U + 1)) (hw_nonneg U)))
          hvariation
      _ = 2 * w 0 * C := by ring

/-- Source steps 5--7 of equation (59): once the backward-window double count
supplies `K*T/4` gain-weighted mass, the coboundary identity and weighted
Cauchy--Schwarz give the exact `64*n*W₀` energy denominator. -/
theorem weighted_window_influence_lower_of_gain_mass
    (N : NetworkSetup n) (T : PositiveHorizon)
    (s : AdmissibleDimensionlessStepsize n)
    (hmass :
      (epsilon / s.1) * T.1 / 4 ≤
        ∑ t ∈ Finset.range T.1,
          gain N t * windowLength N T.1 (t + 1) s.1)
    (hcob :
      16 * Real.sqrt n * coboundaryBound N / gainFloor N ≤ T.1) :
    0 < windowLength N T.1 0 s.1 ∧
      (epsilon / s.1) ^ 2 * T.1 /
          (64 * n * windowLength N T.1 0 s.1) ≤
        windowInfluenceSum N T.1 s.1 := by
  classical
  let W : ℕ → ℝ := fun t => windowLength N T.1 t s.1
  let K : ℝ := epsilon / s.1
  let g : ℝ := gainFloor N
  let R : ℝ := coboundaryBound N
  let b : ℕ → Fin n → ℝ := influenceRow N
  let r : ℕ → Fin n → ℝ := coboundaryRow N
  let c : ℕ → ℝ := fun t => ∑ i, r t i
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr N.hn
  have hT : (0 : ℝ) < T.1 := Nat.cast_pos.mpr T.2
  have hs : 0 < s.1 := s.2.1
  have hK : 0 < K := by
    dsimp [K]
    exact div_pos (by norm_num [epsilon]) hs
  have hmu : 0 < mixingMinorization N := by
    unfold mixingMinorization
    split_ifs
    · exact pow_pos ((lt_min_iff).2 ⟨N.ha, by norm_num⟩) _
    · norm_num
  have hg : 0 < g := by
    dsimp [g]
    exact (mul_pos hn hmu).trans_le
      (gainFloor_ge_n_mul_mixingMinorization N)
  have hD : 0 < influenceOperatorBound N := by
    unfold influenceOperatorBound columnMixingConstant
    exact div_pos
      (div_pos (Real.sqrt_pos.2 hn) (blockContraction_pos N))
      (sub_pos.mpr (mixingRate_lt_one N))
  have hR_nonneg : 0 ≤ R := by
    dsimp [R, coboundaryBound]
    exact mul_nonneg (by positivity) hD.le
  have hW_nonneg : ∀ t, 0 ≤ W t := fun t => by
    dsimp [W]
    exact Nat.cast_nonneg _
  have hW_anti : ∀ t, W (t + 1) ≤ W t := by
    intro t
    dsimp [W]
    exact_mod_cast windowLength_antitone N T.1 s.1 (Nat.le_succ t)
  have hW_le_zero : ∀ t, W t ≤ W 0 := by
    intro t
    dsimp [W]
    exact_mod_cast windowLength_antitone N T.1 s.1 (Nat.zero_le t)
  have hW0_upper : W 0 ≤ K / g := by
    dsimp [W, K, g]
    calc
      (windowLength N T.1 0 s.1 : ℝ) ≤
          epsilon / (s.1 * gainFloor N) :=
        windowLength_le_budget_div_gainFloor N T.1 0 s.1 hs
      _ = (epsilon / s.1) / gainFloor N := by ring
  have hmass_pos :
      0 < ∑ t ∈ Finset.range T.1, gain N t * W (t + 1) := by
    have hleft : 0 < K * T.1 / 4 := div_pos (mul_pos hK hT) (by norm_num)
    exact hleft.trans_le (by simpa [K, W] using hmass)
  have hW0 : 0 < W 0 := by
    by_contra hnot
    have hzero : W 0 = 0 := le_antisymm (le_of_not_gt hnot) (hW_nonneg 0)
    have hall : ∀ t, W (t + 1) = 0 := by
      intro t
      exact le_antisymm ((hW_le_zero (t + 1)).trans_eq hzero)
        (hW_nonneg (t + 1))
    have hsumzero :
        (∑ t ∈ Finset.range T.1, gain N t * W (t + 1)) = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      rw [hall t, mul_zero]
    rw [hsumzero] at hmass_pos
    exact lt_irrefl 0 hmass_pos
  have hnorm (y : Fin n → ℝ) :
      ‖WithLp.toLp 2 y‖ = nodeL2Norm y := by
    simp [PiLp.norm_eq_of_L2, nodeL2Norm, Real.norm_eq_abs, sq_abs]
  have hc_bound : ∀ t, |c t| ≤ Real.sqrt n * R := by
    intro t
    calc
      |c t| = |∑ i, r t i| := rfl
      _ ≤ ∑ i, |r t i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ Real.sqrt n * nodeL2Norm (r t) := by
        simpa [Real.norm_eq_abs, hnorm] using
          (sum_norm_le_sqrt_card_mul_dependentProductL2Seminorm (r t))
      _ ≤ Real.sqrt n * R :=
        mul_le_mul_of_nonneg_left (by
          dsimp [r, R]
          exact coboundaryRow_nodeL2_le N t) (Real.sqrt_nonneg _)
  have hcob_error :
      |∑ t ∈ Finset.range T.1,
          W (t + 1) * (c t - c (t + 1))| ≤
        2 * W 0 * (Real.sqrt n * R) := by
    have hraw := abs_sum_range_weight_mul_coboundary_le
      (fun t => W (t + 1)) c T.1 (Real.sqrt n * R)
      (fun t => hW_nonneg (t + 1))
      (fun t => hW_anti (t + 1))
      (mul_nonneg (Real.sqrt_nonneg _) hR_nonneg) hc_bound
    exact hraw.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hW_anti 0) (by norm_num))
        (mul_nonneg (Real.sqrt_nonneg _) hR_nonneg))
  have hb_sum (t : ℕ) :
      ∑ i, b t i = gain N t + c t - c (t + 1) := by
    simp_rw [b, influenceRow_coboundary_identity]
    dsimp [c, r]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn
    have hconst :
        (∑ _i : Fin n, gain N t / (n : ℝ)) = gain N t := by
      calc
        (∑ _i : Fin n, gain N t / (n : ℝ)) =
            (n : ℝ) * (gain N t / (n : ℝ)) := by simp
        _ = gain N t := by field_simp [hn_ne]
    rw [hconst]
  have hweighted_identity :
      (∑ t ∈ Finset.range T.1, W (t + 1) * ∑ i, b t i) =
        (∑ t ∈ Finset.range T.1, gain N t * W (t + 1)) +
          ∑ t ∈ Finset.range T.1,
            W (t + 1) * (c t - c (t + 1)) := by
    simp_rw [hb_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  have herror_absorb :
      2 * W 0 * (Real.sqrt n * R) ≤ K * T.1 / 8 := by
    have hcob' : 16 * Real.sqrt n * R ≤ (T.1 : ℝ) * g := by
      dsimp [R, g] at hcob ⊢
      exact (div_le_iff₀
        ((mul_pos hn hmu).trans_le
          (gainFloor_ge_n_mul_mixingMinorization N))).mp hcob
    have hWg : W 0 * g ≤ K := (le_div_iff₀ hg).mp hW0_upper
    have hstep₁ :
        16 * Real.sqrt n * R * W 0 ≤ (T.1 : ℝ) * g * W 0 :=
      mul_le_mul_of_nonneg_right hcob' (hW_nonneg 0)
    have hstep₂ : (T.1 : ℝ) * g * W 0 ≤ T.1 * K := by
      nlinarith [mul_le_mul_of_nonneg_left hWg hT.le]
    nlinarith [hstep₁, hstep₂]
  have hretained :
      K * T.1 / 8 ≤
        ∑ t ∈ Finset.range T.1, W (t + 1) * ∑ i, b t i := by
    rw [hweighted_identity]
    have hneg := neg_abs_le
      (∑ t ∈ Finset.range T.1, W (t + 1) * (c t - c (t + 1)))
    have hmass' :
        K * T.1 / 4 ≤
          ∑ t ∈ Finset.range T.1, gain N t * W (t + 1) := by
      simpa [K, W] using hmass
    nlinarith [hcob_error, herror_absorb]
  have hweighted_energy :
      (∑ t ∈ Finset.range T.1, ∑ i, (W (t + 1) * b t i) ^ 2) ≤
        W 0 * windowInfluenceSum N T.1 s.1 := by
    unfold windowInfluenceSum
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t ht
    unfold influenceEnergy
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hWt := hW_le_zero (t + 1)
    calc
      (W (t + 1) * b t i) ^ 2 =
          W (t + 1) * W (t + 1) * (b t i) ^ 2 := by ring
      _ ≤ W 0 * W (t + 1) * (b t i) ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hWt (hW_nonneg (t + 1)))
          (sq_nonneg _)
      _ = W 0 * ((b t i) ^ 2 * W (t + 1)) := by ring
  have hcs :
      (∑ t ∈ Finset.range T.1, W (t + 1) * ∑ i, b t i) ^ 2 ≤
        ((n : ℝ) * T.1) *
          (W 0 * windowInfluenceSum N T.1 s.1) := by
    have hraw := sq_sum_le_card_mul_sum_sq
      (s := (Finset.range T.1).product (Finset.univ : Finset (Fin n)))
      (f := fun p : ℕ × Fin n => W (p.1 + 1) * b p.1 p.2)
    have hraw' :
        (∑ t ∈ Finset.range T.1, ∑ i, W (t + 1) * b t i) ^ 2 ≤
          ((n : ℝ) * T.1) *
            (∑ t ∈ Finset.range T.1, ∑ i,
              (W (t + 1) * b t i) ^ 2) := by
      simpa [Finset.sum_product, Nat.cast_mul, mul_comm, mul_left_comm,
        mul_assoc] using hraw
    calc
      (∑ t ∈ Finset.range T.1, W (t + 1) * ∑ i, b t i) ^ 2 =
          (∑ t ∈ Finset.range T.1, ∑ i, W (t + 1) * b t i) ^ 2 := by
        congr 1
        apply Finset.sum_congr rfl
        intro t ht
        rw [Finset.mul_sum]
      _ ≤ ((n : ℝ) * T.1) *
          (∑ t ∈ Finset.range T.1, ∑ i,
            (W (t + 1) * b t i) ^ 2) := hraw'
      _ ≤ ((n : ℝ) * T.1) *
          (W 0 * windowInfluenceSum N T.1 s.1) :=
        mul_le_mul_of_nonneg_left hweighted_energy
          (mul_nonneg hn.le hT.le)
  have hlower_nonneg : 0 ≤ K * T.1 / 8 :=
    (div_pos (mul_pos hK hT) (by norm_num)).le
  have htotal_nonneg :
      0 ≤ ∑ t ∈ Finset.range T.1, W (t + 1) * ∑ i, b t i :=
    hlower_nonneg.trans hretained
  have hsquare :
      (K * T.1 / 8) ^ 2 ≤
        (∑ t ∈ Finset.range T.1, W (t + 1) * ∑ i, b t i) ^ 2 :=
    (sq_le_sq₀ hlower_nonneg htotal_nonneg).2 hretained
  have hmain := hsquare.trans hcs
  constructor
  · change 0 < (windowLength N T.1 0 s.1 : ℝ) at hW0
    exact_mod_cast hW0
  · dsimp [K, W] at hmain ⊢
    apply (div_le_iff₀ (mul_pos (mul_pos (by norm_num) hn) hW0)).2
    have hcancel :
        (T.1 : ℝ) * ((epsilon / s.1) ^ 2 * T.1) ≤
          (T.1 : ℝ) *
            (64 * n * W 0 * windowInfluenceSum N T.1 s.1) := by
      dsimp [W]
      nlinarith [hmain]
    have hcanceled := le_of_mul_le_mul_left hcancel hT
    convert hcanceled using 1 <;> ring

/-- For every sufficiently late endpoint, the longest admissible backward
window retains more than half of the gain budget after its two boundary
increments are removed.  This is the endpoint-local part of the source's
double-counting argument for equation (59). -/
theorem exists_backward_window_start
    (N : NetworkSetup n) (s : AdmissibleDimensionlessStepsize n) (u : ℕ)
    (hu : Nat.ceil ((epsilon / s.1) / gainFloor N) ≤ u) :
    ∃ P : ℕ, P ≤ u ∧
      s.1 * ∑ t ∈ Finset.Ico P (u + 1), gain N t ≤ epsilon ∧
      (epsilon / s.1) / 2 < ∑ t ∈ Finset.Ico P u, gain N t := by
  classical
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr N.hn
  have hs : 0 < s.1 := s.2.1
  have hmu : 0 < mixingMinorization N := by
    unfold mixingMinorization
    split_ifs
    · exact pow_pos ((lt_min_iff).2 ⟨N.ha, by norm_num⟩) _
    · norm_num
  have hg : 0 < gainFloor N :=
    (mul_pos hn hmu).trans_le
      (gainFloor_ge_n_mul_mixingMinorization N)
  have hK4n : 4 * (n : ℝ) ≤ epsilon / s.1 := by
    apply (le_div_iff₀ hs).2
    calc
      4 * (n : ℝ) * s.1 ≤ 4 * n * (1 / (64 * n)) := by
        exact mul_le_mul_of_nonneg_left s.2.2
          (mul_nonneg (by norm_num) hn.le)
      _ = epsilon := by
        unfold epsilon
        field_simp
        ring
  let A : Finset ℕ :=
    (Finset.Icc 0 u).filter fun P =>
      s.1 * ∑ t ∈ Finset.Ico P (u + 1), gain N t ≤ epsilon
  have huA : u ∈ A := by
    simp only [A, Finset.mem_filter, Finset.mem_Icc, le_refl, and_self,
      Nat.zero_le, true_and]
    have hone :
        (∑ t ∈ Finset.Ico u (u + 1), gain N t) = gain N u := by simp
    rw [hone]
    calc
      s.1 * gain N u ≤ s.1 * n :=
        mul_le_mul_of_nonneg_left (gain_le_n N u) hs.le
      _ ≤ (1 / (64 * (n : ℝ))) * n :=
        mul_le_mul_of_nonneg_right s.2.2 hn.le
      _ ≤ epsilon := by
        unfold epsilon
        field_simp
        norm_num
  let P : ℕ := A.min' ⟨u, huA⟩
  have hPmem : P ∈ A := by
    dsimp [P]
    exact A.min'_mem ⟨u, huA⟩
  have hPbounds : 0 ≤ P ∧ P ≤ u := by
    have hPA :
        (0 ≤ P ∧ P ≤ u) ∧
          s.1 * ∑ t ∈ Finset.Ico P (u + 1), gain N t ≤ epsilon := by
      simpa only [A, Finset.mem_filter, Finset.mem_Icc] using hPmem
    exact hPA.1
  have hPbudget :
      s.1 * ∑ t ∈ Finset.Ico P (u + 1), gain N t ≤ epsilon := by
    have hPA :
        (0 ≤ P ∧ P ≤ u) ∧
          s.1 * ∑ t ∈ Finset.Ico P (u + 1), gain N t ≤ epsilon := by
      simpa only [A, Finset.mem_filter, Finset.mem_Icc] using hPmem
    exact hPA.2
  have hKg_le_u : (epsilon / s.1) / gainFloor N ≤ (u : ℝ) := by
    calc
      (epsilon / s.1) / gainFloor N ≤
          Nat.ceil ((epsilon / s.1) / gainFloor N) := Nat.le_ceil _
      _ ≤ u := by exact_mod_cast hu
  have hpref_gain :
      epsilon / s.1 < ∑ t ∈ Finset.Ico 0 (u + 1), gain N t := by
    have hfloor_sum :
        ((u + 1 : ℕ) : ℝ) * gainFloor N ≤
          ∑ t ∈ Finset.Ico 0 (u + 1), gain N t := by
      calc
        ((u + 1 : ℕ) : ℝ) * gainFloor N =
            ∑ t ∈ Finset.Ico 0 (u + 1), gainFloor N := by simp
        _ ≤ ∑ t ∈ Finset.Ico 0 (u + 1), gain N t := by
          exact Finset.sum_le_sum fun t _ => gainFloor_le_gain N t
    have hKg : epsilon / s.1 ≤ (u : ℝ) * gainFloor N :=
      (div_le_iff₀ hg).mp hKg_le_u
    calc
      epsilon / s.1 ≤ (u : ℝ) * gainFloor N := hKg
      _ < ((u + 1 : ℕ) : ℝ) * gainFloor N := by
        push_cast
        nlinarith
      _ ≤ ∑ t ∈ Finset.Ico 0 (u + 1), gain N t := hfloor_sum
  have hPpos : 0 < P := by
    by_contra hnot
    have hPzero : P = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hPzero] at hPbudget
    have hdiv :
        (∑ t ∈ Finset.Ico 0 (u + 1), gain N t) ≤ epsilon / s.1 :=
      (le_div_iff₀ hs).2 (by simpa [mul_comm] using hPbudget)
    exact (not_lt_of_ge hdiv) hpref_gain
  have hprev_not_mem : P - 1 ∉ A := by
    intro hprev
    have hmin : P ≤ P - 1 := by
      dsimp [P]
      exact A.min'_le (P - 1) hprev
    omega
  have hprev_bounds : P - 1 ∈ Finset.Icc 0 u := by
    simp only [Finset.mem_Icc, Nat.zero_le, true_and]
    omega
  have hprev_over :
      epsilon < s.1 * ∑ t ∈ Finset.Ico (P - 1) (u + 1), gain N t := by
    have hnotbudget :
        ¬ s.1 * ∑ t ∈ Finset.Ico (P - 1) (u + 1), gain N t ≤ epsilon := by
      intro hbudget
      apply hprev_not_mem
      exact Finset.mem_filter.2 ⟨hprev_bounds, hbudget⟩
    exact lt_of_not_ge hnotbudget
  have hprev_gain :
      epsilon / s.1 <
        ∑ t ∈ Finset.Ico (P - 1) (u + 1), gain N t := by
    exact (div_lt_iff₀ hs).2 (by simpa [mul_comm] using hprev_over)
  have hsplit_left :
      (∑ t ∈ Finset.Ico (P - 1) (u + 1), gain N t) =
        gain N (P - 1) + ∑ t ∈ Finset.Ico P (u + 1), gain N t := by
    have hprevP : P - 1 ≤ P := Nat.sub_le _ _
    have hPu : P ≤ u + 1 := hPbounds.2.trans (Nat.le_succ u)
    rw [← Finset.sum_Ico_consecutive (gain N) hprevP hPu]
    have hsucc : P - 1 + 1 = P := Nat.sub_add_cancel hPpos
    rw [← hsucc]
    simp
  have hsplit_right :
      (∑ t ∈ Finset.Ico P (u + 1), gain N t) =
        (∑ t ∈ Finset.Ico P u, gain N t) + gain N u := by
    exact Finset.sum_Ico_succ_top hPbounds.2 (gain N)
  refine ⟨P, hPbounds.2, hPbudget, ?_⟩
  rw [hsplit_left, hsplit_right] at hprev_gain
  have hleft := gain_le_n N (P - 1)
  have hright := gain_le_n N u
  nlinarith

/-- A concrete admissible interval is bounded by the maximal future-window
length at every earlier starting time. -/
theorem interval_length_le_windowLength
    (N : NetworkSetup n) (T t P Q : ℕ) (s : ℝ)
    (htT : t < T) (htP : t ≤ P) (hPQ : P < Q) (hQT : Q ≤ T)
    (hbudget : s * ∑ r ∈ Finset.Ico P Q, gain N r ≤ epsilon) :
    Q - P ≤ windowLength N T t s := by
  classical
  unfold windowLength
  rw [if_pos htT]
  have hPmem : P ∈ Finset.Icc t T := by
    simp only [Finset.mem_Icc]
    exact ⟨htP, (Nat.le_of_lt hPQ).trans hQT⟩
  have hQmem : Q ∈ Finset.Icc (P + 1) T := by
    simp only [Finset.mem_Icc]
    exact ⟨hPQ, hQT⟩
  have hinner :
      Q - P ≤ (Finset.Icc (P + 1) T).sup fun Q =>
        if s * ∑ r ∈ Finset.Ico P Q, gain N r ≤ epsilon
        then Q - P else 0 := by
    have hselected :
        Q - P ≤
          (if s * ∑ r ∈ Finset.Ico P Q, gain N r ≤ epsilon
           then Q - P else 0) := by simp [hbudget]
    exact hselected.trans (Finset.le_sup
      (s := Finset.Icc (P + 1) T)
      (f := fun Q =>
        if s * ∑ r ∈ Finset.Ico P Q, gain N r ≤ epsilon
        then Q - P else 0) hQmem)
  exact hinner.trans (Finset.le_sup
    (s := Finset.Icc t T)
    (f := fun P =>
      (Finset.Icc (P + 1) T).sup fun Q =>
        if s * ∑ r ∈ Finset.Ico P Q, gain N r ≤ epsilon
        then Q - P else 0) hPmem)

/-- Source steps 3--4 of equation (59): summing the retained gain in the
endpoint-local backward windows and reversing the two finite sums gives the
`K*T/4` gain-window mass bound. -/
theorem backward_window_gain_mass_lower
    (N : NetworkSetup n) (T : PositiveHorizon)
    (s : AdmissibleDimensionlessStepsize n)
    (hhorizon :
      2 * Nat.ceil ((epsilon / s.1) / gainFloor N) + 2 ≤ T.1) :
    (epsilon / s.1) * T.1 / 4 ≤
      ∑ t ∈ Finset.range T.1,
        gain N t * windowLength N T.1 (t + 1) s.1 := by
  classical
  let K : ℝ := epsilon / s.1
  let m : ℕ := Nat.ceil (K / gainFloor N)
  let U : Finset ℕ := Finset.Ico m T.1
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr N.hn
  have hs : 0 < s.1 := s.2.1
  have hmu : 0 < mixingMinorization N := by
    unfold mixingMinorization
    split_ifs
    · exact pow_pos ((lt_min_iff).2 ⟨N.ha, by norm_num⟩) _
    · norm_num
  have hg : 0 < gainFloor N :=
    (mul_pos hn hmu).trans_le
      (gainFloor_ge_n_mul_mixingMinorization N)
  have hgain_nonneg : ∀ t, 0 ≤ gain N t := by
    intro t
    exact hg.le.trans (gainFloor_le_gain N t)
  have hmT : m < T.1 := by
    dsimp [m, K] at hhorizon ⊢
    omega
  have hex (u : ℕ) :
      ∃ P : ℕ, u ∈ U →
        P ≤ u ∧
        s.1 * ∑ t ∈ Finset.Ico P (u + 1), gain N t ≤ epsilon ∧
        K / 2 < ∑ t ∈ Finset.Ico P u, gain N t := by
    by_cases huU : u ∈ U
    · have hum : m ≤ u := (Finset.mem_Ico.1 huU).1
      obtain ⟨P, hPu, hbudget, hretained⟩ :=
        exists_backward_window_start N s u (by simpa [m, K] using hum)
      exact ⟨P, fun _ => ⟨hPu, hbudget, by simpa [K] using hretained⟩⟩
    · exact ⟨0, fun h => False.elim (huU h)⟩
  let P : ℕ → ℕ := fun u => Classical.choose (hex u)
  have hP (u : ℕ) (huU : u ∈ U) :
      P u ≤ u ∧
      s.1 * ∑ t ∈ Finset.Ico (P u) (u + 1), gain N t ≤ epsilon ∧
      K / 2 < ∑ t ∈ Finset.Ico (P u) u, gain N t := by
    exact Classical.choose_spec (hex u) huU
  have hendpoint_sum :
      (U.card : ℝ) * (K / 2) ≤
        ∑ u ∈ U, ∑ t ∈ Finset.Ico (P u) u, gain N t := by
    calc
      (U.card : ℝ) * (K / 2) = ∑ _u ∈ U, K / 2 := by simp
      _ ≤ ∑ u ∈ U, ∑ t ∈ Finset.Ico (P u) u, gain N t := by
        exact Finset.sum_le_sum fun u hu => (hP u hu).2.2.le
  have hcard : K * T.1 / 4 ≤ (U.card : ℝ) * (K / 2) := by
    have hhorizon' : 2 * m + 2 ≤ T.1 := by
      simpa [m, K] using hhorizon
    have hcard_nat : T.1 ≤ 2 * U.card := by
      simp only [U, Nat.card_Ico]
      omega
    have hcard_real : (T.1 : ℝ) ≤ 2 * (U.card : ℝ) := by
      exact_mod_cast hcard_nat
    have hK : 0 ≤ K := (div_pos (by norm_num [epsilon]) hs).le
    nlinarith
  let F : ℕ → Finset ℕ := fun t => U.filter fun u => t ∈ Finset.Ico (P u) u
  have hfiber_card (t : ℕ) :
      (F t).card ≤ windowLength N T.1 (t + 1) s.1 := by
    have hsubset :
        F t ⊆ Finset.Ico (t + 1)
          (t + 1 + windowLength N T.1 (t + 1) s.1) := by
      intro u huF
      have huU : u ∈ U := (Finset.mem_filter.1 huF).1
      have htu : t ∈ Finset.Ico (P u) u := (Finset.mem_filter.1 huF).2
      have huT : u < T.1 := (Finset.mem_Ico.1 huU).2
      have hPt : P u ≤ t := (Finset.mem_Ico.1 htu).1
      have htu_lt : t < u := (Finset.mem_Ico.1 htu).2
      have hsplit :
          (∑ r ∈ Finset.Ico (P u) (t + 1), gain N r) +
              ∑ r ∈ Finset.Ico (t + 1) (u + 1), gain N r =
            ∑ r ∈ Finset.Ico (P u) (u + 1), gain N r := by
        exact Finset.sum_Ico_consecutive (gain N)
          (hPt.trans (Nat.le_succ t)) (Nat.succ_le_succ (Nat.le_of_lt htu_lt))
      have hsubsum :
          (∑ r ∈ Finset.Ico (t + 1) (u + 1), gain N r) ≤
            ∑ r ∈ Finset.Ico (P u) (u + 1), gain N r := by
        have hprefix_nonneg :
            0 ≤ ∑ r ∈ Finset.Ico (P u) (t + 1), gain N r :=
          Finset.sum_nonneg fun r _ => hgain_nonneg r
        linarith
      have hsubbudget :
          s.1 * ∑ r ∈ Finset.Ico (t + 1) (u + 1), gain N r ≤ epsilon :=
        (mul_le_mul_of_nonneg_left hsubsum hs.le).trans (hP u huU).2.1
      have hlen :
          (u + 1) - (t + 1) ≤ windowLength N T.1 (t + 1) s.1 :=
        interval_length_le_windowLength N T.1 (t + 1) (t + 1) (u + 1) s.1
          (lt_of_le_of_lt (Nat.succ_le_of_lt htu_lt) huT)
          le_rfl (Nat.succ_lt_succ htu_lt) (Nat.succ_le_of_lt huT) hsubbudget
      have hu_lower : t + 1 ≤ u := Nat.succ_le_of_lt htu_lt
      have hu_upper : u < t + 1 + windowLength N T.1 (t + 1) s.1 := by
        have : u - t ≤ windowLength N T.1 (t + 1) s.1 := by
          simpa [Nat.add_sub_add_right] using hlen
        omega
      exact Finset.mem_Ico.2 ⟨hu_lower, hu_upper⟩
    have hcards := Finset.card_le_card hsubset
    simpa using hcards
  have hdouble :
      (∑ u ∈ U, ∑ t ∈ Finset.Ico (P u) u, gain N t) ≤
        ∑ t ∈ Finset.range T.1,
          gain N t * windowLength N T.1 (t + 1) s.1 := by
    have hreindex :
        (∑ u ∈ U, ∑ t ∈ Finset.Ico (P u) u, gain N t) =
          ∑ t ∈ Finset.range T.1,
            ∑ u ∈ U, if t ∈ Finset.Ico (P u) u then gain N t else 0 := by
      calc
        (∑ u ∈ U, ∑ t ∈ Finset.Ico (P u) u, gain N t) =
            ∑ u ∈ U, ∑ t ∈ Finset.range T.1,
              if t ∈ Finset.Ico (P u) u then gain N t else 0 := by
          apply Finset.sum_congr rfl
          intro u huU
          have huT : u < T.1 := (Finset.mem_Ico.1 huU).2
          rw [← Finset.sum_filter]
          apply Finset.sum_congr
          · apply Finset.ext
            intro q
            constructor
            · intro hq
              exact Finset.mem_filter.2
                ⟨Finset.mem_range.2 ((Finset.mem_Ico.1 hq).2.trans huT), hq⟩
            · intro hq
              exact (Finset.mem_filter.1 hq).2
          · intro t ht
            rfl
        _ = ∑ t ∈ Finset.range T.1,
            ∑ u ∈ U, if t ∈ Finset.Ico (P u) u then gain N t else 0 := by
          rw [Finset.sum_comm]
    rw [hreindex]
    apply Finset.sum_le_sum
    intro t ht
    have hfiber :
        (∑ u ∈ U, if t ∈ Finset.Ico (P u) u then gain N t else 0) =
          (F t).card * gain N t := by
      rw [← Finset.sum_filter]
      change (∑ _u ∈ F t, gain N t) = (F t).card * gain N t
      simp
    rw [hfiber]
    have hcast : ((F t).card : ℝ) ≤ windowLength N T.1 (t + 1) s.1 := by
      exact_mod_cast hfiber_card t
    nlinarith [mul_le_mul_of_nonneg_right hcast (hgain_nonneg t)]
  exact hcard.trans (hendpoint_sum.trans hdouble)

/-- Exact equation-(59) weighted-window influence lower bound. -/
theorem weighted_window_influence_lower
    (N : NetworkSetup n) (T : PositiveHorizon)
    (s : AdmissibleDimensionlessStepsize n)
    (hceil :
      2 * Nat.ceil ((epsilon / s.1) / gainFloor N) + 2 ≤ T.1)
    (hcob :
      16 * Real.sqrt n * coboundaryBound N / gainFloor N ≤ T.1) :
    0 < windowLength N T.1 0 s.1 ∧
      (epsilon / s.1) ^ 2 * T.1 /
          (64 * n * windowLength N T.1 0 s.1) ≤
        windowInfluenceSum N T.1 s.1 := by
  exact weighted_window_influence_lower_of_gain_mass N T s
    (backward_window_gain_mass_lower N T s hceil) hcob

/-- Substitution of equation (59) into the explicit comparator, with the
source's exact stochastic coefficient. -/
theorem comparator_two_term_lower_from_weighted_window
    (N : NetworkSetup n) (L Δ σ : ℝ) (T : PositiveHorizon)
    (s : AdmissibleDimensionlessStepsize n)
    (hceil :
      2 * Nat.ceil ((epsilon / s.1) / gainFloor N) + 2 ≤ T.1)
    (hcob :
      16 * Real.sqrt n * coboundaryBound N / gainFloor N ≤ T.1) :
    0 < windowLength N T.1 0 s.1 ∧
    (epsilon / s.1) ^ 2 * T.1 /
          (64 * n * windowLength N T.1 0 s.1) ≤
        windowInfluenceSum N T.1 s.1 ∧
    ADelta L Δ * windowLength N T.1 0 s.1 /
            (epsilon * T.1) +
          σ ^ 2 * epsilon /
            (128 * n * windowLength N T.1 0 s.1) ≤
        comparatorAt N L Δ σ T s := by
  have hw := weighted_window_influence_lower N T s hceil hcob
  refine ⟨hw.1, hw.2, ?_⟩
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr N.hn
  have hT : (0 : ℝ) < T.1 := Nat.cast_pos.mpr T.2
  have hs : 0 < s.1 := s.2.1
  have heps : 0 < epsilon := by norm_num [epsilon]
  have hW : (0 : ℝ) < windowLength N T.1 0 s.1 := by
    exact_mod_cast hw.1
  have hbase :
      epsilon / (128 * n * windowLength N T.1 0 s.1) ≤
        (s.1 ^ 2 / 2 * windowInfluenceSum N T.1 s.1) /
          (epsilon * T.1) := by
    have henergy := hw.2
    field_simp [ne_of_gt hn, ne_of_gt hT, ne_of_gt hs, ne_of_gt heps,
      ne_of_gt hW] at henergy ⊢
    nlinarith
  unfold comparatorAt comparatorNumerator
  rw [add_div]
  apply add_le_add le_rfl
  calc
    σ ^ 2 * epsilon /
          (128 * n * windowLength N T.1 0 s.1) ≤
        σ ^ 2 * ((s.1 ^ 2 / 2 * windowInfluenceSum N T.1 s.1) /
          (epsilon * T.1)) :=
      by
        convert mul_le_mul_of_nonneg_left hbase (sq_nonneg σ) using 1 <;> ring
    _ = ((σ ^ 2 / 2) * s.1 ^ 2 *
          windowInfluenceSum N T.1 s.1) / (epsilon * T.1) := by ring

/-- The exact AM--GM constant in equation (59). -/
theorem centralized_scale_le_two_term_window_bound
    (N : NetworkSetup n) (L Δ σ : ℝ)
    (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 < σ)
    (T : PositiveHorizon) (W : ℝ) (hW : 0 < W) :
    (1 / (4 * Real.sqrt 2)) * centralizedStochasticScale n L Δ σ T ≤
      ADelta L Δ * W / (epsilon * T.1) +
        σ ^ 2 * epsilon / (128 * n * W) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr N.hn
  have hT : (0 : ℝ) < T.1 := Nat.cast_pos.mpr T.2
  have hA : 0 < ADelta L Δ := by
    unfold ADelta
    exact mul_pos hL hΔ
  have heps : 0 < epsilon := by norm_num [epsilon]
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  let x := ADelta L Δ * W / (epsilon * T.1)
  let y := σ ^ 2 * epsilon / (128 * n * W)
  let z := (1 / (4 * Real.sqrt 2)) *
    centralizedStochasticScale n L Δ σ T
  have hx : 0 ≤ x := by
    dsimp [x]
    positivity
  have hy : 0 ≤ y := by
    dsimp [y]
    positivity
  have hz : 0 ≤ z := by
    dsimp [z, centralizedStochasticScale]
    positivity
  have hrad : 0 ≤ ADelta L Δ / ((n : ℝ) * T.1) :=
    (div_pos hA (mul_pos hn hT)).le
  have hzsq : z ^ 2 = 4 * x * y := by
    dsimp [z, x, y, centralizedStochasticScale]
    rw [mul_pow, mul_pow, Real.sq_sqrt hrad]
    field_simp [ne_of_gt hn, ne_of_gt hT, ne_of_gt hW, ne_of_gt heps,
      ne_of_gt hsqrt2]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have hxy : 4 * x * y ≤ (x + y) ^ 2 := by
    nlinarith [sq_nonneg (x - y)]
  have hsquares : z ^ 2 ≤ (x + y) ^ 2 := by
    rw [hzsq]
    exact hxy
  exact (sq_le_sq₀ hz (add_nonneg hx hy)).1 hsquares

/-- Equation (59), including both its weighted-window and AM--GM comparator
consequences. -/
theorem comparator_lower_from_weighted_window
    (N : NetworkSetup n) (L Δ σ : ℝ)
    (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 < σ)
    (T : PositiveHorizon) (s : AdmissibleDimensionlessStepsize n)
    (hceil :
      2 * Nat.ceil ((epsilon / s.1) / gainFloor N) + 2 ≤ T.1)
    (hcob :
      16 * Real.sqrt n * coboundaryBound N / gainFloor N ≤ T.1) :
    0 < windowLength N T.1 0 s.1 ∧
    (epsilon / s.1) ^ 2 * T.1 /
          (64 * n * windowLength N T.1 0 s.1) ≤
        windowInfluenceSum N T.1 s.1 ∧
    ADelta L Δ * windowLength N T.1 0 s.1 /
            (epsilon * T.1) +
          σ ^ 2 * epsilon /
            (128 * n * windowLength N T.1 0 s.1) ≤
        comparatorAt N L Δ σ T s ∧
    (1 / (4 * Real.sqrt 2)) * centralizedStochasticScale n L Δ σ T ≤
        comparatorAt N L Δ σ T s := by
  have htwo := comparator_two_term_lower_from_weighted_window
    N L Δ σ T s hceil hcob
  refine ⟨htwo.1, htwo.2.1, htwo.2.2, ?_⟩
  exact (centralized_scale_le_two_term_window_bound N L Δ σ hL hΔ hσ T
    (windowLength N T.1 0 s.1) (by exact_mod_cast htwo.1)).trans htwo.2.2

/-- Positivity of all fixed coefficients used in competing-step localization. -/
theorem comparator_localization_constants_pos
    (N : NetworkSetup n) (L Δ σ : ℝ)
    (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 < σ) :
    0 < ADelta L Δ ∧
    0 < gainFloor N ∧
    0 < comparatorLocalizationBaseCost N L Δ σ ∧
    0 < comparatorLocalizationBudget N L Δ σ ∧
    0 < comparatorStepLowerConstant N L Δ σ ∧
    0 < comparatorStepUpperConstant N L Δ σ := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr N.hn
  have hA : 0 < ADelta L Δ := by
    unfold ADelta
    exact mul_pos hL hΔ
  have hmu : 0 < mixingMinorization N := by
    unfold mixingMinorization
    split_ifs
    · exact pow_pos ((lt_min_iff).2 ⟨N.ha, by norm_num⟩) _
    · norm_num
  have hg : 0 < gainFloor N :=
    (mul_pos hn hmu).trans_le
      (gainFloor_ge_n_mul_mixingMinorization N)
  have hbase : 0 < comparatorLocalizationBaseCost N L Δ σ := by
    unfold comparatorLocalizationBaseCost
    apply div_pos
    exact add_pos_of_pos_of_nonneg hA
      (div_nonneg (mul_nonneg (sq_nonneg σ) (sq_nonneg _)) (by norm_num))
    exact hg
  have hbudget : 0 < comparatorLocalizationBudget N L Δ σ := by
    unfold comparatorLocalizationBudget
    exact add_pos hbase hA
  have hlower : 0 < comparatorStepLowerConstant N L Δ σ := by
    unfold comparatorStepLowerConstant
    exact div_pos hA (mul_pos (mul_pos (by norm_num) hn) hbudget)
  have hupper : 0 < comparatorStepUpperConstant N L Δ σ := by
    unfold comparatorStepUpperConstant
    exact div_pos
      (by positivity)
      (mul_pos (sq_pos_of_pos hσ) (sq_pos_of_pos hg))
  exact ⟨hA, hg, hbase, hbudget, hlower, hupper⟩

/-- The initial future window contains the source floor-scale signal block. -/
theorem initial_window_floor_lower
    (N : NetworkSetup n) (T : PositiveHorizon)
    (s : AdmissibleDimensionlessStepsize n) :
    min T.1 (Nat.floor (epsilon / (n * s.1))) ≤
      windowLength N T.1 0 s.1 := by
  classical
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr N.hn
  have hs : 0 < s.1 := s.2.1
  let m : ℕ := Nat.floor (epsilon / ((n : ℝ) * s.1))
  let q : ℕ := min T.1 m
  by_cases hq : q = 0
  · simpa [q, m, hq]
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    have hqT : q ≤ T.1 := by simp [q]
    have hqm : q ≤ m := by simp [q]
    have hsum :
        (∑ r ∈ Finset.Ico 0 q, gain N r) ≤ (q : ℝ) * n := by
      calc
        (∑ r ∈ Finset.Ico 0 q, gain N r) ≤
            ∑ _r ∈ Finset.Ico 0 q, (n : ℝ) := by
          exact Finset.sum_le_sum fun r _ => gain_le_n N r
        _ = (q : ℝ) * n := by simp [mul_comm]
    have hfloor : (m : ℝ) ≤ epsilon / ((n : ℝ) * s.1) := by
      dsimp [m]
      exact Nat.floor_le (div_nonneg (by norm_num [epsilon])
        (mul_pos hn hs).le)
    have hqreal : (q : ℝ) ≤ m := by exact_mod_cast hqm
    have hbudget :
        s.1 * ∑ r ∈ Finset.Ico 0 q, gain N r ≤ epsilon := by
      have hprod : (q : ℝ) * n * s.1 ≤ epsilon := by
        calc
          (q : ℝ) * n * s.1 ≤ (m : ℝ) * n * s.1 := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hqreal hn.le) hs.le
          _ ≤ (epsilon / ((n : ℝ) * s.1)) * n * s.1 := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hfloor hn.le) hs.le
          _ = epsilon := by field_simp [ne_of_gt hn, ne_of_gt hs]
      nlinarith [mul_le_mul_of_nonneg_left hsum hs.le]
    change q ≤ windowLength N T.1 0 s.1
    exact interval_length_le_windowLength N T.1 0 0 q s.1 T.2
      le_rfl hqpos hqT hbudget

/-- Signal-side lower bound used to localize every competing stepsize. -/
theorem comparatorAt_signal_floor_lower
    (N : NetworkSetup n) (L Δ σ : ℝ)
    (hL : 0 < L) (hΔ : 0 < Δ)
    (T : PositiveHorizon) (s : AdmissibleDimensionlessStepsize n) :
    ADelta L Δ * min T.1 (Nat.floor (epsilon / (n * s.1))) /
        (epsilon * T.1) ≤ comparatorAt N L Δ σ T s := by
  have hA : 0 ≤ ADelta L Δ := by
    unfold ADelta
    exact (mul_pos hL hΔ).le
  have hW := initial_window_floor_lower N T s
  have henergy : 0 ≤ windowInfluenceSum N T.1 s.1 := by
    unfold windowInfluenceSum influenceEnergy
    exact Finset.sum_nonneg fun t _ =>
      mul_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)
        (Nat.cast_nonneg _)
  have hnoise :
      0 ≤ (σ ^ 2 / 2) * s.1 ^ 2 * windowInfluenceSum N T.1 s.1 := by
    positivity
  have hnum :
      ADelta L Δ * min T.1 (Nat.floor (epsilon / (n * s.1))) ≤
        comparatorNumerator N L Δ σ T s := by
    unfold comparatorNumerator
    exact (mul_le_mul_of_nonneg_left (by exact_mod_cast hW) hA).trans
      (le_add_of_nonneg_right hnoise)
  have hden : 0 < epsilon * (T.1 : ℝ) :=
    mul_pos (by norm_num [epsilon]) (Nat.cast_pos.mpr T.2)
  unfold comparatorAt
  exact (div_le_div_iff_of_pos_right hden).2 hnum

/-- The first `T-m` indices carry a uniform stochastic window contribution,
where `m=floor (epsilon/(n*s))`.  This is the noise-side localization bridge
preceding equation (19). -/
theorem windowInfluenceSum_floor_prefix_lower
    (N : NetworkSetup n) (T : PositiveHorizon)
    (s : AdmissibleDimensionlessStepsize n)
    (h2m :
      2 * Nat.floor (epsilon / ((n : ℝ) * s.1)) ≤ T.1)
    (hthreshold :
      influenceEnergyWindowThreshold N ≤
        T.1 - Nat.floor (epsilon / ((n : ℝ) * s.1))) :
    epsilon * T.1 * gainFloor N ^ 2 /
        (16 * (n : ℝ) ^ 2 * s.1) ≤
      windowInfluenceSum N T.1 s.1 := by
  classical
  let m : ℕ := Nat.floor (epsilon / ((n : ℝ) * s.1))
  let ℓ : ℕ := T.1 - m
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr N.hn
  have hs : 0 < s.1 := s.2.1
  have hns : (n : ℝ) * s.1 ≤ 1 / 64 := by
    calc
      (n : ℝ) * s.1 ≤ (n : ℝ) * (1 / (64 * (n : ℝ))) :=
        mul_le_mul_of_nonneg_left s.2.2 hn.le
      _ = 1 / 64 := by field_simp
  have hx4 : 4 ≤ epsilon / ((n : ℝ) * s.1) := by
    rw [le_div_iff₀ (mul_pos hn hs)]
    norm_num [epsilon] at hns ⊢
    linarith
  have hmpos : 0 < m := by
    dsimp [m]
    exact Nat.floor_pos.mpr (by linarith)
  have hfloor_lt :
      epsilon / ((n : ℝ) * s.1) < (m : ℝ) + 1 := by
    simpa [m] using
      (Nat.lt_floor_add_one (epsilon / ((n : ℝ) * s.1)))
  have hm_lower :
      epsilon / (2 * (n : ℝ) * s.1) ≤ (m : ℝ) := by
    have hxhalf :
        epsilon / (2 * (n : ℝ) * s.1) =
          (epsilon / ((n : ℝ) * s.1)) / 2 := by ring
    rw [hxhalf]
    nlinarith
  have hmT : m ≤ T.1 := by
    dsimp [m] at h2m ⊢
    omega
  have hℓhalf : (T.1 : ℝ) / 2 ≤ (ℓ : ℝ) := by
    have h2mR : 2 * (m : ℝ) ≤ (T.1 : ℝ) := by
      exact_mod_cast (by simpa [m] using h2m)
    dsimp [ℓ]
    rw [Nat.cast_sub hmT]
    nlinarith
  have henergy_nonneg (j : ℕ) : 0 ≤ influenceEnergy N j := by
    unfold influenceEnergy
    exact Finset.sum_nonneg fun i _ => sq_nonneg (influenceRow N j i)
  have hwindow (j : ℕ) (hj : j ∈ Finset.range ℓ) :
      m ≤ windowLength N T.1 (j + 1) s.1 := by
    have hjℓ : j < ℓ := Finset.mem_range.1 hj
    let P := j + 1
    let Q := P + m
    have hPT : P < T.1 := by
      dsimp [P, ℓ] at hjℓ ⊢
      omega
    have hPQ : P < Q := by
      dsimp [Q]
      omega
    have hQT : Q ≤ T.1 := by
      dsimp [P, Q, ℓ] at hjℓ ⊢
      omega
    have hsum :
        (∑ r ∈ Finset.Ico P Q, gain N r) ≤ (m : ℝ) * n := by
      calc
        (∑ r ∈ Finset.Ico P Q, gain N r) ≤
            ∑ _r ∈ Finset.Ico P Q, (n : ℝ) := by
          exact Finset.sum_le_sum fun r _ => gain_le_n N r
        _ = (m : ℝ) * n := by simp [P, Q]
    have hm_floor :
        (m : ℝ) ≤ epsilon / ((n : ℝ) * s.1) := by
      dsimp [m]
      exact Nat.floor_le (div_nonneg (by norm_num [epsilon])
        (mul_pos hn hs).le)
    have hbudget :
        s.1 * ∑ r ∈ Finset.Ico P Q, gain N r ≤ epsilon := by
      have hprod : (m : ℝ) * n * s.1 ≤ epsilon := by
        calc
          (m : ℝ) * n * s.1 ≤
              (epsilon / ((n : ℝ) * s.1)) * n * s.1 := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hm_floor hn.le) hs.le
          _ = epsilon := by field_simp [ne_of_gt hn, ne_of_gt hs]
      nlinarith [mul_le_mul_of_nonneg_left hsum hs.le]
    have hlen := interval_length_le_windowLength
      N T.1 P P Q s.1 hPT le_rfl hPQ hQT hbudget
    simpa [Q, P] using hlen
  have hrestricted :
      (∑ j ∈ Finset.range ℓ, influenceEnergy N j * (m : ℝ)) ≤
        windowInfluenceSum N T.1 s.1 := by
    unfold windowInfluenceSum
    calc
      (∑ j ∈ Finset.range ℓ, influenceEnergy N j * (m : ℝ)) ≤
          ∑ j ∈ Finset.range ℓ,
            influenceEnergy N j * windowLength N T.1 (j + 1) s.1 := by
        exact Finset.sum_le_sum fun j hj =>
          mul_le_mul_of_nonneg_left (by exact_mod_cast hwindow j hj)
            (henergy_nonneg j)
      _ ≤ ∑ j ∈ Finset.range T.1,
            influenceEnergy N j * windowLength N T.1 (j + 1) s.1 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.range_mono (Nat.sub_le T.1 m)
        · intro j _ _
          exact mul_nonneg (henergy_nonneg j) (Nat.cast_nonneg _)
  have henergy := window_influence_energy_lower N 0 ℓ (by
    simpa [ℓ, m] using hthreshold)
  have henergy' :
      (ℓ : ℝ) * gainFloor N ^ 2 / (4 * (n : ℝ)) ≤
        ∑ j ∈ Finset.range ℓ, influenceEnergy N j := by
    simpa using henergy
  have hscaled :
      (m : ℝ) * ((ℓ : ℝ) * gainFloor N ^ 2 / (4 * (n : ℝ))) ≤
        ∑ j ∈ Finset.range ℓ, influenceEnergy N j * (m : ℝ) := by
    calc
      (m : ℝ) * ((ℓ : ℝ) * gainFloor N ^ 2 / (4 * (n : ℝ))) ≤
          (m : ℝ) * ∑ j ∈ Finset.range ℓ, influenceEnergy N j :=
        mul_le_mul_of_nonneg_left henergy' (Nat.cast_nonneg m)
      _ = ∑ j ∈ Finset.range ℓ, influenceEnergy N j * (m : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  calc
    epsilon * T.1 * gainFloor N ^ 2 /
          (16 * (n : ℝ) ^ 2 * s.1) =
        (epsilon / (2 * (n : ℝ) * s.1)) * ((T.1 : ℝ) / 2) *
          gainFloor N ^ 2 / (4 * (n : ℝ)) := by
      field_simp [ne_of_gt hn, ne_of_gt hs]
      <;> ring
    _ ≤ (m : ℝ) * (ℓ : ℝ) * gainFloor N ^ 2 /
          (4 * (n : ℝ)) := by
      gcongr
    _ = (m : ℝ) *
          ((ℓ : ℝ) * gainFloor N ^ 2 / (4 * (n : ℝ))) := by ring
    _ ≤ ∑ j ∈ Finset.range ℓ, influenceEnergy N j * (m : ℝ) := hscaled
    _ ≤ windowInfluenceSum N T.1 s.1 := hrestricted

/-- The two source bounds before equation (19), localized uniformly once the
horizon dominates the signal exclusion, prefix length, and energy threshold. -/
theorem competingStepsize_localization_of_horizon
    (N : NetworkSetup n) (L Δ σ : ℝ)
    (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 < σ)
    (T : PositiveHorizon)
    (hsignalOnset :
      2 * epsilon * comparatorLocalizationBudget N L Δ σ /
          ADelta L Δ ≤ Real.sqrt T.1)
    (henergyOnset : 2 * influenceEnergyWindowThreshold N ≤ T.1)
    (s : AdmissibleDimensionlessStepsize n)
    (hcomp : IsCompetingStepsize N L Δ σ T s) :
    comparatorStepLowerConstant N L Δ σ / Real.sqrt T.1 ≤ s.1 ∧
      s.1 ≤ comparatorStepUpperConstant N L Δ σ /
        Real.sqrt T.1 := by
  let m : ℕ := Nat.floor (epsilon / ((n : ℝ) * s.1))
  have hconst := comparator_localization_constants_pos N L Δ σ hL hΔ hσ
  have hA : 0 < ADelta L Δ := hconst.1
  have hg : 0 < gainFloor N := hconst.2.1
  have hM : 0 < comparatorLocalizationBudget N L Δ σ := hconst.2.2.2.1
  have hc : 0 < comparatorStepLowerConstant N L Δ σ :=
    hconst.2.2.2.2.1
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr N.hn
  have hs : 0 < s.1 := s.2.1
  have hT : (0 : ℝ) < T.1 := Nat.cast_pos.mpr T.2
  have hsqrt : 0 < Real.sqrt T.1 := Real.sqrt_pos.2 hT
  have hsqrt_sq : (Real.sqrt T.1) ^ 2 = (T.1 : ℝ) :=
    Real.sq_sqrt hT.le
  have hfloor_lt :
      epsilon / ((n : ℝ) * s.1) < (m : ℝ) + 1 := by
    simpa [m] using
      (Nat.lt_floor_add_one (epsilon / ((n : ℝ) * s.1)))
  have hns : (n : ℝ) * s.1 ≤ 1 / 64 := by
    calc
      (n : ℝ) * s.1 ≤ (n : ℝ) * (1 / (64 * (n : ℝ))) :=
        mul_le_mul_of_nonneg_left s.2.2 hn.le
      _ = 1 / 64 := by field_simp
  have hx4 : 4 ≤ epsilon / ((n : ℝ) * s.1) := by
    rw [le_div_iff₀ (mul_pos hn hs)]
    norm_num [epsilon] at hns ⊢
    linarith
  have hm_lower :
      epsilon / (2 * (n : ℝ) * s.1) ≤ (m : ℝ) := by
    have hxhalf :
        epsilon / (2 * (n : ℝ) * s.1) =
          (epsilon / ((n : ℝ) * s.1)) / 2 := by ring
    rw [hxhalf]
    nlinarith
  have h2m : 2 * m ≤ T.1 := by
    by_contra hnot
    have hlt : T.1 < 2 * m := by omega
    have hmin : (T.1 : ℝ) / 2 < (min T.1 m : ℝ) := by
      have hminNat : T.1 < 2 * min T.1 m := by omega
      have hminR : (T.1 : ℝ) < 2 * (min T.1 m : ℝ) := by
        exact_mod_cast hminNat
      linarith
    have hsignal := comparatorAt_signal_floor_lower N L Δ σ hL hΔ T s
    have hsignal_strict :
        ADelta L Δ / (2 * epsilon) < comparatorAt N L Δ σ T s := by
      have heps : 0 < epsilon := by norm_num [epsilon]
      have hratio :
          (1 / 2 : ℝ) < (min T.1 m : ℝ) / T.1 := by
        rw [lt_div_iff₀ hT]
        nlinarith
      have hmul := mul_lt_mul_of_pos_left hratio (div_pos hA heps)
      calc
        ADelta L Δ / (2 * epsilon) =
            (ADelta L Δ / epsilon) * (1 / 2) := by ring
        _ < (ADelta L Δ / epsilon) *
            ((min T.1 m : ℝ) / T.1) := hmul
        _ =
            ADelta L Δ * min T.1 m / (epsilon * T.1) := by
          simp only [Nat.cast_min]
          field_simp
        _ ≤ comparatorAt N L Δ σ T s := by
          simpa [m] using hsignal
    have hbudget_upper :
        comparatorLocalizationBudget N L Δ σ / Real.sqrt T.1 ≤
          ADelta L Δ / (2 * epsilon) := by
      rw [div_le_div_iff₀ hsqrt (by norm_num [epsilon])]
      have hon := hsignalOnset
      field_simp [ne_of_gt hA] at hon
      nlinarith
    exact (not_lt_of_ge (hcomp.trans hbudget_upper)) hsignal_strict
  have hmT : m ≤ T.1 := by omega
  have hmin_eq : min T.1 m = m := min_eq_right hmT
  have hsignal := comparatorAt_signal_floor_lower N L Δ σ hL hΔ T s
  have hsignal_s :
      ADelta L Δ / (2 * (n : ℝ) * s.1 * T.1) ≤
        comparatorAt N L Δ σ T s := by
    calc
      ADelta L Δ / (2 * (n : ℝ) * s.1 * T.1) ≤
          ADelta L Δ * (m : ℝ) / (epsilon * T.1) := by
        field_simp [ne_of_gt hn, ne_of_gt hs, ne_of_gt hT, epsilon] at hm_lower ⊢
        nlinarith
      _ ≤ comparatorAt N L Δ σ T s := by
        simpa [m, hmin_eq] using hsignal
  have hlower :
      comparatorStepLowerConstant N L Δ σ / Real.sqrt T.1 ≤ s.1 := by
    have hchain := hsignal_s.trans hcomp
    unfold comparatorStepLowerConstant
    field_simp [ne_of_gt hn, ne_of_gt hs, ne_of_gt hT,
      ne_of_gt hsqrt, ne_of_gt hM] at hchain ⊢
    nlinarith [hsqrt_sq]
  have hm_floor :
      (m : ℝ) ≤ epsilon / ((n : ℝ) * s.1) := by
    dsimp [m]
    exact Nat.floor_le (div_nonneg (by norm_num [epsilon])
      (mul_pos hn hs).le)
  have h2m_again : 2 * m ≤ T.1 := h2m
  have hthreshold : influenceEnergyWindowThreshold N ≤ T.1 - m := by
    omega
  have hprefix := windowInfluenceSum_floor_prefix_lower N T s h2m_again hthreshold
  have hwindow_nonneg :
      (0 : ℝ) ≤ (windowLength N T.1 0 s.1 : ℝ) := Nat.cast_nonneg _
  have hnoise_lower :
      σ ^ 2 * gainFloor N ^ 2 * s.1 / (32 * (n : ℝ) ^ 2) ≤
        comparatorAt N L Δ σ T s := by
    have hnoise_nonneg :
        0 ≤ ADelta L Δ * windowLength N T.1 0 s.1 :=
      mul_nonneg hA.le hwindow_nonneg
    unfold comparatorAt comparatorNumerator
    have hden : 0 < epsilon * (T.1 : ℝ) :=
      mul_pos (by norm_num [epsilon]) hT
    rw [le_div_iff₀ hden]
    calc
      σ ^ 2 * gainFloor N ^ 2 * s.1 /
            (32 * (n : ℝ) ^ 2) * (epsilon * T.1) ≤
          (σ ^ 2 / 2) * s.1 ^ 2 * windowInfluenceSum N T.1 s.1 := by
        have hcoeff : 0 ≤ (σ ^ 2 / 2) * s.1 ^ 2 := by positivity
        have hmul := mul_le_mul_of_nonneg_left hprefix hcoeff
        convert hmul using 1 <;>
          field_simp [ne_of_gt hn, ne_of_gt hs, epsilon] <;> ring
      _ ≤ ADelta L Δ * windowLength N T.1 0 s.1 +
          (σ ^ 2 / 2) * s.1 ^ 2 * windowInfluenceSum N T.1 s.1 :=
        le_add_of_nonneg_left hnoise_nonneg
  have hupper :
      s.1 ≤ comparatorStepUpperConstant N L Δ σ /
        Real.sqrt T.1 := by
    have hchain := hnoise_lower.trans hcomp
    unfold comparatorStepUpperConstant
    field_simp [ne_of_gt hn, ne_of_gt hsqrt, ne_of_gt hσ,
      ne_of_gt hg] at hchain ⊢
    nlinarith
  exact ⟨hlower, hupper⟩

/-- The source's explicit qualification for a varying family of networks:
the constants and both matching/absorption onsets must be uniform. -/
def UniformMatchingOnset (F : Set (NetworkSetup n))
    (L Δ σ H : ℝ) : Prop :=
  ∃ K₂ : ℝ, ∃ Tstar Tzero : ℕ, ∀ N ∈ F,
    (∀ T : PositiveHorizon, Tstar ≤ T.1 →
      ENNReal.ofReal (comparator N L Δ σ T / 6400) ≤
        minimaxRisk (fixedInstanceClass N L Δ σ H) T ∧
      minimaxRisk (fixedInstanceClass N L Δ σ H) T ≤
        ENNReal.ofReal (512 * comparator N L Δ σ T + K₂ / T.1)) ∧
    (∀ T : PositiveHorizon, Tzero ≤ T.1 →
      minimaxRisk (fixedInstanceClass N L Δ σ H) T ≤
        ENNReal.ofReal (1024 * comparator N L Δ σ T))

def UniformCentralizedComparator (F : Set (NetworkSetup n))
    (L Δ σ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ Tonset : ℕ, ∀ N ∈ F,
    ∀ T : PositiveHorizon, Tonset ≤ T.1 →
      comparator N L Δ σ T ≤ C * centralizedStochasticScale n L Δ σ T

def UniformWindowSpeedupCriterion (F : Set (NetworkSetup n))
    (L Δ σ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ Tonset : ℕ, ∀ N ∈ F,
    ∀ T : PositiveHorizon, Tonset ≤ T.1 →
      ∃ s : AdmissibleDimensionlessStepsize n,
        comparatorNumerator N L Δ σ T s ≤
          C * epsilon * σ * Real.sqrt (ADelta L Δ * T.1 / n)

/-- The horizon factor converting the optimized comparator scale to the
pre-optimization numerator scale in equation (60). -/
theorem horizon_sqrt_budget_normalization
    (A nr tr : ℝ) (hA : 0 < A) (hnr : 0 < nr) (htr : 0 < tr) :
    tr * Real.sqrt (A / (nr * tr)) = Real.sqrt (A * tr / nr) := by
  have hrad_left : 0 ≤ A / (nr * tr) :=
    (div_pos hA (mul_pos hnr htr)).le
  have hrad_right : 0 ≤ A * tr / nr :=
    (div_pos (mul_pos hA htr) hnr).le
  apply (sq_eq_sq₀ (mul_nonneg htr.le (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)).mp
  rw [mul_pow, Real.sq_sqrt hrad_left, Real.sq_sqrt hrad_right]
  field_simp

/-- The initial window contributes at least one step, so every explicit
comparator value, and hence their infimum, retains the positive objective-gap
term needed to form equation (58). -/
theorem comparator_initial_window_lower_bound
    (N : NetworkSetup n) (L Δ σ : ℝ) (hL : 0 < L) (hΔ : 0 < Δ)
    (T : PositiveHorizon) :
    ADelta L Δ / (epsilon * T.1) ≤ comparator N L Δ σ T := by
  have hn : (0 : ℝ) < n := by exact_mod_cast N.hn
  have hT : (0 : ℝ) < T.1 := by exact_mod_cast T.2
  have hden : 0 < epsilon * (T.1 : ℝ) :=
    mul_pos (by norm_num [epsilon]) hT
  have hrange_nonempty :
      (Set.range fun s : AdmissibleDimensionlessStepsize n =>
        comparatorAt N L Δ σ T s).Nonempty := by
    let s₀ : AdmissibleDimensionlessStepsize n :=
      ⟨1 / (64 * (n : ℝ)), one_div_pos.mpr (mul_pos (by norm_num) hn), le_rfl⟩
    exact ⟨comparatorAt N L Δ σ T s₀, ⟨s₀, rfl⟩⟩
  unfold comparator
  apply le_csInf hrange_nonempty
  rintro y ⟨s, rfl⟩
  have hgain_nonneg : 0 ≤ gain N 0 := by
    unfold gain dotProduct
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg ((absoluteProbability_mem_stdSimplex N 1).1 i)
        (pushMass_nonneg N 0 i)
  have hbudget : s.1 * gain N 0 ≤ epsilon := by
    calc
      s.1 * gain N 0 ≤ (1 / (64 * (n : ℝ))) * n := by
        exact mul_le_mul s.2.2 (gain_le_n N 0) hgain_nonneg
          (one_div_pos.mpr (mul_pos (by norm_num) hn)).le
      _ ≤ epsilon := by
        unfold epsilon
        field_simp
        norm_num
  have hwindow : 1 ≤ windowLength N T.1 0 s.1 := by
    unfold windowLength
    rw [if_pos T.2]
    have hinner :
        1 ≤ (Finset.Icc (0 + 1) T.1).sup fun Q =>
          if s.1 * ∑ r ∈ Finset.Ico 0 Q, gain N r ≤ epsilon
          then Q - 0 else 0 := by
      have hQmem : 1 ∈ Finset.Icc (0 + 1) T.1 := by
        simp
        omega
      have hselected :
          1 ≤ (if s.1 * ∑ r ∈ Finset.Ico 0 1, gain N r ≤ epsilon
            then 1 - 0 else 0) := by
        simp [hbudget]
      exact hselected.trans (Finset.le_sup
        (s := Finset.Icc (0 + 1) T.1)
        (f := fun Q =>
          if s.1 * ∑ r ∈ Finset.Ico 0 Q, gain N r ≤ epsilon
          then Q - 0 else 0) hQmem)
    have hPmem : 0 ∈ Finset.Icc 0 T.1 := by simp
    exact hinner.trans (Finset.le_sup
      (s := Finset.Icc 0 T.1)
      (f := fun P =>
        (Finset.Icc (P + 1) T.1).sup fun Q =>
          if s.1 * ∑ r ∈ Finset.Ico P Q, gain N r ≤ epsilon
          then Q - P else 0) hPmem)
  have hA : 0 ≤ ADelta L Δ := by
    unfold ADelta
    exact (mul_pos hL hΔ).le
  have henergy : ∀ j, 0 ≤ influenceEnergy N j := by
    intro j
    unfold influenceEnergy
    exact Finset.sum_nonneg fun i _ => sq_nonneg (influenceRow N j i)
  have hwindowSum : 0 ≤ windowInfluenceSum N T.1 s.1 := by
    unfold windowInfluenceSum
    exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (henergy j) (Nat.cast_nonneg _)
  have hsecond :
      0 ≤ (σ ^ 2 / 2) * s.1 ^ 2 * windowInfluenceSum N T.1 s.1 := by
    exact mul_nonneg
      (mul_nonneg (div_nonneg (sq_nonneg σ) (by norm_num)) (sq_nonneg s.1))
      hwindowSum
  have hnumerator :
      ADelta L Δ ≤ comparatorNumerator N L Δ σ T s := by
    unfold comparatorNumerator
    calc
      ADelta L Δ = ADelta L Δ * 1 + 0 := by ring
      _ ≤ ADelta L Δ * windowLength N T.1 0 s.1 +
          (σ ^ 2 / 2) * s.1 ^ 2 * windowInfluenceSum N T.1 s.1 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (by exact_mod_cast hwindow) hA)
          hsecond
  unfold comparatorAt
  exact (div_le_div_iff_of_pos_right hden).2 hnumerator

/-- Every explicit comparator value is nonnegative, so its range has the
lower bound needed by the conditionally complete infimum API. -/
theorem comparatorAt_range_bddBelow
    (N : NetworkSetup n) (L Δ σ : ℝ) (hL : 0 < L) (hΔ : 0 < Δ)
    (T : PositiveHorizon) :
    BddBelow (Set.range fun s : AdmissibleDimensionlessStepsize n =>
      comparatorAt N L Δ σ T s) := by
  refine ⟨0, ?_⟩
  rintro y ⟨s, rfl⟩
  have hA : 0 ≤ ADelta L Δ := by
    unfold ADelta
    exact (mul_pos hL hΔ).le
  have henergy : ∀ j, 0 ≤ influenceEnergy N j := by
    intro j
    unfold influenceEnergy
    exact Finset.sum_nonneg fun i _ => sq_nonneg (influenceRow N j i)
  have hwindow : 0 ≤ windowInfluenceSum N T.1 s.1 := by
    unfold windowInfluenceSum
    exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (henergy j) (Nat.cast_nonneg _)
  have hnumerator : 0 ≤ comparatorNumerator N L Δ σ T s := by
    unfold comparatorNumerator
    exact add_nonneg
      (mul_nonneg hA (Nat.cast_nonneg _))
      (mul_nonneg
        (mul_nonneg (div_nonneg (sq_nonneg σ) (by norm_num)) (sq_nonneg s.1))
        hwindow)
  have hT : (0 : ℝ) < T.1 := by exact_mod_cast T.2
  unfold comparatorAt
  exact div_nonneg hnumerator (mul_pos (by norm_num [epsilon]) hT).le

/-- An eventual additive near-minimizer of the explicit comparator is already
on the source's competing square-root scale, and hence lies below the
corrected-center cap.  This is the selection/localization part of (19)--(20),
separated from the fixed-class analytic upper estimate. -/
theorem localized_near_comparator_with_center_cap
    (N : NetworkSetup n) (L Δ σ : ℝ)
    (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 < σ) :
    ∃ Tloc : ℕ, ∀ T : PositiveHorizon, Tloc ≤ T.1 →
      ∃ s : AdmissibleDimensionlessStepsize n,
        comparatorAt N L Δ σ T s ≤
            comparator N L Δ σ T + ADelta L Δ / T.1 ∧
          comparatorStepLowerConstant N L Δ σ / Real.sqrt T.1 ≤ s.1 ∧
          s.1 ≤ comparatorStepUpperConstant N L Δ σ /
            Real.sqrt T.1 ∧
          s.1 ≤ correctedCenterStepCap N ∧
          epsilon / 2 ≤ s.1 * ∑ t ∈ Finset.range T.1, gain N t := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr N.hn
  have hconstants :=
    comparator_localization_constants_pos N L Δ σ hL hΔ hσ
  have hA : 0 < ADelta L Δ := hconstants.1
  have hg : 0 < gainFloor N := hconstants.2.1
  have hbase : 0 < comparatorLocalizationBaseCost N L Δ σ :=
    hconstants.2.2.1
  have hbudget : 0 < comparatorLocalizationBudget N L Δ σ :=
    hconstants.2.2.2.1
  have hupper : 0 < comparatorStepUpperConstant N L Δ σ :=
    hconstants.2.2.2.2.2
  have hrate : mixingRate N < 1 := mixingRate_lt_one N
  have hrow : 0 < rowMixingConstant N := by
    unfold rowMixingConstant
    exact div_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 hn))
      (blockContraction_pos N)
  have hdisagreement : 0 < disagreementKernel N := by
    unfold disagreementKernel
    exact div_pos (sq_pos_of_pos hrow) (sq_pos_of_pos (sub_pos.mpr hrate))
  have hcolumn : 0 < columnMixingConstant N := by
    unfold columnMixingConstant
    exact div_pos (Real.sqrt_pos.2 hn) (blockContraction_pos N)
  have hincrement : 0 < incrementKernel N := by
    unfold incrementKernel
    positivity
  have htrackerIncrement : 0 < trackerIncrementKernel N := by
    unfold trackerIncrementKernel
    exact div_pos
      (mul_pos
        (mul_pos
          (mul_pos (by norm_num : (0 : ℝ) < 2) (sq_pos_of_pos hcolumn))
          (sq_pos_of_pos (by positivity : 0 < 1 + Real.sqrt n)))
        hincrement)
      (sq_pos_of_pos (sub_pos.mpr hrate))
  have hcontrolRB : 0 < controlRB N := by
    unfold controlRB controlKa controlMB
    have hcoef : 0 < (3 * (n : ℝ) + 6 * (n : ℝ) ^ 2) := by positivity
    positivity
  have hcap : 0 < correctedCenterStepCap N := by
    unfold correctedCenterStepCap
    simp only [lt_min_iff]
    refine ⟨by norm_num, by positivity, ?_, ?_, ?_⟩
    · exact one_div_pos.mpr (Real.sqrt_pos.2 (by positivity))
    · exact one_div_pos.mpr (Real.sqrt_pos.2 (by positivity))
    · exact div_pos hg (Real.sqrt_pos.2 (by positivity))
  let signalScale : ℝ :=
    2 * epsilon * comparatorLocalizationBudget N L Δ σ / ADelta L Δ
  let capScale : ℝ :=
    comparatorStepUpperConstant N L Δ σ / correctedCenterStepCap N
  let blockScale : ℝ :=
    epsilon /
      (2 * gainFloor N * comparatorStepLowerConstant N L Δ σ)
  let preOnsetScale : ℝ :=
    max (((64 * n : ℕ) ^ 2 : ℕ) : ℝ)
      (max ((2 * influenceEnergyWindowThreshold N : ℕ) : ℝ)
        (max (signalScale ^ 2) (capScale ^ 2)))
  let onsetScale : ℝ := max preOnsetScale (blockScale ^ 2)
  obtain ⟨Tloc, hTloc⟩ := exists_nat_ge onsetScale
  refine ⟨Tloc, ?_⟩
  intro T hTlocT
  have hTloc_cast : (Tloc : ℝ) ≤ T.1 := by exact_mod_cast hTlocT
  have honset : onsetScale ≤ (T.1 : ℝ) := hTloc.trans hTloc_cast
  have hpreOnset : preOnsetScale ≤ (T.1 : ℝ) :=
    (le_max_left _ _).trans honset
  have htrial : (64 * n : ℕ) ^ 2 ≤ T.1 := by
    exact_mod_cast
      ((le_max_left _ _).trans hpreOnset)
  have henergyOnset : 2 * influenceEnergyWindowThreshold N ≤ T.1 := by
    exact_mod_cast
      ((le_max_left _ _).trans ((le_max_right _ _).trans hpreOnset))
  have hsignal_nonneg : 0 ≤ signalScale := by
    dsimp [signalScale]
    exact (div_pos
      (mul_pos (mul_pos (by norm_num) (by norm_num [epsilon])) hbudget) hA).le
  have hcapScale_nonneg : 0 ≤ capScale := by
    dsimp [capScale]
    exact (div_pos hupper hcap).le
  have hblockScale_nonneg : 0 ≤ blockScale := by
    dsimp [blockScale]
    exact (div_pos (by norm_num [epsilon])
      (mul_pos (mul_pos (by norm_num) hg) hconstants.2.2.2.2.1)).le
  have hTreal : (0 : ℝ) < T.1 := Nat.cast_pos.mpr T.2
  have hsqrt_pos : 0 < Real.sqrt T.1 := Real.sqrt_pos.2 hTreal
  have hsqrt_sq : (Real.sqrt T.1) ^ 2 = (T.1 : ℝ) :=
    Real.sq_sqrt hTreal.le
  have hsignal_sq : signalScale ^ 2 ≤ (T.1 : ℝ) :=
    (le_max_left _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hpreOnset))
  have hcap_sq : capScale ^ 2 ≤ (T.1 : ℝ) :=
    (le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hpreOnset))
  have hblock_sq : blockScale ^ 2 ≤ (T.1 : ℝ) :=
    (le_max_right _ _).trans honset
  have hsignalOnset :
      2 * epsilon * comparatorLocalizationBudget N L Δ σ /
          ADelta L Δ ≤ Real.sqrt T.1 := by
    change signalScale ≤ Real.sqrt T.1
    exact (sq_le_sq₀ hsignal_nonneg hsqrt_pos.le).mp
      (by simpa [hsqrt_sq] using hsignal_sq)
  have hcapOnset :
      comparatorStepUpperConstant N L Δ σ / Real.sqrt T.1 ≤
        correctedCenterStepCap N := by
    have hscale : capScale ≤ Real.sqrt T.1 :=
      (sq_le_sq₀ hcapScale_nonneg hsqrt_pos.le).mp
        (by simpa [hsqrt_sq] using hcap_sq)
    dsimp [capScale] at hscale
    rw [div_le_iff₀ hsqrt_pos]
    rw [div_le_iff₀ hcap] at hscale
    nlinarith
  have hblockOnset :
      epsilon /
          (2 * gainFloor N * comparatorStepLowerConstant N L Δ σ) ≤
        Real.sqrt T.1 := by
    change blockScale ≤ Real.sqrt T.1
    exact (sq_le_sq₀ hblockScale_nonneg hsqrt_pos.le).mp
      (by simpa [hsqrt_sq] using hblock_sq)
  have hrange_nonempty :
      (Set.range fun s : AdmissibleDimensionlessStepsize n =>
        comparatorAt N L Δ σ T s).Nonempty := by
    let s₀ : AdmissibleDimensionlessStepsize n :=
      ⟨1 / (64 * (n : ℝ)), one_div_pos.mpr (mul_pos (by norm_num) hn), le_rfl⟩
    exact ⟨comparatorAt N L Δ σ T s₀, ⟨s₀, rfl⟩⟩
  have hbdd := comparatorAt_range_bddBelow N L Δ σ hL hΔ T
  have hinf :
      sInf (Set.range fun s : AdmissibleDimensionlessStepsize n =>
        comparatorAt N L Δ σ T s) <
          comparator N L Δ σ T + ADelta L Δ / T.1 := by
    have hslack : 0 < ADelta L Δ / (T.1 : ℝ) := div_pos hA hTreal
    simpa only [comparator] using
      (lt_add_of_pos_right
        (sInf (Set.range fun s : AdmissibleDimensionlessStepsize n =>
          comparatorAt N L Δ σ T s)) hslack)
  rcases exists_lt_of_csInf_lt hrange_nonempty hinf with
    ⟨y, ⟨s, rfl⟩, hsnear⟩
  have htrialUpper :=
    actual_quadratic_comparator_trial_upper N L Δ σ hL hΔ T htrial
  have hsqrt_le_T : Real.sqrt T.1 ≤ (T.1 : ℝ) := by
    have hTone : (1 : ℝ) ≤ T.1 := by exact_mod_cast T.2
    nlinarith [hsqrt_sq]
  have hslack_le :
      ADelta L Δ / (T.1 : ℝ) ≤ ADelta L Δ / Real.sqrt T.1 :=
    div_le_div_of_nonneg_left hA.le hsqrt_pos hsqrt_le_T
  have hcompeting : IsCompetingStepsize N L Δ σ T s := by
    unfold IsCompetingStepsize
    calc
      comparatorAt N L Δ σ T s ≤
          comparator N L Δ σ T + ADelta L Δ / T.1 := hsnear.le
      _ ≤ comparatorLocalizationBaseCost N L Δ σ / Real.sqrt T.1 +
          ADelta L Δ / Real.sqrt T.1 :=
        add_le_add htrialUpper hslack_le
      _ = comparatorLocalizationBudget N L Δ σ / Real.sqrt T.1 := by
        unfold comparatorLocalizationBudget
        ring
  have hlocalized := competingStepsize_localization_of_horizon
    N L Δ σ hL hΔ hσ T hsignalOnset henergyOnset s hcompeting
  have hsumGain :
      (T.1 : ℝ) * gainFloor N ≤
        ∑ t ∈ Finset.range T.1, gain N t := by
    calc
      (T.1 : ℝ) * gainFloor N =
          ∑ t ∈ Finset.range T.1, gainFloor N := by simp
      _ ≤ ∑ t ∈ Finset.range T.1, gain N t :=
        Finset.sum_le_sum fun t _ht =>
          (gain_bounds_before_corrected_center_control N t).1
  have hbase :
      epsilon / 2 ≤
        comparatorStepLowerConstant N L Δ σ * Real.sqrt T.1 *
          gainFloor N := by
    have hscale := mul_le_mul_of_nonneg_left hblockOnset
      (mul_nonneg
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hg.le)
        hconstants.2.2.2.2.1.le)
    field_simp [ne_of_gt hg, ne_of_gt hconstants.2.2.2.2.1] at hscale
    have hcancel :
        comparatorStepLowerConstant N L Δ σ * epsilon /
            comparatorStepLowerConstant N L Δ σ = epsilon := by
      field_simp [ne_of_gt hconstants.2.2.2.2.1]
    rw [hcancel] at hscale
    nlinarith
  have htotalGain :
      epsilon / 2 ≤ s.1 * ∑ t ∈ Finset.range T.1, gain N t := by
    calc
      epsilon / 2 ≤
          comparatorStepLowerConstant N L Δ σ * Real.sqrt T.1 *
            gainFloor N := hbase
      _ = (comparatorStepLowerConstant N L Δ σ / Real.sqrt T.1) *
          ((T.1 : ℝ) * gainFloor N) := by
        field_simp [ne_of_gt hsqrt_pos]
        nlinarith [hsqrt_sq]
      _ ≤ s.1 * ((T.1 : ℝ) * gainFloor N) := by
        exact mul_le_mul_of_nonneg_right hlocalized.1
          (mul_nonneg hTreal.le hg.le)
      _ ≤ s.1 * ∑ t ∈ Finset.range T.1, gain N t :=
        mul_le_mul_of_nonneg_left hsumGain s.2.1.le
  exact ⟨s, hsnear.le, hlocalized.1, hlocalized.2,
    hlocalized.2.trans hcapOnset, htotalGain⟩

/-- Pointwise arithmetic-output transfer used in source step (17): the
gradient at the arithmetic output is controlled by the corrected gradient and
the corrected-center offset. -/
theorem stationarityIntegrand_le_corrected_energy
    (S : Setup n d Ω) (omega : Ω) (alpha : ℝ) (t : ℕ) :
    stationarityIntegrand S alpha t omega ≤
      2 * ‖gradient (averageObjective S)
          (correctedCenter S omega alpha t)‖ ^ 2 +
        2 * S.L ^ 2 *
          ‖correctedCenter S omega alpha t -
            arithmeticMean S omega alpha t‖ ^ 2 := by
  have hgradEq (x : Point d) :
      gradient (averageObjective S) x =
        (n : ℝ)⁻¹ • ∑ i : Fin n, gradient (S.localObjective i) x := by
    have hfun : averageObjective S =
        SOptLib.finiteUniformAverage S.localObjective := by
      funext y
      simp [averageObjective, SOptLib.finiteUniformAverage_def,
        Fintype.card_fin, smul_eq_mul]
    have h :=
      SOptLib.gradient_finiteUniformAverage_eq_finiteUniformAverage_gradient
        S.localObjective (fun i y => gradient (S.localObjective i) y) x
        (fun i => ((S.local_smooth i).1 x).hasGradientAt)
    rw [hfun]
    simpa [SOptLib.finiteUniformAverage_def, Fintype.card_fin] using h
  have hLip :
      ‖gradient (averageObjective S) (arithmeticMean S omega alpha t) -
          gradient (averageObjective S) (correctedCenter S omega alpha t)‖ ≤
        S.L * ‖arithmeticMean S omega alpha t -
          correctedCenter S omega alpha t‖ := by
    rw [hgradEq, hgradEq, ← smul_sub, ← Finset.sum_sub_distrib,
      norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
    calc
      (n : ℝ)⁻¹ *
          ‖∑ i : Fin n,
            (gradient (S.localObjective i) (arithmeticMean S omega alpha t) -
              gradient (S.localObjective i)
                (correctedCenter S omega alpha t))‖ ≤
          (n : ℝ)⁻¹ * ∑ i : Fin n,
            ‖gradient (S.localObjective i) (arithmeticMean S omega alpha t) -
              gradient (S.localObjective i)
                (correctedCenter S omega alpha t)‖ := by
        exact mul_le_mul_of_nonneg_left
          (norm_sum_le Finset.univ fun i : Fin n =>
            gradient (S.localObjective i) (arithmeticMean S omega alpha t) -
              gradient (S.localObjective i) (correctedCenter S omega alpha t))
          (inv_nonneg.mpr (Nat.cast_nonneg n))
      _ ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n,
          S.L * ‖arithmeticMean S omega alpha t -
            correctedCenter S omega alpha t‖ := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg n))
        exact Finset.sum_le_sum fun i _ => (S.local_smooth i).2.norm_sub_le _ _
      _ = S.L * ‖arithmeticMean S omega alpha t -
            correctedCenter S omega alpha t‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt S.hn)
        field_simp
  have hdiffsq :
      ‖gradient (averageObjective S) (arithmeticMean S omega alpha t) -
          gradient (averageObjective S) (correctedCenter S omega alpha t)‖ ^ 2 ≤
        S.L ^ 2 * ‖arithmeticMean S omega alpha t -
          correctedCenter S omega alpha t‖ ^ 2 := by
    have hrhs : 0 ≤ S.L * ‖arithmeticMean S omega alpha t -
        correctedCenter S omega alpha t‖ :=
      mul_nonneg S.hL.le (norm_nonneg _)
    simpa [mul_pow] using ((sq_le_sq₀ (norm_nonneg _) hrhs).2 hLip)
  have hadd := SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq
    (gradient (averageObjective S) (arithmeticMean S omega alpha t) -
      gradient (averageObjective S) (correctedCenter S omega alpha t))
    (gradient (averageObjective S) (correctedCenter S omega alpha t))
  rw [sub_add_cancel] at hadd
  unfold stationarityIntegrand
  calc
    ‖gradient (averageObjective S) (arithmeticMean S omega alpha t)‖ ^ 2 ≤
        2 * ‖gradient (averageObjective S) (arithmeticMean S omega alpha t) -
            gradient (averageObjective S) (correctedCenter S omega alpha t)‖ ^ 2 +
          2 * ‖gradient (averageObjective S)
            (correctedCenter S omega alpha t)‖ ^ 2 := hadd
    _ ≤ 2 * (S.L ^ 2 *
          ‖arithmeticMean S omega alpha t -
            correctedCenter S omega alpha t‖ ^ 2) +
          2 * ‖gradient (averageObjective S)
            (correctedCenter S omega alpha t)‖ ^ 2 := by
      gcongr
    _ = _ := by
      rw [norm_sub_rev]
      ring

/-- Expected finite-horizon form of the arithmetic-output transfer. -/
theorem stationarityError_le_corrected_energy
    (S : Setup n d Ω) (alpha : ℝ) (T : PositiveHorizon) :
    stationarityError S alpha T ≤
      (T.1 : ℝ)⁻¹ *
        (2 * correctedGradientEnergy S alpha T +
          2 * S.L ^ 2 * correctedCenterOffsetEnergy S alpha T) := by
  classical
  letI : IsProbabilityMeasure S.probability := S.is_probability
  have hpoint (t : ℕ) :
      SOptLib.expectation S.probability (stationarityIntegrand S alpha t) ≤
        2 * SOptLib.expectation S.probability (fun omega =>
          ‖gradient (averageObjective S)
            (correctedCenter S omega alpha t)‖ ^ 2) +
        2 * S.L ^ 2 * SOptLib.expectation S.probability (fun omega =>
          ‖correctedCenter S omega alpha t -
            arithmeticMean S omega alpha t‖ ^ 2) := by
    have hcenterMem := (corrected_center_descent_payload_memLp_two S alpha t).1
    have hgradientMem :=
      (corrected_center_descent_payload_memLp_two S alpha t).2.1
    have hmeanMem := arithmeticMean_memLp_two S alpha t
    have hoffsetMem := hcenterMem.sub hmeanMem
    have hgradientInt : Integrable (fun omega =>
        ‖gradient (averageObjective S)
          (correctedCenter S omega alpha t)‖ ^ 2) S.probability :=
      (memLp_two_iff_integrable_sq_norm
        hgradientMem.aestronglyMeasurable).1 hgradientMem
    have hoffsetInt : Integrable (fun omega =>
        ‖correctedCenter S omega alpha t -
          arithmeticMean S omega alpha t‖ ^ 2) S.probability :=
      (memLp_two_iff_integrable_sq_norm
        hoffsetMem.aestronglyMeasurable).1 hoffsetMem
    let A : Ω → ℝ := fun omega =>
      2 * ‖gradient (averageObjective S)
        (correctedCenter S omega alpha t)‖ ^ 2
    let B : Ω → ℝ := fun omega =>
      2 * S.L ^ 2 *
        ‖correctedCenter S omega alpha t -
          arithmeticMean S omega alpha t‖ ^ 2
    have hAint : Integrable A S.probability := hgradientInt.const_mul 2
    have hBint : Integrable B S.probability :=
      hoffsetInt.const_mul (2 * S.L ^ 2)
    have hmono := MeasureTheory.integral_mono
      (stationarityIntegrand_integrable S alpha t) (hAint.add hBint)
      (fun omega => stationarityIntegrand_le_corrected_energy S omega alpha t)
    calc
      SOptLib.expectation S.probability (stationarityIntegrand S alpha t) ≤
          ∫ omega, A omega + B omega ∂S.probability := by
        simpa [A, B] using hmono
      _ = (∫ omega, A omega ∂S.probability) +
          ∫ omega, B omega ∂S.probability :=
        MeasureTheory.integral_add hAint hBint
      _ = _ := by
        dsimp [A, B]
        rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_const_mul]
        rfl
  have hsum := Finset.sum_le_sum fun t (_ht : t ∈ Finset.range T.1) =>
    hpoint t
  unfold stationarityError correctedGradientEnergy correctedCenterOffsetEnergy
  calc
    (T.1 : ℝ)⁻¹ * ∑ t ∈ Finset.range T.1,
        SOptLib.expectation S.probability (stationarityIntegrand S alpha t) ≤
      (T.1 : ℝ)⁻¹ * ∑ t ∈ Finset.range T.1,
        (2 * SOptLib.expectation S.probability (fun omega =>
            ‖gradient (averageObjective S)
              (correctedCenter S omega alpha t)‖ ^ 2) +
          2 * S.L ^ 2 * SOptLib.expectation S.probability (fun omega =>
            ‖correctedCenter S omega alpha t -
              arithmeticMean S omega alpha t‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = (T.1 : ℝ)⁻¹ *
        (2 * ∑ t ∈ Finset.range T.1,
            SOptLib.expectation S.probability (fun omega =>
              ‖gradient (averageObjective S)
                (correctedCenter S omega alpha t)‖ ^ 2) +
          2 * S.L ^ 2 * ∑ t ∈ Finset.range T.1,
            SOptLib.expectation S.probability (fun omega =>
              ‖correctedCenter S omega alpha t -
                arithmeticMean S omega alpha t‖ ^ 2)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- The source's backward greedy gain-budget construction, at the level of
its contiguous cut points.  Each extracted right block is the longest suffix
whose gain is at most `1/(32s)`; a remaining left prefix below `1/(64s)` is
merged into that block.  The larger `1/(16s)` upper allowance records exactly
the slack needed by this final merge. -/
theorem exists_backward_gain_budget_partition
    (N : NetworkSetup n) (T : PositiveHorizon)
    (s : AdmissibleDimensionlessStepsize n)
    (htotal : epsilon / 2 ≤
      s.1 * ∑ t ∈ Finset.range T.1, gain N t) :
    ∃ blockCount : ℕ, ∃ endpoint : ℕ → ℕ,
      0 < blockCount ∧ endpoint 0 = 0 ∧ endpoint blockCount = T.1 ∧
      (∀ j < blockCount, endpoint j < endpoint (j + 1)) ∧
      ∀ j < blockCount,
        1 / (64 * s.1) ≤
            ∑ t ∈ Finset.Ico (endpoint j) (endpoint (j + 1)), gain N t ∧
          (∑ t ∈ Finset.Ico (endpoint j) (endpoint (j + 1)), gain N t) ≤
            1 / (16 * s.1) := by
  classical
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr N.hn
  have hs : 0 < s.1 := s.2.1
  have hsn : s.1 * (n : ℝ) ≤ 1 / 64 := by
    calc
      s.1 * (n : ℝ) ≤ (1 / (64 * (n : ℝ))) * n :=
        mul_le_mul_of_nonneg_right s.2.2 hn.le
      _ = 1 / 64 := by field_simp
  have hn_lower : (n : ℝ) ≤ 1 / (64 * s.1) := by
    rw [div_eq_mul_inv, le_mul_inv_iff₀ (mul_pos (by norm_num) hs)]
    nlinarith
  have hlower_pos : 0 < 1 / (64 * s.1) :=
    one_div_pos.mpr (mul_pos (by norm_num) hs)
  have hgeneral : ∀ R : ℕ,
      1 / (64 * s.1) ≤ ∑ t ∈ Finset.range R, gain N t →
      ∃ blockCount : ℕ, ∃ endpoint : ℕ → ℕ,
        0 < blockCount ∧ endpoint 0 = 0 ∧ endpoint blockCount = R ∧
        (∀ j < blockCount, endpoint j < endpoint (j + 1)) ∧
        ∀ j < blockCount,
          1 / (64 * s.1) ≤
              ∑ t ∈ Finset.Ico (endpoint j) (endpoint (j + 1)), gain N t ∧
            (∑ t ∈ Finset.Ico (endpoint j) (endpoint (j + 1)), gain N t) ≤
              1 / (16 * s.1) := by
    intro R
    induction R using Nat.strong_induction_on with
    | h R ih =>
      intro hRlower
      have hRpos : 0 < R := by
        by_contra hnot
        have hRzero : R = 0 := Nat.eq_zero_of_not_pos hnot
        subst R
        have : 1 / (64 * s.1) ≤ 0 := by simpa using hRlower
        exact (not_le_of_gt hlower_pos) this
      let admissibleStarts : Finset ℕ :=
        (Finset.Icc 0 (R - 1)).filter fun P =>
          (∑ t ∈ Finset.Ico P R, gain N t) ≤ 1 / (32 * s.1)
      have hlast_mem : R - 1 ∈ admissibleStarts := by
        simp only [admissibleStarts, Finset.mem_filter, Finset.mem_Icc,
          Nat.zero_le, true_and]
        constructor
        · omega
        · have hsingle :
              (∑ t ∈ Finset.Ico (R - 1) R, gain N t) =
                gain N (R - 1) := by
              have : R - 1 + 1 = R := Nat.sub_add_cancel hRpos
              rw [← this]
              simp
          rw [hsingle]
          calc
            gain N (R - 1) ≤ (n : ℝ) :=
              (gain_bounds_before_corrected_center_control N (R - 1)).2
            _ ≤ 1 / (64 * s.1) := hn_lower
            _ ≤ 1 / (32 * s.1) := by
              have : 0 < 64 * s.1 := mul_pos (by norm_num) hs
              have : 0 < 32 * s.1 := mul_pos (by norm_num) hs
              field_simp [ne_of_gt hs]
              norm_num
      let P : ℕ := admissibleStarts.min' ⟨R - 1, hlast_mem⟩
      have hPmem : P ∈ admissibleStarts := by
        dsimp [P]
        exact admissibleStarts.min'_mem ⟨R - 1, hlast_mem⟩
      have hPbound : P ≤ R - 1 := by
        have hbounds : P ∈ Finset.Icc 0 (R - 1) :=
          (Finset.mem_filter.1 hPmem).1
        exact (Finset.mem_Icc.1 hbounds).2
      have hPR : P < R := by omega
      have hsuffix_upper :
          (∑ t ∈ Finset.Ico P R, gain N t) ≤ 1 / (32 * s.1) := by
        exact (Finset.mem_filter.1 hPmem).2
      have hsum_split :
          (∑ t ∈ Finset.range R, gain N t) =
            (∑ t ∈ Finset.range P, gain N t) +
              ∑ t ∈ Finset.Ico P R, gain N t := by
        exact (Finset.sum_range_add_sum_Ico (gain N) hPR.le).symm
      by_cases hprefix :
          1 / (64 * s.1) ≤ ∑ t ∈ Finset.range P, gain N t
      · obtain ⟨k, endpoint, hkpos, he0, hek, hestrict, hebudget⟩ :=
          ih P hPR hprefix
        let endpoint' : ℕ → ℕ := fun j => if j ≤ k then endpoint j else R
        refine ⟨k + 1, endpoint', by omega, ?_, ?_, ?_, ?_⟩
        · simp [endpoint', he0]
        · simp [endpoint']
        · intro j hj
          by_cases hjk : j < k
          · have hjle : j ≤ k := hjk.le
            have hjsle : j + 1 ≤ k := by omega
            simp only [endpoint', if_pos hjle, if_pos hjsle]
            exact hestrict j hjk
          · have hj_eq : j = k := by omega
            subst j
            simp only [endpoint', if_pos le_rfl, if_neg (by omega : ¬ k + 1 ≤ k), hek]
            exact hPR
        · intro j hj
          by_cases hjk : j < k
          · have hjle : j ≤ k := hjk.le
            have hjsle : j + 1 ≤ k := by omega
            simp only [endpoint', if_pos hjle, if_pos hjsle]
            exact hebudget j hjk
          · have hj_eq : j = k := by omega
            subst j
            simp only [endpoint', if_pos le_rfl, if_neg (by omega : ¬ k + 1 ≤ k), hek]
            have hPpos : 0 < P := by
              by_contra hnot
              have hPzero : P = 0 := Nat.eq_zero_of_not_pos hnot
              have hprefix0 := hprefix
              rw [hPzero] at hprefix0
              have : 1 / (64 * s.1) ≤ 0 := by simpa using hprefix0
              exact (not_le_of_gt hlower_pos) this
            have hprev_not_mem : P - 1 ∉ admissibleStarts := by
              intro hprev
              have hmin : P ≤ P - 1 := by
                dsimp [P]
                exact admissibleStarts.min'_le (P - 1) hprev
              omega
            have hprev_bounds : P - 1 ∈ Finset.Icc 0 (R - 1) := by
              simp only [Finset.mem_Icc, Nat.zero_le, true_and]
              omega
            have hprev_over :
                1 / (32 * s.1) <
                  ∑ t ∈ Finset.Ico (P - 1) R, gain N t := by
              have hnot : ¬ (∑ t ∈ Finset.Ico (P - 1) R, gain N t) ≤
                  1 / (32 * s.1) := by
                intro hle
                apply hprev_not_mem
                exact Finset.mem_filter.2 ⟨hprev_bounds, hle⟩
              exact lt_of_not_ge hnot
            have hsplit_left :
                (∑ t ∈ Finset.Ico (P - 1) R, gain N t) =
                  gain N (P - 1) + ∑ t ∈ Finset.Ico P R, gain N t := by
              have hsucc : P - 1 + 1 = P := Nat.sub_add_cancel hPpos
              rw [← Finset.sum_Ico_consecutive (gain N)
                (Nat.sub_le P 1) hPR.le, ← hsucc]
              simp
            have hgain_prev : gain N (P - 1) ≤ (n : ℝ) :=
              (gain_bounds_before_corrected_center_control N (P - 1)).2
            have hsuffix_lower :
                1 / (64 * s.1) ≤
                  ∑ t ∈ Finset.Ico P R, gain N t := by
              rw [hsplit_left] at hprev_over
              have hrel :
                  1 / (32 * s.1) = 2 * (1 / (64 * s.1)) := by
                field_simp [ne_of_gt hs]
                ring
              rw [hrel] at hprev_over
              nlinarith [hgain_prev, hn_lower]
            exact ⟨hsuffix_lower, hsuffix_upper.trans (by
              have : 0 < 32 * s.1 := mul_pos (by norm_num) hs
              have : 0 < 16 * s.1 := mul_pos (by norm_num) hs
              field_simp [ne_of_gt hs]
              norm_num)⟩
      · have hprefix_lt :
            (∑ t ∈ Finset.range P, gain N t) < 1 / (64 * s.1) :=
          lt_of_not_ge hprefix
        refine ⟨1, fun j => if j = 0 then 0 else R,
          by norm_num, by simp, by simp, ?_, ?_⟩
        · intro j hj
          have hj0 : j = 0 := by omega
          subst j
          simp [hRpos]
        · intro j hj
          have hj0 : j = 0 := by omega
          subst j
          simp only [if_pos rfl, zero_add, if_neg one_ne_zero]
          change
            1 / (64 * s.1) ≤ ∑ t ∈ Finset.Ico 0 R, gain N t ∧
              (∑ t ∈ Finset.Ico 0 R, gain N t) ≤ 1 / (16 * s.1)
          have hwhole :
              (∑ t ∈ Finset.Ico 0 R, gain N t) =
                ∑ t ∈ Finset.range R, gain N t := by simp
          rw [hwhole]
          refine ⟨hRlower, ?_⟩
          rw [hsum_split]
          have htarget_upper :
              1 / (64 * s.1) + 1 / (32 * s.1) ≤
                1 / (16 * s.1) := by
            field_simp [ne_of_gt hs]
            norm_num
          linarith
  apply hgeneral T.1
  rw [div_le_iff₀ (mul_pos (by norm_num) hs)]
  norm_num [epsilon] at htotal ⊢
  nlinarith

/-- The positive-overcount telescope in the display preceding source equation
(18).  `M j` is the maximum length of block `j` or a later block.  A strict
drop of this suffix maximum can therefore occur only when the current block
has length `M j`.  If the causal window at every point of the current block
already covers the next suffix maximum, the total excess charge is at most
the square of the largest block length. -/
theorem suffix_max_block_window_overcount
    (blocks : ℕ → Finset ℕ) (M W : ℕ → ℕ) (q : ℕ → ℝ)
    (B : ℝ) (blockCount : ℕ)
    (hB : 0 ≤ B)
    (hMmono : ∀ j < blockCount, M (j + 1) ≤ M j)
    (hMterminal : M blockCount = 0)
    (hdropCard : ∀ j < blockCount,
      M (j + 1) < M j → (blocks j).card = M j)
    (hwindow : ∀ j < blockCount, ∀ t ∈ blocks j,
      M (j + 1) ≤ W (t + 1))
    (hq_nonneg : ∀ t, 0 ≤ q t)
    (hq_upper : ∀ t, q t ≤ B) :
    (∑ j ∈ Finset.range blockCount,
        (M j : ℝ) * ∑ t ∈ blocks j, q t) ≤
      (∑ j ∈ Finset.range blockCount,
        ∑ t ∈ blocks j, (W (t + 1) : ℝ) * q t) +
        B * (M 0 : ℝ) ^ 2 := by
  have hblock (j : ℕ) (hj : j ∈ Finset.range blockCount) :
      (M j : ℝ) * ∑ t ∈ blocks j, q t ≤
        (∑ t ∈ blocks j, (W (t + 1) : ℝ) * q t) +
          B * (M j : ℝ) * ((M j : ℝ) - M (j + 1)) := by
    have hjlt : j < blockCount := Finset.mem_range.1 hj
    have hmonoNat := hMmono j hjlt
    have hmonoReal : (M (j + 1) : ℝ) ≤ M j := by exact_mod_cast hmonoNat
    have hpoint (t : ℕ) (ht : t ∈ blocks j) :
        (M j : ℝ) * q t ≤
          (W (t + 1) : ℝ) * q t +
            B * ((M j : ℝ) - M (j + 1)) := by
      have hwNat := hwindow j hjlt t ht
      have hwReal : (M (j + 1) : ℝ) ≤ W (t + 1) := by
        exact_mod_cast hwNat
      nlinarith [hq_nonneg t, hq_upper t]
    have hsum := Finset.sum_le_sum fun t (ht : t ∈ blocks j) => hpoint t ht
    rw [Finset.mul_sum]
    calc
      ∑ t ∈ blocks j, (M j : ℝ) * q t ≤
          ∑ t ∈ blocks j,
            ((W (t + 1) : ℝ) * q t +
              B * ((M j : ℝ) - M (j + 1))) := hsum
      _ = (∑ t ∈ blocks j, (W (t + 1) : ℝ) * q t) +
          ((blocks j).card : ℝ) *
            (B * ((M j : ℝ) - M (j + 1))) := by
        rw [Finset.sum_add_distrib]
        simp
      _ ≤ (∑ t ∈ blocks j, (W (t + 1) : ℝ) * q t) +
          B * (M j : ℝ) * ((M j : ℝ) - M (j + 1)) := by
        by_cases heq : M (j + 1) = M j
        · rw [heq]
          ring_nf
          exact le_rfl
        · have hlt : M (j + 1) < M j := lt_of_le_of_ne hmonoNat heq
          rw [hdropCard j hjlt hlt]
          ring
          exact le_rfl
  have hsum := Finset.sum_le_sum fun j (hj : j ∈ Finset.range blockCount) =>
    hblock j hj
  have htelescope :
      (∑ j ∈ Finset.range blockCount,
          (M j : ℝ) * ((M j : ℝ) - M (j + 1))) ≤
        (M 0 : ℝ) ^ 2 := by
    have hterm (j : ℕ) (hj : j ∈ Finset.range blockCount) :
        (M j : ℝ) * ((M j : ℝ) - M (j + 1)) ≤
          (M j : ℝ) ^ 2 - (M (j + 1) : ℝ) ^ 2 := by
      have hmonoNat := hMmono j (Finset.mem_range.1 hj)
      have hmonoReal : (M (j + 1) : ℝ) ≤ M j := by exact_mod_cast hmonoNat
      have hnext : 0 ≤ (M (j + 1) : ℝ) := Nat.cast_nonneg _
      nlinarith
    calc
      (∑ j ∈ Finset.range blockCount,
          (M j : ℝ) * ((M j : ℝ) - M (j + 1))) ≤
          ∑ j ∈ Finset.range blockCount,
            ((M j : ℝ) ^ 2 - (M (j + 1) : ℝ) ^ 2) :=
        Finset.sum_le_sum hterm
      _ = (M 0 : ℝ) ^ 2 - (M blockCount : ℝ) ^ 2 := by
        exact Finset.sum_range_sub' (fun j => (M j : ℝ) ^ 2) blockCount
      _ = (M 0 : ℝ) ^ 2 := by simp [hMterminal]
  calc
    (∑ j ∈ Finset.range blockCount,
        (M j : ℝ) * ∑ t ∈ blocks j, q t) ≤
      ∑ j ∈ Finset.range blockCount,
        ((∑ t ∈ blocks j, (W (t + 1) : ℝ) * q t) +
          B * (M j : ℝ) * ((M j : ℝ) - M (j + 1))) := hsum
    _ = (∑ j ∈ Finset.range blockCount,
          ∑ t ∈ blocks j, (W (t + 1) : ℝ) * q t) +
        B * ∑ j ∈ Finset.range blockCount,
          ((M j : ℝ) * ((M j : ℝ) - M (j + 1))) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      have hfactor :
          (∑ j ∈ Finset.range blockCount,
              B * (M j : ℝ) * ((M j : ℝ) - M (j + 1))) =
            ∑ j ∈ Finset.range blockCount,
              B * ((M j : ℝ) * ((M j : ℝ) - M (j + 1))) := by
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      exact congrArg
        (fun z : ℝ =>
          (∑ j ∈ Finset.range blockCount,
            ∑ t ∈ blocks j, (W (t + 1) : ℝ) * q t) + z)
        hfactor
    _ ≤ (∑ j ∈ Finset.range blockCount,
          ∑ t ∈ blocks j, (W (t + 1) : ℝ) * q t) +
        B * (M 0 : ℝ) ^ 2 := by
      gcongr

/-- Source equation (18)'s causal-window estimate after the backward blocks
have been constructed.  The hypotheses are precisely the finite partition
certificate produced by that construction: suffix maxima decrease, a strict
drop identifies the current block as a longest remaining block, every next
block fits in the causal window of the current block, and the blocks reindex
the full horizon. -/
theorem gain_block_suffix_influence_overcount
    (N : NetworkSetup n) (T : PositiveHorizon)
    (s : AdmissibleDimensionlessStepsize n)
    (blocks : ℕ → Finset ℕ) (M : ℕ → ℕ) (omega : ℕ → ℝ)
    (blockCount : ℕ)
    (hMmono : ∀ j < blockCount, M (j + 1) ≤ M j)
    (hMterminal : M blockCount = 0)
    (hdropCard : ∀ j < blockCount,
      M (j + 1) < M j → (blocks j).card = M j)
    (hwindow : ∀ j < blockCount, ∀ t ∈ blocks j,
      M (j + 1) ≤ windowLength N T.1 (t + 1) s.1)
    (hpartition : ∀ f : ℕ → ℝ,
      (∑ j ∈ Finset.range blockCount, ∑ t ∈ blocks j, f t) =
        ∑ t ∈ Finset.range T.1, f t)
    (homega : ∀ j < blockCount,
      omega j ≤ 64 * s.1 * (M j : ℝ))
    (hMzero : M 0 ≤ windowLength N T.1 0 s.1) :
    (∑ j ∈ Finset.range blockCount,
        omega j * ∑ t ∈ blocks j, influenceEnergy N t) ≤
      64 * s.1 *
        (windowInfluenceSum N T.1 s.1 +
          influenceRowBound N ^ 2 *
            (windowLength N T.1 0 s.1 : ℝ) ^ 2) := by
  have henergy_nonneg (t : ℕ) : 0 ≤ influenceEnergy N t := by
    unfold influenceEnergy
    exact Finset.sum_nonneg fun i _hi => sq_nonneg (influenceRow N t i)
  have henergy_upper (t : ℕ) :
      influenceEnergy N t ≤ influenceRowBound N ^ 2 := by
    have hnormsq : nodeL2Norm (influenceRow N t) ^ 2 =
        influenceEnergy N t := by
      unfold nodeL2Norm influenceEnergy
      rw [Real.sq_sqrt]
      exact Finset.sum_nonneg fun i _hi => sq_nonneg (influenceRow N t i)
    have hnorm_nonneg : 0 ≤ nodeL2Norm (influenceRow N t) := by
      unfold nodeL2Norm
      exact Real.sqrt_nonneg _
    rw [← hnormsq]
    nlinarith [influenceRow_nodeL2_le N t]
  have hB_nonneg : 0 ≤ influenceRowBound N ^ 2 := sq_nonneg _
  have hover := suffix_max_block_window_overcount
    blocks M (fun t => windowLength N T.1 t s.1)
    (influenceEnergy N) (influenceRowBound N ^ 2) blockCount
    hB_nonneg hMmono hMterminal hdropCard hwindow
    henergy_nonneg henergy_upper
  have hweighted :
      (∑ j ∈ Finset.range blockCount,
          omega j * ∑ t ∈ blocks j, influenceEnergy N t) ≤
        64 * s.1 *
          ∑ j ∈ Finset.range blockCount,
            (M j : ℝ) * ∑ t ∈ blocks j, influenceEnergy N t := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hqsum : 0 ≤ ∑ t ∈ blocks j, influenceEnergy N t :=
      Finset.sum_nonneg fun t _ht => henergy_nonneg t
    calc
      omega j * ∑ t ∈ blocks j, influenceEnergy N t ≤
          (64 * s.1 * (M j : ℝ)) *
            ∑ t ∈ blocks j, influenceEnergy N t :=
        mul_le_mul_of_nonneg_right
          (homega j (Finset.mem_range.1 hj)) hqsum
      _ = 64 * s.1 *
          ((M j : ℝ) * ∑ t ∈ blocks j, influenceEnergy N t) := by ring
  have hscale_nonneg : 0 ≤ 64 * s.1 :=
    mul_nonneg (by norm_num) s.2.1.le
  have hscaled := mul_le_mul_of_nonneg_left hover hscale_nonneg
  have hpartition_window :
      (∑ j ∈ Finset.range blockCount,
          ∑ t ∈ blocks j,
            (windowLength N T.1 (t + 1) s.1 : ℝ) *
              influenceEnergy N t) =
        windowInfluenceSum N T.1 s.1 := by
    simpa [windowInfluenceSum, mul_comm] using
      hpartition (fun t =>
        (windowLength N T.1 (t + 1) s.1 : ℝ) * influenceEnergy N t)
  have hMzeroReal : (M 0 : ℝ) ≤ windowLength N T.1 0 s.1 := by
    exact_mod_cast hMzero
  have hMzeroSq : (M 0 : ℝ) ^ 2 ≤
      (windowLength N T.1 0 s.1 : ℝ) ^ 2 := by
    exact (sq_le_sq₀ (Nat.cast_nonneg _) (Nat.cast_nonneg _)).2 hMzeroReal
  calc
    (∑ j ∈ Finset.range blockCount,
        omega j * ∑ t ∈ blocks j, influenceEnergy N t) ≤
      64 * s.1 *
        ∑ j ∈ Finset.range blockCount,
          (M j : ℝ) * ∑ t ∈ blocks j, influenceEnergy N t := hweighted
    _ ≤ 64 * s.1 *
        ((∑ j ∈ Finset.range blockCount,
            ∑ t ∈ blocks j,
              (windowLength N T.1 (t + 1) s.1 : ℝ) *
                influenceEnergy N t) +
          influenceRowBound N ^ 2 * (M 0 : ℝ) ^ 2) := hscaled
    _ ≤ 64 * s.1 *
        (windowInfluenceSum N T.1 s.1 +
          influenceRowBound N ^ 2 *
            (windowLength N T.1 0 s.1 : ℝ) ^ 2) := by
      rw [hpartition_window]
      gcongr

end Algorithms.Unverified.GeneralPushPull
end
