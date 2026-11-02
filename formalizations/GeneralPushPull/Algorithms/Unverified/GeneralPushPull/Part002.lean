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
import Algorithms.Unverified.GeneralPushPull.Part001

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

/-- Finite linear combinations may be moved through the corrected lift. -/
theorem influenceOperator_finset_sum_smul
    {I : Type*} [DecidableEq I]
    (N : NetworkSetup n) (t : ℕ) (s : Finset I)
    (a : I → ℝ) (W : I → ZeroSumNodeVector n) :
    influenceOperator N t
        ⟨fun j => ∑ i ∈ s, a i * (W i).1 j, by
          change ∑ j, ∑ i ∈ s, a i * (W i).1 j = 0
          rw [Finset.sum_comm]
          apply Finset.sum_eq_zero
          intro i hi
          rw [← Finset.mul_sum, (W i).2, mul_zero]⟩ =
      ∑ i ∈ s, a i * influenceOperator N t (W i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [influenceOperator]
  | @insert i s hi ih =>
      let Wi : ZeroSumNodeVector n :=
        ⟨fun j => a i * (W i).1 j, by
          change ∑ j, a i * (W i).1 j = 0
          rw [← Finset.mul_sum, (W i).2, mul_zero]⟩
      let Ws : ZeroSumNodeVector n :=
        ⟨fun j => ∑ u ∈ s, a u * (W u).1 j, by
          change ∑ j, ∑ u ∈ s, a u * (W u).1 j = 0
          rw [Finset.sum_comm]
          apply Finset.sum_eq_zero
          intro u hu
          rw [← Finset.mul_sum, (W u).2, mul_zero]⟩
      have hsplit :
          (⟨fun j => ∑ u ∈ insert i s, a u * (W u).1 j, by
            change ∑ j, ∑ u ∈ insert i s, a u * (W u).1 j = 0
            rw [Finset.sum_comm]
            apply Finset.sum_eq_zero
            intro u hu
            rw [← Finset.mul_sum, (W u).2, mul_zero]⟩ : ZeroSumNodeVector n) =
            Wi + Ws := by
        apply Subtype.ext
        funext j
        simp [Wi, Ws, hi]
      rw [hsplit, influenceOperator_add]
      have hWi : influenceOperator N t Wi =
          a i * influenceOperator N t (W i) := by
        simpa [Wi] using influenceOperator_smul N t (a i) (W i)
      have hWs : influenceOperator N t Ws =
          ∑ u ∈ s, a u * influenceOperator N t (W u) := by
        simpa [Ws] using ih
      rw [hWi, hWs]
      simp [hi]

/-- The normalized push mass is a simplex vector at every time. -/
theorem normalizedPushMass_mem_stdSimplex
    (N : NetworkSetup n) (t : ℕ) :
    normalizedPushMass N t ∈ stdSimplex ℝ (Fin n) := by
  constructor
  · intro i
    unfold normalizedPushMass
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
      (pushMass_nonneg N t i)
  · exact normalizedPushMass_sum_eq_one N t

/-- The coboundary row has the exact source uniform Euclidean bound. -/
theorem coboundaryRow_nodeL2_le
    (N : NetworkSetup n) (t : ℕ) :
    nodeL2Norm (coboundaryRow N t) ≤ coboundaryBound N := by
  classical
  let r := coboundaryRow N t
  let v := normalizedPushMass N t
  let Z : ZeroSumNodeVector n :=
    ⟨fun j => ∑ i, r i * (coboundaryInput N t i).1 j, by
      change ∑ j, ∑ i, r i * (coboundaryInput N t i).1 j = 0
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro i hi
      rw [← Finset.mul_sum, (coboundaryInput N t i).2, mul_zero]⟩
  have hlinear :
      influenceOperator N t Z = ∑ i, (r i) ^ 2 := by
    have h := influenceOperator_finset_sum_smul
      N t (Finset.univ : Finset (Fin n)) r (coboundaryInput N t)
    simpa [Z, r, coboundaryRow, pow_two] using h
  have hZval : Z.1 = fun j => r j - v j * ∑ i, r i := by
    funext j
    simp only [Z, r, v, coboundaryInput, Subtype.coe_mk]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    simp [mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum]
    rw [← Finset.sum_mul]
  have hv := normalizedPushMass_mem_stdSimplex N t
  have hv_nonneg : ∀ i, 0 ≤ v i := by
    simpa [v] using hv.1
  have hv_sum : ∑ i, v i = 1 := by
    simpa [v] using hv.2
  have hnorm (y : Fin n → ℝ) :
      ‖WithLp.toLp 2 y‖ = nodeL2Norm y := by
    simp [PiLp.norm_eq_of_L2, nodeL2Norm, Real.norm_eq_abs, sq_abs]
  have hvnorm : ‖WithLp.toLp 2 v‖ ≤ 1 := by
    calc
      ‖WithLp.toLp 2 v‖ ≤ ∑ i, ‖v i‖ :=
        dependentProductL2Seminorm_le_sum_norm v
      _ = 1 := by
        simp [Real.norm_eq_abs, abs_of_nonneg (hv_nonneg _), hv_sum]
  have hsumr : |∑ i, r i| ≤ Real.sqrt n * nodeL2Norm r := by
    calc
      |∑ i, r i| ≤ ∑ i, |r i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ Real.sqrt n * nodeL2Norm r := by
        simpa [Real.norm_eq_abs, hnorm] using
          (sum_norm_le_sqrt_card_mul_dependentProductL2Seminorm r)
  have hr_nonneg : 0 ≤ nodeL2Norm r := by
    unfold nodeL2Norm
    exact Real.sqrt_nonneg _
  have hZnorm :
      nodeL2Norm Z.1 ≤ (1 + Real.sqrt n) * nodeL2Norm r := by
    rw [← hnorm, hZval]
    calc
      ‖WithLp.toLp 2 (fun j => r j - v j * ∑ i, r i)‖ =
          ‖WithLp.toLp 2 r - (∑ i, r i) • WithLp.toLp 2 v‖ := by
        congr 1
        ext j
        simp [mul_comm]
      _ ≤ ‖WithLp.toLp 2 r‖ +
          ‖(∑ i, r i) • WithLp.toLp 2 v‖ := norm_sub_le _ _
      _ = nodeL2Norm r + |∑ i, r i| * ‖WithLp.toLp 2 v‖ := by
        rw [norm_smul, Real.norm_eq_abs, hnorm]
      _ ≤ nodeL2Norm r +
          (Real.sqrt n * nodeL2Norm r) * 1 := by
        have hm := mul_le_mul hsumr hvnorm (norm_nonneg _)
          (mul_nonneg (Real.sqrt_nonneg _) hr_nonneg)
        simpa [add_comm] using add_le_add_left hm (nodeL2Norm r)
      _ = (1 + Real.sqrt n) * nodeL2Norm r := by ring
  have hDpos : 0 < influenceOperatorBound N := by
    unfold influenceOperatorBound columnMixingConstant
    exact div_pos
      (div_pos (Real.sqrt_pos.2 (Nat.cast_pos.mpr N.hn))
        (blockContraction_pos N))
      (sub_pos.mpr (mixingRate_lt_one N))
  have henergy :
      nodeL2Norm r ^ 2 ≤ coboundaryBound N * nodeL2Norm r := by
    calc
      nodeL2Norm r ^ 2 = ∑ i, (r i) ^ 2 := by
        unfold nodeL2Norm
        rw [Real.sq_sqrt]
        exact Finset.sum_nonneg fun i _ => sq_nonneg (r i)
      _ = influenceOperator N t Z := hlinear.symm
      _ ≤ |influenceOperator N t Z| := le_abs_self _
      _ ≤ influenceOperatorBound N * nodeL2Norm Z.1 :=
        influenceOperator_norm_le N t Z
      _ ≤ influenceOperatorBound N *
          ((1 + Real.sqrt n) * nodeL2Norm r) :=
        mul_le_mul_of_nonneg_left hZnorm hDpos.le
      _ = coboundaryBound N * nodeL2Norm r := by
        unfold coboundaryBound
        ring
  change nodeL2Norm r ≤ coboundaryBound N
  by_cases hr : nodeL2Norm r = 0
  · rw [hr]
    unfold coboundaryBound
    exact (mul_nonneg (by positivity) hDpos.le)
  · have hrpos : 0 < nodeL2Norm r := lt_of_le_of_ne hr_nonneg (Ne.symm hr)
    nlinarith

/-- The corrected-lift part of the influence row has the same source bound as
the coboundary row. -/
theorem columnInnovationLiftRow_nodeL2_le
    (N : NetworkSetup n) (t : ℕ) :
    nodeL2Norm (fun i =>
      influenceOperator N (t + 1) (columnInnovation N t i)) ≤
      coboundaryBound N := by
  classical
  let c : Fin n → ℝ := fun i =>
    influenceOperator N (t + 1) (columnInnovation N t i)
  let Z : ZeroSumNodeVector n :=
    ⟨fun j => ∑ i, c i * (columnInnovation N t i).1 j, by
      change ∑ j, ∑ i, c i * (columnInnovation N t i).1 j = 0
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro i hi
      rw [← Finset.mul_sum, (columnInnovation N t i).2, mul_zero]⟩
  have hlinear : influenceOperator N (t + 1) Z = ∑ i, (c i) ^ 2 := by
    have h := influenceOperator_finset_sum_smul
      N (t + 1) (Finset.univ : Finset (Fin n)) c (columnInnovation N t)
    simpa [Z, c, pow_two] using h
  have hZval : Z.1 = Matrix.smulVec (N.colMix t) c - c := by
    funext j
    simp only [Z, c, columnInnovation, Subtype.coe_mk, Pi.sub_apply,
      Matrix.smulVec_apply]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    simp [mul_assoc, mul_comm, mul_left_comm]
  have hnorm (y : Fin n → ℝ) :
      ‖WithLp.toLp 2 y‖ = nodeL2Norm y := by
    simp [PiLp.norm_eq_of_L2, nodeL2Norm, Real.norm_eq_abs, sq_abs]
  have hc_nonneg : 0 ≤ nodeL2Norm c := by
    unfold nodeL2Norm
    exact Real.sqrt_nonneg _
  have hsumc : ∑ i, ‖c i‖ ≤ Real.sqrt n * nodeL2Norm c := by
    simpa [hnorm] using
      (sum_norm_le_sqrt_card_mul_dependentProductL2Seminorm c)
  have hZnorm :
      nodeL2Norm Z.1 ≤ (1 + Real.sqrt n) * nodeL2Norm c := by
    rw [← hnorm, hZval]
    calc
      ‖WithLp.toLp 2 (Matrix.smulVec (N.colMix t) c - c)‖ =
          ‖WithLp.toLp 2 (Matrix.smulVec (N.colMix t) c) -
            WithLp.toLp 2 c‖ := by
        congr 1
      _ ≤
          ‖WithLp.toLp 2 (Matrix.smulVec (N.colMix t) c)‖ +
            ‖WithLp.toLp 2 c‖ := norm_sub_le _ _
      _ ≤ FiniteNetwork.stateL1Norm
            (Matrix.smulVec (N.colMix t) c) + nodeL2Norm c := by
        rw [hnorm]
        exact add_le_add
          (by
            have hout := dependentProductL2Seminorm_le_sum_norm
              (Matrix.smulVec (N.colMix t) c)
            rw [hnorm] at hout
            simpa [FiniteNetwork.stateL1Norm_def] using hout) (hnorm c).le
      _ ≤ FiniteNetwork.stateL1Norm c + nodeL2Norm c := by
        exact add_le_add
          (Matrix.stateL1Norm_smulVec_le_of_mem_colStochastic
            c (N.col_stochastic t)) le_rfl
      _ ≤ Real.sqrt n * nodeL2Norm c + nodeL2Norm c := by
        exact add_le_add hsumc le_rfl
      _ = (1 + Real.sqrt n) * nodeL2Norm c := by ring
  have hDpos : 0 < influenceOperatorBound N := by
    unfold influenceOperatorBound columnMixingConstant
    exact div_pos
      (div_pos (Real.sqrt_pos.2 (Nat.cast_pos.mpr N.hn))
        (blockContraction_pos N))
      (sub_pos.mpr (mixingRate_lt_one N))
  have henergy :
      nodeL2Norm c ^ 2 ≤ coboundaryBound N * nodeL2Norm c := by
    calc
      nodeL2Norm c ^ 2 = ∑ i, (c i) ^ 2 := by
        unfold nodeL2Norm
        rw [Real.sq_sqrt]
        exact Finset.sum_nonneg fun i _ => sq_nonneg (c i)
      _ = influenceOperator N (t + 1) Z := hlinear.symm
      _ ≤ |influenceOperator N (t + 1) Z| := le_abs_self _
      _ ≤ influenceOperatorBound N * nodeL2Norm Z.1 :=
        influenceOperator_norm_le N (t + 1) Z
      _ ≤ influenceOperatorBound N *
          ((1 + Real.sqrt n) * nodeL2Norm c) :=
        mul_le_mul_of_nonneg_left hZnorm hDpos.le
      _ = coboundaryBound N * nodeL2Norm c := by
        unfold coboundaryBound
        ring
  change nodeL2Norm c ≤ coboundaryBound N
  by_cases hc : nodeL2Norm c = 0
  · rw [hc]
    unfold coboundaryBound
    exact mul_nonneg (by positivity) hDpos.le
  · have hcpos : 0 < nodeL2Norm c := lt_of_le_of_ne hc_nonneg (Ne.symm hc)
    nlinarith

/-- The full influence row has the exact source uniform Euclidean bound. -/
theorem influenceRow_nodeL2_le
    (N : NetworkSetup n) (t : ℕ) :
    nodeL2Norm (influenceRow N t) ≤ influenceRowBound N := by
  let p := absoluteProbability N (t + 1)
  let c : Fin n → ℝ := fun i =>
    influenceOperator N (t + 1) (columnInnovation N t i)
  have hp := absoluteProbability_mem_stdSimplex N (t + 1)
  have hnorm (y : Fin n → ℝ) :
      ‖WithLp.toLp 2 y‖ = nodeL2Norm y := by
    simp [PiLp.norm_eq_of_L2, nodeL2Norm, Real.norm_eq_abs, sq_abs]
  have hpnorm : nodeL2Norm p ≤ 1 := by
    rw [← hnorm]
    calc
      ‖WithLp.toLp 2 p‖ ≤ ∑ i, ‖p i‖ :=
        dependentProductL2Seminorm_le_sum_norm p
      _ = 1 := by
        simp [p, Real.norm_eq_abs, abs_of_nonneg (hp.1 _), hp.2]
  have hc : nodeL2Norm c ≤ coboundaryBound N := by
    simpa [c] using columnInnovationLiftRow_nodeL2_le N t
  have hrow : influenceRow N t = p + c := by
    funext i
    rfl
  rw [hrow, ← hnorm]
  calc
    ‖WithLp.toLp 2 (p + c)‖ =
        ‖WithLp.toLp 2 p + WithLp.toLp 2 c‖ := by
      congr 1
    _ ≤
        ‖WithLp.toLp 2 p‖ + ‖WithLp.toLp 2 c‖ := norm_add_le _ _
    _ = nodeL2Norm p + nodeL2Norm c := by rw [hnorm, hnorm]
    _ ≤ 1 + coboundaryBound N := add_le_add hpnorm hc
    _ = influenceRowBound N := by
      unfold influenceRowBound coboundaryBound
      ring

/-- Equation (5): the influence row is a constant gain component plus the
discrete coboundary generated by the corrected-lift resolvent. -/
theorem influenceRow_coboundary_identity
    (N : NetworkSetup n) (t : ℕ) (i : Fin n) :
    influenceRow N t i = gain N t / (n : ℝ) +
      coboundaryRow N t i - coboundaryRow N (t + 1) i := by
  classical
  let W := advanceZeroSum N t (coboundaryInput N t i)
  let V := coboundaryInput N (t + 1) i
  let D : ZeroSumNodeVector n :=
    ⟨W.1 - V.1, by
      change ∑ j, (W.1 j - V.1 j) = 0
      rw [Finset.sum_sub_distrib, W.2, V.2, sub_self]⟩
  have hD : columnInnovation N t i = D := by
    apply Subtype.ext
    funext j
    simp [D, W, V, columnInnovation, advanceZeroSum, coboundaryInput,
      normalizedPushMass, pushMass_succ, Matrix.smulVec, Matrix.mulVec,
      dotProduct, Finset.mul_sum, Finset.sum_sub_distrib,
      mul_assoc, mul_comm, mul_left_comm]
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    simp
    ring
  have hWsum : Summable (fun ℓ =>
      FiniteNetwork.periodicCorrectedLiftSeriesTerm
        N.colMix (absoluteProbability N) (t + 1) ℓ W) := by
    simpa [influenceSeriesTerm] using
      influenceSeries_summable N (t + 1) W
  have hVsum : Summable (fun ℓ =>
      FiniteNetwork.periodicCorrectedLiftSeriesTerm
        N.colMix (absoluteProbability N) (t + 1) ℓ V) := by
    simpa [influenceSeriesTerm] using
      influenceSeries_summable N (t + 1) V
  have hlift_sub :
      influenceOperator N (t + 1) (columnInnovation N t i) =
        influenceOperator N (t + 1) W - influenceOperator N (t + 1) V := by
    rw [hD]
    simpa [influenceOperator, D] using
      (FiniteNetwork.periodicCorrectedLift_sub
        N.colMix (absoluteProbability N) (t + 1) W V hWsum hVsum)
  have hdot :
      dotProduct (absoluteProbability N (t + 1))
          (coboundaryInput N t i).1 =
        absoluteProbability N (t + 1) i - gain N t / (n : ℝ) := by
    simp [coboundaryInput, dotProduct, normalizedPushMass, gain,
      Finset.mul_sum, Finset.sum_sub_distrib, div_eq_mul_inv,
      mul_assoc, mul_comm, mul_left_comm]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    simp [mul_assoc, mul_comm, mul_left_comm]
  unfold influenceRow coboundaryRow
  rw [hlift_sub, influenceOperator_resolvent N t (coboundaryInput N t i),
    hdot]
  dsimp [W, V]
  ring

/-- Equation (6): sufficiently long windows carry the displayed influence
energy.  The proof telescopes equation (5), absorbs the two coboundary
endpoints with the source threshold, and applies finite Cauchy--Schwarz on the
node--time product. -/
theorem window_influence_energy_lower
    (N : NetworkSetup n) (k ℓ : ℕ)
    (hℓ : influenceEnergyWindowThreshold N ≤ ℓ) :
    (ℓ : ℝ) * gainFloor N ^ 2 / (4 * (n : ℝ)) ≤
      ∑ j ∈ Finset.Ico k (k + ℓ), influenceEnergy N j := by
  classical
  let S := Finset.Ico k (k + ℓ)
  let r := coboundaryRow N
  let b := influenceRow N
  let g := gainFloor N
  let R := coboundaryBound N
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr N.hn
  have hmu_pos : 0 < mixingMinorization N := by
    unfold mixingMinorization
    split_ifs
    · exact pow_pos ((lt_min_iff).2 ⟨N.ha, by norm_num⟩) _
    · norm_num
  have hg_pos : 0 < g := by
    dsimp [g]
    exact (mul_pos hnR hmu_pos).trans_le
      (gainFloor_ge_n_mul_mixingMinorization N)
  have hℓ_one : 1 ≤ ℓ := by
    exact (le_max_left 1 (Nat.ceil
      (4 * Real.sqrt n * coboundaryBound N / gainFloor N))).trans hℓ
  have hℓR_pos : (0 : ℝ) < ℓ := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hℓ_one)
  have hthreshold : 4 * Real.sqrt n * R ≤ (ℓ : ℝ) * g := by
    have hratio :
        4 * Real.sqrt n * coboundaryBound N / gainFloor N ≤
          (influenceEnergyWindowThreshold N : ℝ) := by
      simpa [influenceEnergyWindowThreshold] using
        (le_positive_ceil_max_one
          (4 * Real.sqrt n * coboundaryBound N / gainFloor N))
    have hcast :
        (influenceEnergyWindowThreshold N : ℝ) ≤ (ℓ : ℝ) := by
      exact_mod_cast hℓ
    have := hratio.trans hcast
    dsimp [R, g]
    exact (div_le_iff₀ hg_pos).mp this
  have htel (i : Fin n) :
      ∑ j ∈ S, b j i =
        ∑ j ∈ S, gain N j / (n : ℝ) + r k i - r (k + ℓ) i := by
    dsimp [S]
    rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    simp_rw [b, r, influenceRow_coboundary_identity]
    simp_rw [add_sub_assoc]
    rw [Finset.sum_add_distrib]
    have htelescope :=
      Finset.sum_range_sub' (fun q => coboundaryRow N (k + q) i) ℓ
    have htelescope' :
        (∑ q ∈ Finset.range ℓ,
            (coboundaryRow N (k + q) i -
              coboundaryRow N (k + q + 1) i)) =
          coboundaryRow N k i - coboundaryRow N (k + ℓ) i := by
      simpa [Nat.add_assoc] using htelescope
    rw [htelescope']
  have htotal :
      (∑ i, ∑ j ∈ S, b j i) =
        (∑ j ∈ S, gain N j) +
          ∑ i, (r k i - r (k + ℓ) i) := by
    calc
      (∑ i, ∑ j ∈ S, b j i) =
          ∑ i, ((∑ j ∈ S, gain N j / (n : ℝ)) +
            r k i - r (k + ℓ) i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact htel i
      _ = (∑ j ∈ S, gain N j) +
          ∑ i, (r k i - r (k + ℓ) i) := by
        simp_rw [add_sub_assoc]
        rw [Finset.sum_add_distrib]
        have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hnR
        simp [hn_ne]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        field_simp [hn_ne]
  have hgain_sum : (ℓ : ℝ) * g ≤ ∑ j ∈ S, gain N j := by
    calc
      (ℓ : ℝ) * g = ∑ j ∈ S, g := by
        simp [S]
      _ ≤ ∑ j ∈ S, gain N j := by
        exact Finset.sum_le_sum fun j _ => gainFloor_le_gain N j
  have hnorm (y : Fin n → ℝ) :
      ‖WithLp.toLp 2 y‖ = nodeL2Norm y := by
    simp [PiLp.norm_eq_of_L2, nodeL2Norm, Real.norm_eq_abs, sq_abs]
  have hend_norm :
      nodeL2Norm (fun i => r k i - r (k + ℓ) i) ≤ 2 * R := by
    rw [← hnorm]
    calc
      ‖WithLp.toLp 2 (fun i => r k i - r (k + ℓ) i)‖ =
          ‖WithLp.toLp 2 (r k) - WithLp.toLp 2 (r (k + ℓ))‖ := by
        congr 1
      _ ≤ ‖WithLp.toLp 2 (r k)‖ +
          ‖WithLp.toLp 2 (r (k + ℓ))‖ := norm_sub_le _ _
      _ = nodeL2Norm (r k) + nodeL2Norm (r (k + ℓ)) := by
        rw [hnorm, hnorm]
      _ ≤ R + R := add_le_add
        (coboundaryRow_nodeL2_le N k)
        (coboundaryRow_nodeL2_le N (k + ℓ))
      _ = 2 * R := by ring
  have hend_abs :
      |∑ i, (r k i - r (k + ℓ) i)| ≤ 2 * Real.sqrt n * R := by
    calc
      |∑ i, (r k i - r (k + ℓ) i)| ≤
          ∑ i, |r k i - r (k + ℓ) i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ Real.sqrt n *
          nodeL2Norm (fun i => r k i - r (k + ℓ) i) := by
        simpa [Real.norm_eq_abs, hnorm] using
          (sum_norm_le_sqrt_card_mul_dependentProductL2Seminorm
            (fun i => r k i - r (k + ℓ) i))
      _ ≤ Real.sqrt n * (2 * R) :=
        mul_le_mul_of_nonneg_left hend_norm (Real.sqrt_nonneg _)
      _ = 2 * Real.sqrt n * R := by ring
  have hend_abs_half :
      |∑ i, (r k i - r (k + ℓ) i)| ≤ (ℓ : ℝ) * g / 2 := by
    linarith
  have htotal_lower :
      (ℓ : ℝ) * g / 2 ≤ ∑ i, ∑ j ∈ S, b j i := by
    rw [htotal]
    have hneg := neg_abs_le (∑ i, (r k i - r (k + ℓ) i))
    linarith
  have hsquare_lower :
      ((ℓ : ℝ) * g / 2) ^ 2 ≤
        (∑ i, ∑ j ∈ S, b j i) ^ 2 := by
    have hlower_nonneg : 0 ≤ (ℓ : ℝ) * g / 2 := by positivity
    have htotal_nonneg : 0 ≤ ∑ i, ∑ j ∈ S, b j i :=
      hlower_nonneg.trans htotal_lower
    exact (sq_le_sq₀ hlower_nonneg htotal_nonneg).2 htotal_lower
  have hsquare_upper :
      (∑ i, ∑ j ∈ S, b j i) ^ 2 ≤
        ((n : ℝ) * (ℓ : ℝ)) *
          (∑ j ∈ S, influenceEnergy N j) := by
    have hcs := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin n)).product S)
      (f := fun p : Fin n × ℕ => b p.2 p.1)
    have hcs' :
        (∑ i, ∑ j ∈ S, b j i) ^ 2 ≤
          ((n : ℝ) * (ℓ : ℝ)) *
            (∑ i, ∑ j ∈ S, (b j i) ^ 2) := by
      simpa [S, Finset.sum_product, Nat.cast_mul, mul_assoc] using hcs
    calc
      (∑ i, ∑ j ∈ S, b j i) ^ 2 ≤
          ((n : ℝ) * (ℓ : ℝ)) *
            (∑ i, ∑ j ∈ S, (b j i) ^ 2) := hcs'
      _ = ((n : ℝ) * (ℓ : ℝ)) *
          (∑ j ∈ S, influenceEnergy N j) := by
        congr 1
        rw [Finset.sum_comm]
        simp [b, influenceEnergy]
  have hmain := hsquare_lower.trans hsquare_upper
  have hden : 0 < 4 * (n : ℝ) := mul_pos (by norm_num) hnR
  apply (div_le_iff₀ hden).2
  nlinarith

/-- Equations (2)--(6), including the limit definition of `π`, zero-sum
series convergence and resolvent identity for `D`, all displayed uniform
constants and norm bounds, the coboundary identity, and the explicit `ℓ_q`
interval-energy threshold. -/
theorem uniform_mixing_and_influence (N : NetworkSetup n) :
    0 < mixingRate N ∧ mixingRate N < 1 ∧
    (∀ k : ℕ,
      Filter.Tendsto
        (fun t => uniformRow n ᵥ* forwardProduct N.rowMix t k)
        Filter.atTop (nhds (absoluteProbability N k))) ∧
    (∀ t i, mixingMinorization N ≤ absoluteProbability N t i) ∧
    (∀ t k : ℕ, k ≤ t → ∀ z : Fin n → ℝ, (∑ i, z i) = 0 →
      nodeL2Norm ((forwardProduct N.colMix t k) *ᵥ z) ≤
        columnMixingConstant N * mixingRate N ^ (t - k) * nodeL2Norm z) ∧
    (∀ t k : ℕ, k ≤ t → ∀ x : Fin n → ℝ,
      nodeL2Norm (disagreement ((forwardProduct N.rowMix t k) *ᵥ x)) ≤
        rowMixingConstant N * mixingRate N ^ (t - k) *
          nodeL2Norm (disagreement x)) ∧
    (∀ t (z : ZeroSumNodeVector n),
      Summable (fun ℓ => influenceSeriesTerm N t ℓ z) ∧
      HasSum (fun ℓ => influenceSeriesTerm N t ℓ z)
        (influenceOperator N t z) ∧
      |influenceOperator N t z| ≤
        influenceOperatorBound N * nodeL2Norm z.1 ∧
      influenceOperator N t z =
        dotProduct (absoluteProbability N (t + 1)) z.1 +
          influenceOperator N (t + 1) (advanceZeroSum N t z)) ∧
    0 < gainFloor N ∧
    (∀ t, gainFloor N ≤ gain N t ∧ gain N t ≤ n) ∧
    (1 < n → n * mixingMinorization N ≤ gainFloor N) ∧
    (n = 1 → ∀ t, gain N t = 1) ∧
    (∀ t i, influenceRow N t i = gain N t / n +
      coboundaryRow N t i - coboundaryRow N (t + 1) i) ∧
    (∀ t, nodeL2Norm (coboundaryRow N t) ≤ coboundaryBound N) ∧
    (∀ t, nodeL2Norm (influenceRow N t) ≤ influenceRowBound N) ∧
    0 < influenceEnergyWindowThreshold N ∧
    ∀ k ℓ : ℕ, influenceEnergyWindowThreshold N ≤ ℓ →
      ℓ * gainFloor N ^ 2 / (4 * n) ≤
        ∑ j ∈ Finset.Ico k (k + ℓ), influenceEnergy N j := by
  have hrate_pos : 0 < mixingRate N := by
    unfold mixingRate
    exact Real.rpow_pos_of_pos (blockContraction_pos N) _
  refine ⟨hrate_pos, mixingRate_lt_one N, absoluteProbability_tendsto N, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact absolute_probability_ge_mixingMinorization N
  · intro t k hkt z hz
    exact scalar_colMix_nodeL2_geometric N t k hkt z hz
  · intro t k hkt x
    exact rowMix_disagreement_nodeL2_geometric N t k hkt x
  · intro t z
    exact ⟨influenceSeries_summable N t z, influenceOperator_hasSum N t z,
      influenceOperator_norm_le N t z, influenceOperator_resolvent N t z⟩
  · have hmu_pos : 0 < mixingMinorization N := by
      unfold mixingMinorization
      split_ifs
      · exact pow_pos ((lt_min_iff).2 ⟨N.ha, by norm_num⟩) _
      · norm_num
    exact (mul_pos (Nat.cast_pos.mpr N.hn) hmu_pos).trans_le
      (gainFloor_ge_n_mul_mixingMinorization N)
  · intro t
    exact ⟨gainFloor_le_gain N t, gain_le_n N t⟩
  · intro _hn
    exact gainFloor_ge_n_mul_mixingMinorization N
  · intro hn1 t
    exact gain_eq_one_of_n_eq_one N hn1 t
  · intro t i
    exact influenceRow_coboundary_identity N t i
  · exact coboundaryRow_nodeL2_le N
  · exact influenceRow_nodeL2_le N
  · unfold influenceEnergyWindowThreshold
    exact lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  · intro k ℓ hℓ
    exact window_influence_energy_lower N k ℓ hℓ

/-- The tracker aggregate equals the current oracle aggregate at every time. -/
theorem tracker_sum_eq_sampledOracle_sum
    (S : Setup n d Ω) (ω : Ω) (α : ℝ) (t : ℕ) :
    ∑ i, tracker S ω α t i = ∑ i, sampledOracle S ω α t i := by
  classical
  induction t with
  | zero =>
      rw [tracker_zero]
  | succ t ih =>
      rw [tracker_succ]
      simp only [leftAct, Pi.add_apply, Pi.sub_apply, Finset.sum_add_distrib,
        Finset.sum_sub_distrib]
      rw [Matrix.sum_smulVec_of_mem_colStochastic _ (S.col_stochastic t), ih,
        add_sub_cancel_left]

/-! ## Canonical retained-tracker loading construction, equations (21)--(40) -/

/-- The positive-half derivative in the compactly supported potential (31).
Book `#/key_lemmas/3/proof/15/math`:
“`V_D'(x)=L\begin{cases}x,&0\le x\le D/2,\\D-x,&D/2\le x\le3D/2,
\\x-2D,&3D/2\le x\le2D,\\0,&x\ge2D.\end{cases}`”. -/
def negativeCurvatureDerivativePositive (L D x : ℝ) : ℝ :=
  L * if x ≤ D / 2 then x
    else if x ≤ 3 * D / 2 then D - x
    else if x ≤ 2 * D then x - 2 * D else 0

/-- The odd extension of the displayed derivative `V_D'` from (31). Book
`#/key_lemmas/3/proof/15/description`:
“Fix D>0, define the even flat-tailed storage potential, and verify from its
printed derivative that it is nonnegative, globally L-smooth,
bounded-gradient, and exactly negative quadratic on [D/2,3D/2].” -/
def negativeCurvatureDerivative (L D x : ℝ) : ℝ :=
  if x < 0 then -negativeCurvatureDerivativePositive L D (-x)
  else negativeCurvatureDerivativePositive L D x

/-- The printed piecewise-linear storage derivative is continuous.  This is
the finite-recursion regularity input needed for the equation-(38)
calibration map; no trajectory regularity is assumed. -/
theorem negative_curvature_derivative_continuous (L D : ℝ)
    (hD : 0 ≤ D) :
    Continuous (negativeCurvatureDerivative L D) := by
  have h₁ : Continuous (fun x : ℝ => L * x) :=
    continuous_const.mul continuous_id
  have h₂ : Continuous (fun x : ℝ => L * (D - x)) :=
    continuous_const.mul (continuous_const.sub continuous_id)
  have h₃ : Continuous (fun x : ℝ => L * (x - 2 * D)) :=
    continuous_const.mul (continuous_id.sub continuous_const)
  have h₀ : Continuous (fun _x : ℝ => (0 : ℝ)) := continuous_const
  have h₃₀ : Continuous (fun x : ℝ =>
      if x ≤ 2 * D then L * (x - 2 * D) else 0) := by
    exact h₃.if_le h₀ continuous_id continuous_const (by
      intro x hx
      rw [hx]
      ring)
  have h₂₃₀ : Continuous (fun x : ℝ =>
      if x ≤ 3 * D / 2 then L * (D - x)
      else if x ≤ 2 * D then L * (x - 2 * D) else 0) := by
    exact h₂.if_le h₃₀ continuous_id continuous_const (by
      intro x hx
      change x = 3 * D / 2 at hx
      subst x
      have hle : 3 * D / 2 ≤ 2 * D := by linarith
      rw [if_pos hle]
      ring)
  have hpos : Continuous (negativeCurvatureDerivativePositive L D) := by
    unfold negativeCurvatureDerivativePositive
    simpa only [mul_ite, mul_zero] using
      h₁.if_le h₂₃₀ continuous_id continuous_const (by
      intro x hx
      change x = D / 2 at hx
      subst x
      have hle : D / 2 ≤ 3 * D / 2 := by linarith
      rw [if_pos hle]
      ring)
  have hneg : Continuous (fun x : ℝ =>
      -negativeCurvatureDerivativePositive L D (-x)) :=
    (hpos.comp continuous_id.neg).neg
  have hwhole : Continuous (fun x : ℝ =>
      if (0 : ℝ) ≤ x then negativeCurvatureDerivativePositive L D x
      else -negativeCurvatureDerivativePositive L D (-x)) := by
    exact hpos.if_le hneg continuous_const continuous_id (by
      intro x hx
      change (0 : ℝ) = x at hx
      subst x
      have hhalf : (0 : ℝ) ≤ D / 2 := by linarith
      simp [negativeCurvatureDerivativePositive, hhalf])
  convert hwhole using 1
  funext x
  unfold negativeCurvatureDerivative
  by_cases hx : x < 0
  · simp [hx, not_le.mpr hx]
  · simp [hx, le_of_not_gt hx]

theorem negativeCurvatureDerivative_zero (L D : ℝ) :
    negativeCurvatureDerivative L D 0 = 0 := by
  unfold negativeCurvatureDerivative negativeCurvatureDerivativePositive
  simp only [lt_self_iff_false, if_false]
  by_cases hhalf : 0 ≤ D / 2
  · simp [hhalf]
  · have hDneg : D < 0 := by linarith
    simp [hhalf, show ¬0 ≤ 3 * D / 2 by linarith,
      show ¬0 ≤ 2 * D by linarith]

/-- The printed storage derivative is globally bounded by `LD/2`.  This is
the bounded nonlinear input used in the loading variation-of-constants
estimate (34); it does not require the trajectory to have entered a shoulder. -/
theorem abs_negativeCurvatureDerivative_le
    (L D x : ℝ) (hL : 0 ≤ L) (hD : 0 ≤ D) :
    |negativeCurvatureDerivative L D x| ≤ L * D / 2 := by
  have hpositive (y : ℝ) (hy : 0 ≤ y) :
      |negativeCurvatureDerivativePositive L D y| ≤ L * D / 2 := by
    unfold negativeCurvatureDerivativePositive
    split_ifs with hhalf hthree htwo
    · rw [abs_mul, abs_of_nonneg hL, abs_of_nonneg hy]
      simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left hhalf hL
    · have hy_lower : D / 2 ≤ y := le_of_not_ge hhalf
      have hinner : |D - y| ≤ D / 2 := by
        rw [abs_le]
        constructor <;> linarith
      rw [abs_mul, abs_of_nonneg hL]
      simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left hinner hL
    · have hy_lower : 3 * D / 2 ≤ y := le_of_not_ge hthree
      have hinner : |y - 2 * D| ≤ D / 2 := by
        rw [abs_le]
        constructor <;> linarith
      rw [abs_mul, abs_of_nonneg hL]
      simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left hinner hL
    · simp only [mul_zero, abs_zero]
      positivity
  unfold negativeCurvatureDerivative
  split_ifs with hx
  · rw [abs_neg]
    exact hpositive (-x) (by linarith)
  · exact hpositive x (le_of_not_gt hx)

/-- Either source shoulder is uniformly separated from the zero of the
negative-quadratic branch, hence carries the equation-(40) derivative floor. -/
theorem negativeCurvatureDerivative_ge_on_safe_shoulders
    (L D x : ℝ) (hL : 0 < L) (hD : 0 < D)
    (hx : (D / 2 ≤ x ∧ x ≤ 15 * D / 16) ∨
      (17 * D / 16 ≤ x ∧ x ≤ 3 * D / 2)) :
    L * D / 16 ≤ |negativeCurvatureDerivative L D x| := by
  have hxpos : 0 < x := by
    rcases hx with hx | hx <;> nlinarith [hD]
  rw [negativeCurvatureDerivative, if_neg (not_lt_of_ge hxpos.le)]
  unfold negativeCurvatureDerivativePositive
  rcases hx with hleft | hright
  · by_cases hhalf : x ≤ D / 2
    · have hxeq : x = D / 2 := le_antisymm hhalf hleft.1
      rw [if_pos hhalf, abs_mul, abs_of_pos hL, hxeq,
        abs_of_pos (by linarith : 0 < D / 2)]
      nlinarith [hL, hD]
    · have hthree : x ≤ 3 * D / 2 := by nlinarith [hleft.2, hD]
      rw [if_neg hhalf, if_pos hthree, abs_mul, abs_of_pos hL,
        abs_of_nonneg (by nlinarith [hleft.2] : 0 ≤ D - x)]
      nlinarith [hL, hD, hleft.2]
  · have hhalf : ¬x ≤ D / 2 := by nlinarith [hright.1, hD]
    have hthree : x ≤ 3 * D / 2 := hright.2
    rw [if_neg hhalf, if_pos hthree, abs_mul, abs_of_pos hL,
      abs_of_nonpos (by nlinarith [hright.1] : D - x ≤ 0)]
    nlinarith [hL, hD, hright.1]

/-- Exact formula on the negative-quadratic branch used in equations
(21)--(28). -/
theorem negativeCurvatureDerivative_eq_negative_branch
    (L D x : ℝ) (hD : 0 < D) (hx_lo : D / 2 ≤ x)
    (hx_hi : x ≤ 3 * D / 2) :
    negativeCurvatureDerivative L D x = L * (D - x) := by
  have hxpos : 0 < x := by nlinarith
  rw [negativeCurvatureDerivative, if_neg (not_lt_of_ge hxpos.le)]
  unfold negativeCurvatureDerivativePositive
  by_cases hhalf : x ≤ D / 2
  · have hxeq : x = D / 2 := le_antisymm hhalf hx_lo
    rw [if_pos hhalf, hxeq]
    ring
  · rw [if_neg hhalf, if_pos hx_hi]

/-- The source's even flat-tailed potential `V_D`, normalized by `V_D(0)=0`.
Book `#/key_lemmas/3/proof/15/description`:
“Fix D>0, define the even flat-tailed storage potential, and verify from its
printed derivative that it is nonnegative, globally L-smooth,
bounded-gradient, and exactly negative quadratic on [D/2,3D/2].” -/
def negativeCurvaturePotential (L D x : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..x, negativeCurvatureDerivative L D y

/-- A single node-time pulse, with no tracker reset. Book
`#/key_lemmas/3/proof/17/description`:
“For a flat objective and one node-time pulse, define both exact network
kernels and their responses; conservation of the corrected center identifies
the final displacement d=-alpha b_{j,i}e.” -/
def loadingPulse (j : ℕ) (i : Fin n) (e : ℝ) (t : ℕ) : Fin n → ℝ :=
  fun k => if t = j ∧ k = i then e else 0

/-- Lean realization of the source derivative plus its one node-time pulse.
It introduces no independent oracle witness; see
`#/key_lemmas/3/proof/15/math` for `V_D'` and
`#/key_lemmas/3/proof/17/description` for “one node-time pulse”. -/
def loadingOracle (L D : ℝ) (j : ℕ) (i : Fin n) (e : ℝ)
    (t : ℕ) (X : Fin n → ℝ) : Fin n → ℝ :=
  fun k => negativeCurvatureDerivative L D (X k) + loadingPulse j i e t k

/-- After the unique pulse time, branch membership rewrites the actual loading
oracle to the affine negative-curvature formula, with no tracker reset. -/
theorem loadingOracle_eq_negative_branch
    (L D : ℝ) (j t : ℕ) (i : Fin n) (e : ℝ) (X : Fin n → ℝ)
    (hD : 0 < D) (hjt : j < t)
    (hbranch : ∀ q, D / 2 ≤ X q ∧ X q ≤ 3 * D / 2) :
    loadingOracle L D j i e t X = fun q => L * (D - X q) := by
  funext q
  unfold loadingOracle loadingPulse
  rw [negativeCurvatureDerivative_eq_negative_branch L D (X q) hD
    (hbranch q).1 (hbranch q).2]
  simp [ne_of_gt hjt]

/-- The actual scalar Push--Pull state driven by the source pulse. Book
`#/algorithm_spec/steps/0/math`: “`X_{t+1}=R_tX_t-\alpha_TY_t`”; Book
`#/algorithm_spec/steps/1/math`: “`Y_{t+1}=C_tY_t+G_{t+1}-G_t`”. -/
def loadingTrajectory (N : NetworkSetup n) (L D s : ℝ)
    (j : ℕ) (i : Fin n) (e : ℝ) : ℕ → SOptLib.PushPullState (Fin n) ℝ
  | 0 =>
      { primal := 0
        tracker := loadingOracle L D j i e 0 0 }
  | t + 1 =>
      SOptLib.pushPullStep Matrix.smulVec N.rowMix N.colMix (s / L)
        (loadingOracle L D j i e) t (loadingTrajectory N L D s j i e t)

/-- Every coordinate of the genuine finite loading recursion is continuous in
the pulse amplitude.  This follows from the exact `pushPullStep`, not from the
linear reference orbit used later in equation (38). -/
theorem loading_trajectory_continuous_in_pulse
    (N : NetworkSetup n) (L D s : ℝ) (j : ℕ) (i : Fin n)
    (hD : 0 ≤ D) (t : ℕ) :
    (∀ q, Continuous (fun e : ℝ =>
      (loadingTrajectory N L D s j i e t).primal q)) ∧
    (∀ q, Continuous (fun e : ℝ =>
      (loadingTrajectory N L D s j i e t).tracker q)) := by
  have hderiv : Continuous (negativeCurvatureDerivative L D) :=
    negative_curvature_derivative_continuous L D hD
  induction t with
  | zero =>
      constructor
      · intro q
        simpa [loadingTrajectory] using
          (continuous_const : Continuous (fun _e : ℝ => (0 : ℝ)))
      · intro q
        by_cases hpulse : 0 = j ∧ q = i
        · simpa [loadingTrajectory, loadingOracle, loadingPulse, hpulse,
            negativeCurvatureDerivative_zero] using
            continuous_id
        · simpa [loadingTrajectory, loadingOracle, loadingPulse, hpulse,
            negativeCurvatureDerivative_zero] using
            (continuous_const : Continuous (fun _e : ℝ => (0 : ℝ)))
  | succ t ih =>
      have hrow (q : Fin n) : Continuous (fun e : ℝ =>
          (N.rowMix t *ᵥ
            (loadingTrajectory N L D s j i e t).primal) q) := by
        simp only [Matrix.smulVec, Matrix.mulVec, dotProduct, smul_eq_mul]
        exact continuous_finset_sum _ (fun r _ =>
          continuous_const.mul (ih.1 r))
      have hcol (q : Fin n) : Continuous (fun e : ℝ =>
          (N.colMix t *ᵥ
            (loadingTrajectory N L D s j i e t).tracker) q) := by
        simp only [Matrix.smulVec, Matrix.mulVec, dotProduct, smul_eq_mul]
        exact continuous_finset_sum _ (fun r _ =>
          continuous_const.mul (ih.2 r))
      have hnext (q : Fin n) : Continuous (fun e : ℝ =>
          (N.rowMix t *ᵥ
              (loadingTrajectory N L D s j i e t).primal) q -
            (s / L) *
              (loadingTrajectory N L D s j i e t).tracker q) :=
        (hrow q).sub (continuous_const.mul (ih.2 q))
      have horacle (u : ℕ) (Z : ℝ → Fin n → ℝ)
          (hZ : ∀ q, Continuous (fun e : ℝ => Z e q)) (q : Fin n) :
          Continuous (fun e : ℝ => loadingOracle L D j i e u (Z e) q) := by
        have hpulse : Continuous (fun e : ℝ => loadingPulse j i e u q) := by
          by_cases h : u = j ∧ q = i
          · simpa [loadingPulse, h] using continuous_id
          · simpa [loadingPulse, h] using
              (continuous_const : Continuous (fun _e : ℝ => (0 : ℝ)))
        exact (hderiv.comp (hZ q)).add hpulse
      constructor
      · intro q
        simpa [loadingTrajectory, SOptLib.pushPullStep, smul_eq_mul] using
          hnext q
      · intro q
        have hcurrent := horacle t
          (fun e => (loadingTrajectory N L D s j i e t).primal) ih.1 q
        have hnew := horacle (t + 1)
          (fun e r =>
            (N.rowMix t *ᵥ
                (loadingTrajectory N L D s j i e t).primal) r -
              (s / L) *
                (loadingTrajectory N L D s j i e t).tracker r)
          hnext q
        simpa [loadingTrajectory, SOptLib.pushPullStep, smul_eq_mul] using
          ((hcol q).add hnew).sub hcurrent

/-- The retained tracker `V_t^{tr}=Y_t-G_t` from (32). Book
`#/key_lemmas/3/proof/16/description`:
“Retain the true tracker V_t^{tr}=Y_t-G_t and rewrite the exact algorithm for
arbitrary gradient and noise inputs.” -/
def retainedLoadingTracker (N : NetworkSetup n) (L D s : ℝ)
    (j : ℕ) (i : Fin n) (e : ℝ) (t : ℕ) : Fin n → ℝ :=
  (loadingTrajectory N L D s j i e t).tracker -
    loadingOracle L D j i e t (loadingTrajectory N L D s j i e t).primal

/-- Exact retained-tracker successor identity (32), specialized to the
canonical loading trajectory. -/
theorem retained_loading_tracker_succ
    (N : NetworkSetup n) (L D s : ℝ) (j : ℕ) (i : Fin n) (e : ℝ) (t : ℕ) :
    retainedLoadingTracker N L D s j i e (t + 1) =
      N.colMix t *ᵥ retainedLoadingTracker N L D s j i e t +
        (N.colMix t - 1) *ᵥ
          (fun k => negativeCurvatureDerivative L D
            ((loadingTrajectory N L D s j i e t).primal k) +
            loadingPulse j i e t k) := by
  classical
  funext k
  simp only [retainedLoadingTracker, loadingTrajectory, SOptLib.pushPullStep,
    loadingOracle, Pi.sub_apply, Pi.add_apply, Matrix.sub_mulVec,
    Matrix.one_mulVec]
  simp only [Matrix.smulVec, Matrix.mulVec, dotProduct, smul_eq_mul]
  simp only [Pi.sub_apply, Pi.add_apply, loadingOracle]
  simp_rw [mul_sub, mul_add]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

/-- Exact shifted negative-branch recurrence (21) for the actual loading
trajectory and its retained tracker.  The branch hypothesis is nodewise and
the unique pulse is required to be in the past. -/
theorem loading_negative_branch_shifted_recurrence
    (N : NetworkSetup n) (L D s : ℝ) (j : ℕ) (i : Fin n) (e : ℝ) (t : ℕ)
    (hL : 0 < L) (hD : 0 < D) (hjt : j < t)
    (hbranch : ∀ q,
      D / 2 ≤ (loadingTrajectory N L D s j i e t).primal q ∧
      (loadingTrajectory N L D s j i e t).primal q ≤ 3 * D / 2) :
    (fun q => (loadingTrajectory N L D s j i e (t + 1)).primal q - D) =
        (fun q =>
          (N.rowMix t *ᵥ
            (fun r => (loadingTrajectory N L D s j i e t).primal r - D)) q +
          s * ((loadingTrajectory N L D s j i e t).primal q - D) +
          s * (-retainedLoadingTracker N L D s j i e t q / L)) ∧
    (fun q => -retainedLoadingTracker N L D s j i e (t + 1) q / L) =
        (fun q =>
          (N.colMix t *ᵥ
            (fun r => -retainedLoadingTracker N L D s j i e t r / L)) q +
          ((N.colMix t - 1) *ᵥ
            (fun r => (loadingTrajectory N L D s j i e t).primal r - D)) q) := by
  let X : Fin n → ℝ := (loadingTrajectory N L D s j i e t).primal
  let V : Fin n → ℝ := retainedLoadingTracker N L D s j i e t
  have hG : loadingOracle L D j i e t X = fun q => L * (D - X q) :=
    loadingOracle_eq_negative_branch L D j t i e X hD hjt (by
      intro q
      simpa [X] using hbranch q)
  have htracker :
      (loadingTrajectory N L D s j i e t).tracker =
        V + loadingOracle L D j i e t X := by
    funext q
    dsimp [V, retainedLoadingTracker, X]
    ring
  have hLne : L ≠ 0 := ne_of_gt hL
  constructor
  · funext q
    have hrow_sum : ∑ r, N.rowMix t q r = 1 :=
      Matrix.sum_row_of_mem_rowStochastic (N.row_stochastic t) q
    change
      (N.rowMix t *ᵥ X) q - (s / L) *
          (loadingTrajectory N L D s j i e t).tracker q - D = _
    rw [htracker]
    simp only [Pi.add_apply, hG]
    change
      (N.rowMix t *ᵥ X) q - (s / L) * (V q + L * (D - X q)) - D =
        (N.rowMix t *ᵥ (fun r => X r - D)) q +
          s * (X q - D) + s * (-V q / L)
    simp only [Matrix.mulVec, dotProduct]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hrow_sum]
    field_simp [hLne]
    ring
  · rw [retained_loading_tracker_succ]
    change
      (fun q => -((Matrix.smulVec (N.colMix t) V +
          Matrix.smulVec (N.colMix t - 1) (loadingOracle L D j i e t X) :
            Fin n → ℝ) q) / L) = _
    rw [hG]
    funext q
    change
      -((Matrix.smulVec (N.colMix t) V +
          Matrix.smulVec (N.colMix t - 1) (fun r => L * (D - X r)) :
            Fin n → ℝ) q) / L = _
    simp only [Pi.add_apply, Matrix.smulVec, Matrix.mulVec, dotProduct]
    dsimp [V, X]
    field_simp [hLne]
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, neg_add]
    rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    field_simp [hLne]
    ring

/-- The retained loading tracker is exactly the canonical zero-initial
time-varying innovation response.  This exposes equation (32) through the
reusable SOptLib recurrence rather than as paper-local recursion syntax. -/
theorem retainedLoadingTracker_eq_trackerInnovationResponse
    (N : NetworkSetup n) (L D s : ℝ) (j : ℕ) (i : Fin n) (e : ℝ) (t : ℕ) :
    retainedLoadingTracker N L D s j i e t =
      FiniteNetwork.trackerInnovationResponse N.colMix
        (fun r => loadingOracle L D j i e r
          (loadingTrajectory N L D s j i e r).primal) t := by
  induction t with
  | zero =>
      rw [FiniteNetwork.trackerInnovationResponse_zero]
      simp [retainedLoadingTracker, loadingTrajectory]
  | succ t ih =>
      rw [retained_loading_tracker_succ, ih,
        FiniteNetwork.trackerInnovationResponse_succ_sub_one]
      rfl

/-- Linearity of the canonical innovation response in its driving table. -/
theorem trackerInnovationResponse_add_scalar
    (C : ℕ → NetworkMatrix n) (U V : ℕ → Fin n → ℝ) (t : ℕ) :
    FiniteNetwork.trackerInnovationResponse C (fun r => U r + V r) t =
      FiniteNetwork.trackerInnovationResponse C U t +
        FiniteNetwork.trackerInnovationResponse C V t := by
  induction t with
  | zero =>
      simp only [FiniteNetwork.trackerInnovationResponse_zero, add_zero]
  | succ t ih =>
      rw [FiniteNetwork.trackerInnovationResponse_succ,
        FiniteNetwork.trackerInnovationResponse_succ,
        FiniteNetwork.trackerInnovationResponse_succ, ih]
      funext k
      simp only [Matrix.smulVec, Matrix.mulVec, dotProduct, Pi.add_apply,
        Pi.sub_apply, Finset.sum_add_distrib, smul_add]
      abel

/-- Exact nonlinear/pulse superposition of the retained loading tracker. -/
theorem retainedLoadingTracker_eq_nonlinearResponse_add_pulseResponse
    (N : NetworkSetup n) (L D s : ℝ) (j : ℕ) (i : Fin n) (e : ℝ) (t : ℕ) :
    retainedLoadingTracker N L D s j i e t =
      FiniteNetwork.trackerInnovationResponse N.colMix
          (fun r k => negativeCurvatureDerivative L D
            ((loadingTrajectory N L D s j i e r).primal k)) t +
        FiniteNetwork.trackerInnovationResponse N.colMix
          (fun r => loadingPulse j i e r) t := by
  rw [retainedLoadingTracker_eq_trackerInnovationResponse]
  change FiniteNetwork.trackerInnovationResponse N.colMix
      (fun r =>
        (fun k => negativeCurvatureDerivative L D
          ((loadingTrajectory N L D s j i e r).primal k)) +
          loadingPulse j i e r) t = _
  exact trackerInnovationResponse_add_scalar N.colMix _ _ t

/-- Exact finite variation-of-constants formula for the canonical tracker
innovation response.  This is the algebraic input to the geometric estimate
in source equation (34). -/
theorem trackerInnovationResponse_eq_sum_forwardProduct
    (C : ℕ → NetworkMatrix n) (U : ℕ → Fin n → ℝ) (t : ℕ) :
    FiniteNetwork.trackerInnovationResponse C U t =
      ∑ r ∈ Finset.range t,
        Matrix.smulVec (forwardProduct C t (r + 1))
          (Matrix.smulVec (C r - 1) (U r)) := by
  classical
  induction t with
  | zero =>
      rw [FiniteNetwork.trackerInnovationResponse_zero]
      simp
  | succ t ih =>
      rw [FiniteNetwork.trackerInnovationResponse_succ_sub_one, ih,
        Finset.sum_range_succ]
      have hprop (r : ℕ) (hr : r ∈ Finset.range t) :
          C t * forwardProduct C t (r + 1) =
            forwardProduct C (t + 1) (r + 1) := by
        have hrlt : r < t := Finset.mem_range.mp hr
        unfold forwardProduct
        rw [show t + 1 - (r + 1) = (t - (r + 1)) + 1 by
          omega, FiniteNetwork.consecutiveProduct_succ,
          show r + 1 + (t - (r + 1)) = t by omega]
      have hdistrib :
          Matrix.smulVec (C t) (∑ r ∈ Finset.range t,
              Matrix.smulVec (forwardProduct C t (r + 1))
                (Matrix.smulVec (C r - 1) (U r))) =
            ∑ r ∈ Finset.range t,
              Matrix.smulVec (C t)
                (Matrix.smulVec (forwardProduct C t (r + 1))
                  (Matrix.smulVec (C r - 1) (U r))) := by
        funext q
        simp only [Matrix.smulVec_apply, Finset.sum_apply,
          Finset.smul_sum]
        rw [Finset.sum_comm]
      have haction (A B : NetworkMatrix n) (X : Fin n → ℝ) :
          Matrix.smulVec (A * B) X =
            Matrix.smulVec A (Matrix.smulVec B X) := by
        funext q
        simp only [Matrix.smulVec_apply, Matrix.mul_apply, Finset.smul_sum,
          Finset.sum_smul, mul_smul]
        rw [Finset.sum_comm]
      rw [hdistrib]
      congr 1
      · apply Finset.sum_congr rfl
        intro r hr
        rw [← haction, hprop r hr]
      · unfold forwardProduct
        rw [Nat.sub_self, FiniteNetwork.consecutiveProduct_zero]
        funext q
        simp [Matrix.smulVec_apply, Matrix.one_apply]

/-- A uniformly bounded scalar driving table generates a uniformly bounded
zero-sum tracker response.  This is the column-mixing half of equation (34). -/
theorem trackerInnovationResponse_nodeL1_le_of_uniform
    (N : NetworkSetup n) (U : ℕ → Fin n → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hU : ∀ r q, |U r q| ≤ M) (t : ℕ) :
    FiniteNetwork.stateL1Norm
        (FiniteNetwork.trackerInnovationResponse N.colMix U t) ≤
      ((blockContraction N)⁻¹ * (2 * (n : ℝ) * M)) /
        (1 - mixingRate N) := by
  classical
  have hdelta : 0 ≤ (blockContraction N)⁻¹ := by
    exact inv_nonneg.mpr (blockContraction_pos N).le
  have hrho : 0 ≤ mixingRate N := mixingRate_nonneg N
  have hrho_lt : mixingRate N < 1 := mixingRate_lt_one N
  have hsource (r : ℕ) :
      FiniteNetwork.stateL1Norm (U r) ≤ (n : ℝ) * M := by
    rw [FiniteNetwork.stateL1Norm_def]
    calc
      (∑ q : Fin n, ‖U r q‖) ≤ ∑ _q : Fin n, M := by
        exact Finset.sum_le_sum fun q _ => by
          simpa [Real.norm_eq_abs] using hU r q
      _ = (n : ℝ) * M := by simp
  have hinnovation (r : ℕ) :
      FiniteNetwork.stateL1Norm
          (Matrix.smulVec (N.colMix r - 1) (U r)) ≤
        2 * (n : ℝ) * M := by
    rw [Matrix.sub_one_smulVec]
    rw [FiniteNetwork.stateL1Norm_def]
    calc
      (∑ q : Fin n, ‖Matrix.smulVec (N.colMix r) (U r) q - U r q‖) ≤
          (∑ q : Fin n, ‖Matrix.smulVec (N.colMix r) (U r) q‖) +
            ∑ q : Fin n, ‖U r q‖ := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun q _ => norm_sub_le _ _
      _ ≤ FiniteNetwork.stateL1Norm (U r) +
            FiniteNetwork.stateL1Norm (U r) := by
        exact add_le_add
          (Matrix.stateL1Norm_smulVec_le_of_mem_colStochastic
            (U r) (N.col_stochastic r)) le_rfl
      _ ≤ ((n : ℝ) * M) + (n : ℝ) * M := by
        exact add_le_add (hsource r) (hsource r)
      _ = 2 * (n : ℝ) * M := by ring
  have hterm (r : ℕ) (hr : r ∈ Finset.range t) :
      FiniteNetwork.stateL1Norm
          (Matrix.smulVec (forwardProduct N.colMix t (r + 1))
            (Matrix.smulVec (N.colMix r - 1) (U r))) ≤
        (blockContraction N)⁻¹ * mixingRate N ^ (t - 1 - r) *
          (2 * (n : ℝ) * M) := by
    have hrlt : r < t := Finset.mem_range.mp hr
    let z : FiniteNetwork.ZeroSumState (Fin n) ℝ :=
      ⟨Matrix.smulVec (N.colMix r - 1) (U r),
        Matrix.sum_sub_one_smulVec_eq_zero_of_mem_colStochastic
          (U r) (N.col_stochastic r)⟩
    have hc := colMix_stateL1_geometric N (r + 1) (t - (r + 1)) z
    change FiniteNetwork.stateL1Norm
        (Matrix.smulVec
          (FiniteNetwork.consecutiveProduct N.colMix (r + 1) (t - (r + 1)))
          z.1) ≤ _ at hc
    calc
      FiniteNetwork.stateL1Norm
          (Matrix.smulVec (forwardProduct N.colMix t (r + 1))
            (Matrix.smulVec (N.colMix r - 1) (U r))) =
          FiniteNetwork.stateL1Norm
            (Matrix.smulVec
              (FiniteNetwork.consecutiveProduct N.colMix (r + 1) (t - (r + 1)))
              z.1) := by
        rfl
      _ ≤ (blockContraction N)⁻¹ * mixingRate N ^ (t - (r + 1)) *
          FiniteNetwork.stateL1Norm z.1 := hc
      _ ≤ (blockContraction N)⁻¹ * mixingRate N ^ (t - (r + 1)) *
          (2 * (n : ℝ) * M) := by
        exact mul_le_mul_of_nonneg_left (hinnovation r)
          (mul_nonneg hdelta (pow_nonneg hrho _))
      _ = (blockContraction N)⁻¹ * mixingRate N ^ (t - 1 - r) *
          (2 * (n : ℝ) * M) := by
        rw [show t - (r + 1) = t - 1 - r by omega]
  rw [trackerInnovationResponse_eq_sum_forwardProduct]
  have hsum :
      FiniteNetwork.stateL1Norm
          (∑ r ∈ Finset.range t,
            Matrix.smulVec (forwardProduct N.colMix t (r + 1))
              (Matrix.smulVec (N.colMix r - 1) (U r))) ≤
        ∑ r ∈ Finset.range t,
          (blockContraction N)⁻¹ * mixingRate N ^ (t - 1 - r) *
            (2 * (n : ℝ) * M) := by
    rw [FiniteNetwork.stateL1Norm_def]
    simp only [Real.norm_eq_abs]
    calc
      (∑ q : Fin n, |(∑ r ∈ Finset.range t,
          Matrix.smulVec (forwardProduct N.colMix t (r + 1))
            (Matrix.smulVec (N.colMix r - 1) (U r))) q|) ≤
          ∑ q : Fin n, ∑ r ∈ Finset.range t,
            |Matrix.smulVec (forwardProduct N.colMix t (r + 1))
              (Matrix.smulVec (N.colMix r - 1) (U r)) q| := by
        exact Finset.sum_le_sum fun q _ => by
          simpa only [Finset.sum_apply] using
            (Finset.abs_sum_le_sum_abs
              (fun r => Matrix.smulVec (forwardProduct N.colMix t (r + 1))
                (Matrix.smulVec (N.colMix r - 1) (U r)) q)
              (Finset.range t))
      _ = ∑ r ∈ Finset.range t, FiniteNetwork.stateL1Norm
          (Matrix.smulVec (forwardProduct N.colMix t (r + 1))
            (Matrix.smulVec (N.colMix r - 1) (U r))) := by
        rw [Finset.sum_comm]
        simp only [FiniteNetwork.stateL1Norm_def, Real.norm_eq_abs]
      _ ≤ _ := Finset.sum_le_sum fun r hr => hterm r hr
  refine hsum.trans ?_
  have hgeom := sum_range_geometric_reverse_mul_le_div_one_sub
    (mixingRate N) ((blockContraction N)⁻¹ * (2 * (n : ℝ) * M)) t
    hrho hrho_lt (mul_nonneg hdelta (by positivity))
  convert hgeom using 1 <;> ring

/-- The tracker response to the single loading pulse is exactly the flat
tracker kernel from equation (33). -/
theorem trackerInnovationResponse_loadingPulse_eq_flatTrackerKernel
    (N : NetworkSetup n) (j : ℕ) (i : Fin n) (e : ℝ) (t : ℕ)
    (hjt : j + 1 ≤ t) :
    FiniteNetwork.trackerInnovationResponse N.colMix
        (fun r => loadingPulse j i e r) t =
      fun q =>
        ((forwardProduct N.colMix t (j + 1) * (N.colMix j - 1)) *ᵥ
          (fun r => if r = i then 1 else 0)) q * e := by
  classical
  rw [trackerInnovationResponse_eq_sum_forwardProduct]
  rw [Finset.sum_eq_single j]
  · funext q
    unfold loadingPulse
    simp only [Matrix.smulVec_apply, Matrix.mulVec, dotProduct,
      Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, smul_eq_mul]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    ring
  · intro r hr hrne
    have hrne' : r ≠ j := by simpa [eq_comm] using hrne
    have hpulse : loadingPulse j i e r = 0 := by
      funext q
      simp [loadingPulse, hrne']
    rw [hpulse, Matrix.smulVec_zero, Matrix.smulVec_zero]
  · intro hjnot
    exfalso
    exact hjnot (Finset.mem_range.mpr (by omega))

/-- Before the pulse is applied, both the primal and the retained tracker are
zero.  This supplies the exact zero-error initial condition for equation (34). -/
theorem loadingTrajectory_primal_retained_zero_before_pulse
    (N : NetworkSetup n) (L D s : ℝ) (j : ℕ) (i : Fin n) (e : ℝ)
    (t : ℕ) (htj : t ≤ j) :
    (loadingTrajectory N L D s j i e t).primal = 0 ∧
      retainedLoadingTracker N L D s j i e t = 0 := by
  induction t with
  | zero =>
      constructor
      · rfl
      · simp [retainedLoadingTracker, loadingTrajectory]
  | succ t ih =>
      have htlt : t < j := by omega
      obtain ⟨hX, hV⟩ := ih (by omega)
      have hpulse : loadingPulse j i e t = 0 := by
        funext q
        simp [loadingPulse, ne_of_lt htlt]
      have horacle :
          loadingOracle L D j i e t
            (loadingTrajectory N L D s j i e t).primal = 0 := by
        rw [hX]
        funext q
        simp [loadingOracle, hpulse, negativeCurvatureDerivative_zero]
      have htracker :
          (loadingTrajectory N L D s j i e t).tracker = 0 := by
        rw [retainedLoadingTracker, horacle, sub_zero] at hV
        exact hV
      constructor
      · simp [loadingTrajectory, SOptLib.pushPullStep, hX, htracker]
      · rw [retained_loading_tracker_succ, hV, hX, hpulse]
        simp only [Pi.zero_apply, negativeCurvatureDerivative_zero, zero_add]
        have hz : (fun _ : Fin n => (0 : ℝ)) = 0 := rfl
        rw [hz, Matrix.mulVec_zero, Matrix.mulVec_zero, zero_add]

/-- Arithmetic node mean of the loading trajectory. Book
`#/setup/problem/math`: “`\bar x_t=\frac1n\mathbf1^\top X_t`”. -/
def loadingArithmeticMean (N : NetworkSetup n) (L D s : ℝ)
    (j : ℕ) (i : Fin n) (e : ℝ) (t : ℕ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ k, (loadingTrajectory N L D s j i e t).primal k

/-- The actual finite-time arithmetic endpoint used in equation (38) is
continuous in the calibration parameter.  In particular, this statement is
about `loadingTrajectory`, not `loadingUnitCenterReferenceOrbit`. -/
theorem loading_endpoint_map_continuous
    (N : NetworkSetup n) (L D s : ℝ) (j : ℕ) (i : Fin n)
    (hD : 0 ≤ D) (t : ℕ) :
    Continuous (fun a : ℝ =>
      loadingArithmeticMean N L D s j i
        (-a * D / ((s / L) * influenceRow N j i)) t) := by
  have he : Continuous (fun a : ℝ =>
      -a * D / ((s / L) * influenceRow N j i)) :=
    ((continuous_id.neg.mul continuous_const).div_const _)
  have htrajectory :=
    loading_trajectory_continuous_in_pulse N L D s j i hD t
  unfold loadingArithmeticMean
  exact continuous_const.mul
    (continuous_finset_sum _ (fun q _ => (htrajectory.1 q).comp he))

/-- The source's fixed flat-kernel rate `ρ_flat∈(ρ,1)` from the paragraph
preceding (33). Book `#/key_lemmas/3/proof/18/description`:
“Fix a flat-kernel decay rate strictly between rho and one”. -/
def loadingFlatRate (N : NetworkSetup n) : ℝ := (1 + mixingRate N) / 2

/-- The triangular fast-system rate `r=(1+ρ)/2`. Book
`#/key_lemmas/3/proof/4/description`: “Choose the intermediate contraction rate used to
dominate the triangular convolution”. -/
def loadingTriangularRate (N : NetworkSetup n) : ℝ :=
  (1 + mixingRate N) / 2

/-- The explicit triangular-product constant `M`. Book
`#/key_lemmas/3/proof/5/math`:
“`M={2\over\delta}+{1\over\delta}+{4n\over\delta^2r(1-\rho/r)^2}`”. -/
def loadingTriangularConstant (N : NetworkSetup n) : ℝ :=
  2 / blockContraction N + 1 / blockContraction N +
    4 * n / (blockContraction N ^ 2 * loadingTriangularRate N *
      (1 - mixingRate N / loadingTriangularRate N) ^ 2)

/-- The perturbed fast rate `r_f=(1+r)/2`. Book
`#/key_lemmas/3/proof/6/math`: “`r_f=(1+r)/2`”. -/
def loadingFastRate (N : NetworkSetup n) : ℝ :=
  (1 + loadingTriangularRate N) / 2

/-- The transverse rate `r_2=(1+r_f)/2`. Book
`#/key_lemmas/3/proof/9/math`: “`r_2=(1+r_f)/2`”. -/
def loadingTransverseRate (N : NetworkSetup n) : ℝ :=
  (1 + loadingFastRate N) / 2

/-- Lean realization of the supremum norm in
`#/key_lemmas/3/proof/19/math`; it introduces no source object. -/
def nodeSupNorm (x : Fin n → ℝ) : ℝ := ⨆ i, |x i|

/-- Lean realization of the coordinate `ℓ¹` norm in
`#/key_lemmas/3/proof/19/math`; it introduces no source object. -/
def nodeL1Norm (x : Fin n → ℝ) : ℝ := ∑ i, |x i|

/-- A row-stochastic scalar network action is nonexpansive in the node
supremum norm. -/
theorem rowMix_nodeSupNorm_le
    (N : NetworkSetup n) (t : ℕ) (x : Fin n → ℝ) :
    nodeSupNorm (N.rowMix t *ᵥ x) ≤ nodeSupNorm x := by
  classical
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp N.hn
  have hcoord (r : Fin n) : |x r| ≤ nodeSupNorm x := by
    unfold nodeSupNorm
    exact le_ciSup (Finite.bddAbove_range (fun k : Fin n => |x k|)) r
  have hpoint (q : Fin n) :
      |(N.rowMix t *ᵥ x) q| ≤ nodeSupNorm x := by
    rw [Matrix.mulVec, dotProduct]
    calc
      |∑ r, N.rowMix t q r * x r| ≤
          ∑ r, |N.rowMix t q r * x r| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ r, N.rowMix t q r * |x r| := by
        apply Finset.sum_congr rfl
        intro r _
        rw [abs_mul, abs_of_nonneg
          (Matrix.nonneg_of_mem_rowStochastic (N.row_stochastic t))]
      _ ≤ ∑ r, N.rowMix t q r * nodeSupNorm x := by
        exact Finset.sum_le_sum fun r _ =>
          mul_le_mul_of_nonneg_left (hcoord r)
            (Matrix.nonneg_of_mem_rowStochastic (N.row_stochastic t))
      _ = nodeSupNorm x := by
        rw [← Finset.sum_mul,
          Matrix.sum_row_of_mem_rowStochastic (N.row_stochastic t), one_mul]
  unfold nodeSupNorm
  exact ciSup_le hpoint

/-- Every coordinate is bounded by the scalar network Euclidean norm. -/
theorem abs_le_nodeL2Norm (x : Fin n → ℝ) (i : Fin n) :
    |x i| ≤ nodeL2Norm x := by
  rw [nodeL2Norm, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt
    (Finset.single_le_sum (fun r _ => sq_nonneg (x r)) (Finset.mem_univ i))

theorem abs_le_nodeSupNorm (x : Fin n → ℝ) (i : Fin n) :
    |x i| ≤ nodeSupNorm x := by
  unfold nodeSupNorm
  exact le_ciSup (Finite.bddAbove_range (fun r : Fin n => |x r|)) i

/-- Orthogonal centering by the arithmetic mean does not increase scalar
Euclidean network energy. -/
theorem disagreement_nodeL2_le (N : NetworkSetup n) (x : Fin n → ℝ) :
    nodeL2Norm (disagreement x) ≤ nodeL2Norm x := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp N.hn
  have henergy :=
    SOptLib.sum_norm_sq_sub_finiteUniformAverage_le_sum_norm_sq x
  unfold nodeL2Norm disagreement
  apply Real.sqrt_le_sqrt
  simpa [Real.norm_eq_abs, sq_abs] using henergy

/-- Finite-window form of the absolute-probability recurrence.  This is the
row-vector propagation used to identify the consensus center of every row
product in the flat-kernel calculation. -/
theorem absoluteProbability_vecMul_forwardProduct
    (N : NetworkSetup n) (t k : ℕ) (hkt : k ≤ t) :
    absoluteProbability N t ᵥ* forwardProduct N.rowMix t k =
      absoluteProbability N k := by
  have hrec := (absoluteProbability_spec N).2.2
  have hwindow :=
    FiniteNetwork.vecMul_consecutiveMatrixProduct_eq_of_step
      N.rowMix (absoluteProbability N) k (t - k) (by
        intro q hq
        simpa [Nat.add_assoc] using hrec (k + q))
  simpa [forwardProduct, Nat.add_sub_of_le hkt] using hwindow

/-- A row product approaches its source-canonical absolute-probability
consensus center at the completed disagreement rate. -/
theorem rowProduct_sub_absoluteConsensus_sup_geometric
    (N : NetworkSetup n) (t k : ℕ) (hkt : k ≤ t) (x : Fin n → ℝ) :
    nodeSupNorm (fun i =>
        (forwardProduct N.rowMix t k *ᵥ x) i -
          dotProduct (absoluteProbability N k) x) ≤
      (2 * rowMixingConstant N) * mixingRate N ^ (t - k) *
        nodeL2Norm (disagreement x) := by
  classical
  let y := forwardProduct N.rowMix t k *ᵥ x
  let d := disagreement y
  have hpi_nonneg : ∀ r, 0 ≤ absoluteProbability N t r :=
    (absoluteProbability_spec N).1 t
  have hpi_sum : ∑ r, absoluteProbability N t r = 1 :=
    (absoluteProbability_spec N).2.1 t
  have hcenter :
      dotProduct (absoluteProbability N t) y =
        dotProduct (absoluteProbability N k) x := by
    dsimp [y]
    rw [Matrix.dotProduct_mulVec,
      absoluteProbability_vecMul_forwardProduct N t k hkt]
  have hweighted :
      dotProduct (absoluteProbability N t) y =
        dotProduct (absoluteProbability N t) d +
          (n : ℝ)⁻¹ * ∑ r, y r := by
    dsimp [d]
    unfold disagreement dotProduct
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hpi_sum]
    ring
  have hweighted_abs :
      |dotProduct (absoluteProbability N t) d| ≤ nodeL2Norm d := by
    unfold dotProduct
    calc
      |∑ r, absoluteProbability N t r * d r| ≤
          ∑ r, |absoluteProbability N t r * d r| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ r, absoluteProbability N t r * |d r| := by
        apply Finset.sum_congr rfl
        intro r _
        rw [abs_mul, abs_of_nonneg (hpi_nonneg r)]
      _ ≤ ∑ r, absoluteProbability N t r * nodeL2Norm d := by
        exact Finset.sum_le_sum fun r _ =>
          mul_le_mul_of_nonneg_left (abs_le_nodeL2Norm d r) (hpi_nonneg r)
      _ = nodeL2Norm d := by rw [← Finset.sum_mul, hpi_sum, one_mul]
  have hpoint : ∀ i,
      |y i - dotProduct (absoluteProbability N k) x| ≤ 2 * nodeL2Norm d := by
    intro i
    have hid :
        y i - dotProduct (absoluteProbability N k) x =
          d i - dotProduct (absoluteProbability N t) d := by
      rw [← hcenter, hweighted]
      dsimp [d]
      unfold disagreement
      ring
    rw [hid]
    calc
      |d i - dotProduct (absoluteProbability N t) d| ≤
          |d i| + |dotProduct (absoluteProbability N t) d| := abs_sub _ _
      _ ≤ nodeL2Norm d + nodeL2Norm d :=
        add_le_add (abs_le_nodeL2Norm d i) hweighted_abs
      _ = 2 * nodeL2Norm d := by ring
  have hmix := rowMix_disagreement_nodeL2_geometric N t k hkt x
  have hsup :
      nodeSupNorm (fun i =>
          (forwardProduct N.rowMix t k *ᵥ x) i -
            dotProduct (absoluteProbability N k) x) ≤
        2 * nodeL2Norm d := by
    letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp N.hn
    unfold nodeSupNorm
    exact ciSup_le
      (f := fun i : Fin n =>
        |(forwardProduct N.rowMix t k *ᵥ x) i -
          dotProduct (absoluteProbability N k) x|)
      (c := (2 * nodeL2Norm d : ℝ))
      (fun i => by simpa [y] using hpoint i)
  refine hsup.trans ?_
  dsimp [d, y] at hmix ⊢
  calc
    2 * nodeL2Norm
        (disagreement (forwardProduct N.rowMix t k *ᵥ x)) ≤
        2 * (rowMixingConstant N * mixingRate N ^ (t - k) *
          nodeL2Norm (disagreement x)) :=
      mul_le_mul_of_nonneg_left hmix (by norm_num)
    _ = (2 * rowMixingConstant N) * mixingRate N ^ (t - k) *
        nodeL2Norm (disagreement x) := by ring

/-- The two geometric legs in a triangular row/column convolution have a
common total exponent; summing them contributes exactly the lag cardinality. -/
theorem sum_Ico_split_geometric_powers
    (ρ : ℝ) (j t : ℕ) (hjt : j + 1 ≤ t) :
    (∑ r ∈ Finset.Ico (j + 1) t,
      ρ ^ (t - r - 1) * ρ ^ (r - j - 1)) =
      (t - j - 1 : ℕ) * ρ ^ (t - j - 2) := by
  calc
    (∑ r ∈ Finset.Ico (j + 1) t,
        ρ ^ (t - r - 1) * ρ ^ (r - j - 1)) =
        ∑ _r ∈ Finset.Ico (j + 1) t, ρ ^ (t - j - 2) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [← pow_add]
      congr 1
      have hrange := Finset.mem_Ico.mp hr
      omega
    _ = (t - j - 1 : ℕ) * ρ ^ (t - j - 2) := by
      simp [Nat.card_Ico]
      congr 1
      omega

/-- Start-index form of the same triangular geometric convolution. -/
theorem sum_Ico_geometric_convolution
    (ρ : ℝ) (k t : ℕ) (hkt : k ≤ t) :
    (∑ r ∈ Finset.Ico k t,
      ρ ^ (t - r - 1) * ρ ^ (r - k)) =
      (t - k : ℕ) * ρ ^ (t - k - 1) := by
  by_cases hEq : k = t
  · subst t
    simp
  · have hlt : k < t := lt_of_le_of_ne hkt hEq
    calc
      (∑ r ∈ Finset.Ico k t,
          ρ ^ (t - r - 1) * ρ ^ (r - k)) =
          ∑ _r ∈ Finset.Ico k t, ρ ^ (t - k - 1) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [← pow_add]
        congr 1
        have hrange := Finset.mem_Ico.mp hr
        omega
      _ = (t - k : ℕ) * ρ ^ (t - k - 1) := by
        simp [Nat.card_Ico, hkt]

/-- Coordinate `ℓ¹` triangle inequality for a finite sum of node vectors. -/
theorem nodeL1Norm_finset_sum_le
    {ι : Type*} (S : Finset ι) (f : ι → Fin n → ℝ) :
    nodeL1Norm (∑ r ∈ S, f r) ≤ ∑ r ∈ S, nodeL1Norm (f r) := by
  classical
  unfold nodeL1Norm
  calc
    (∑ i : Fin n, |(∑ r ∈ S, f r) i|) ≤
        ∑ i : Fin n, ∑ r ∈ S, |f r i| := by
      apply Finset.sum_le_sum
      intro i _
      simp only [Finset.sum_apply]
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ r ∈ S, ∑ i : Fin n, |f r i| := by
      rw [Finset.sum_comm]

/-- The scalar `ℓ²` network norm is bounded by the coordinate `ℓ¹` norm. -/
theorem nodeL2Norm_le_nodeL1Norm (x : Fin n → ℝ) :
    nodeL2Norm x ≤ nodeL1Norm x := by
  calc
    nodeL2Norm x = ‖WithLp.toLp 2 x‖ := by
      simp [PiLp.norm_eq_of_L2, nodeL2Norm, Real.norm_eq_abs, sq_abs]
    _ ≤ ∑ i, ‖x i‖ := dependentProductL2Seminorm_le_sum_norm _
    _ = nodeL1Norm x := by simp [nodeL1Norm, Real.norm_eq_abs]

/-- A finite coordinate `ℓ¹` norm is bounded by cardinality times the
coordinate supremum norm. -/
theorem nodeL1Norm_le_card_mul_nodeSupNorm (x : Fin n → ℝ) :
    nodeL1Norm x ≤ (n : ℝ) * nodeSupNorm x := by
  classical
  unfold nodeL1Norm
  calc
    (∑ i : Fin n, |x i|) ≤ ∑ _i : Fin n, nodeSupNorm x :=
      Finset.sum_le_sum fun i _ => abs_le_nodeSupNorm x i
    _ = (n : ℝ) * nodeSupNorm x := by simp

/-- Sharp enough row leg for the triangular fast product: if the canonical
absolute-probability center vanishes at the initial time, the whole row
product is geometrically small in coordinate supremum norm.  This is the row
half of source equation (23), derived from the completed row-product estimate
rather than assumed by the loading argument. -/
theorem rowProduct_center_zero_sup_geometric
    (N : NetworkSetup n) (t k : ℕ) (hkt : k ≤ t) (x : Fin n → ℝ)
    (hcenter : dotProduct (absoluteProbability N k) x = 0) :
    nodeSupNorm (forwardProduct N.rowMix t k *ᵥ x) ≤
      (2 * rowMixingConstant N * (n : ℝ)) * mixingRate N ^ (t - k) *
        nodeSupNorm x := by
  have hrow := rowProduct_sub_absoluteConsensus_sup_geometric N t k hkt x
  have hdisagreement :
      nodeL2Norm (disagreement x) ≤ (n : ℝ) * nodeSupNorm x :=
    (disagreement_nodeL2_le N x).trans
      ((nodeL2Norm_le_nodeL1Norm x).trans
        (nodeL1Norm_le_card_mul_nodeSupNorm x))
  have hcoeff :
      0 ≤ (2 * rowMixingConstant N) * mixingRate N ^ (t - k) := by
    have hrow_nonneg : 0 ≤ rowMixingConstant N := by
      unfold rowMixingConstant
      exact div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
        (blockContraction_pos N).le
    exact mul_nonneg (mul_nonneg (by norm_num) hrow_nonneg)
      (pow_nonneg (mixingRate_nonneg N) _)
  calc
    nodeSupNorm (forwardProduct N.rowMix t k *ᵥ x) =
        nodeSupNorm (fun i =>
          (forwardProduct N.rowMix t k *ᵥ x) i -
            dotProduct (absoluteProbability N k) x) := by simp [hcenter]
    _ ≤ (2 * rowMixingConstant N) * mixingRate N ^ (t - k) *
          nodeL2Norm (disagreement x) := hrow
    _ ≤ (2 * rowMixingConstant N) * mixingRate N ^ (t - k) *
          ((n : ℝ) * nodeSupNorm x) :=
      mul_le_mul_of_nonneg_left hdisagreement hcoeff
    _ = (2 * rowMixingConstant N * (n : ℝ)) *
          mixingRate N ^ (t - k) * nodeSupNorm x := by ring

theorem nodeSupNorm_nonneg (N : NetworkSetup n) (x : Fin n → ℝ) :
    0 ≤ nodeSupNorm x := by
  let i : Fin n := ⟨0, N.hn⟩
  exact (abs_nonneg (x i)).trans (abs_le_nodeSupNorm x i)

/-- A column-stochastic innovation costs at most twice the coordinate `ℓ¹`
mass, hence at most `2n` times the coordinate supremum.  Its zero-sum
property is supplied separately by the standard column-stochastic API. -/
theorem colMix_sub_one_nodeL1_le_sup
    (N : NetworkSetup n) (t : ℕ) (x : Fin n → ℝ) :
    nodeL1Norm ((N.colMix t - 1) *ᵥ x) ≤
      2 * (n : ℝ) * nodeSupNorm x := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  have htriangle :
      nodeL1Norm (N.colMix t *ᵥ x - x) ≤
        nodeL1Norm (N.colMix t *ᵥ x) + nodeL1Norm x := by
    unfold nodeL1Norm
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => abs_sub _ _
  have hcontract :
      nodeL1Norm (N.colMix t *ᵥ x) ≤ nodeL1Norm x := by
    simpa [nodeL1Norm, FiniteNetwork.stateL1Norm_def, Real.norm_eq_abs] using
      Matrix.stateL1Norm_smulVec_le_of_mem_colStochastic x
        (N.col_stochastic t)
  calc
    nodeL1Norm (N.colMix t *ᵥ x - x) ≤
        nodeL1Norm (N.colMix t *ᵥ x) + nodeL1Norm x := htriangle
    _ ≤ nodeL1Norm x + nodeL1Norm x := add_le_add hcontract le_rfl
    _ ≤ ((n : ℝ) * nodeSupNorm x) + (n : ℝ) * nodeSupNorm x :=
      add_le_add (nodeL1Norm_le_card_mul_nodeSupNorm x)
        (nodeL1Norm_le_card_mul_nodeSupNorm x)
    _ = 2 * (n : ℝ) * nodeSupNorm x := by ring

/-- One off-diagonal summand of the triangular fast product (23).  The row
leg is centered by the source absolute-probability sequence, the column
innovation is genuinely zero-sum, and the completed row/column geometric
estimates are both consumed here. -/
theorem loading_triangular_cross_term_geometric
    (N : NetworkSetup n) (k r t : ℕ) (hkr : k ≤ r) (hrt : r + 1 ≤ t)
    (x : Fin n → ℝ)
    (hcenter : dotProduct (absoluteProbability N k) x = 0) :
    nodeL1Norm
        (forwardProduct N.colMix t (r + 1) *ᵥ
          ((N.colMix r - 1) *ᵥ (forwardProduct N.rowMix r k *ᵥ x))) ≤
      (blockContraction N)⁻¹ * mixingRate N ^ (t - r - 1) *
        (2 * (n : ℝ) *
          ((2 * rowMixingConstant N * (n : ℝ)) *
            mixingRate N ^ (r - k) * nodeSupNorm x)) := by
  let y : Fin n → ℝ := forwardProduct N.rowMix r k *ᵥ x
  let z : ZeroSumNodeVector n :=
    ⟨(N.colMix r - 1) *ᵥ y,
      Matrix.sum_sub_one_smulVec_eq_zero_of_mem_colStochastic y
        (N.col_stochastic r)⟩
  have hcol := colMix_stateL1_geometric N (r + 1) (t - (r + 1)) z
  have hinnovation :
      nodeL1Norm z.1 ≤ 2 * (n : ℝ) * nodeSupNorm y := by
    simpa [z] using colMix_sub_one_nodeL1_le_sup N r y
  have hrow :
      nodeSupNorm y ≤
        (2 * rowMixingConstant N * (n : ℝ)) * mixingRate N ^ (r - k) *
          nodeSupNorm x := by
    simpa [y] using rowProduct_center_zero_sup_geometric N r k hkr x hcenter
  have hdelta_nonneg : 0 ≤ (blockContraction N)⁻¹ :=
    inv_nonneg.mpr (blockContraction_pos N).le
  have hcolcoeff :
      0 ≤ (blockContraction N)⁻¹ * mixingRate N ^ (t - (r + 1)) :=
    mul_nonneg hdelta_nonneg (pow_nonneg (mixingRate_nonneg N) _)
  have hn_nonneg : 0 ≤ 2 * (n : ℝ) := by positivity
  calc
    nodeL1Norm
        (forwardProduct N.colMix t (r + 1) *ᵥ
          ((N.colMix r - 1) *ᵥ (forwardProduct N.rowMix r k *ᵥ x))) =
        FiniteNetwork.stateL1Norm
          (Matrix.smulVec
            (FiniteNetwork.consecutiveProduct N.colMix (r + 1) (t - (r + 1)))
            z.1) := by
      change nodeL1Norm
          (Matrix.smulVec
            (FiniteNetwork.consecutiveProduct N.colMix (r + 1) (t - (r + 1)))
            z.1) = _
      simp [nodeL1Norm, FiniteNetwork.stateL1Norm_def, Real.norm_eq_abs]
    _ ≤ (blockContraction N)⁻¹ * mixingRate N ^ (t - (r + 1)) *
          FiniteNetwork.stateL1Norm z.1 := hcol
    _ ≤ (blockContraction N)⁻¹ * mixingRate N ^ (t - (r + 1)) *
          (2 * (n : ℝ) * nodeSupNorm y) :=
      mul_le_mul_of_nonneg_left hinnovation hcolcoeff
    _ ≤ (blockContraction N)⁻¹ * mixingRate N ^ (t - (r + 1)) *
          (2 * (n : ℝ) *
            ((2 * rowMixingConstant N * (n : ℝ)) *
              mixingRate N ^ (r - k) * nodeSupNorm x)) := by
      gcongr
    _ = (blockContraction N)⁻¹ * mixingRate N ^ (t - r - 1) *
          (2 * (n : ℝ) *
            ((2 * rowMixingConstant N * (n : ℝ)) *
              mixingRate N ^ (r - k) * nodeSupNorm x)) := by
      rw [show t - (r + 1) = t - r - 1 by omega]

/-- Aggregated off-diagonal block of the true triangular fast product.  This
is the exact product-contraction inequality immediately below the source's
one-summand row/column estimates and before absorption of the linear lag into
the larger fast rate. -/
theorem loading_triangular_cross_sum_geometric
    (N : NetworkSetup n) (k t : ℕ) (hkt : k ≤ t) (x : Fin n → ℝ)
    (hcenter : dotProduct (absoluteProbability N k) x = 0) :
    nodeL1Norm
        (∑ r ∈ Finset.Ico k t,
          forwardProduct N.colMix t (r + 1) *ᵥ
            ((N.colMix r - 1) *ᵥ (forwardProduct N.rowMix r k *ᵥ x))) ≤
      ((blockContraction N)⁻¹ *
          (2 * (n : ℝ) * (2 * rowMixingConstant N * (n : ℝ)))) *
        ((t - k : ℕ) * mixingRate N ^ (t - k - 1)) * nodeSupNorm x := by
  have htriangle := nodeL1Norm_finset_sum_le (Finset.Ico k t)
    (fun r => forwardProduct N.colMix t (r + 1) *ᵥ
      ((N.colMix r - 1) *ᵥ (forwardProduct N.rowMix r k *ᵥ x)))
  refine htriangle.trans ?_
  calc
    (∑ r ∈ Finset.Ico k t,
        nodeL1Norm
          (forwardProduct N.colMix t (r + 1) *ᵥ
            ((N.colMix r - 1) *ᵥ (forwardProduct N.rowMix r k *ᵥ x)))) ≤
        ∑ r ∈ Finset.Ico k t,
          ((blockContraction N)⁻¹ *
            (2 * (n : ℝ) * (2 * rowMixingConstant N * (n : ℝ)))) *
          (mixingRate N ^ (t - r - 1) * mixingRate N ^ (r - k)) *
            nodeSupNorm x := by
      apply Finset.sum_le_sum
      intro r hr
      have hrange := Finset.mem_Ico.mp hr
      have hterm := loading_triangular_cross_term_geometric N k r t
        hrange.1 (by omega) x hcenter
      calc
        nodeL1Norm
            (forwardProduct N.colMix t (r + 1) *ᵥ
              ((N.colMix r - 1) *ᵥ
                (forwardProduct N.rowMix r k *ᵥ x))) ≤
            (blockContraction N)⁻¹ * mixingRate N ^ (t - r - 1) *
              (2 * (n : ℝ) *
                ((2 * rowMixingConstant N * (n : ℝ)) *
                  mixingRate N ^ (r - k) * nodeSupNorm x)) := hterm
        _ = ((blockContraction N)⁻¹ *
              (2 * (n : ℝ) * (2 * rowMixingConstant N * (n : ℝ)))) *
            (mixingRate N ^ (t - r - 1) * mixingRate N ^ (r - k)) *
              nodeSupNorm x := by ring
    _ = ((blockContraction N)⁻¹ *
          (2 * (n : ℝ) * (2 * rowMixingConstant N * (n : ℝ)))) *
        (∑ r ∈ Finset.Ico k t,
          mixingRate N ^ (t - r - 1) * mixingRate N ^ (r - k)) *
          nodeSupNorm x := by
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = ((blockContraction N)⁻¹ *
          (2 * (n : ℝ) * (2 * rowMixingConstant N * (n : ℝ)))) *
        ((t - k : ℕ) * mixingRate N ^ (t - k - 1)) * nodeSupNorm x := by
      rw [sum_Ico_geometric_convolution (mixingRate N) k t hkt]

/-- The linear lag in the triangular convolution is uniformly absorbed by
the source's strictly larger fast rate. -/
theorem exists_loading_fast_lag_constant (N : NetworkSetup n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ,
      (m : ℝ) * mixingRate N ^ (m - 1) ≤
        C * loadingFastRate N ^ m := by
  have hrho_nonneg : 0 ≤ mixingRate N := mixingRate_nonneg N
  have hrho_lt_one : mixingRate N < 1 := mixingRate_lt_one N
  have hrho_fast : mixingRate N < loadingFastRate N := by
    unfold loadingFastRate loadingTriangularRate
    linarith
  have hfast_pos : 0 < loadingFastRate N := hrho_nonneg.trans_lt hrho_fast
  obtain ⟨C₀, hC₀, hbound⟩ :=
    exists_const_one_add_natCast_mul_pow_le_pow_of_lt hrho_nonneg hrho_fast
  refine ⟨C₀ / loadingFastRate N, div_nonneg hC₀ hfast_pos.le, ?_⟩
  intro m
  cases m with
  | zero =>
      simpa using div_nonneg hC₀ hfast_pos.le
  | succ q =>
      have hq := hbound q
      rw [Nat.succ_sub_one]
      calc
        ((q + 1 : ℕ) : ℝ) * mixingRate N ^ q ≤
            C₀ * loadingFastRate N ^ q := by simpa using hq
        _ = (C₀ / loadingFastRate N) * loadingFastRate N ^ (q + 1) := by
          rw [pow_succ]
          field_simp

theorem nodeL1Norm_add_le (x y : Fin n → ℝ) :
    nodeL1Norm (x + y) ≤ nodeL1Norm x + nodeL1Norm y := by
  unfold nodeL1Norm
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => abs_add_le _ _

/-- Equation-(23) product estimate for the genuine triangular row/column fast
system.  The row component has zero canonical center, the column component has
zero total mass, and the off-diagonal forcing is exactly `(C_r-I)E_r`. -/
theorem exists_loading_triangular_product_constant
    (N : NetworkSetup n) :
    ∃ M : ℝ, loadingTriangularConstant N ≤ M ∧ 0 ≤ M ∧
      ∀ (k t : ℕ), k ≤ t → ∀ (E K : Fin n → ℝ),
      dotProduct (absoluteProbability N k) E = 0 →
      (∑ i, K i) = 0 →
      nodeSupNorm (forwardProduct N.rowMix t k *ᵥ E) +
          nodeL1Norm
            (forwardProduct N.colMix t k *ᵥ K +
              ∑ r ∈ Finset.Ico k t,
                forwardProduct N.colMix t (r + 1) *ᵥ
                  ((N.colMix r - 1) *ᵥ
                    (forwardProduct N.rowMix r k *ᵥ E))) ≤
        M * loadingFastRate N ^ (t - k) *
          (nodeSupNorm E + nodeL1Norm K) := by
  obtain ⟨Clag, hClag, hlag⟩ := exists_loading_fast_lag_constant N
  let Arow : ℝ := 2 * rowMixingConstant N * (n : ℝ)
  let Acol : ℝ := (blockContraction N)⁻¹
  let Across : ℝ := Acol * (2 * (n : ℝ) * Arow)
  let B : ℝ := Arow + Acol + Across * Clag
  let M : ℝ := max (loadingTriangularConstant N) B
  have hArow : 0 ≤ Arow := by
    dsimp [Arow]
    have hrow : 0 ≤ rowMixingConstant N := by
      unfold rowMixingConstant
      exact div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
        (blockContraction_pos N).le
    positivity
  have hAcol : 0 ≤ Acol := by
    dsimp [Acol]
    exact inv_nonneg.mpr (blockContraction_pos N).le
  have hAcross : 0 ≤ Across := by
    dsimp [Across]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hB_le_M : B ≤ M := by exact le_max_right _ _
  refine ⟨M, le_max_left _ _, hB.trans hB_le_M, ?_⟩
  intro k t hkt E K hEcenter hKsum
  let l : ℕ := t - k
  have hrho_fast : mixingRate N ≤ loadingFastRate N := by
    unfold loadingFastRate loadingTriangularRate
    linarith [mixingRate_lt_one N]
  have hfast_nonneg : 0 ≤ loadingFastRate N :=
    (mixingRate_nonneg N).trans hrho_fast
  have hpowers : mixingRate N ^ l ≤ loadingFastRate N ^ l :=
    pow_le_pow_left₀ (mixingRate_nonneg N) hrho_fast l
  have hsupE : 0 ≤ nodeSupNorm E := nodeSupNorm_nonneg N E
  have hL1K : 0 ≤ nodeL1Norm K := by
    unfold nodeL1Norm
    exact Finset.sum_nonneg fun i _ => abs_nonneg _
  have hrow :
      nodeSupNorm (forwardProduct N.rowMix t k *ᵥ E) ≤
        Arow * loadingFastRate N ^ l * nodeSupNorm E := by
    calc
      nodeSupNorm (forwardProduct N.rowMix t k *ᵥ E) ≤
          Arow * mixingRate N ^ l * nodeSupNorm E := by
        simpa [Arow, l] using
          rowProduct_center_zero_sup_geometric N t k hkt E hEcenter
      _ ≤ Arow * loadingFastRate N ^ l * nodeSupNorm E := by gcongr
  let z : ZeroSumNodeVector n := ⟨K, hKsum⟩
  have hcolraw := colMix_stateL1_geometric N k l z
  have hcol :
      nodeL1Norm (forwardProduct N.colMix t k *ᵥ K) ≤
        Acol * loadingFastRate N ^ l * nodeL1Norm K := by
    calc
      nodeL1Norm (forwardProduct N.colMix t k *ᵥ K) =
          FiniteNetwork.stateL1Norm
            (Matrix.smulVec (FiniteNetwork.consecutiveProduct N.colMix k l) z.1) := by
        change nodeL1Norm
            (Matrix.smulVec (FiniteNetwork.consecutiveProduct N.colMix k l) z.1) = _
        simp [nodeL1Norm, FiniteNetwork.stateL1Norm_def, Real.norm_eq_abs]
      _ ≤ (blockContraction N)⁻¹ * mixingRate N ^ l *
            FiniteNetwork.stateL1Norm z.1 := hcolraw
      _ ≤ Acol * loadingFastRate N ^ l * nodeL1Norm K := by
        dsimp [Acol, z]
        simp only [FiniteNetwork.stateL1Norm_def, Real.norm_eq_abs, nodeL1Norm]
        gcongr
  have hcrossraw :=
    loading_triangular_cross_sum_geometric N k t hkt E hEcenter
  have hlag_l :
      (l : ℝ) * mixingRate N ^ (l - 1) ≤
        Clag * loadingFastRate N ^ l := hlag l
  have hcross :
      nodeL1Norm
          (∑ r ∈ Finset.Ico k t,
            forwardProduct N.colMix t (r + 1) *ᵥ
              ((N.colMix r - 1) *ᵥ
                (forwardProduct N.rowMix r k *ᵥ E))) ≤
        Across * Clag * loadingFastRate N ^ l * nodeSupNorm E := by
    calc
      nodeL1Norm
          (∑ r ∈ Finset.Ico k t,
            forwardProduct N.colMix t (r + 1) *ᵥ
              ((N.colMix r - 1) *ᵥ
                (forwardProduct N.rowMix r k *ᵥ E))) ≤
          Across * ((l : ℝ) * mixingRate N ^ (l - 1)) * nodeSupNorm E := by
        simpa [Across, Acol, Arow, l] using hcrossraw
      _ ≤ Across * (Clag * loadingFastRate N ^ l) * nodeSupNorm E := by
        gcongr
      _ = Across * Clag * loadingFastRate N ^ l * nodeSupNorm E := by ring
  have htracker :
      nodeL1Norm
          (forwardProduct N.colMix t k *ᵥ K +
            ∑ r ∈ Finset.Ico k t,
              forwardProduct N.colMix t (r + 1) *ᵥ
                ((N.colMix r - 1) *ᵥ
                  (forwardProduct N.rowMix r k *ᵥ E))) ≤
        Acol * loadingFastRate N ^ l * nodeL1Norm K +
          Across * Clag * loadingFastRate N ^ l * nodeSupNorm E :=
    (nodeL1Norm_add_le _ _).trans (add_le_add hcol hcross)
  calc
    nodeSupNorm (forwardProduct N.rowMix t k *ᵥ E) +
        nodeL1Norm
          (forwardProduct N.colMix t k *ᵥ K +
            ∑ r ∈ Finset.Ico k t,
              forwardProduct N.colMix t (r + 1) *ᵥ
                ((N.colMix r - 1) *ᵥ
                  (forwardProduct N.rowMix r k *ᵥ E))) ≤
        Arow * loadingFastRate N ^ l * nodeSupNorm E +
          (Acol * loadingFastRate N ^ l * nodeL1Norm K +
            Across * Clag * loadingFastRate N ^ l * nodeSupNorm E) :=
      add_le_add hrow htracker
    _ = (Arow + Across * Clag) * loadingFastRate N ^ l * nodeSupNorm E +
          Acol * loadingFastRate N ^ l * nodeL1Norm K := by ring
    _ ≤ B * loadingFastRate N ^ l * nodeSupNorm E +
          B * loadingFastRate N ^ l * nodeL1Norm K := by
      have hrowcoef : Arow + Across * Clag ≤ B := by
        dsimp [B]
        linarith [hAcol]
      have hcolcoef : Acol ≤ B := by
        dsimp [B]
        linarith [hArow, mul_nonneg hAcross hClag]
      gcongr
    _ = B * loadingFastRate N ^ l *
          (nodeSupNorm E + nodeL1Norm K) := by ring
    _ ≤ M * loadingFastRate N ^ l *
          (nodeSupNorm E + nodeL1Norm K) := by gcongr
    _ = M * loadingFastRate N ^ (t - k) *
          (nodeSupNorm E + nodeL1Norm K) := by rfl

/-- The perturbation input `-J_t(E,K)` in source equation (22) stays in the
time-`t+1` constrained fast space and has the printed `J₀ = 2(n+1)` bound.
This is the carrier fact needed to apply the homogeneous triangular estimate
to every Duhamel innovation. -/
theorem loading_fast_perturbation_input_invariants_bound
    (N : NetworkSetup n) (t : ℕ) (E K : Fin n → ℝ) :
    let ell := dotProduct (absoluteProbability N (t + 1)) (E + K)
    let JE : Fin n → ℝ := fun q => E q + K q - ell
    let JK : Fin n → ℝ := fun q =>
      -(pushMass N (t + 1) q - 1) * ell
    dotProduct (absoluteProbability N (t + 1)) JE = 0 ∧
      (∑ q, JK q) = 0 ∧
      nodeSupNorm JE + nodeL1Norm JK ≤
        2 * ((n : ℝ) + 1) * (nodeSupNorm E + nodeL1Norm K) := by
  classical
  dsimp only
  let p : Fin n → ℝ := absoluteProbability N (t + 1)
  let ell : ℝ := dotProduct p (E + K)
  let g : ℝ := nodeSupNorm E + nodeL1Norm K
  have hp_nonneg (q : Fin n) : 0 ≤ p q := by
    exact (absoluteProbability_spec N).1 (t + 1) q
  have hp_sum : ∑ q, p q = 1 := by
    exact (absoluteProbability_spec N).2.1 (t + 1)
  have hKcoord (q : Fin n) : |K q| ≤ nodeL1Norm K := by
    unfold nodeL1Norm
    exact Finset.single_le_sum (fun r _ => abs_nonneg (K r))
      (Finset.mem_univ q)
  have hpoint (q : Fin n) : |E q + K q| ≤ g := by
    dsimp [g]
    exact (abs_add_le _ _).trans
      (add_le_add (abs_le_nodeSupNorm E q) (hKcoord q))
  have hg_nonneg : 0 ≤ g := by
    dsimp [g]
    exact add_nonneg (nodeSupNorm_nonneg N E)
      (Finset.sum_nonneg fun q _ => abs_nonneg (K q))
  have hell : |ell| ≤ g := by
    dsimp [ell]
    unfold dotProduct
    calc
      |∑ q, p q * (E + K) q| ≤ ∑ q, |p q * (E + K) q| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ q, p q * |E q + K q| := by
        apply Finset.sum_congr rfl
        intro q _
        rw [Pi.add_apply, abs_mul, abs_of_nonneg (hp_nonneg q)]
      _ ≤ ∑ q, p q * g := by
        exact Finset.sum_le_sum fun q _ =>
          mul_le_mul_of_nonneg_left (hpoint q) (hp_nonneg q)
      _ = g := by rw [← Finset.sum_mul, hp_sum, one_mul]
  have hcenter :
      dotProduct p (fun q => E q + K q - ell) = 0 := by
    unfold dotProduct
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp_sum, one_mul]
    exact sub_self ell
  have hmass : (∑ q, (pushMass N (t + 1) q - 1)) = 0 := by
    rw [Finset.sum_sub_distrib, pushMass_sum_eq_n]
    simp
  have hzero :
      (∑ q, -(pushMass N (t + 1) q - 1) * ell) = 0 := by
    calc
      (∑ q, -(pushMass N (t + 1) q - 1) * ell) =
          -(∑ q, (pushMass N (t + 1) q - 1)) * ell := by
        rw [← Finset.sum_mul, Finset.sum_neg_distrib]
      _ = 0 := by rw [hmass]; ring
  have hJEpoint (q : Fin n) : |E q + K q - ell| ≤ 2 * g := by
    calc
      |E q + K q - ell| ≤ |E q + K q| + |ell| := abs_sub _ _
      _ ≤ g + g := add_le_add (hpoint q) hell
      _ = 2 * g := by ring
  have hJE : nodeSupNorm (fun q => E q + K q - ell) ≤ 2 * g := by
    letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp N.hn
    unfold nodeSupNorm
    exact ciSup_le hJEpoint
  have hw_abs :
      (∑ q, |pushMass N (t + 1) q - 1|) ≤ 2 * (n : ℝ) := by
    calc
      (∑ q, |pushMass N (t + 1) q - 1|) ≤
          ∑ q, (pushMass N (t + 1) q + 1) := by
        apply Finset.sum_le_sum
        intro q _
        calc
          |pushMass N (t + 1) q - 1| ≤
              |pushMass N (t + 1) q| + |(1 : ℝ)| := abs_sub _ _
          _ = pushMass N (t + 1) q + 1 := by
            rw [abs_of_nonneg (pushMass_nonneg N (t + 1) q), abs_one]
      _ = 2 * (n : ℝ) := by
        rw [Finset.sum_add_distrib, pushMass_sum_eq_n]
        simp
        ring
  have hJK :
      nodeL1Norm (fun q => -(pushMass N (t + 1) q - 1) * ell) ≤
        2 * (n : ℝ) * g := by
    unfold nodeL1Norm
    simp_rw [abs_mul, abs_neg]
    rw [← Finset.sum_mul]
    exact mul_le_mul hw_abs hell (abs_nonneg ell) (by positivity)
  refine ⟨?_, hzero, ?_⟩
  · simpa [p, ell] using hcenter
  · change nodeSupNorm (fun q => E q + K q - ell) +
        nodeL1Norm (fun q => -(pushMass N (t + 1) q - 1) * ell) ≤ _
    calc
      nodeSupNorm (fun q => E q + K q - ell) +
          nodeL1Norm (fun q => -(pushMass N (t + 1) q - 1) * ell) ≤
          2 * g + 2 * (n : ℝ) * g := add_le_add hJE hJK
      _ = 2 * ((n : ℝ) + 1) * g := by ring
      _ = 2 * ((n : ℝ) + 1) *
          (nodeSupNorm E + nodeL1Norm K) := by rfl

def loadingFastStep (N : NetworkSetup n) (t : ℕ)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    (Fin n → ℝ) × (Fin n → ℝ) :=
  (N.rowMix t *ᵥ z.1,
    N.colMix t *ᵥ z.2 + (N.colMix t - 1) *ᵥ z.1)

def loadingFastPerturbationInput (N : NetworkSetup n) (t : ℕ)
    (E K : Fin n → ℝ) : (Fin n → ℝ) × (Fin n → ℝ) :=
  let ell := dotProduct (absoluteProbability N (t + 1)) (E + K)
  (fun q => E q + K q - ell,
    fun q => -(pushMass N (t + 1) q - 1) * ell)

/-- The source term `-B_t ξ_t` from equation (22), before multiplication by
the stepsize.  Its first coordinate is `Q_t w_t ξ_t`, while its second
coordinate is `-(w_{t+1}-1) κ_t ξ_t`. -/
def loadingFastCenterInput (N : NetworkSetup n) (t : ℕ) (xi : ℝ) :
    (Fin n → ℝ) × (Fin n → ℝ) :=
  (fun q => (pushMass N t q - gain N t) * xi,
    fun q => -(pushMass N (t + 1) q - 1) * gain N t * xi)

/-- The slow coordinate `ξ_t=π_tᵀX_t` in the source decomposition preceding
equation (22). -/
def loadingSlowCenter (N : NetworkSetup n)
    (X : ℕ → Fin n → ℝ) (t : ℕ) : ℝ :=
  dotProduct (absoluteProbability N t) (X t)

/-- The constrained pair `(E_t,K_t)` in the source decomposition preceding
equation (22), for a shifted primal state `X` and scaled retained state `U`. -/
def loadingFastCoordinates (N : NetworkSetup n)
    (X U : ℕ → Fin n → ℝ) (t : ℕ) :
    (Fin n → ℝ) × (Fin n → ℝ) :=
  let xi := loadingSlowCenter N X t
  (fun q => X t q - xi,
    fun q => U t q - (pushMass N t q - 1) * xi)

/-- The arithmetic output differs from the absolute-probability slow center
only by the arithmetic mean of the first fast coordinate.  This is the
output bridge used when equation (38) transports a calibrated slow/fast state
to the paper-facing arithmetic mean. -/
theorem loading_arithmetic_mean_center_error_le_fast
    (N : NetworkSetup n) (L D s : ℝ) (j : ℕ) (i : Fin n)
    (e : ℝ) (t : ℕ) :
    let X : ℕ → Fin n → ℝ := fun r q =>
      (loadingTrajectory N L D s j i e r).primal q - D
    let U : ℕ → Fin n → ℝ := fun r q =>
      -retainedLoadingTracker N L D s j i e r q / L
    let xi := loadingSlowCenter N X
    let F := loadingFastCoordinates N X U
    |loadingArithmeticMean N L D s j i e t - D - xi t| ≤
      nodeSupNorm (F t).1 := by
  dsimp only
  let X : ℕ → Fin n → ℝ := fun r q =>
    (loadingTrajectory N L D s j i e r).primal q - D
  let U : ℕ → Fin n → ℝ := fun r q =>
    -retainedLoadingTracker N L D s j i e r q / L
  let xi := loadingSlowCenter N X
  let F := loadingFastCoordinates N X U
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr N.hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hidentity :
      loadingArithmeticMean N L D s j i e t - D - xi t =
        (n : ℝ)⁻¹ * ∑ q, (F t).1 q := by
    dsimp [loadingArithmeticMean, F, loadingFastCoordinates, X]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp [hnne]
    ring
  rw [hidentity, abs_mul, abs_of_nonneg (inv_nonneg.mpr hnpos.le)]
  calc
    (n : ℝ)⁻¹ * |∑ q, (F t).1 q| ≤
        (n : ℝ)⁻¹ * ∑ q, |(F t).1 q| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
        (inv_nonneg.mpr hnpos.le)
    _ ≤ (n : ℝ)⁻¹ * ∑ _q : Fin n, nodeSupNorm (F t).1 := by
      gcongr with q
      exact abs_le_nodeSupNorm (F t).1 q
    _ = nodeSupNorm (F t).1 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp [hnne]

def loadingFastScale (s : ℝ)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    (Fin n → ℝ) × (Fin n → ℝ) :=
  (fun q => s * z.1 q, fun q => s * z.2 q)

theorem loadingFastPerturbationInput_spec
    (N : NetworkSetup n) (t : ℕ) (E K : Fin n → ℝ) :
    dotProduct (absoluteProbability N (t + 1))
        (loadingFastPerturbationInput N t E K).1 = 0 ∧
      (∑ q, (loadingFastPerturbationInput N t E K).2 q) = 0 ∧
      nodeSupNorm (loadingFastPerturbationInput N t E K).1 +
          nodeL1Norm (loadingFastPerturbationInput N t E K).2 ≤
        2 * ((n : ℝ) + 1) * (nodeSupNorm E + nodeL1Norm K) := by
  simpa [loadingFastPerturbationInput] using
    loading_fast_perturbation_input_invariants_bound N t E K

/-- The genuine center forcing in equation (22) lies in the time-`t+1` fast
carrier.  This is the invariant interface needed before feeding that forcing
to the nonautonomous Duhamel expansion. -/
theorem loadingFastCenterInput_invariants
    (N : NetworkSetup n) (t : ℕ) (xi : ℝ) :
    dotProduct (absoluteProbability N (t + 1))
        (loadingFastCenterInput N t xi).1 = 0 ∧
      (∑ q, (loadingFastCenterInput N t xi).2 q) = 0 := by
  have hpi_sum : ∑ q, absoluteProbability N (t + 1) q = 1 :=
    (absoluteProbability_spec N).2.1 (t + 1)
  have hgain :
      dotProduct (absoluteProbability N (t + 1)) (pushMass N t) =
        gain N t := rfl
  have hmass : ∑ q, (pushMass N (t + 1) q - 1) = 0 := by
    rw [Finset.sum_sub_distrib, pushMass_sum_eq_n]
    simp
  constructor
  · simp only [loadingFastCenterInput]
    unfold dotProduct at hgain ⊢
    simp only [← mul_assoc]
    rw [← Finset.sum_mul]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hpi_sum, one_mul,
      hgain, sub_self, zero_mul]
  · simp only [loadingFastCenterInput]
    calc
      (∑ q, -(pushMass N (t + 1) q - 1) * gain N t * xi) =
          -(∑ q, (pushMass N (t + 1) q - 1)) * gain N t * xi := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, Finset.sum_neg_distrib]
      _ = 0 := by rw [hmass]; ring

/-- The printed equation-(22) center-input bound
`‖B_t ξ‖ ≤ 2 n (n+1) |ξ|`. -/
theorem loadingFastCenterInput_gauge_le
    (N : NetworkSetup n) (t : ℕ) (xi : ℝ) :
    nodeSupNorm (loadingFastCenterInput N t xi).1 +
        nodeL1Norm (loadingFastCenterInput N t xi).2 ≤
      2 * (n : ℝ) * ((n : ℝ) + 1) * |xi| := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hgain_nonneg : 0 ≤ gain N t := by
    unfold gain dotProduct
    exact Finset.sum_nonneg fun q _ =>
      mul_nonneg ((absoluteProbability_spec N).1 (t + 1) q)
        (pushMass_nonneg N t q)
  have hgain_le : gain N t ≤ (n : ℝ) :=
    (gain_bounds_before_corrected_center_control N t).2
  have hpush_le (q : Fin n) : pushMass N t q ≤ (n : ℝ) := by
    calc
      pushMass N t q ≤ ∑ r, pushMass N t r :=
        Finset.single_le_sum (fun r _ => pushMass_nonneg N t r)
          (Finset.mem_univ q)
      _ = (n : ℝ) := pushMass_sum_eq_n N t
  have hfirst_point (q : Fin n) :
      |(pushMass N t q - gain N t) * xi| ≤
        2 * (n : ℝ) * |xi| := by
    rw [abs_mul]
    calc
      |pushMass N t q - gain N t| * |xi| ≤
          (pushMass N t q + gain N t) * |xi| := by
        exact mul_le_mul_of_nonneg_right
          ((abs_sub _ _).trans_eq (by
            rw [abs_of_nonneg (pushMass_nonneg N t q),
              abs_of_nonneg hgain_nonneg])) (abs_nonneg xi)
      _ ≤ (2 * (n : ℝ)) * |xi| := by
        gcongr
        linarith [hpush_le q, hgain_le]
  have hfirst : nodeSupNorm (loadingFastCenterInput N t xi).1 ≤
      2 * (n : ℝ) * |xi| := by
    letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp N.hn
    unfold nodeSupNorm
    apply ciSup_le
    intro q
    exact hfirst_point q
  have hw_abs :
      (∑ q, |pushMass N (t + 1) q - 1|) ≤ 2 * (n : ℝ) := by
    calc
      (∑ q, |pushMass N (t + 1) q - 1|) ≤
          ∑ q, (pushMass N (t + 1) q + 1) := by
        apply Finset.sum_le_sum
        intro q _
        calc
          |pushMass N (t + 1) q - 1| ≤
              |pushMass N (t + 1) q| + |(1 : ℝ)| := abs_sub _ _
          _ = pushMass N (t + 1) q + 1 := by
            rw [abs_of_nonneg (pushMass_nonneg N (t + 1) q), abs_one]
      _ = 2 * (n : ℝ) := by
        rw [Finset.sum_add_distrib, pushMass_sum_eq_n]
        simp
        ring
  have hsecond_eq :
      nodeL1Norm (loadingFastCenterInput N t xi).2 =
        gain N t * |xi| *
          (∑ q, |pushMass N (t + 1) q - 1|) := by
    unfold nodeL1Norm loadingFastCenterInput
    simp_rw [abs_mul, abs_neg, abs_of_nonneg hgain_nonneg]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  have hsecond : nodeL1Norm (loadingFastCenterInput N t xi).2 ≤
      2 * (n : ℝ) * (n : ℝ) * |xi| := by
    rw [hsecond_eq]
    calc
      gain N t * |xi| * (∑ q, |pushMass N (t + 1) q - 1|) ≤
          (n : ℝ) * |xi| * (2 * (n : ℝ)) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right hgain_le (abs_nonneg xi)) hw_abs
          (Finset.sum_nonneg fun q _ => abs_nonneg _) (by positivity)
      _ = 2 * (n : ℝ) * (n : ℝ) * |xi| := by ring
  calc
    nodeSupNorm (loadingFastCenterInput N t xi).1 +
        nodeL1Norm (loadingFastCenterInput N t xi).2 ≤
      2 * (n : ℝ) * |xi| + 2 * (n : ℝ) * (n : ℝ) * |xi| :=
        add_le_add hfirst hsecond
    _ = 2 * (n : ℝ) * ((n : ℝ) + 1) * |xi| := by ring

/-- Algebraic equation-(22) bridge for a shifted primal state and a retained
state satisfying the exact negative-branch recurrence (21).  In particular,
the nonhomogeneous `-s B_t ξ_t` term is retained. -/
theorem loading_slow_fast_coordinates_of_recurrence
    (N : NetworkSetup n) (s : ℝ) (X U : ℕ → Fin n → ℝ) (t : ℕ)
    (hUzero : ∀ r, (∑ q, U r q) = 0)
    (hXrec : X (t + 1) = fun q =>
      (N.rowMix t *ᵥ X t) q + s * X t q + s * U t q)
    (hUrec : U (t + 1) = fun q =>
      (N.colMix t *ᵥ U t) q + ((N.colMix t - 1) *ᵥ X t) q) :
    let xi := loadingSlowCenter N X
    let F := loadingFastCoordinates N X U
    (dotProduct (absoluteProbability N t) (F t).1 = 0 ∧
      (∑ q, (F t).2 q) = 0) ∧
    xi (t + 1) =
      (1 + s * gain N t) * xi t +
        s * dotProduct (absoluteProbability N (t + 1))
          ((F t).1 + (F t).2) ∧
    F (t + 1) =
      loadingFastStep N t (F t) +
        loadingFastScale s
          (loadingFastPerturbationInput N t (F t).1 (F t).2) +
        loadingFastScale s (loadingFastCenterInput N t (xi t)) := by
  dsimp only
  have hpi_sum : ∑ q, absoluteProbability N t q = 1 :=
    (absoluteProbability_spec N).2.1 t
  have hcenter : dotProduct (absoluteProbability N t)
      (loadingFastCoordinates N X U t).1 = 0 := by
    simp only [loadingFastCoordinates, loadingSlowCenter]
    unfold dotProduct
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hpi_sum, one_mul,
      sub_self]
  have hmass : ∑ q, (pushMass N t q - 1) = 0 := by
    rw [Finset.sum_sub_distrib, pushMass_sum_eq_n]
    simp
  have hzero : (∑ q, (loadingFastCoordinates N X U t).2 q) = 0 := by
    simp only [loadingFastCoordinates]
    rw [Finset.sum_sub_distrib, hUzero t, ← Finset.sum_mul, hmass,
      zero_mul, sub_zero]
  let p : Fin n → ℝ := absoluteProbability N (t + 1)
  let xi : ℝ := loadingSlowCenter N X t
  have hrow : dotProduct p (N.rowMix t *ᵥ X t) = xi := by
    dsimp [p, xi, loadingSlowCenter]
    rw [Matrix.dotProduct_mulVec, absoluteProbability_step]
  have hEK :
      (loadingFastCoordinates N X U t).1 +
          (loadingFastCoordinates N X U t).2 =
        fun q => X t q + U t q - pushMass N t q * xi := by
    funext q
    simp only [loadingFastCoordinates, Pi.add_apply]
    dsimp [xi]
    ring
  have hell : dotProduct p
      ((loadingFastCoordinates N X U t).1 +
        (loadingFastCoordinates N X U t).2) =
      dotProduct p (X t) + dotProduct p (U t) - gain N t * xi := by
    rw [hEK]
    unfold dotProduct gain
    simp_rw [mul_sub, mul_add, ← mul_assoc]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul]
    dsimp [p]
    rfl
  have hnext : loadingSlowCenter N X (t + 1) =
      xi + s * dotProduct p (X t) + s * dotProduct p (U t) := by
    unfold loadingSlowCenter
    rw [hXrec]
    change dotProduct p (fun q =>
        (N.rowMix t *ᵥ X t) q + s * X t q + s * U t q) = _
    unfold dotProduct
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hXscale : (∑ q, p q * (s * X t q)) =
        s * ∑ q, p q * X t q := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    have hUscale : (∑ q, p q * (s * U t q)) =
        s * ∑ q, p q * U t q := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    rw [hXscale, hUscale]
    rw [show (∑ q, p q * (N.rowMix t *ᵥ X t) q) = xi by
      simpa [dotProduct] using hrow]
  have hxi_rec : loadingSlowCenter N X (t + 1) =
      (1 + s * gain N t) * loadingSlowCenter N X t +
        s * dotProduct (absoluteProbability N (t + 1))
          ((loadingFastCoordinates N X U t).1 +
            (loadingFastCoordinates N X U t).2) := by
    rw [hnext, hell]
    dsimp [xi, p]
    ring
  refine ⟨⟨hcenter, hzero⟩, hxi_rec, ?_⟩
  let F := loadingFastCoordinates N X U t
  let ell := dotProduct p (F.1 + F.2)
  have hrow_fast (q : Fin n) :
      (N.rowMix t *ᵥ F.1) q = (N.rowMix t *ᵥ X t) q - xi := by
    have hrow_sum : ∑ r, N.rowMix t q r = 1 :=
      Matrix.sum_row_of_mem_rowStochastic (N.row_stochastic t) q
    dsimp [F, loadingFastCoordinates]
    simp only [Matrix.smulVec, Matrix.mulVec, dotProduct]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hrow_sum, one_mul]
  apply Prod.ext
  · funext q
    change X (t + 1) q - loadingSlowCenter N X (t + 1) =
      (N.rowMix t *ᵥ F.1) q +
        s * (F.1 q + F.2 q - ell) +
        s * ((pushMass N t q - gain N t) * xi)
    rw [congrFun hXrec q, hxi_rec, hrow_fast]
    have hEKq := congrFun hEK q
    simp only [Pi.add_apply] at hEKq
    rw [hEKq]
    dsimp [ell, F, p] at *
    ring
  · have hFst : F.1 = X t - fun _ => xi := by
      funext q
      dsimp [F, loadingFastCoordinates, xi]
    have hSnd : F.2 = U t - fun q => (pushMass N t q - 1) * xi := by
      funext q
      dsimp [F, loadingFastCoordinates]
    have hcenter_transport (q : Fin n) :
        (N.colMix t *ᵥ (fun r => (pushMass N t r - 1) * xi)) q +
            ((N.colMix t - 1) *ᵥ (fun _ => xi)) q =
          (pushMass N (t + 1) q - 1) * xi := by
      have hCw :
          (∑ r, N.colMix t q r * ((pushMass N t r - 1) * xi)) =
            (∑ r, N.colMix t q r * pushMass N t r) * xi -
              (∑ r, N.colMix t q r) * xi := by
        calc
          (∑ r, N.colMix t q r * ((pushMass N t r - 1) * xi)) =
              ∑ r, ((N.colMix t q r * pushMass N t r) * xi -
                N.colMix t q r * xi) := by
            apply Finset.sum_congr rfl
            intro r _
            ring
          _ = (∑ r, N.colMix t q r * pushMass N t r) * xi -
                (∑ r, N.colMix t q r) * xi := by
            rw [Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_mul]
      have hCone : (∑ r, N.colMix t q r * xi) =
          (∑ r, N.colMix t q r) * xi := by
        rw [Finset.sum_mul]
      rw [pushMass_succ, Matrix.sub_mulVec, Matrix.one_mulVec]
      simp only [Pi.add_apply, Pi.sub_apply, Matrix.smulVec, Matrix.mulVec,
        dotProduct]
      rw [hCw, hCone]
      ring
    have hbase (q : Fin n) :
        (loadingFastStep N t F).2 q =
          U (t + 1) q - (pushMass N (t + 1) q - 1) * xi := by
      simp only [loadingFastStep, Pi.add_apply]
      rw [hFst, hSnd, Matrix.mulVec_sub, Matrix.mulVec_sub]
      simp only [Pi.sub_apply]
      rw [congrFun hUrec q, ← hcenter_transport q]
      ring
    funext q
    change U (t + 1) q -
        (pushMass N (t + 1) q - 1) * loadingSlowCenter N X (t + 1) =
      (loadingFastStep N t F).2 q +
        s * (-(pushMass N (t + 1) q - 1) * ell) +
        s * (-(pushMass N (t + 1) q - 1) * gain N t * xi)
    rw [hbase, hxi_rec]
    dsimp [ell, F, p, xi]
    ring

/-- Equation (22) instantiated on the shifted true loading trajectory and its
retained tracker.  The recurrence premise is supplied by the verified
negative-branch identity (21); no tracker reset is introduced. -/
theorem loading_negative_branch_slow_fast_coordinates
    (N : NetworkSetup n) (L D s a : ℝ) (j : ℕ) (i : Fin n) (t : ℕ)
    (hrec :
      let e := -a * D / ((s / L) * influenceRow N j i)
      let X : ℕ → Fin n → ℝ := fun r q =>
        (loadingTrajectory N L D s j i e r).primal q - D
      let U : ℕ → Fin n → ℝ := fun r q =>
        -retainedLoadingTracker N L D s j i e r q / L
      X (t + 1) = (fun q =>
        (N.rowMix t *ᵥ X t) q + s * X t q + s * U t q) ∧
      U (t + 1) = (fun q =>
        (N.colMix t *ᵥ U t) q + ((N.colMix t - 1) *ᵥ X t) q)) :
    let e := -a * D / ((s / L) * influenceRow N j i)
    let X : ℕ → Fin n → ℝ := fun r q =>
      (loadingTrajectory N L D s j i e r).primal q - D
    let U : ℕ → Fin n → ℝ := fun r q =>
      -retainedLoadingTracker N L D s j i e r q / L
    let xi := loadingSlowCenter N X
    let F := loadingFastCoordinates N X U
    (dotProduct (absoluteProbability N t) (F t).1 = 0 ∧
      (∑ q, (F t).2 q) = 0) ∧
    xi (t + 1) =
      (1 + s * gain N t) * xi t +
        s * dotProduct (absoluteProbability N (t + 1))
          ((F t).1 + (F t).2) ∧
    F (t + 1) =
      loadingFastStep N t (F t) +
        loadingFastScale s
          (loadingFastPerturbationInput N t (F t).1 (F t).2) +
        loadingFastScale s (loadingFastCenterInput N t (xi t)) := by
  let e : ℝ := -a * D / ((s / L) * influenceRow N j i)
  let X : ℕ → Fin n → ℝ := fun r q =>
    (loadingTrajectory N L D s j i e r).primal q - D
  let U : ℕ → Fin n → ℝ := fun r q =>
    -retainedLoadingTracker N L D s j i e r q / L
  have hrec' :
      X (t + 1) = (fun q =>
        (N.rowMix t *ᵥ X t) q + s * X t q + s * U t q) ∧
      U (t + 1) = (fun q =>
        (N.colMix t *ᵥ U t) q + ((N.colMix t - 1) *ᵥ X t) q) := by
    simpa [e, X, U] using hrec
  have hUzero (r : ℕ) : (∑ q, U r q) = 0 := by
    have hVzero :
        (∑ q, retainedLoadingTracker N L D s j i e r q) = 0 := by
      rw [retainedLoadingTracker_eq_trackerInnovationResponse]
      exact FiniteNetwork.trackerInnovationResponse_sum_eq_zero
        N.colMix
        (fun u => loadingOracle L D j i e u
          (loadingTrajectory N L D s j i e u).primal) r
        (fun u q =>
          Matrix.sum_col_of_mem_colStochastic (N.col_stochastic u) q)
    dsimp [U]
    rw [← Finset.sum_div, Finset.sum_neg_distrib, hVzero]
    simp
  simpa [e, X, U] using
    loading_slow_fast_coordinates_of_recurrence N s X U t hUzero
      hrec'.1 hrec'.2

theorem nodeSupNorm_const_mul_le
    (N : NetworkSetup n) (s : ℝ) (hs : 0 ≤ s) (x : Fin n → ℝ) :
    nodeSupNorm (fun q => s * x q) ≤ s * nodeSupNorm x := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp N.hn
  unfold nodeSupNorm
  apply ciSup_le
  intro q
  rw [abs_mul, abs_of_nonneg hs]
  exact mul_le_mul_of_nonneg_left (abs_le_nodeSupNorm x q) hs

theorem nodeL1Norm_const_mul
    (s : ℝ) (hs : 0 ≤ s) (x : Fin n → ℝ) :
    nodeL1Norm (fun q => s * x q) = s * nodeL1Norm x := by
  unfold nodeL1Norm
  simp_rw [abs_mul, abs_of_nonneg hs]
  exact (Finset.mul_sum _ _ _).symm

theorem loadingFastScale_invariants_bound
    (N : NetworkSetup n) (t : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (z : (Fin n → ℝ) × (Fin n → ℝ))
    (hcenter : dotProduct (absoluteProbability N t) z.1 = 0)
    (hzero : (∑ q, z.2 q) = 0) :
    dotProduct (absoluteProbability N t) (loadingFastScale s z).1 = 0 ∧
      (∑ q, (loadingFastScale s z).2 q) = 0 ∧
      nodeSupNorm (loadingFastScale s z).1 +
          nodeL1Norm (loadingFastScale s z).2 ≤
        s * (nodeSupNorm z.1 + nodeL1Norm z.2) := by
  constructor
  · simp only [loadingFastScale]
    unfold dotProduct at hcenter ⊢
    calc
      (∑ q, absoluteProbability N t q * (s * z.1 q)) =
          s * ∑ q, absoluteProbability N t q * z.1 q := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        ring
      _ = 0 := by rw [hcenter, mul_zero]
  constructor
  · simp only [loadingFastScale]
    rw [← Finset.mul_sum, hzero, mul_zero]
  · simp only [loadingFastScale]
    rw [nodeL1Norm_const_mul s hs]
    calc
      nodeSupNorm (fun q => s * z.1 q) + s * nodeL1Norm z.2 ≤
          s * nodeSupNorm z.1 + s * nodeL1Norm z.2 :=
        add_le_add (nodeSupNorm_const_mul_le N s hs z.1) le_rfl
      _ = s * (nodeSupNorm z.1 + nodeL1Norm z.2) := by ring

/-- The homogeneous triangular step transports the time-indexed fast-space
constraints from `t` to `t+1`. -/
theorem loadingFastStep_invariants
    (N : NetworkSetup n) (t : ℕ) (E K : Fin n → ℝ)
    (hE : dotProduct (absoluteProbability N t) E = 0)
    (hK : (∑ q, K q) = 0) :
    dotProduct (absoluteProbability N (t + 1))
        (loadingFastStep N t (E, K)).1 = 0 ∧
      (∑ q, (loadingFastStep N t (E, K)).2 q) = 0 := by
  constructor
  · simp only [loadingFastStep]
    rw [Matrix.dotProduct_mulVec, (absoluteProbability_spec N).2.2 t, hE]
  · simp only [loadingFastStep, Pi.add_apply, Finset.sum_add_distrib]
    have hcol : (∑ q, (N.colMix t *ᵥ K) q) = 0 := by
      rw [Matrix.sum_mulVec_of_mem_colStochastic (N.col_stochastic t), hK]
    have hinnovation :
        (∑ q, ((N.colMix t - 1) *ᵥ E) q) = 0 := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      simp only [Pi.sub_apply]
      rw [Finset.sum_sub_distrib,
        Matrix.sum_mulVec_of_mem_colStochastic (N.col_stochastic t)]
      ring
    rw [hcol, hinnovation]
    ring

/-- Supremum-norm triangle inequality for a finite sum of node vectors. -/
theorem nodeSupNorm_finset_sum_le
    (N : NetworkSetup n) {ι : Type*} (S : Finset ι) (f : ι → Fin n → ℝ) :
    nodeSupNorm (∑ r ∈ S, f r) ≤ ∑ r ∈ S, nodeSupNorm (f r) := by
  classical
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp N.hn
  unfold nodeSupNorm
  apply ciSup_le
  intro q
  calc
    |(∑ r ∈ S, f r) q| = |∑ r ∈ S, f r q| := by simp
    _ ≤ ∑ r ∈ S, |f r q| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ S, ⨆ i, |f r i| := by
      exact Finset.sum_le_sum fun r _ =>
        le_ciSup (Finite.bddAbove_range (fun i : Fin n => |f r i|)) q

/-- The source fast gauge is subadditive over finite pair-valued sums. -/
theorem loadingFastGauge_finset_sum_le
    (N : NetworkSetup n) {ι : Type*} (S : Finset ι)
    (z : ι → (Fin n → ℝ) × (Fin n → ℝ)) :
    nodeSupNorm (∑ r ∈ S, (z r).1) +
        nodeL1Norm (∑ r ∈ S, (z r).2) ≤
      ∑ r ∈ S, (nodeSupNorm (z r).1 + nodeL1Norm (z r).2) := by
  calc
    nodeSupNorm (∑ r ∈ S, (z r).1) +
        nodeL1Norm (∑ r ∈ S, (z r).2) ≤
      (∑ r ∈ S, nodeSupNorm (z r).1) +
        ∑ r ∈ S, nodeL1Norm (z r).2 :=
      add_le_add (nodeSupNorm_finset_sum_le N S (fun r => (z r).1))
        (nodeL1Norm_finset_sum_le S (fun r => (z r).2))
    _ = ∑ r ∈ S, (nodeSupNorm (z r).1 + nodeL1Norm (z r).2) := by
      rw [Finset.sum_add_distrib]

theorem nodeSupNorm_add_le
    (N : NetworkSetup n) (x y : Fin n → ℝ) :
    nodeSupNorm (x + y) ≤ nodeSupNorm x + nodeSupNorm y := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp N.hn
  unfold nodeSupNorm
  apply ciSup_le
  intro q
  exact (abs_add_le (x q) (y q)).trans
    (add_le_add (le_ciSup (Finite.bddAbove_range (fun i : Fin n => |x i|)) q)
      (le_ciSup (Finite.bddAbove_range (fun i : Fin n => |y i|)) q))

theorem loadingFastGauge_add_le
    (N : NetworkSetup n)
    (z w : (Fin n → ℝ) × (Fin n → ℝ)) :
    nodeSupNorm (z + w).1 + nodeL1Norm (z + w).2 ≤
      (nodeSupNorm z.1 + nodeL1Norm z.2) +
        (nodeSupNorm w.1 + nodeL1Norm w.2) := by
  simp only [Prod.fst_add, Prod.snd_add]
  exact (add_le_add (nodeSupNorm_add_le N z.1 w.1)
    (nodeL1Norm_add_le z.2 w.2)).trans_eq (by ring)

/-- Finite mixed-geometric identity underlying the bounded-perturbation
Duhamel estimate. -/
theorem geometric_add_eq_initial_add_convolution
    (r d : ℝ) (m : ℕ) :
    r ^ m + d * (∑ q ∈ Finset.range m,
      r ^ (m - q - 1) * (r + d) ^ q) = (r + d) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hsplit :
          (∑ q ∈ Finset.range (m + 1),
              r ^ (m + 1 - q - 1) * (r + d) ^ q) =
            r * (∑ q ∈ Finset.range m,
              r ^ (m - q - 1) * (r + d) ^ q) + (r + d) ^ m := by
        rw [Finset.sum_range_succ]
        have hlast :
            r ^ (m + 1 - m - 1) * (r + d) ^ m = (r + d) ^ m := by
          simp
        rw [hlast]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        have hqm : q < m := Finset.mem_range.mp hq
        have hexp : m + 1 - q - 1 = (m - q - 1) + 1 := by omega
        rw [hexp, pow_succ]
        ring
      rw [hsplit, pow_succ, pow_succ, ← ih]
      ring

/-- A nonnegative response dominated by its own geometric Duhamel convolution
inherits the perturbed rate `r + M d`.  This is the scalar form of the source
estimate `M(r+Md)^m`. -/
theorem geometric_bound_of_self_duhamel
    (u : ℕ → ℝ) (M r d : ℝ)
    (hM : 1 ≤ M) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (hu : ∀ m, 0 ≤ u m)
    (hduhamel : ∀ m,
      u m ≤ M * r ^ m * u 0 +
        M * d * (∑ q ∈ Finset.range m,
          r ^ (m - q - 1) * u q)) :
    ∀ m, u m ≤ M * (r + M * d) ^ m * u 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      have hsum :
          (∑ q ∈ Finset.range m, r ^ (m - q - 1) * u q) ≤
            ∑ q ∈ Finset.range m,
              r ^ (m - q - 1) *
                (M * (r + M * d) ^ q * u 0) := by
        apply Finset.sum_le_sum
        intro q hq
        exact mul_le_mul_of_nonneg_left
          (ih q (Finset.mem_range.mp hq)) (pow_nonneg hr _)
      have hMd : 0 ≤ M * d := mul_nonneg (by linarith) hd
      calc
        u m ≤ M * r ^ m * u 0 +
            M * d * (∑ q ∈ Finset.range m,
              r ^ (m - q - 1) * u q) := hduhamel m
        _ ≤ M * r ^ m * u 0 +
            M * d * (∑ q ∈ Finset.range m,
              r ^ (m - q - 1) *
                (M * (r + M * d) ^ q * u 0)) := by
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum hMd)
        _ = M * (r ^ m + (M * d) *
              (∑ q ∈ Finset.range m,
                r ^ (m - q - 1) * (r + M * d) ^ q)) * u 0 := by
          have hfactor :
              (∑ q ∈ Finset.range m,
                r ^ (m - q - 1) *
                  (M * (r + M * d) ^ q * u 0)) =
                M * u 0 * (∑ q ∈ Finset.range m,
                  r ^ (m - q - 1) * (r + M * d) ^ q) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro q _
            ring
          rw [hfactor]
          ring
        _ = M * (r + M * d) ^ m * u 0 := by
          rw [geometric_add_eq_initial_add_convolution r (M * d) m]

/-- The explicit homogeneous triangular propagator occurring in equation (23). -/
def loadingFastPropagator (N : NetworkSetup n) (t k : ℕ)
    (E K : Fin n → ℝ) : (Fin n → ℝ) × (Fin n → ℝ) :=
  (forwardProduct N.rowMix t k *ᵥ E,
    forwardProduct N.colMix t k *ᵥ K +
      ∑ r ∈ Finset.Ico k t,
        forwardProduct N.colMix t (r + 1) *ᵥ
          ((N.colMix r - 1) *ᵥ
            (forwardProduct N.rowMix r k *ᵥ E)))

theorem loadingFastStep_add (N : NetworkSetup n) (t : ℕ)
    (z w : (Fin n → ℝ) × (Fin n → ℝ)) :
    loadingFastStep N t (z + w) =
      loadingFastStep N t z + loadingFastStep N t w := by
  apply Prod.ext <;> funext q
  · simp [loadingFastStep, Matrix.mulVec_add]
  · simp [loadingFastStep, Matrix.mulVec_add]
    ring

theorem loadingFastStep_sum {ι : Type*} (N : NetworkSetup n) (t : ℕ)
    (S : Finset ι) (z : ι → (Fin n → ℝ) × (Fin n → ℝ)) :
    loadingFastStep N t (∑ r ∈ S, z r) =
      ∑ r ∈ S, loadingFastStep N t (z r) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [loadingFastStep]
  | @insert a S ha ih =>
      simp only [Finset.sum_insert, ha, not_false_eq_true]
      rw [loadingFastStep_add, ih]

theorem loadingFastPropagator_self
    (N : NetworkSetup n) (k : ℕ) (E K : Fin n → ℝ) :
    loadingFastPropagator N k k E K = (E, K) := by
  simp [loadingFastPropagator, forwardProduct]

/-- The explicit product has the expected one-step triangular successor law. -/
theorem loadingFastPropagator_succ
    (N : NetworkSetup n) (t k : ℕ) (hkt : k ≤ t) (E K : Fin n → ℝ) :
    loadingFastPropagator N (t + 1) k E K =
      loadingFastStep N t (loadingFastPropagator N t k E K) := by
  have hforward (W : ℕ → NetworkMatrix n) (q : ℕ) (hqt : q ≤ t) :
      forwardProduct W (t + 1) q = W t * forwardProduct W t q := by
    unfold forwardProduct
    rw [show t + 1 - q = (t - q) + 1 by omega,
      FiniteNetwork.consecutiveProduct_succ,
      show q + (t - q) = t by omega]
  have hend (W : ℕ → NetworkMatrix n) :
      forwardProduct W (t + 1) (t + 1) = 1 := by
    simp [forwardProduct]
  have hsum :
      (∑ r ∈ Finset.Ico k t,
        forwardProduct N.colMix (t + 1) (r + 1) *ᵥ
          ((N.colMix r - 1) *ᵥ
            (forwardProduct N.rowMix r k *ᵥ E))) =
      N.colMix t *ᵥ
        (∑ r ∈ Finset.Ico k t,
          forwardProduct N.colMix t (r + 1) *ᵥ
            ((N.colMix r - 1) *ᵥ
              (forwardProduct N.rowMix r k *ᵥ E))) := by
    rw [Matrix.mulVec_sum]
    apply Finset.sum_congr rfl
    intro r hr
    have hrt : r + 1 ≤ t := Nat.succ_le_of_lt (Finset.mem_Ico.mp hr).2
    rw [hforward N.colMix (r + 1) hrt]
    simp only [Matrix.mulVec_mulVec, mul_assoc]
  apply Prod.ext
  · simp only [loadingFastPropagator, loadingFastStep]
    rw [hforward N.rowMix k hkt]
    simp only [Matrix.mulVec_mulVec]
  · simp only [loadingFastPropagator, loadingFastStep]
    rw [hforward N.colMix k hkt,
      Finset.sum_Ico_succ_top hkt, hsum, hend, Matrix.one_mulVec,
      Matrix.mulVec_add]
    simp only [Matrix.mulVec_mulVec]
    abel

/-- Exact finite Duhamel expansion for the forced triangular fast system. -/
theorem loading_fast_duhamel
    (N : NetworkSetup n)
    (E K IE IK : ℕ → Fin n → ℝ) (k : ℕ)
    (hstep : ∀ t, k ≤ t →
      (E (t + 1), K (t + 1)) =
        loadingFastStep N t (E t, K t) + (IE t, IK t)) :
    ∀ t, k ≤ t →
      (E t, K t) =
        loadingFastPropagator N t k (E k) (K k) +
          ∑ r ∈ Finset.Ico k t,
            loadingFastPropagator N t (r + 1) (IE r) (IK r) := by
  intro t hkt
  induction t with
  | zero =>
      have hk : k = 0 := by omega
      subst k
      simp [loadingFastPropagator_self]
  | succ t ih =>
      by_cases hEq : k = t + 1
      · subst k
        simp [loadingFastPropagator_self]
      · have hkt' : k ≤ t := by omega
        rw [hstep t hkt', ih hkt']
        rw [loadingFastStep_add, loadingFastStep_sum]
        rw [← loadingFastPropagator_succ N t k hkt' (E k) (K k)]
        have hprop (r : ℕ) (hr : r ∈ Finset.Ico k t) :
            loadingFastStep N t
                (loadingFastPropagator N t (r + 1) (IE r) (IK r)) =
              loadingFastPropagator N (t + 1) (r + 1) (IE r) (IK r) := by
          symm
          exact loadingFastPropagator_succ N t (r + 1)
            (Nat.succ_le_of_lt (Finset.mem_Ico.mp hr).2) (IE r) (IK r)
        have hsum :
            (∑ r ∈ Finset.Ico k t,
              loadingFastStep N t
                (loadingFastPropagator N t (r + 1) (IE r) (IK r))) =
            ∑ r ∈ Finset.Ico k t,
              loadingFastPropagator N (t + 1) (r + 1) (IE r) (IK r) := by
          apply Finset.sum_congr rfl
          intro r hr
          exact hprop r hr
        rw [hsum, Finset.sum_Ico_succ_top hkt',
          loadingFastPropagator_self]
        abel

/-- Every actual `A_t-sJ_t` step preserves the canonical-center and zero-sum
constraints; the indices advance together with the absolute-probability
sequence. -/
theorem loading_perturbed_fast_invariants
    (N : NetworkSetup n) (s : ℝ) (hs : 0 ≤ s)
    (E K : ℕ → Fin n → ℝ) (k : ℕ)
    (hE0 : dotProduct (absoluteProbability N k) (E k) = 0)
    (hK0 : (∑ q, K k q) = 0)
    (hstep : ∀ t, k ≤ t →
      (E (t + 1), K (t + 1)) =
        loadingFastStep N t (E t, K t) +
          loadingFastScale s (loadingFastPerturbationInput N t (E t) (K t))) :
    ∀ t, k ≤ t →
      dotProduct (absoluteProbability N t) (E t) = 0 ∧
        (∑ q, K t q) = 0 := by
  intro t hkt
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkt
  induction m with
  | zero => simpa using And.intro hE0 hK0
  | succ m ih =>
      let r : ℕ := k + m
      have hkr : k ≤ r := by dsimp [r]; omega
      have ih' := ih hkr
      have hA := loadingFastStep_invariants N r (E r) (K r) ih'.1 ih'.2
      have hP := loadingFastPerturbationInput_spec N r (E r) (K r)
      have hSP := loadingFastScale_invariants_bound N (r + 1) s hs
        (loadingFastPerturbationInput N r (E r) (K r)) hP.1 hP.2.1
      have hrec := hstep r hkr
      have hErec : E (r + 1) =
          (loadingFastStep N r (E r, K r)).1 +
            (loadingFastScale s
              (loadingFastPerturbationInput N r (E r) (K r))).1 := by
        exact congrArg Prod.fst hrec
      have hKrec : K (r + 1) =
          (loadingFastStep N r (E r, K r)).2 +
            (loadingFastScale s
              (loadingFastPerturbationInput N r (E r) (K r))).2 := by
        exact congrArg Prod.snd hrec
      have htime : k + (m + 1) = r + 1 := by dsimp [r]; omega
      rw [htime]
      constructor
      · rw [hErec]
        change dotProduct (absoluteProbability N (r + 1))
          ((loadingFastStep N r (E r, K r)).1 +
            (loadingFastScale s
              (loadingFastPerturbationInput N r (E r) (K r))).1) = 0
        unfold dotProduct at hA hSP ⊢
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
        rw [hA.1, hSP.1]
        ring
      · rw [hKrec]
        change (∑ q,
          ((loadingFastStep N r (E r, K r)).2 +
            (loadingFastScale s
              (loadingFastPerturbationInput N r (E r) (K r))).2) q) = 0
        simp only [Pi.add_apply, Finset.sum_add_distrib]
        rw [hA.2, hSP.2.1]
        ring

theorem loadingFastPropagator_gauge_le
    (N : NetworkSetup n) (M r : ℝ)
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
        M * r ^ (t - k) * (nodeSupNorm E + nodeL1Norm K))
    (t k : ℕ) (hkt : k ≤ t) (E K : Fin n → ℝ)
    (hE : dotProduct (absoluteProbability N k) E = 0)
    (hK : (∑ i, K i) = 0) :
    nodeSupNorm (loadingFastPropagator N t k E K).1 +
        nodeL1Norm (loadingFastPropagator N t k E K).2 ≤
      M * r ^ (t - k) * (nodeSupNorm E + nodeL1Norm K) := by
  simpa [loadingFastPropagator] using htriangular k t hkt E K hE hK

theorem loadingFastScale_perturbation_gauge_le
    (N : NetworkSetup n) (t : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (E K : Fin n → ℝ) :
    nodeSupNorm
        (loadingFastScale s (loadingFastPerturbationInput N t E K)).1 +
      nodeL1Norm
        (loadingFastScale s (loadingFastPerturbationInput N t E K)).2 ≤
      s * (2 * ((n : ℝ) + 1)) *
        (nodeSupNorm E + nodeL1Norm K) := by
  have hP := loadingFastPerturbationInput_spec N t E K
  have hscale := loadingFastScale_invariants_bound N (t + 1) s hs
    (loadingFastPerturbationInput N t E K) hP.1 hP.2.1
  calc
    nodeSupNorm
          (loadingFastScale s (loadingFastPerturbationInput N t E K)).1 +
        nodeL1Norm
          (loadingFastScale s (loadingFastPerturbationInput N t E K)).2 ≤
        s * (nodeSupNorm (loadingFastPerturbationInput N t E K).1 +
          nodeL1Norm (loadingFastPerturbationInput N t E K).2) := hscale.2.2
    _ ≤ s * (2 * ((n : ℝ) + 1) *
          (nodeSupNorm E + nodeL1Norm K)) :=
      mul_le_mul_of_nonneg_left hP.2.2 hs
    _ = s * (2 * ((n : ℝ) + 1)) *
          (nodeSupNorm E + nodeL1Norm K) := by ring

/-- Termwise geometric estimate for an exact triangular Duhamel expansion. -/
theorem loading_fast_duhamel_gauge_le
    (N : NetworkSetup n) (M r : ℝ)
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
        M * r ^ (t - k) * (nodeSupNorm E + nodeL1Norm K))
    (E K IE IK : ℕ → Fin n → ℝ) (k t : ℕ) (hkt : k ≤ t)
    (hE0 : dotProduct (absoluteProbability N k) (E k) = 0)
    (hK0 : (∑ i, K k i) = 0)
    (hI : ∀ q ∈ Finset.Ico k t,
      dotProduct (absoluteProbability N (q + 1)) (IE q) = 0 ∧
        (∑ i, IK q i) = 0)
    (hduhamel : (E t, K t) =
      loadingFastPropagator N t k (E k) (K k) +
        ∑ q ∈ Finset.Ico k t,
          loadingFastPropagator N t (q + 1) (IE q) (IK q)) :
    nodeSupNorm (E t) + nodeL1Norm (K t) ≤
      M * r ^ (t - k) * (nodeSupNorm (E k) + nodeL1Norm (K k)) +
        ∑ q ∈ Finset.Ico k t,
          M * r ^ (t - q - 1) *
            (nodeSupNorm (IE q) + nodeL1Norm (IK q)) := by
  let z0 := loadingFastPropagator N t k (E k) (K k)
  let zsum := ∑ q ∈ Finset.Ico k t,
    loadingFastPropagator N t (q + 1) (IE q) (IK q)
  have hbase := loadingFastPropagator_gauge_le N M r htriangular
    t k hkt (E k) (K k) hE0 hK0
  have hresponse := loadingFastGauge_finset_sum_le N (Finset.Ico k t)
    (fun q => loadingFastPropagator N t (q + 1) (IE q) (IK q))
  have hzsum_fst : zsum.1 =
      ∑ q ∈ Finset.Ico k t,
        (loadingFastPropagator N t (q + 1) (IE q) (IK q)).1 := by
    classical
    dsimp [zsum]
    let S := Finset.Ico k t
    change (∑ q ∈ S,
      loadingFastPropagator N t (q + 1) (IE q) (IK q)).1 =
        ∑ q ∈ S,
          (loadingFastPropagator N t (q + 1) (IE q) (IK q)).1
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a S ha ih => simp [ha, ih]
  have hzsum_snd : zsum.2 =
      ∑ q ∈ Finset.Ico k t,
        (loadingFastPropagator N t (q + 1) (IE q) (IK q)).2 := by
    classical
    dsimp [zsum]
    let S := Finset.Ico k t
    change (∑ q ∈ S,
      loadingFastPropagator N t (q + 1) (IE q) (IK q)).2 =
        ∑ q ∈ S,
          (loadingFastPropagator N t (q + 1) (IE q) (IK q)).2
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a S ha ih => simp [ha, ih]
  have hresponse' :
      nodeSupNorm zsum.1 + nodeL1Norm zsum.2 ≤
        ∑ q ∈ Finset.Ico k t,
          (nodeSupNorm (loadingFastPropagator N t (q + 1) (IE q) (IK q)).1 +
            nodeL1Norm (loadingFastPropagator N t (q + 1) (IE q) (IK q)).2) := by
    rw [hzsum_fst, hzsum_snd]
    exact hresponse
  have hterm (q : ℕ) (hq : q ∈ Finset.Ico k t) :
      nodeSupNorm (loadingFastPropagator N t (q + 1) (IE q) (IK q)).1 +
          nodeL1Norm (loadingFastPropagator N t (q + 1) (IE q) (IK q)).2 ≤
        M * r ^ (t - q - 1) *
          (nodeSupNorm (IE q) + nodeL1Norm (IK q)) := by
    have hqt : q + 1 ≤ t := Nat.succ_le_of_lt (Finset.mem_Ico.mp hq).2
    have hraw := loadingFastPropagator_gauge_le N M r htriangular
      t (q + 1) hqt (IE q) (IK q) (hI q hq).1 (hI q hq).2
    simpa [show t - (q + 1) = t - q - 1 by omega] using hraw
  change nodeSupNorm ((E t, K t).1) + nodeL1Norm ((E t, K t).2) ≤ _
  rw [hduhamel]
  calc
    nodeSupNorm (z0 + zsum).1 + nodeL1Norm (z0 + zsum).2 ≤
        (nodeSupNorm z0.1 + nodeL1Norm z0.2) +
          (nodeSupNorm zsum.1 + nodeL1Norm zsum.2) :=
      loadingFastGauge_add_le N z0 zsum
    _ ≤ (nodeSupNorm z0.1 + nodeL1Norm z0.2) +
          ∑ q ∈ Finset.Ico k t,
            (nodeSupNorm (loadingFastPropagator N t (q + 1) (IE q) (IK q)).1 +
              nodeL1Norm (loadingFastPropagator N t (q + 1) (IE q) (IK q)).2) :=
      by
        exact add_le_add le_rfl hresponse'
    _ ≤ M * r ^ (t - k) * (nodeSupNorm (E k) + nodeL1Norm (K k)) +
          ∑ q ∈ Finset.Ico k t,
            M * r ^ (t - q - 1) *
              (nodeSupNorm (IE q) + nodeL1Norm (IK q)) := by
      exact add_le_add hbase (Finset.sum_le_sum fun q hq => hterm q hq)

/-- Geometric decay for the genuine constrained nonautonomous
`A_t-sJ_t` evolution.  The explicit cap is the source condition
`M s J₀ ≤ r_f-r`; no bound is inferred from the public `1/(64n)` cap. -/
theorem loading_perturbed_fast_product_geometric
    (N : NetworkSetup n) (M s : ℝ)
    (hM : 1 ≤ M) (hs : 0 ≤ s)
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
          (nodeSupNorm E + nodeL1Norm K))
    (hcap : loadingFastRate N +
      M * (s * (2 * ((n : ℝ) + 1))) ≤ loadingTransverseRate N)
    (E K : ℕ → Fin n → ℝ) (k : ℕ)
    (hE0 : dotProduct (absoluteProbability N k) (E k) = 0)
    (hK0 : (∑ i, K k i) = 0)
    (hstep : ∀ t, k ≤ t →
      (E (t + 1), K (t + 1)) =
        loadingFastStep N t (E t, K t) +
          loadingFastScale s
            (loadingFastPerturbationInput N t (E t) (K t))) :
    ∀ t, k ≤ t →
      nodeSupNorm (E t) + nodeL1Norm (K t) ≤
        M * loadingTransverseRate N ^ (t - k) *
          (nodeSupNorm (E k) + nodeL1Norm (K k)) := by
  let J0 : ℝ := 2 * ((n : ℝ) + 1)
  let d : ℝ := s * J0
  let u : ℕ → ℝ := fun m =>
    nodeSupNorm (E (k + m)) + nodeL1Norm (K (k + m))
  let IE : ℕ → Fin n → ℝ := fun t =>
    (loadingFastScale s
      (loadingFastPerturbationInput N t (E t) (K t))).1
  let IK : ℕ → Fin n → ℝ := fun t =>
    (loadingFastScale s
      (loadingFastPerturbationInput N t (E t) (K t))).2
  have hinv := loading_perturbed_fast_invariants N s hs E K k hE0 hK0 hstep
  have hexact := loading_fast_duhamel N E K IE IK k (by
    intro t hkt
    simpa [IE, IK] using hstep t hkt)
  have hu_nonneg (m : ℕ) : 0 ≤ u m := by
    dsimp [u]
    exact add_nonneg (nodeSupNorm_nonneg N _)
      (Finset.sum_nonneg fun q _ => abs_nonneg _)
  have hd : 0 ≤ d := by dsimp [d, J0]; positivity
  have hfast_nonneg : 0 ≤ loadingFastRate N := by
    unfold loadingFastRate loadingTriangularRate
    linarith [mixingRate_nonneg N]
  have hconv (m : ℕ) :
      u m ≤ M * loadingFastRate N ^ m * u 0 +
        M * d * (∑ q ∈ Finset.range m,
          loadingFastRate N ^ (m - q - 1) * u q) := by
    let t : ℕ := k + m
    have hkt : k ≤ t := by dsimp [t]; omega
    have hI (q : ℕ) (hq : q ∈ Finset.Ico k t) :
        dotProduct (absoluteProbability N (q + 1)) (IE q) = 0 ∧
          (∑ i, IK q i) = 0 := by
      have hP := loadingFastPerturbationInput_spec N q (E q) (K q)
      have hSP := loadingFastScale_invariants_bound N (q + 1) s hs
        (loadingFastPerturbationInput N q (E q) (K q)) hP.1 hP.2.1
      simpa [IE, IK] using And.intro hSP.1 hSP.2.1
    have hraw := loading_fast_duhamel_gauge_le N M (loadingFastRate N)
      htriangular E K IE IK k t hkt hE0 hK0 hI (hexact t hkt)
    have hsum :
        (∑ q ∈ Finset.Ico k t,
          M * loadingFastRate N ^ (t - q - 1) *
            (nodeSupNorm (IE q) + nodeL1Norm (IK q))) ≤
        ∑ q ∈ Finset.Ico k t,
          M * loadingFastRate N ^ (t - q - 1) *
            (d * (nodeSupNorm (E q) + nodeL1Norm (K q))) := by
      apply Finset.sum_le_sum
      intro q hq
      have hpert := loadingFastScale_perturbation_gauge_le
        N q s hs (E q) (K q)
      have hcoeff : 0 ≤ M * loadingFastRate N ^ (t - q - 1) :=
        mul_nonneg (by linarith) (pow_nonneg hfast_nonneg _)
      apply mul_le_mul_of_nonneg_left _ hcoeff
      simpa [IE, IK, d, J0, mul_assoc] using hpert
    calc
      u m = nodeSupNorm (E t) + nodeL1Norm (K t) := by simp [u, t]
      _ ≤ M * loadingFastRate N ^ (t - k) *
            (nodeSupNorm (E k) + nodeL1Norm (K k)) +
          ∑ q ∈ Finset.Ico k t,
            M * loadingFastRate N ^ (t - q - 1) *
              (nodeSupNorm (IE q) + nodeL1Norm (IK q)) := hraw
      _ ≤ M * loadingFastRate N ^ (t - k) *
            (nodeSupNorm (E k) + nodeL1Norm (K k)) +
          ∑ q ∈ Finset.Ico k t,
            M * loadingFastRate N ^ (t - q - 1) *
              (d * (nodeSupNorm (E q) + nodeL1Norm (K q))) :=
        add_le_add le_rfl hsum
      _ = M * loadingFastRate N ^ m * u 0 +
          M * d * (∑ q ∈ Finset.range m,
            loadingFastRate N ^ (m - q - 1) * u q) := by
        dsimp [t, u]
        rw [Finset.sum_Ico_eq_sum_range]
        simp only [Nat.add_sub_cancel_left]
        rw [Finset.mul_sum]
        apply congrArg₂ (· + ·)
        · congr 2 <;> omega
        · apply Finset.sum_congr rfl
          intro q hq
          have hqm : q < m := Finset.mem_range.mp hq
          rw [show k + m - (k + q) - 1 = m - q - 1 by omega]
          ring
  have hperturbed := geometric_bound_of_self_duhamel u M
    (loadingFastRate N) d hM hfast_nonneg hd hu_nonneg hconv
  intro t hkt
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkt
  have hrate_nonneg : 0 ≤ loadingFastRate N + M * d :=
    add_nonneg hfast_nonneg (mul_nonneg (by linarith) hd)
  have hrate : loadingFastRate N + M * d ≤ loadingTransverseRate N := by
    simpa [d, J0] using hcap
  calc
    nodeSupNorm (E (k + m)) + nodeL1Norm (K (k + m)) = u m := rfl
    _ ≤ M * (loadingFastRate N + M * d) ^ m * u 0 := hperturbed m
    _ ≤ M * loadingTransverseRate N ^ m * u 0 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hrate_nonneg hrate m) (by linarith))
        (hu_nonneg 0)
    _ = M * loadingTransverseRate N ^ (k + m - k) *
          (nodeSupNorm (E k) + nodeL1Norm (K k)) := by
      simp [u]

/-- One homogeneous `A_t-sJ_t` step from equation (22). -/
def loadingPerturbedFastStep (N : NetworkSetup n) (s : ℝ) (t : ℕ)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    (Fin n → ℝ) × (Fin n → ℝ) :=
  loadingFastStep N t z +
    loadingFastScale s (loadingFastPerturbationInput N t z.1 z.2)

/-- The perturbed step is additive, which is the algebraic prerequisite for
the forced equation-(24) Duhamel expansion. -/
theorem loadingPerturbedFastStep_add
    (N : NetworkSetup n) (s : ℝ) (t : ℕ)
    (z w : (Fin n → ℝ) × (Fin n → ℝ)) :
    loadingPerturbedFastStep N s t (z + w) =
      loadingPerturbedFastStep N s t z +
        loadingPerturbedFastStep N s t w := by
  apply Prod.ext <;> funext q
  · simp only [loadingPerturbedFastStep, loadingFastStep,
      loadingFastScale, loadingFastPerturbationInput, Prod.fst_add,
      Prod.snd_add, Pi.add_apply, Matrix.mulVec_add]
    unfold dotProduct
    simp_rw [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  · simp only [loadingPerturbedFastStep, loadingFastStep,
      loadingFastScale, loadingFastPerturbationInput, Prod.fst_add,
      Prod.snd_add, Pi.add_apply, Matrix.mulVec_add]
    unfold dotProduct
    have hdot :
        (∑ i, absoluteProbability N (t + 1) i *
          (z.1 + w.1 + (z.2 + w.2)) i) =
        (∑ i, absoluteProbability N (t + 1) i * (z.1 + z.2) i) +
          ∑ i, absoluteProbability N (t + 1) i * (w.1 + w.2) i := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Pi.add_apply]
      ring
    rw [hdot]
    ring

theorem loadingFastScale_scale
    (a b : ℝ) (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    loadingFastScale a (loadingFastScale b z) =
      loadingFastScale (a * b) z := by
  apply Prod.ext <;> funext q <;> simp [loadingFastScale] <;> ring

theorem loadingFastCenterInput_scale
    (N : NetworkSetup n) (t : ℕ) (a x : ℝ) :
    loadingFastCenterInput N t (a * x) =
      loadingFastScale a (loadingFastCenterInput N t x) := by
  apply Prod.ext <;> funext q <;>
    simp [loadingFastCenterInput, loadingFastScale] <;> ring

theorem loadingPerturbedFastStep_scale
    (N : NetworkSetup n) (s a : ℝ) (t : ℕ)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    loadingPerturbedFastStep N s t (loadingFastScale a z) =
      loadingFastScale a (loadingPerturbedFastStep N s t z) := by
  apply Prod.ext <;> funext q
  · simp only [loadingPerturbedFastStep, loadingFastStep,
      loadingFastScale, loadingFastPerturbationInput, Prod.fst_add,
      Prod.snd_add, Pi.add_apply, Matrix.smulVec, Matrix.mulVec]
    unfold dotProduct
    simp only [Pi.add_apply]
    rw [show (∑ i, N.rowMix t q i * (a * z.1 i)) =
        a * ∑ i, N.rowMix t q i * z.1 i by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring]
    rw [show (∑ i, absoluteProbability N (t + 1) i *
          (a * z.1 i + a * z.2 i)) =
        a * ∑ i, absoluteProbability N (t + 1) i *
          (z.1 i + z.2 i) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring]
    ring

  · simp only [loadingPerturbedFastStep, loadingFastStep,
      loadingFastScale, loadingFastPerturbationInput, Prod.fst_add,
      Prod.snd_add, Pi.add_apply, Matrix.smulVec, Matrix.mulVec,
      Matrix.sub_apply, Matrix.one_apply]
    unfold dotProduct
    simp only [Pi.add_apply]
    rw [show (∑ i, N.colMix t q i * (a * z.2 i)) =
        a * ∑ i, N.colMix t q i * z.2 i by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring]
    rw [show (∑ i, (N.colMix t q i - if q = i then 1 else 0) *
          (a * z.1 i)) =
        a * ∑ i, (N.colMix t q i - if q = i then 1 else 0) *
          z.1 i by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring]
    rw [show (∑ i, absoluteProbability N (t + 1) i *
          (a * z.1 i + a * z.2 i)) =
        a * ∑ i, absoluteProbability N (t + 1) i *
          (z.1 i + z.2 i) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring]
    ring

theorem loadingPerturbedFastStep_sub
    (N : NetworkSetup n) (s : ℝ) (t : ℕ)
    (z w : (Fin n → ℝ) × (Fin n → ℝ)) :
    loadingPerturbedFastStep N s t (z - w) =
      loadingPerturbedFastStep N s t z -
        loadingPerturbedFastStep N s t w := by
  have hsub : z - w = z + loadingFastScale (-1) w := by
    apply Prod.ext <;> funext q <;> simp [loadingFastScale] <;> ring
  rw [hsub, loadingPerturbedFastStep_add,
    loadingPerturbedFastStep_scale]
  apply Prod.ext <;> funext q <;> simp [loadingFastScale] <;> ring

/-- The homogeneous perturbed orbit started at absolute time `k`. -/
def loadingPerturbedFastOrbit (N : NetworkSetup n) (s : ℝ) (k : ℕ)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    ℕ → (Fin n → ℝ) × (Fin n → ℝ)
  | 0 => z
  | m + 1 => loadingPerturbedFastStep N s (k + m)
      (loadingPerturbedFastOrbit N s k z m)

@[simp] theorem loadingPerturbedFastOrbit_zero
    (N : NetworkSetup n) (s : ℝ) (k : ℕ)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    loadingPerturbedFastOrbit N s k z 0 = z := rfl

@[simp] theorem loadingPerturbedFastOrbit_succ
    (N : NetworkSetup n) (s : ℝ) (k m : ℕ)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    loadingPerturbedFastOrbit N s k z (m + 1) =
      loadingPerturbedFastStep N s (k + m)
        (loadingPerturbedFastOrbit N s k z m) := rfl

/-- The source equation-(23) perturbed-product estimate, exposed for an orbit
started at an arbitrary absolute time. -/
theorem loadingPerturbedFastOrbit_gauge_le
    (N : NetworkSetup n) (M s : ℝ)
    (hM : 1 ≤ M) (hs : 0 ≤ s)
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
          (nodeSupNorm E + nodeL1Norm K))
    (hcap : loadingFastRate N +
      M * (s * (2 * ((n : ℝ) + 1))) ≤ loadingTransverseRate N)
    (k m : ℕ) (z : (Fin n → ℝ) × (Fin n → ℝ))
    (hE : dotProduct (absoluteProbability N k) z.1 = 0)
    (hK : (∑ q, z.2 q) = 0) :
    nodeSupNorm (loadingPerturbedFastOrbit N s k z m).1 +
        nodeL1Norm (loadingPerturbedFastOrbit N s k z m).2 ≤
      M * loadingTransverseRate N ^ m *
        (nodeSupNorm z.1 + nodeL1Norm z.2) := by
  let O := loadingPerturbedFastOrbit N s k z
  let E : ℕ → Fin n → ℝ := fun t =>
    if k ≤ t then (O (t - k)).1 else z.1
  let K : ℕ → Fin n → ℝ := fun t =>
    if k ≤ t then (O (t - k)).2 else z.2
  have hEk : E k = z.1 := by simp [E, O]
  have hKk : K k = z.2 := by simp [K, O]
  have hstep (t : ℕ) (hkt : k ≤ t) :
      (E (t + 1), K (t + 1)) =
        loadingFastStep N t (E t, K t) +
          loadingFastScale s
            (loadingFastPerturbationInput N t (E t) (K t)) := by
    have hsucc : t + 1 - k = (t - k) + 1 := by omega
    have htime : k + (t - k) = t := by omega
    simp only [E, K, if_pos hkt, if_pos (by omega : k ≤ t + 1)]
    rw [hsucc]
    change loadingPerturbedFastOrbit N s k z ((t - k) + 1) =
      loadingPerturbedFastStep N s t
        (loadingPerturbedFastOrbit N s k z (t - k))
    rw [loadingPerturbedFastOrbit_succ, htime]
  have hbound := loading_perturbed_fast_product_geometric
    N M s hM hs htriangular hcap E K k
      (by simpa [hEk] using hE) (by simpa [hKk] using hK) hstep
      (k + m) (by omega)
  simpa [E, K, O] using hbound

theorem loadingPerturbedFastStep_sum
    {ι : Type*} (N : NetworkSetup n) (s : ℝ) (t : ℕ)
    (S : Finset ι) (z : ι → (Fin n → ℝ) × (Fin n → ℝ)) :
    loadingPerturbedFastStep N s t (∑ r ∈ S, z r) =
      ∑ r ∈ S, loadingPerturbedFastStep N s t (z r) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      apply Prod.ext <;> funext q
      · simp [loadingPerturbedFastStep, loadingFastStep,
          loadingFastScale, loadingFastPerturbationInput]
      · simp [loadingPerturbedFastStep, loadingFastStep,
          loadingFastScale, loadingFastPerturbationInput]
  | @insert a S ha ih =>
      simp only [Finset.sum_insert, ha, not_false_eq_true]
      rw [loadingPerturbedFastStep_add, ih]

/-- Exact nonautonomous Duhamel formula for the forced `A_t-sJ_t` system.
Unlike the earlier triangular formula, this is the source interface needed for
the nonhomogeneous `-sB_t ξ_t` term in equation (24). -/
theorem loading_perturbed_fast_duhamel
    (N : NetworkSetup n) (s : ℝ)
    (F I : ℕ → (Fin n → ℝ) × (Fin n → ℝ)) (k : ℕ)
    (hstep : ∀ t, k ≤ t →
      F (t + 1) = loadingPerturbedFastStep N s t (F t) + I t) :
    ∀ t, k ≤ t →
      F t = loadingPerturbedFastOrbit N s k (F k) (t - k) +
        ∑ r ∈ Finset.Ico k t,
          loadingPerturbedFastOrbit N s (r + 1) (I r) (t - r - 1) := by
  intro t hkt
  induction t with
  | zero =>
      have hk : k = 0 := by omega
      subst k
      simp
  | succ t ih =>
      by_cases hEq : k = t + 1
      · subst k
        simp
      · have hkt' : k ≤ t := by omega
        rw [hstep t hkt', ih hkt']
        rw [loadingPerturbedFastStep_add,
          loadingPerturbedFastStep_sum]
        have hinitial :
            loadingPerturbedFastStep N s t
                (loadingPerturbedFastOrbit N s k (F k) (t - k)) =
              loadingPerturbedFastOrbit N s k (F k) (t + 1 - k) := by
          rw [show t + 1 - k = (t - k) + 1 by omega,
            loadingPerturbedFastOrbit_succ,
            show k + (t - k) = t by omega]
        rw [hinitial]
        have hterm (r : ℕ) (hr : r ∈ Finset.Ico k t) :
            loadingPerturbedFastStep N s t
                (loadingPerturbedFastOrbit N s (r + 1) (I r)
                  (t - r - 1)) =
              loadingPerturbedFastOrbit N s (r + 1) (I r)
                (t + 1 - r - 1) := by
          have hrt : r < t := (Finset.mem_Ico.mp hr).2
          rw [show t + 1 - r - 1 = (t - r - 1) + 1 by omega,
            loadingPerturbedFastOrbit_succ,
            show r + 1 + (t - r - 1) = t by
              omega]
        have hsum :
            (∑ r ∈ Finset.Ico k t,
              loadingPerturbedFastStep N s t
                (loadingPerturbedFastOrbit N s (r + 1) (I r)
                  (t - r - 1))) =
              ∑ r ∈ Finset.Ico k t,
                loadingPerturbedFastOrbit N s (r + 1) (I r)
                  (t + 1 - r - 1) := by
          apply Finset.sum_congr rfl
          intro r hr
          exact hterm r hr
        have hzeroexp : t + 1 - t - 1 = 0 := by omega
        rw [hsum, Finset.sum_Ico_succ_top hkt', hzeroexp,
          loadingPerturbedFastOrbit_zero]
        abel

/-- Endpoint-restricted Duhamel formula.  Unlike the older global-step
interface, this version asks for the recurrence only on the finite interval
which actually contributes to the endpoint.  This is the form needed by a
first-exit branch bootstrap. -/
theorem loading_perturbed_fast_duhamel_on_Ico
    (N : NetworkSetup n) (s : ℝ)
    (F I : ℕ → (Fin n → ℝ) × (Fin n → ℝ)) (k T : ℕ)
    (hkT : k ≤ T)
    (hstep : ∀ r, k ≤ r → r < T →
      F (r + 1) = loadingPerturbedFastStep N s r (F r) + I r) :
    F T = loadingPerturbedFastOrbit N s k (F k) (T - k) +
      ∑ r ∈ Finset.Ico k T,
        loadingPerturbedFastOrbit N s (r + 1) (I r) (T - r - 1) := by
  induction T generalizing k with
  | zero =>
      have hk : k = 0 := by omega
      subst k
      simp
  | succ t ih =>
      by_cases hEq : k = t + 1
      · subst k
        simp
      · have hkt' : k ≤ t := by omega
        have hstep' : ∀ r, k ≤ r → r < t →
            F (r + 1) = loadingPerturbedFastStep N s r (F r) + I r := by
          intro r hkr hrt
          exact hstep r hkr (by omega)
        rw [hstep t hkt' (by omega), ih k hkt' hstep']
        rw [loadingPerturbedFastStep_add,
          loadingPerturbedFastStep_sum]
        have hinitial :
            loadingPerturbedFastStep N s t
                (loadingPerturbedFastOrbit N s k (F k) (t - k)) =
              loadingPerturbedFastOrbit N s k (F k) (t + 1 - k) := by
          rw [show t + 1 - k = (t - k) + 1 by omega,
            loadingPerturbedFastOrbit_succ,
            show k + (t - k) = t by omega]
        rw [hinitial]
        have hterm (r : ℕ) (hr : r ∈ Finset.Ico k t) :
            loadingPerturbedFastStep N s t
                (loadingPerturbedFastOrbit N s (r + 1) (I r)
                  (t - r - 1)) =
              loadingPerturbedFastOrbit N s (r + 1) (I r)
                (t + 1 - r - 1) := by
          have hrt : r < t := (Finset.mem_Ico.mp hr).2
          rw [show t + 1 - r - 1 = (t - r - 1) + 1 by omega,
            loadingPerturbedFastOrbit_succ,
            show r + 1 + (t - r - 1) = t by omega]
        have hsum :
            (∑ r ∈ Finset.Ico k t,
              loadingPerturbedFastStep N s t
                (loadingPerturbedFastOrbit N s (r + 1) (I r)
                  (t - r - 1))) =
              ∑ r ∈ Finset.Ico k t,
                loadingPerturbedFastOrbit N s (r + 1) (I r)
                  (t + 1 - r - 1) := by
          apply Finset.sum_congr rfl
          intro r hr
          exact hterm r hr
        have hzeroexp : t + 1 - t - 1 = 0 := by omega
        rw [hsum, Finset.sum_Ico_succ_top hkt', hzeroexp,
          loadingPerturbedFastOrbit_zero]
        abel

/-- Gauge estimate for the exact forced perturbed Duhamel formula.  This is
the reusable equation-(24) response bound before specializing the innovation
to `-sB_t a_t`. -/
theorem loading_perturbed_fast_duhamel_gauge_le
    (N : NetworkSetup n) (M s : ℝ)
    (hM : 1 ≤ M) (hs : 0 ≤ s)
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
          (nodeSupNorm E + nodeL1Norm K))
    (hcap : loadingFastRate N +
      M * (s * (2 * ((n : ℝ) + 1))) ≤ loadingTransverseRate N)
    (F I : ℕ → (Fin n → ℝ) × (Fin n → ℝ)) (k t : ℕ) (hkt : k ≤ t)
    (hFcenter : dotProduct (absoluteProbability N k) (F k).1 = 0)
    (hFzero : (∑ q, (F k).2 q) = 0)
    (hI : ∀ r ∈ Finset.Ico k t,
      dotProduct (absoluteProbability N (r + 1)) (I r).1 = 0 ∧
        (∑ q, (I r).2 q) = 0)
    (hstep : ∀ r, k ≤ r → r < t →
      F (r + 1) = loadingPerturbedFastStep N s r (F r) + I r) :
    nodeSupNorm (F t).1 + nodeL1Norm (F t).2 ≤
      M * loadingTransverseRate N ^ (t - k) *
          (nodeSupNorm (F k).1 + nodeL1Norm (F k).2) +
        ∑ r ∈ Finset.Ico k t,
          M * loadingTransverseRate N ^ (t - r - 1) *
            (nodeSupNorm (I r).1 + nodeL1Norm (I r).2) := by
  let z0 := loadingPerturbedFastOrbit N s k (F k) (t - k)
  let zsum := ∑ r ∈ Finset.Ico k t,
    loadingPerturbedFastOrbit N s (r + 1) (I r) (t - r - 1)
  have hexact := loading_perturbed_fast_duhamel_on_Ico
    N s F I k t hkt hstep
  have hbase : nodeSupNorm z0.1 + nodeL1Norm z0.2 ≤
      M * loadingTransverseRate N ^ (t - k) *
        (nodeSupNorm (F k).1 + nodeL1Norm (F k).2) := by
    exact loadingPerturbedFastOrbit_gauge_le N M s hM hs htriangular hcap
      k (t - k) (F k) hFcenter hFzero
  have hzsum_fst : zsum.1 =
      ∑ r ∈ Finset.Ico k t,
        (loadingPerturbedFastOrbit N s (r + 1) (I r)
          (t - r - 1)).1 := by
    classical
    dsimp [zsum]
    let S := Finset.Ico k t
    change (∑ r ∈ S,
      loadingPerturbedFastOrbit N s (r + 1) (I r) (t - r - 1)).1 =
        ∑ r ∈ S,
          (loadingPerturbedFastOrbit N s (r + 1) (I r)
            (t - r - 1)).1
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a S ha ih => simp [ha, ih]
  have hzsum_snd : zsum.2 =
      ∑ r ∈ Finset.Ico k t,
        (loadingPerturbedFastOrbit N s (r + 1) (I r)
          (t - r - 1)).2 := by
    classical
    dsimp [zsum]
    let S := Finset.Ico k t
    change (∑ r ∈ S,
      loadingPerturbedFastOrbit N s (r + 1) (I r) (t - r - 1)).2 =
        ∑ r ∈ S,
          (loadingPerturbedFastOrbit N s (r + 1) (I r)
            (t - r - 1)).2
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a S ha ih => simp [ha, ih]
  have hresponse : nodeSupNorm zsum.1 + nodeL1Norm zsum.2 ≤
      ∑ r ∈ Finset.Ico k t,
        (nodeSupNorm
            (loadingPerturbedFastOrbit N s (r + 1) (I r)
              (t - r - 1)).1 +
          nodeL1Norm
            (loadingPerturbedFastOrbit N s (r + 1) (I r)
              (t - r - 1)).2) := by
    rw [hzsum_fst, hzsum_snd]
    exact loadingFastGauge_finset_sum_le N (Finset.Ico k t)
      (fun r => loadingPerturbedFastOrbit N s (r + 1) (I r)
        (t - r - 1))
  have hterms :
      (∑ r ∈ Finset.Ico k t,
        (nodeSupNorm
            (loadingPerturbedFastOrbit N s (r + 1) (I r)
              (t - r - 1)).1 +
          nodeL1Norm
            (loadingPerturbedFastOrbit N s (r + 1) (I r)
              (t - r - 1)).2)) ≤
        ∑ r ∈ Finset.Ico k t,
          M * loadingTransverseRate N ^ (t - r - 1) *
            (nodeSupNorm (I r).1 + nodeL1Norm (I r).2) := by
    apply Finset.sum_le_sum
    intro r hr
    exact loadingPerturbedFastOrbit_gauge_le N M s hM hs htriangular hcap
      (r + 1) (t - r - 1) (I r) (hI r hr).1 (hI r hr).2
  change nodeSupNorm (F t).1 + nodeL1Norm (F t).2 ≤ _
  rw [hexact]
  change nodeSupNorm (z0 + zsum).1 + nodeL1Norm (z0 + zsum).2 ≤ _
  calc
    nodeSupNorm (z0 + zsum).1 + nodeL1Norm (z0 + zsum).2 ≤
        (nodeSupNorm z0.1 + nodeL1Norm z0.2) +
          (nodeSupNorm zsum.1 + nodeL1Norm zsum.2) :=
      loadingFastGauge_add_le N z0 zsum
    _ ≤ (M * loadingTransverseRate N ^ (t - k) *
          (nodeSupNorm (F k).1 + nodeL1Norm (F k).2)) +
        ∑ r ∈ Finset.Ico k t,
          M * loadingTransverseRate N ^ (t - r - 1) *
            (nodeSupNorm (I r).1 + nodeL1Norm (I r).2) :=
      add_le_add hbase (hresponse.trans hterms)

/-- Equation-(24) fast response estimate with the genuine center forcing
`-sB_t ξ_t`.  This is the first direct consumer of both the perturbed product
bound and the printed `B₀=2n(n+1)` estimate. -/
theorem loading_center_forced_fast_gauge_le
    (N : NetworkSetup n) (M s : ℝ)
    (hM : 1 ≤ M) (hs : 0 ≤ s)
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
          (nodeSupNorm E + nodeL1Norm K))
    (hcap : loadingFastRate N +
      M * (s * (2 * ((n : ℝ) + 1))) ≤ loadingTransverseRate N)
    (xi : ℕ → ℝ) (F : ℕ → (Fin n → ℝ) × (Fin n → ℝ))
    (k t : ℕ) (hkt : k ≤ t)
    (hFcenter : dotProduct (absoluteProbability N k) (F k).1 = 0)
    (hFzero : (∑ q, (F k).2 q) = 0)
    (hstep : ∀ r, k ≤ r → r < t →
      F (r + 1) =
        loadingFastStep N r (F r) +
          loadingFastScale s
            (loadingFastPerturbationInput N r (F r).1 (F r).2) +
          loadingFastScale s (loadingFastCenterInput N r (xi r))) :
    nodeSupNorm (F t).1 + nodeL1Norm (F t).2 ≤
      M * loadingTransverseRate N ^ (t - k) *
          (nodeSupNorm (F k).1 + nodeL1Norm (F k).2) +
        ∑ r ∈ Finset.Ico k t,
          M * loadingTransverseRate N ^ (t - r - 1) *
            (s * (2 * (n : ℝ) * ((n : ℝ) + 1) * |xi r|)) := by
  let I : ℕ → (Fin n → ℝ) × (Fin n → ℝ) := fun r =>
    loadingFastScale s (loadingFastCenterInput N r (xi r))
  have hIcarrier (r : ℕ) :
      dotProduct (absoluteProbability N (r + 1)) (I r).1 = 0 ∧
        (∑ q, (I r).2 q) = 0 := by
    have hB := loadingFastCenterInput_invariants N r (xi r)
    have hscaled := loadingFastScale_invariants_bound N (r + 1) s hs
      (loadingFastCenterInput N r (xi r)) hB.1 hB.2
    simpa [I] using And.intro hscaled.1 hscaled.2.1
  have hIgauge (r : ℕ) :
      nodeSupNorm (I r).1 + nodeL1Norm (I r).2 ≤
        s * (2 * (n : ℝ) * ((n : ℝ) + 1) * |xi r|) := by
    have hB := loadingFastCenterInput_invariants N r (xi r)
    have hscaled := loadingFastScale_invariants_bound N (r + 1) s hs
      (loadingFastCenterInput N r (xi r)) hB.1 hB.2
    calc
      nodeSupNorm (I r).1 + nodeL1Norm (I r).2 ≤
          s * (nodeSupNorm (loadingFastCenterInput N r (xi r)).1 +
            nodeL1Norm (loadingFastCenterInput N r (xi r)).2) := by
        simpa [I] using hscaled.2.2
      _ ≤ s * (2 * (n : ℝ) * ((n : ℝ) + 1) * |xi r|) :=
        mul_le_mul_of_nonneg_left
          (loadingFastCenterInput_gauge_le N r (xi r)) hs
  have hstep' (r : ℕ) (hkr : k ≤ r) (hrt : r < t) :
      F (r + 1) = loadingPerturbedFastStep N s r (F r) + I r := by
    simpa [loadingPerturbedFastStep, I] using hstep r hkr hrt
  have hraw := loading_perturbed_fast_duhamel_gauge_le
    N M s hM hs htriangular hcap F I k t hkt hFcenter hFzero
      (fun r hr => hIcarrier r) hstep'
  refine hraw.trans ?_
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro r hr
  have hcoeff : 0 ≤ M * loadingTransverseRate N ^ (t - r - 1) := by
    have htrans_nonneg : 0 ≤ loadingTransverseRate N := by
      unfold loadingTransverseRate loadingFastRate loadingTriangularRate
      linarith [mixingRate_nonneg N]
    exact mul_nonneg (by linarith) (pow_nonneg htrans_nonneg _)
  exact mul_le_mul_of_nonneg_left (hIgauge r) hcoeff

/-- The scalar feedback from a constrained fast state is controlled by the
same mixed gauge used in the equation-(23) product estimate. -/
theorem loadingCenterFeedback_abs_le_gauge
    (N : NetworkSetup n) (t : ℕ) (E K : Fin n → ℝ) :
    |dotProduct (absoluteProbability N t) (E + K)| ≤
      nodeSupNorm E + nodeL1Norm K := by
  classical
  have hp := absoluteProbability_mem_stdSimplex N t
  have hKcoord (q : Fin n) : |K q| ≤ nodeL1Norm K := by
    unfold nodeL1Norm
    exact Finset.single_le_sum (fun r _ => abs_nonneg (K r))
      (Finset.mem_univ q)
  have hpoint (q : Fin n) : |E q + K q| ≤
      nodeSupNorm E + nodeL1Norm K := by
    exact (abs_add_le _ _).trans
      (add_le_add (abs_le_nodeSupNorm E q) (hKcoord q))
  unfold dotProduct
  calc
    |∑ q, absoluteProbability N t q * (E + K) q| ≤
        ∑ q, |absoluteProbability N t q * (E + K) q| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ q, absoluteProbability N t q * |E q + K q| := by
      apply Finset.sum_congr rfl
      intro q _
      rw [Pi.add_apply, abs_mul, abs_of_nonneg (hp.1 q)]
    _ ≤ ∑ q, absoluteProbability N t q *
          (nodeSupNorm E + nodeL1Norm K) := by
      exact Finset.sum_le_sum fun q _ =>
        mul_le_mul_of_nonneg_left (hpoint q) (hp.1 q)
    _ = nodeSupNorm E + nodeL1Norm K := by
      rw [← Finset.sum_mul, hp.2, one_mul]

/-- The unit-center, zero-fast reference solution of source equation (22),
started at the absolute network time `k`. -/
def loadingUnitCenterReferenceOrbit
    (N : NetworkSetup n) (s : ℝ) (k : ℕ) :
    ℕ → ℝ × ((Fin n → ℝ) × (Fin n → ℝ))
  | 0 => (1, (0, 0))
  | m + 1 =>
      let z := loadingUnitCenterReferenceOrbit N s k m
      let t := k + m
      ((1 + s * gain N t) * z.1 +
          s * dotProduct (absoluteProbability N (t + 1))
            (z.2.1 + z.2.2),
        loadingPerturbedFastStep N s t z.2 +
          loadingFastScale s (loadingFastCenterInput N t z.1))

@[simp] theorem loadingUnitCenterReferenceOrbit_zero
    (N : NetworkSetup n) (s : ℝ) (k : ℕ) :
    loadingUnitCenterReferenceOrbit N s k 0 = (1, (0, 0)) := rfl

@[simp] theorem loadingUnitCenterReferenceOrbit_succ
    (N : NetworkSetup n) (s : ℝ) (k m : ℕ) :
    loadingUnitCenterReferenceOrbit N s k (m + 1) =
      let z := loadingUnitCenterReferenceOrbit N s k m
      let t := k + m
      ((1 + s * gain N t) * z.1 +
          s * dotProduct (absoluteProbability N (t + 1))
            (z.2.1 + z.2.2),
        loadingPerturbedFastStep N s t z.2 +
          loadingFastScale s (loadingFastCenterInput N t z.1)) := rfl

/-- The reference fast component remains in the absolute-probability/zero-sum
carrier at its shifted absolute time. -/
theorem loadingUnitCenterReferenceOrbit_fast_invariants
    (N : NetworkSetup n) (s : ℝ) (k : ℕ) (hs : 0 ≤ s) :
    ∀ m,
      dotProduct (absoluteProbability N (k + m))
          (loadingUnitCenterReferenceOrbit N s k m).2.1 = 0 ∧
        (∑ q, (loadingUnitCenterReferenceOrbit N s k m).2.2 q) = 0 := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      let R := loadingUnitCenterReferenceOrbit N s k
      let t := k + m
      have hA := loadingFastStep_invariants N t (R m).2.1 (R m).2.2
        (by simpa [t] using ih.1) ih.2
      have hP := loadingFastPerturbationInput_spec N t
        (R m).2.1 (R m).2.2
      have hSP := loadingFastScale_invariants_bound N (t + 1) s hs
        (loadingFastPerturbationInput N t (R m).2.1 (R m).2.2)
          hP.1 hP.2.1
      have hC := loadingFastCenterInput_invariants N t (R m).1
      have hSC := loadingFastScale_invariants_bound N (t + 1) s hs
        (loadingFastCenterInput N t (R m).1) hC.1 hC.2
      have hPstep_center :
          dotProduct (absoluteProbability N (t + 1))
            (loadingPerturbedFastStep N s t (R m).2).1 = 0 := by
        simp only [loadingPerturbedFastStep, Prod.fst_add]
        unfold dotProduct at hA hSP ⊢
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
        rw [hA.1, hSP.1]
        ring
      have hPstep_sum :
          (∑ q, (loadingPerturbedFastStep N s t (R m).2).2 q) = 0 := by
        simp only [loadingPerturbedFastStep, Prod.snd_add, Pi.add_apply,
          Finset.sum_add_distrib]
        rw [hA.2, hSP.2.1]
        ring
      have hsucc : (R (m + 1)).2 =
          loadingPerturbedFastStep N s t (R m).2 +
            loadingFastScale s (loadingFastCenterInput N t (R m).1) := by
        simpa [R, t] using congrArg Prod.snd
          (loadingUnitCenterReferenceOrbit_succ N s k m)
      have htime : k + (m + 1) = t + 1 := by dsimp [t]; omega
      rw [htime, hsucc]
      constructor
      · unfold dotProduct at hPstep_center hSC ⊢
        simp only [Prod.fst_add, Pi.add_apply, mul_add,
          Finset.sum_add_distrib]
        rw [hPstep_center, hSC.1]
        ring
      · simp only [Prod.snd_add, Pi.add_apply, Finset.sum_add_distrib]
        rw [hPstep_sum, hSC.2.1]
        ring

/-- Source equation (24): the unit-center reference orbit remains positive,
has the calibrated one-step center ratios, and its fast component is at most
`C_p s` times its current center. -/
theorem loading_unit_center_reference_bounds
    (N : NetworkSetup n) (M s : ℝ) (k : ℕ)
    (hM : 1 ≤ M) (hs : 0 < s)
    (htriangular : ∀ (u t : ℕ), u ≤ t → ∀ (E K : Fin n → ℝ),
      dotProduct (absoluteProbability N u) E = 0 →
      (∑ i, K i) = 0 →
      nodeSupNorm (forwardProduct N.rowMix t u *ᵥ E) +
          nodeL1Norm
            (forwardProduct N.colMix t u *ᵥ K +
              ∑ q ∈ Finset.Ico u t,
                forwardProduct N.colMix t (q + 1) *ᵥ
                  ((N.colMix q - 1) *ᵥ
                    (forwardProduct N.rowMix q u *ᵥ E))) ≤
        M * loadingFastRate N ^ (t - u) *
          (nodeSupNorm E + nodeL1Norm K))
    (hperturbation : loadingFastRate N +
      M * (s * (2 * ((n : ℝ) + 1))) ≤ loadingTransverseRate N)
    (hcenterFloor :
      (M * (2 * (n : ℝ) * ((n : ℝ) + 1)) /
          (1 - loadingTransverseRate N)) * s ≤ gainFloor N / 2)
    (hcenterOne :
      (M * (2 * (n : ℝ) * ((n : ℝ) + 1)) /
          (1 - loadingTransverseRate N)) * s ≤ 1 / 8) :
    let R := loadingUnitCenterReferenceOrbit N s k
    let Cp := M * (2 * (n : ℝ) * ((n : ℝ) + 1)) /
      (1 - loadingTransverseRate N)
    ∀ m,
      0 < (R m).1 ∧
      1 + s * gain N (k + m) / 2 ≤ (R (m + 1)).1 / (R m).1 ∧
      (R (m + 1)).1 / (R m).1 ≤
        1 + 3 * s * gain N (k + m) / 2 ∧
      nodeSupNorm (R m).2.1 + nodeL1Norm (R m).2.2 ≤
        Cp * s * (R m).1 := by
  dsimp only
  let R := loadingUnitCenterReferenceOrbit N s k
  let rate := loadingTransverseRate N
  let B0 : ℝ := 2 * (n : ℝ) * ((n : ℝ) + 1)
  let Cp : ℝ := M * B0 / (1 - rate)
  have hrate_pos : 0 < rate := by
    dsimp [rate]
    unfold loadingTransverseRate loadingFastRate loadingTriangularRate
    linarith [mixingRate_nonneg N]
  have hrate_lt : rate < 1 := by
    dsimp [rate]
    unfold loadingTransverseRate loadingFastRate loadingTriangularRate
    linarith [mixingRate_lt_one N]
  have hB0 : 0 < B0 := by
    dsimp [B0]
    exact mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr N.hn)) (by
      positivity)
  have hCp : 0 < Cp := by
    dsimp [Cp]
    exact div_pos (mul_pos (lt_of_lt_of_le zero_lt_one hM) hB0)
      (sub_pos.mpr hrate_lt)
  have hgainFloor : 0 < gainFloor N := by
    have hmu : 0 < mixingMinorization N := by
      unfold mixingMinorization
      split_ifs
      · exact pow_pos ((lt_min_iff).2 ⟨N.ha, by norm_num⟩) _
      · norm_num
    exact (mul_pos (Nat.cast_pos.mpr N.hn) hmu).trans_le
      (gainFloor_ge_n_mul_mixingMinorization N)
  have hcenterFloor' : Cp * s ≤ gainFloor N / 2 := by
    simpa [Cp, B0, rate] using hcenterFloor
  have _hcenterOne' : Cp * s ≤ 1 / 8 := by
    simpa [Cp, B0, rate] using hcenterOne
  have hs0 : 0 ≤ s := hs.le
  let xi : ℕ → ℝ := fun t =>
    if k ≤ t then (R (t - k)).1 else 1
  let F : ℕ → (Fin n → ℝ) × (Fin n → ℝ) := fun t =>
    if k ≤ t then (R (t - k)).2 else (0, 0)
  have hxi (m : ℕ) : xi (k + m) = (R m).1 := by
    simp [xi]
  have hF (m : ℕ) : F (k + m) = (R m).2 := by
    simp [F]
  have hFcenter :
      dotProduct (absoluteProbability N k) (F k).1 = 0 := by
    simp [F, R]
  have hFzero : (∑ q, (F k).2 q) = 0 := by
    simp [F, R]
  have hstep (t : ℕ) (hkt : k ≤ t) :
      F (t + 1) =
        loadingFastStep N t (F t) +
          loadingFastScale s
            (loadingFastPerturbationInput N t (F t).1 (F t).2) +
          loadingFastScale s (loadingFastCenterInput N t (xi t)) := by
    have hsucc : t + 1 - k = (t - k) + 1 := by omega
    have htime : k + (t - k) = t := by omega
    rw [show F (t + 1) = (R (t + 1 - k)).2 by
      simp [F, if_pos (by omega : k ≤ t + 1)]]
    rw [show F t = (R (t - k)).2 by simp [F, hkt]]
    rw [show xi t = (R (t - k)).1 by simp [xi, hkt]]
    rw [hsucc]
    simp only [R, loadingUnitCenterReferenceOrbit_succ]
    rw [htime]
    rfl
  suffices hall : ∀ m,
      (0 < (R m).1 ∧
        1 + s * gain N (k + m) / 2 ≤ (R (m + 1)).1 / (R m).1 ∧
        (R (m + 1)).1 / (R m).1 ≤
          1 + 3 * s * gain N (k + m) / 2 ∧
        nodeSupNorm (R m).2.1 + nodeL1Norm (R m).2.2 ≤
          Cp * s * (R m).1) ∧
      ∀ q, q ≤ m → (R q).1 ≤ (R m).1 by
    intro m
    exact (hall m).1
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      have hpos : 0 < (R m).1 := by
        cases m with
        | zero => simp [R]
        | succ p =>
            have hp := (ih p (by omega)).1
            have hgain_nonneg : 0 ≤ gain N (k + p) :=
              (gainFloor_le_gain N (k + p)).trans' hgainFloor.le
            have hratio_one : 1 ≤ (R (p + 1)).1 / (R p).1 := by
              exact (by linarith : 1 ≤ 1 + s * gain N (k + p) / 2).trans
                hp.2.1
            have hstep_mono : (R p).1 ≤ (R (p + 1)).1 := by
              have := (le_div_iff₀ hp.1).mp hratio_one
              simpa using this
            exact hp.1.trans_le hstep_mono
      have hmono_to_m (q : ℕ) (hqm : q ≤ m) : (R q).1 ≤ (R m).1 := by
        cases m with
        | zero =>
            have hq : q = 0 := by omega
            subst q
            exact le_rfl
        | succ p =>
          by_cases hqeq : q = p + 1
          · subst q
            exact le_rfl
          · have hqp : q ≤ p := by omega
            have hpall := ih p (by omega)
            have hp := hpall.1
            have hgain_nonneg : 0 ≤ gain N (k + p) :=
              (gainFloor_le_gain N (k + p)).trans' hgainFloor.le
            have hratio_one :
                1 ≤ (R (p + 1)).1 / (R p).1 := by
              exact (by linarith :
                1 ≤ 1 + s * gain N (k + p) / 2).trans hp.2.1
            have hnext : (R p).1 ≤ (R (p + 1)).1 := by
              have := (le_div_iff₀ hp.1).mp hratio_one
              simpa using this
            exact (hpall.2 q hqp).trans hnext
      have hfast :
          nodeSupNorm (R m).2.1 + nodeL1Norm (R m).2.2 ≤
            Cp * s * (R m).1 := by
        have hraw := loading_center_forced_fast_gauge_le
          N M s hM hs0 htriangular hperturbation xi F k (k + m)
            (by omega) hFcenter hFzero (fun r hkr _ => hstep r hkr)
        rw [hF] at hraw
        have hsum :
            (∑ r ∈ Finset.Ico k (k + m),
              M * rate ^ (k + m - r - 1) * (s * (B0 * |xi r|))) ≤
              ∑ r ∈ Finset.Ico k (k + m),
                rate ^ (k + m - r - 1) *
                  (M * s * B0 * (R m).1) := by
          apply Finset.sum_le_sum
          intro r hr
          have hkr : k ≤ r := (Finset.mem_Ico.mp hr).1
          have hrupper : r < k + m := (Finset.mem_Ico.mp hr).2
          have hrm : r - k < m := by omega
          have hxi_r : xi r = (R (r - k)).1 := by simp [xi, hkr]
          have hpos_r : 0 < (R (r - k)).1 := (ih (r - k) hrm).1.1
          have hcenter_le : (R (r - k)).1 ≤ (R m).1 :=
            hmono_to_m (r - k) (by omega)
          rw [hxi_r, abs_of_pos hpos_r]
          have hpow : 0 ≤ rate ^ (k + m - r - 1) :=
            pow_nonneg hrate_pos.le _
          calc
            M * rate ^ (k + m - r - 1) *
                (s * (B0 * (R (r - k)).1)) =
                rate ^ (k + m - r - 1) *
                  (M * s * B0 * (R (r - k)).1) := by ring
            _ ≤ rate ^ (k + m - r - 1) *
                  (M * s * B0 * (R m).1) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hcenter_le (by positivity)) hpow
        have hgeom :
            (∑ r ∈ Finset.Ico k (k + m),
              rate ^ (k + m - r - 1) *
                (M * s * B0 * (R m).1)) ≤
              (M * s * B0 * (R m).1) / (1 - rate) := by
          rw [Finset.sum_Ico_eq_sum_range]
          simp only [Nat.add_sub_cancel_left]
          have hrawGeom := sum_range_geometric_reverse_mul_le_div_one_sub
            rate (M * s * B0 * (R m).1) m hrate_pos.le hrate_lt
              (by positivity)
          convert hrawGeom using 1
          apply Finset.sum_congr rfl
          intro q hq
          have hqm : q < m := Finset.mem_range.mp hq
          rw [show k + m - (k + q) - 1 = m - 1 - q by omega]
        have hzeroGauge :
            nodeSupNorm (F k).1 + nodeL1Norm (F k).2 = 0 := by
          simp [F, R, nodeSupNorm, nodeL1Norm]
        rw [hzeroGauge, mul_zero, zero_add] at hraw
        have hraw' :
            nodeSupNorm (R m).2.1 + nodeL1Norm (R m).2.2 ≤
              (M * s * B0 * (R m).1) / (1 - rate) := by
          exact hraw.trans (hsum.trans hgeom)
        calc
          nodeSupNorm (R m).2.1 + nodeL1Norm (R m).2.2 ≤
              (M * s * B0 * (R m).1) / (1 - rate) := hraw'
          _ = Cp * s * (R m).1 := by
            dsimp [Cp]
            field_simp
            <;> ring
      have hell :
          |dotProduct (absoluteProbability N (k + m + 1))
              ((R m).2.1 + (R m).2.2)| ≤ Cp * s * (R m).1 :=
        (loadingCenterFeedback_abs_le_gauge N (k + m + 1)
          (R m).2.1 (R m).2.2).trans hfast
      have hgain_lower : gainFloor N ≤ gain N (k + m) :=
        gainFloor_le_gain N (k + m)
      have hgain_nonneg : 0 ≤ gain N (k + m) :=
        hgainFloor.le.trans hgain_lower
      have herr :
          |s * dotProduct (absoluteProbability N (k + m + 1))
              ((R m).2.1 + (R m).2.2)| ≤
            (s * gain N (k + m) / 2) * (R m).1 := by
        rw [abs_mul, abs_of_pos hs]
        calc
          s * |dotProduct (absoluteProbability N (k + m + 1))
              ((R m).2.1 + (R m).2.2)| ≤
              s * (Cp * s * (R m).1) :=
            mul_le_mul_of_nonneg_left hell hs0
          _ ≤ s * ((gainFloor N / 2) * (R m).1) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hcenterFloor' hpos.le) hs0
          _ ≤ (s * gain N (k + m) / 2) * (R m).1 := by
            have hhalf : gainFloor N / 2 ≤ gain N (k + m) / 2 := by
              linarith
            have hmul := mul_le_mul_of_nonneg_right hhalf hpos.le
            nlinarith
      have hcenter_rec :
          (R (m + 1)).1 =
            (1 + s * gain N (k + m)) * (R m).1 +
              s * dotProduct (absoluteProbability N (k + m + 1))
                ((R m).2.1 + (R m).2.2) := by
        simp only [R, loadingUnitCenterReferenceOrbit_succ]
      have hlower_raw :
          (1 + s * gain N (k + m) / 2) * (R m).1 ≤
            (R (m + 1)).1 := by
        rw [hcenter_rec]
        have hneg := (neg_le_of_abs_le herr)
        nlinarith
      have hupper_raw :
          (R (m + 1)).1 ≤
            (1 + 3 * s * gain N (k + m) / 2) * (R m).1 := by
        rw [hcenter_rec]
        have hposerr := (le_of_abs_le herr)
        nlinarith
      have hlower :
          1 + s * gain N (k + m) / 2 ≤
            (R (m + 1)).1 / (R m).1 :=
        (le_div_iff₀ hpos).2 hlower_raw
      have hupper :
          (R (m + 1)).1 / (R m).1 ≤
            1 + 3 * s * gain N (k + m) / 2 :=
        (div_le_iff₀ hpos).2 hupper_raw
      exact ⟨⟨hpos, hlower, hupper, hfast⟩, hmono_to_m⟩

/-- Exact source equation (25) for an actual slow--fast state relative to the
unit-center reference orbit.  The division is only used after the reference
center at the current time has been proved strictly positive. -/
theorem loading_reference_normalized_residual_step
    (N : NetworkSetup n) (s : ℝ) (k m : ℕ)
    (xi : ℕ → ℝ)
    (F : ℕ → (Fin n → ℝ) × (Fin n → ℝ))
    (hxi : xi (k + m + 1) =
      (1 + s * gain N (k + m)) * xi (k + m) +
        s * dotProduct (absoluteProbability N (k + m + 1))
          ((F (k + m)).1 + (F (k + m)).2))
    (hF : F (k + m + 1) =
      loadingPerturbedFastStep N s (k + m) (F (k + m)) +
        loadingFastScale s
          (loadingFastCenterInput N (k + m) (xi (k + m))))
    (href_pos : 0 < (loadingUnitCenterReferenceOrbit N s k m).1)
    (href_next_pos :
      0 < (loadingUnitCenterReferenceOrbit N s k (m + 1)).1) :
    let R := loadingUnitCenterReferenceOrbit N s k
    let H : ℕ → (Fin n → ℝ) × (Fin n → ℝ) := fun r =>
      loadingFastScale ((R r).1)⁻¹ (R r).2
    let G : ℕ → (Fin n → ℝ) × (Fin n → ℝ) := fun r =>
      F (k + r) - loadingFastScale (xi (k + r)) (H r)
    xi (k + m + 1) =
        ((R (m + 1)).1 / (R m).1) * xi (k + m) +
          s * dotProduct (absoluteProbability N (k + m + 1))
            ((G m).1 + (G m).2) ∧
      G (m + 1) =
        loadingPerturbedFastStep N s (k + m) (G m) -
          loadingFastScale s
            (loadingFastScale
              (dotProduct (absoluteProbability N (k + m + 1))
                ((G m).1 + (G m).2))
              (H (m + 1))) := by
  let R := loadingUnitCenterReferenceOrbit N s k
  let H : ℕ → (Fin n → ℝ) × (Fin n → ℝ) := fun r =>
    loadingFastScale ((R r).1)⁻¹ (R r).2
  let G : ℕ → (Fin n → ℝ) × (Fin n → ℝ) := fun r =>
    F (k + r) - loadingFastScale (xi (k + r)) (H r)
  change xi (k + m + 1) =
        ((R (m + 1)).1 / (R m).1) * xi (k + m) +
          s * dotProduct (absoluteProbability N (k + m + 1))
            ((G m).1 + (G m).2) ∧
      G (m + 1) =
        loadingPerturbedFastStep N s (k + m) (G m) -
          loadingFastScale s
            (loadingFastScale
              (dotProduct (absoluteProbability N (k + m + 1))
                ((G m).1 + (G m).2))
              (H (m + 1)))
  have hRcenter : (R (m + 1)).1 =
      (1 + s * gain N (k + m)) * (R m).1 +
        s * dotProduct (absoluteProbability N (k + m + 1))
          ((R m).2.1 + (R m).2.2) := by
    simpa [R] using congrArg Prod.fst
      (loadingUnitCenterReferenceOrbit_succ N s k m)
  have hRfast : (R (m + 1)).2 =
      loadingPerturbedFastStep N s (k + m) (R m).2 +
        loadingFastScale s
          (loadingFastCenterInput N (k + m) (R m).1) := by
    simpa [R] using congrArg Prod.snd
      (loadingUnitCenterReferenceOrbit_succ N s k m)
  have hell :
      dotProduct (absoluteProbability N (k + m + 1))
          ((G m).1 + (G m).2) =
        dotProduct (absoluteProbability N (k + m + 1))
            ((F (k + m)).1 + (F (k + m)).2) -
          xi (k + m) * ((R m).1)⁻¹ *
            dotProduct (absoluteProbability N (k + m + 1))
              ((R m).2.1 + (R m).2.2) := by
    dsimp [G, H]
    unfold dotProduct
    simp only [Prod.fst_sub, Prod.snd_sub, loadingFastScale,
      Pi.add_apply, Pi.sub_apply]
    simp_rw [mul_add, mul_sub]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib]
    rw [show (∑ x, absoluteProbability N (k + m + 1) x *
          (xi (k + m) * ((R m).1⁻¹ * (R m).2.1 x))) =
        xi (k + m) * (R m).1⁻¹ *
          ∑ x, absoluteProbability N (k + m + 1) x * (R m).2.1 x by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring]
    rw [show (∑ x, absoluteProbability N (k + m + 1) x *
          (xi (k + m) * ((R m).1⁻¹ * (R m).2.2 x))) =
        xi (k + m) * (R m).1⁻¹ *
          ∑ x, absoluteProbability N (k + m + 1) x * (R m).2.2 x by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring]
    ring
  have hfirst : xi (k + m + 1) =
      ((R (m + 1)).1 / (R m).1) * xi (k + m) +
        s * dotProduct (absoluteProbability N (k + m + 1))
          ((G m).1 + (G m).2) := by
    have hRne : (R m).1 ≠ 0 := by
      simpa [R] using ne_of_gt href_pos
    rw [hxi, hell, hRcenter]
    field_simp [hRne]
    ring
  refine ⟨hfirst, ?_⟩
  have hRne : (R m).1 ≠ 0 := by
    simpa [R] using ne_of_gt href_pos
  have hRnext_ne : (R (m + 1)).1 ≠ 0 := by
    simpa [R] using ne_of_gt href_next_pos
  let ell := dotProduct (absoluteProbability N (k + m + 1))
    ((G m).1 + (G m).2)
  have hGm : G m =
      F (k + m) -
        loadingFastScale (xi (k + m))
          (loadingFastScale ((R m).1)⁻¹ (R m).2) := by
    rfl
  have hGnext : G (m + 1) =
      F (k + m + 1) -
        loadingFastScale (xi (k + m + 1))
          (loadingFastScale ((R (m + 1)).1)⁻¹ (R (m + 1)).2) := by
    dsimp [G, H]
    rw [show k + (m + 1) = k + m + 1 by omega]
  have hell_expanded :
      dotProduct (absoluteProbability N (k + m + 1))
          (((F (k + m)).1 - fun q =>
              xi (k + m) * ((R m).1⁻¹ * (R m).2.1 q)) +
            ((F (k + m)).2 - fun q =>
              xi (k + m) * ((R m).1⁻¹ * (R m).2.2 q))) = ell := by
    dsimp [ell]
    rw [hGm]
    rfl
  change G (m + 1) =
    loadingPerturbedFastStep N s (k + m) (G m) -
      loadingFastScale s
        (loadingFastScale ell
          (loadingFastScale ((R (m + 1)).1)⁻¹ (R (m + 1)).2))
  rw [hGnext, hF, hfirst, hGm,
    loadingPerturbedFastStep_sub,
    loadingPerturbedFastStep_scale]
  dsimp [H]
  rw [loadingPerturbedFastStep_scale]
  apply Prod.ext <;> funext q
  · have hRq := congrArg (fun z => z.1 q) hRfast
    simp only [Prod.fst_add, Prod.fst_sub, Pi.add_apply, Pi.sub_apply,
      loadingFastScale,
      loadingFastCenterInput] at hRq ⊢
    rw [hell_expanded]
    rw [hRq]
    field_simp [hRne, hRnext_ne]
    ring
  · have hRq := congrArg (fun z => z.2 q) hRfast
    simp only [Prod.snd_add, Prod.snd_sub, Pi.add_apply, Pi.sub_apply,
      loadingFastScale,
      loadingFastCenterInput] at hRq ⊢
    rw [hell_expanded]
    rw [hRq]
    field_simp [hRne, hRnext_ne]
    ring

theorem loadingFastScale_gauge_le_abs
    (N : NetworkSetup n) (a : ℝ)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    nodeSupNorm (loadingFastScale a z).1 +
        nodeL1Norm (loadingFastScale a z).2 ≤
      |a| * (nodeSupNorm z.1 + nodeL1Norm z.2) := by
  have hsup : nodeSupNorm (loadingFastScale a z).1 ≤
      |a| * nodeSupNorm z.1 := by
    letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp N.hn
    unfold nodeSupNorm
    apply ciSup_le
    intro q
    simp only [loadingFastScale, abs_mul]
    exact mul_le_mul_of_nonneg_left
      (le_ciSup (Finite.bddAbove_range (fun i : Fin n => |z.1 i|)) q)
      (abs_nonneg a)
  have hL1 : nodeL1Norm (loadingFastScale a z).2 =
      |a| * nodeL1Norm z.2 := by
    unfold nodeL1Norm
    simp only [loadingFastScale, abs_mul]
    exact (Finset.mul_sum _ _ _).symm
  rw [hL1]
  calc
    nodeSupNorm (loadingFastScale a z).1 + |a| * nodeL1Norm z.2 ≤
        |a| * nodeSupNorm z.1 + |a| * nodeL1Norm z.2 :=
      add_le_add hsup le_rfl
    _ = |a| * (nodeSupNorm z.1 + nodeL1Norm z.2) := by ring

/-- The normalized reference rank-one term in equation (25) is a valid fast
innovation and has the advertised `C_p s²` operator-gauge bound. -/
theorem loading_normalized_reference_correction_invariants_bound
    (N : NetworkSetup n) (s Cp : ℝ) (k m : ℕ)
    (E K : Fin n → ℝ) (hs : 0 ≤ s)
    (href_pos :
      0 < (loadingUnitCenterReferenceOrbit N s k (m + 1)).1)
    (href_fast :
      nodeSupNorm
          (loadingUnitCenterReferenceOrbit N s k (m + 1)).2.1 +
        nodeL1Norm
          (loadingUnitCenterReferenceOrbit N s k (m + 1)).2.2 ≤
        Cp * s *
          (loadingUnitCenterReferenceOrbit N s k (m + 1)).1) :
    let R := loadingUnitCenterReferenceOrbit N s k
    let H := loadingFastScale ((R (m + 1)).1)⁻¹ (R (m + 1)).2
    let ell := dotProduct (absoluteProbability N (k + m + 1)) (E + K)
    let C := loadingFastScale s (loadingFastScale ell H)
    dotProduct (absoluteProbability N (k + m + 1)) C.1 = 0 ∧
      (∑ q, C.2 q) = 0 ∧
      nodeSupNorm C.1 + nodeL1Norm C.2 ≤
        Cp * s ^ 2 * (nodeSupNorm E + nodeL1Norm K) := by
  dsimp only
  let R := loadingUnitCenterReferenceOrbit N s k
  let H := loadingFastScale ((R (m + 1)).1)⁻¹ (R (m + 1)).2
  let ell := dotProduct (absoluteProbability N (k + m + 1)) (E + K)
  let C := loadingFastScale s (loadingFastScale ell H)
  have hRinv := loadingUnitCenterReferenceOrbit_fast_invariants
    N s k hs (m + 1)
  have htime : k + (m + 1) = k + m + 1 := by omega
  rw [htime] at hRinv
  have hHcenter :
      dotProduct (absoluteProbability N (k + m + 1)) H.1 = 0 := by
    dsimp [H]
    unfold dotProduct at hRinv ⊢
    calc
      (∑ q, absoluteProbability N (k + m + 1) q *
          ((R (m + 1)).1⁻¹ * (R (m + 1)).2.1 q)) =
          (R (m + 1)).1⁻¹ *
            ∑ q, absoluteProbability N (k + m + 1) q *
              (R (m + 1)).2.1 q := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        ring
      _ = 0 := by rw [hRinv.1, mul_zero]
  have hHsum : (∑ q, H.2 q) = 0 := by
    dsimp [H, loadingFastScale]
    rw [← Finset.mul_sum, hRinv.2, mul_zero]
  have hCcenter :
      dotProduct (absoluteProbability N (k + m + 1)) C.1 = 0 := by
    dsimp [C]
    unfold dotProduct at hHcenter ⊢
    calc
      (∑ q, absoluteProbability N (k + m + 1) q *
          (s * (ell * H.1 q))) = s * ell *
            ∑ q, absoluteProbability N (k + m + 1) q * H.1 q := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        ring
      _ = 0 := by rw [hHcenter]; ring
  have hCsum : (∑ q, C.2 q) = 0 := by
    dsimp [C]
    calc
      (∑ q, s * (ell * H.2 q)) = s * ell * ∑ q, H.2 q := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        ring
      _ = 0 := by rw [hHsum]; ring
  have hHbound : nodeSupNorm H.1 + nodeL1Norm H.2 ≤ Cp * s := by
    have hRpos : 0 < (R (m + 1)).1 := by simpa [R] using href_pos
    have hRne : (R (m + 1)).1 ≠ 0 := ne_of_gt hRpos
    have hinv_nonneg : 0 ≤ ((R (m + 1)).1)⁻¹ :=
      inv_nonneg.mpr hRpos.le
    have hscale := loadingFastScale_gauge_le_abs N
      ((R (m + 1)).1)⁻¹ (R (m + 1)).2
    rw [abs_of_nonneg hinv_nonneg] at hscale
    calc
      nodeSupNorm H.1 + nodeL1Norm H.2 ≤
          ((R (m + 1)).1)⁻¹ *
            (nodeSupNorm (R (m + 1)).2.1 +
              nodeL1Norm (R (m + 1)).2.2) := by simpa [H] using hscale
      _ ≤ ((R (m + 1)).1)⁻¹ *
            (Cp * s * (R (m + 1)).1) :=
        mul_le_mul_of_nonneg_left (by simpa [R] using href_fast) hinv_nonneg
      _ = Cp * s := by
        field_simp [hRne]
  have hell : |ell| ≤ nodeSupNorm E + nodeL1Norm K := by
    dsimp [ell]
    exact loadingCenterFeedback_abs_le_gauge N (k + m + 1) E K
  have hinner := loadingFastScale_gauge_le_abs N ell H
  have houter := loadingFastScale_gauge_le_abs N s
    (loadingFastScale ell H)
  rw [abs_of_nonneg hs] at houter
  have hgauge_nonneg : 0 ≤ nodeSupNorm E + nodeL1Norm K :=
    add_nonneg (nodeSupNorm_nonneg N E)
      (Finset.sum_nonneg fun q _ => abs_nonneg _)
  have hHgauge_nonneg : 0 ≤ nodeSupNorm H.1 + nodeL1Norm H.2 :=
    add_nonneg (nodeSupNorm_nonneg N H.1)
      (Finset.sum_nonneg fun q _ => abs_nonneg _)
  have hcorr : nodeSupNorm C.1 + nodeL1Norm C.2 ≤
      Cp * s ^ 2 * (nodeSupNorm E + nodeL1Norm K) := by
    calc
      nodeSupNorm C.1 + nodeL1Norm C.2 ≤
          s * (nodeSupNorm (loadingFastScale ell H).1 +
            nodeL1Norm (loadingFastScale ell H).2) := by
        simpa [C] using houter
      _ ≤ s * (|ell| * (nodeSupNorm H.1 + nodeL1Norm H.2)) :=
        mul_le_mul_of_nonneg_left hinner hs
      _ ≤ s * ((nodeSupNorm E + nodeL1Norm K) * (Cp * s)) := by
        apply mul_le_mul_of_nonneg_left _ hs
        calc
          |ell| * (nodeSupNorm H.1 + nodeL1Norm H.2) ≤
              (nodeSupNorm E + nodeL1Norm K) *
                (nodeSupNorm H.1 + nodeL1Norm H.2) :=
            mul_le_mul_of_nonneg_right hell hHgauge_nonneg
          _ ≤ (nodeSupNorm E + nodeL1Norm K) * (Cp * s) :=
            mul_le_mul_of_nonneg_left hHbound hgauge_nonneg
      _ = Cp * s ^ 2 * (nodeSupNorm E + nodeL1Norm K) := by ring
  exact ⟨hCcenter, hCsum, hcorr⟩

/-- The branch-independent innovation in the corrected transverse equation
(25).  It combines the `-sJ_t` perturbation with the normalized rank-one
correction `-s H^a_{t+1} ℓ_t`; the reference orbit is formal and therefore
does not require post-loading branch membership. -/
def loadingCorrectedTransverseInnovation
    (N : NetworkSetup n) (s : ℝ) (k m : ℕ)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    (Fin n → ℝ) × (Fin n → ℝ) :=
  let R := loadingUnitCenterReferenceOrbit N s k
  let H := loadingFastScale ((R (m + 1)).1)⁻¹ (R (m + 1)).2
  let ell := dotProduct (absoluteProbability N (k + m + 1)) (z.1 + z.2)
  loadingFastScale s
      (loadingFastPerturbationInput N (k + m) z.1 z.2) -
    loadingFastScale s (loadingFastScale ell H)

/-- One formal corrected-transverse step from source equation (25). -/
def loadingCorrectedTransverseStep
    (N : NetworkSetup n) (s : ℝ) (k m : ℕ)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    (Fin n → ℝ) × (Fin n → ℝ) :=
  loadingFastStep N (k + m) z +
    loadingCorrectedTransverseInnovation N s k m z

/-- The formal corrected transverse orbit, initialized by the genuine loaded
fast state but evolved without consulting the actual nonlinear branch. -/
def loadingCorrectedTransverseOrbit
    (N : NetworkSetup n) (s : ℝ) (k : ℕ)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    ℕ → (Fin n → ℝ) × (Fin n → ℝ)
  | 0 => z
  | m + 1 => loadingCorrectedTransverseStep N s k m
      (loadingCorrectedTransverseOrbit N s k z m)

@[simp] theorem loadingCorrectedTransverseOrbit_zero
    (N : NetworkSetup n) (s : ℝ) (k : ℕ)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    loadingCorrectedTransverseOrbit N s k z 0 = z := rfl

@[simp] theorem loadingCorrectedTransverseOrbit_succ
    (N : NetworkSetup n) (s : ℝ) (k m : ℕ)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    loadingCorrectedTransverseOrbit N s k z (m + 1) =
      loadingCorrectedTransverseStep N s k m
        (loadingCorrectedTransverseOrbit N s k z m) := rfl

/-- The formal corrected transverse recursion depends continuously on its
initial fast state.  This is the finite-recursion continuity input for the
source calibration equation (38). -/
theorem loading_corrected_transverse_orbit_continuous
    (N : NetworkSetup n) (s : ℝ) (k m : ℕ)
    (z : ℝ → (Fin n → ℝ) × (Fin n → ℝ))
    (hz : Continuous z) :
    Continuous (fun a ↦ loadingCorrectedTransverseOrbit N s k (z a) m) := by
  induction m with
  | zero => simpa using hz
  | succ m ih =>
      simp only [loadingCorrectedTransverseOrbit_succ,
        loadingCorrectedTransverseStep, loadingCorrectedTransverseInnovation,
        loadingFastStep, loadingFastScale, loadingFastPerturbationInput]
      fun_prop

/-- Carrier preservation and the exact combined `sJ₀+Cₛs²` gauge bound
for the corrected innovation in equation (25). -/
theorem loadingCorrectedTransverseInnovation_spec
    (N : NetworkSetup n) (s Cp : ℝ) (k m : ℕ)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) (hs : 0 ≤ s)
    (href_pos :
      0 < (loadingUnitCenterReferenceOrbit N s k (m + 1)).1)
    (href_fast :
      nodeSupNorm
          (loadingUnitCenterReferenceOrbit N s k (m + 1)).2.1 +
        nodeL1Norm
          (loadingUnitCenterReferenceOrbit N s k (m + 1)).2.2 ≤
        Cp * s *
          (loadingUnitCenterReferenceOrbit N s k (m + 1)).1) :
    let I := loadingCorrectedTransverseInnovation N s k m z
    dotProduct (absoluteProbability N (k + m + 1)) I.1 = 0 ∧
      (∑ q, I.2 q) = 0 ∧
      nodeSupNorm I.1 + nodeL1Norm I.2 ≤
        (s * (2 * ((n : ℝ) + 1)) + Cp * s ^ 2) *
          (nodeSupNorm z.1 + nodeL1Norm z.2) := by
  dsimp only
  let P := loadingFastScale s
    (loadingFastPerturbationInput N (k + m) z.1 z.2)
  let R := loadingUnitCenterReferenceOrbit N s k
  let H := loadingFastScale ((R (m + 1)).1)⁻¹ (R (m + 1)).2
  let ell := dotProduct (absoluteProbability N (k + m + 1)) (z.1 + z.2)
  let C := loadingFastScale s (loadingFastScale ell H)
  have hPraw := loadingFastPerturbationInput_spec N (k + m) z.1 z.2
  have hP := loadingFastScale_invariants_bound N (k + m + 1) s hs
    (loadingFastPerturbationInput N (k + m) z.1 z.2)
      hPraw.1 hPraw.2.1
  have hC := loading_normalized_reference_correction_invariants_bound
    N s Cp k m z.1 z.2 hs href_pos href_fast
  have hPcenter :
      dotProduct (absoluteProbability N (k + m + 1)) P.1 = 0 := by
    simpa [P] using hP.1
  have hCcenter :
      dotProduct (absoluteProbability N (k + m + 1)) C.1 = 0 := by
    change dotProduct (absoluteProbability N (k + m + 1)) C.1 = 0 ∧
        (∑ q, C.2 q) = 0 ∧
        nodeSupNorm C.1 + nodeL1Norm C.2 ≤
          Cp * s ^ 2 * (nodeSupNorm z.1 + nodeL1Norm z.2) at hC
    exact hC.1
  have hcenter :
      dotProduct (absoluteProbability N (k + m + 1)) (P - C).1 = 0 := by
    simp only [Prod.fst_sub]
    unfold dotProduct at hPcenter hCcenter ⊢
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    rw [hPcenter, hCcenter]
    ring
  have hzero : (∑ q, (P - C).2 q) = 0 := by
    simp only [Prod.snd_sub, Pi.sub_apply, Finset.sum_sub_distrib]
    rw [show (∑ q, P.2 q) = 0 by simpa [P] using hP.2.1]
    rw [show (∑ q, C.2 q) = 0 by
      simpa [R, H, ell, C] using hC.2.1]
    ring
  have hPbound : nodeSupNorm P.1 + nodeL1Norm P.2 ≤
      s * (2 * ((n : ℝ) + 1)) *
        (nodeSupNorm z.1 + nodeL1Norm z.2) := by
    simpa [P] using loadingFastScale_perturbation_gauge_le
      N (k + m) s hs z.1 z.2
  have hCbound : nodeSupNorm C.1 + nodeL1Norm C.2 ≤
      Cp * s ^ 2 * (nodeSupNorm z.1 + nodeL1Norm z.2) := by
    simpa [R, H, ell, C] using hC.2.2
  have hminus : nodeSupNorm (loadingFastScale (-1) C).1 +
      nodeL1Norm (loadingFastScale (-1) C).2 ≤
        nodeSupNorm C.1 + nodeL1Norm C.2 := by
    have h := loadingFastScale_gauge_le_abs N (-1) C
    norm_num at h ⊢
    exact h
  have hsub : P - C = P + loadingFastScale (-1) C := by
    apply Prod.ext <;> funext q <;>
      simp [loadingFastScale] <;> ring
  have hgauge : nodeSupNorm (P - C).1 + nodeL1Norm (P - C).2 ≤
      (s * (2 * ((n : ℝ) + 1)) + Cp * s ^ 2) *
        (nodeSupNorm z.1 + nodeL1Norm z.2) := by
    rw [hsub]
    calc
      nodeSupNorm (P + loadingFastScale (-1) C).1 +
          nodeL1Norm (P + loadingFastScale (-1) C).2 ≤
        (nodeSupNorm P.1 + nodeL1Norm P.2) +
          (nodeSupNorm (loadingFastScale (-1) C).1 +
            nodeL1Norm (loadingFastScale (-1) C).2) :=
        loadingFastGauge_add_le N P (loadingFastScale (-1) C)
      _ ≤ s * (2 * ((n : ℝ) + 1)) *
            (nodeSupNorm z.1 + nodeL1Norm z.2) +
          Cp * s ^ 2 * (nodeSupNorm z.1 + nodeL1Norm z.2) :=
        add_le_add hPbound (hminus.trans hCbound)
      _ = (s * (2 * ((n : ℝ) + 1)) + Cp * s ^ 2) *
            (nodeSupNorm z.1 + nodeL1Norm z.2) := by ring
  simpa [loadingCorrectedTransverseInnovation, P, R, H, ell, C] using
    And.intro hcenter (And.intro hzero hgauge)

/-- A reusable bounded-innovation product theorem over the homogeneous
triangular propagator.  This is the exact Duhamel-to-geometric bridge needed
for the combined corrected innovation; it does not assume one-step
contraction. -/
theorem loading_fast_product_geometric_of_relative_innovation
    (N : NetworkSetup n) (M rate d : ℝ)
    (hM : 1 ≤ M) (hrate : 0 ≤ rate) (hd : 0 ≤ d)
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
          (nodeSupNorm E + nodeL1Norm K))
    (hcap : loadingFastRate N + M * d ≤ rate)
    (E K IE IK : ℕ → Fin n → ℝ) (k : ℕ)
    (hE0 : dotProduct (absoluteProbability N k) (E k) = 0)
    (hK0 : (∑ i, K k i) = 0)
    (hI : ∀ t, k ≤ t →
      dotProduct (absoluteProbability N (t + 1)) (IE t) = 0 ∧
        (∑ i, IK t i) = 0)
    (hIgauge : ∀ t, k ≤ t →
      nodeSupNorm (IE t) + nodeL1Norm (IK t) ≤
        d * (nodeSupNorm (E t) + nodeL1Norm (K t)))
    (hstep : ∀ t, k ≤ t →
      (E (t + 1), K (t + 1)) =
        loadingFastStep N t (E t, K t) + (IE t, IK t)) :
    ∀ t, k ≤ t →
      nodeSupNorm (E t) + nodeL1Norm (K t) ≤
        M * rate ^ (t - k) *
          (nodeSupNorm (E k) + nodeL1Norm (K k)) := by
  let u : ℕ → ℝ := fun m =>
    nodeSupNorm (E (k + m)) + nodeL1Norm (K (k + m))
  have hexact := loading_fast_duhamel N E K IE IK k hstep
  have hu_nonneg (m : ℕ) : 0 ≤ u m := by
    dsimp [u]
    exact add_nonneg (nodeSupNorm_nonneg N _)
      (Finset.sum_nonneg fun q _ => abs_nonneg _)
  have hfast_nonneg : 0 ≤ loadingFastRate N := by
    unfold loadingFastRate loadingTriangularRate
    linarith [mixingRate_nonneg N]
  have hconv (m : ℕ) :
      u m ≤ M * loadingFastRate N ^ m * u 0 +
        M * d * (∑ q ∈ Finset.range m,
          loadingFastRate N ^ (m - q - 1) * u q) := by
    let t : ℕ := k + m
    have hkt : k ≤ t := by dsimp [t]; omega
    have hraw := loading_fast_duhamel_gauge_le N M (loadingFastRate N)
      htriangular E K IE IK k t hkt hE0 hK0
        (fun q hq => hI q (Finset.mem_Ico.mp hq).1) (hexact t hkt)
    have hsum :
        (∑ q ∈ Finset.Ico k t,
          M * loadingFastRate N ^ (t - q - 1) *
            (nodeSupNorm (IE q) + nodeL1Norm (IK q))) ≤
        ∑ q ∈ Finset.Ico k t,
          M * loadingFastRate N ^ (t - q - 1) *
            (d * (nodeSupNorm (E q) + nodeL1Norm (K q))) := by
      apply Finset.sum_le_sum
      intro q hq
      have hcoeff : 0 ≤ M * loadingFastRate N ^ (t - q - 1) :=
        mul_nonneg (by linarith) (pow_nonneg hfast_nonneg _)
      exact mul_le_mul_of_nonneg_left
        (hIgauge q (Finset.mem_Ico.mp hq).1) hcoeff
    calc
      u m = nodeSupNorm (E t) + nodeL1Norm (K t) := by simp [u, t]
      _ ≤ M * loadingFastRate N ^ (t - k) *
            (nodeSupNorm (E k) + nodeL1Norm (K k)) +
          ∑ q ∈ Finset.Ico k t,
            M * loadingFastRate N ^ (t - q - 1) *
              (nodeSupNorm (IE q) + nodeL1Norm (IK q)) := hraw
      _ ≤ M * loadingFastRate N ^ (t - k) *
            (nodeSupNorm (E k) + nodeL1Norm (K k)) +
          ∑ q ∈ Finset.Ico k t,
            M * loadingFastRate N ^ (t - q - 1) *
              (d * (nodeSupNorm (E q) + nodeL1Norm (K q))) :=
        add_le_add le_rfl hsum
      _ = M * loadingFastRate N ^ m * u 0 +
          M * d * (∑ q ∈ Finset.range m,
            loadingFastRate N ^ (m - q - 1) * u q) := by
        dsimp [t, u]
        rw [Finset.sum_Ico_eq_sum_range]
        simp only [Nat.add_sub_cancel_left]
        rw [Finset.mul_sum]
        apply congrArg₂ (· + ·)
        · congr 2 <;> omega
        · apply Finset.sum_congr rfl
          intro q hq
          rw [show k + m - (k + q) - 1 = m - q - 1 by omega]
          ring
  have hperturbed := geometric_bound_of_self_duhamel u M
    (loadingFastRate N) d hM hfast_nonneg hd hu_nonneg hconv
  intro t hkt
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkt
  have hcombined_nonneg : 0 ≤ loadingFastRate N + M * d :=
    add_nonneg hfast_nonneg (mul_nonneg (by linarith) hd)
  calc
    nodeSupNorm (E (k + m)) + nodeL1Norm (K (k + m)) = u m := rfl
    _ ≤ M * (loadingFastRate N + M * d) ^ m * u 0 := hperturbed m
    _ ≤ M * rate ^ m * u 0 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hcombined_nonneg hcap m) (by linarith))
        (hu_nonneg 0)
    _ = M * rate ^ (k + m - k) *
          (nodeSupNorm (E k) + nodeL1Norm (K k)) := by simp [u]

/-- Source equation-(25) corrected transverse product bound.  The proof
combines the `sJ₀` and `Cₛs²` innovations before applying the triangular
Duhamel estimate, exactly as required by the source cap. -/
theorem loading_corrected_transverse_product_geometric
    (N : NetworkSetup n) (M s Cp : ℝ) (k : ℕ)
    (hM : 1 ≤ M) (hs : 0 ≤ s) (hCp : 0 ≤ Cp)
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
          (nodeSupNorm E + nodeL1Norm K))
    (hcap : loadingFastRate N +
      M * (s * (2 * ((n : ℝ) + 1)) + Cp * s ^ 2) ≤
        loadingTransverseRate N)
    (href_pos : ∀ m,
      0 < (loadingUnitCenterReferenceOrbit N s k m).1)
    (href_fast : ∀ m,
      nodeSupNorm (loadingUnitCenterReferenceOrbit N s k m).2.1 +
        nodeL1Norm (loadingUnitCenterReferenceOrbit N s k m).2.2 ≤
      Cp * s * (loadingUnitCenterReferenceOrbit N s k m).1)
    (z : (Fin n → ℝ) × (Fin n → ℝ))
    (hE : dotProduct (absoluteProbability N k) z.1 = 0)
    (hK : (∑ q, z.2 q) = 0) :
    ∀ m,
      nodeSupNorm (loadingCorrectedTransverseOrbit N s k z m).1 +
        nodeL1Norm (loadingCorrectedTransverseOrbit N s k z m).2 ≤
      M * loadingTransverseRate N ^ m *
        (nodeSupNorm z.1 + nodeL1Norm z.2) := by
  let O := loadingCorrectedTransverseOrbit N s k z
  let E : ℕ → Fin n → ℝ := fun t =>
    if k ≤ t then (O (t - k)).1 else z.1
  let K : ℕ → Fin n → ℝ := fun t =>
    if k ≤ t then (O (t - k)).2 else z.2
  let I : ℕ → (Fin n → ℝ) × (Fin n → ℝ) := fun t =>
    if k ≤ t then
      loadingCorrectedTransverseInnovation N s k (t - k) (E t, K t)
    else (0, 0)
  have hEk : E k = z.1 := by simp [E, O]
  have hKk : K k = z.2 := by simp [K, O]
  have hstep (t : ℕ) (hkt : k ≤ t) :
      (E (t + 1), K (t + 1)) =
        loadingFastStep N t (E t, K t) + I t := by
    have hsucc : t + 1 - k = (t - k) + 1 := by omega
    have htime : k + (t - k) = t := by omega
    simp only [E, K, I, if_pos hkt, if_pos (by omega : k ≤ t + 1)]
    rw [hsucc]
    change O (t - k + 1) = _
    simp only [O, loadingCorrectedTransverseOrbit_succ,
      loadingCorrectedTransverseStep]
    rw [htime]
  have hIspec (t : ℕ) (hkt : k ≤ t) :=
    loadingCorrectedTransverseInnovation_spec N s Cp k (t - k)
      (E t, K t) hs (by
        simpa [show k + (t - k) + 1 = t + 1 by omega] using
          href_pos (t - k + 1)) (by
        simpa [show k + (t - k) + 1 = t + 1 by omega] using
          href_fast (t - k + 1))
  have hbound := loading_fast_product_geometric_of_relative_innovation
    N M (loadingTransverseRate N)
      (s * (2 * ((n : ℝ) + 1)) + Cp * s ^ 2)
      hM (by
        unfold loadingTransverseRate loadingFastRate loadingTriangularRate
        linarith [mixingRate_nonneg N]) (by positivity) htriangular hcap
      E K (fun t => (I t).1) (fun t => (I t).2) k
      (by simpa [hEk] using hE) (by simpa [hKk] using hK)
      (fun t hkt => by
        have h := hIspec t hkt
        simpa [I, hkt] using And.intro h.1 h.2.1)
      (fun t hkt => by
        have h := hIspec t hkt
        simpa [I, hkt] using h.2.2)
      hstep
  intro m
  have h := hbound (k + m) (by omega)
  simpa [E, K, O] using h

/-- The formal slow coordinate coupled to the corrected transverse orbit.
This is the source's pre-persistence system: it is initialized by the genuine
loaded state, but its later values do not inspect the nonlinear trajectory. -/
def loadingFormalCorrectedCenter
    (N : NetworkSetup n) (s : ℝ) (k : ℕ) (xi0 : ℝ)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) : ℕ → ℝ
  | 0 => xi0
  | m + 1 =>
      let R := loadingUnitCenterReferenceOrbit N s k
      let G := loadingCorrectedTransverseOrbit N s k z
      ((R (m + 1)).1 / (R m).1) *
          loadingFormalCorrectedCenter N s k xi0 z m +
        s * dotProduct (absoluteProbability N (k + m + 1))
          ((G m).1 + (G m).2)

/-- The scalar action `Ψ_{k+m,k} z` appearing in source equation (26). -/
def loadingCalibrationFunctional
    (N : NetworkSetup n) (s : ℝ) (k m : ℕ)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  let R := loadingUnitCenterReferenceOrbit N s k
  let G := loadingCorrectedTransverseOrbit N s k z
  s * ∑ q ∈ Finset.range m,
    dotProduct (absoluteProbability N (k + q + 1))
      ((G q).1 + (G q).2) / (R (q + 1)).1

/-- The source equation-(38) calibration map is continuous in any continuous
loaded endpoint.  All later evolution here is the branch-independent formal
recursion, so this result does not assume persistence of the nonlinear
trajectory. -/
theorem loading_calibration_functional_continuous
    (N : NetworkSetup n) (s : ℝ) (k m : ℕ)
    (xi0 : ℝ → ℝ)
    (z : ℝ → (Fin n → ℝ) × (Fin n → ℝ))
    (hxi0 : Continuous xi0) (hz : Continuous z) :
    Continuous (fun a ↦
      loadingFormalCorrectedCenter N s k (xi0 a) (z a) m) := by
  induction m with
  | zero => simpa [loadingFormalCorrectedCenter] using hxi0
  | succ m ih =>
      simp only [loadingFormalCorrectedCenter]
      have hG := loading_corrected_transverse_orbit_continuous
        N s k m z hz
      fun_prop

/-- Source equation (38): a continuous formal calibration map whose two
loaded endpoints satisfy the equation-(37) center and functional errors has a
calibrated parameter in `[3/4,5/4]`.  The theorem is stated entirely for the
formal orbit and therefore does not assume actual-branch persistence. -/
theorem loading_calibration_exists
    (N : NetworkSetup n) (s D : ℝ) (k p : ℕ)
    (xi0 : ℝ → ℝ)
    (z : ℝ → (Fin n → ℝ) × (Fin n → ℝ))
    (hD : 0 < D)
    (hcont : Continuous (fun a ↦
      loadingFormalCorrectedCenter N s k (xi0 a) (z a) p))
    (href_pos : 0 < (loadingUnitCenterReferenceOrbit N s k p).1)
    (href_one : 1 ≤ (loadingUnitCenterReferenceOrbit N s k p).1)
    (hxi_lo : |xi0 (3 / 4) - ((3 / 4 : ℝ) - 1) * D| ≤ D / 32)
    (hxi_hi : |xi0 (5 / 4) - ((5 / 4 : ℝ) - 1) * D| ≤ D / 32)
    (hpsi_lo : |loadingCalibrationFunctional N s k p (z (3 / 4))| ≤
      D / 32)
    (hpsi_hi : |loadingCalibrationFunctional N s k p (z (5 / 4))| ≤
      D / 32)
    (hspec_lo :
      loadingFormalCorrectedCenter N s k (xi0 (3 / 4)) (z (3 / 4)) p /
          (loadingUnitCenterReferenceOrbit N s k p).1 =
        xi0 (3 / 4) +
          loadingCalibrationFunctional N s k p (z (3 / 4)))
    (hspec_hi :
      loadingFormalCorrectedCenter N s k (xi0 (5 / 4)) (z (5 / 4)) p /
          (loadingUnitCenterReferenceOrbit N s k p).1 =
        xi0 (5 / 4) +
          loadingCalibrationFunctional N s k p (z (5 / 4))) :
    ∃ a ∈ Set.Icc (3 / 4 : ℝ) (5 / 4),
      loadingFormalCorrectedCenter N s k (xi0 a) (z a) p = D / 8 := by
  let R : ℝ := (loadingUnitCenterReferenceOrbit N s k p).1
  let f : ℝ → ℝ := fun a ↦
    loadingFormalCorrectedCenter N s k (xi0 a) (z a) p
  have hRne : R ≠ 0 := ne_of_gt (by simpa [R] using href_pos)
  have hxi_lo' : xi0 (3 / 4) ≤ -7 * D / 32 := by
    have := (abs_le.mp hxi_lo).2
    norm_num at this ⊢
    linarith
  have hpsi_lo' : loadingCalibrationFunctional N s k p (z (3 / 4)) ≤
      D / 32 := (abs_le.mp hpsi_lo).2
  have hlo_sum : xi0 (3 / 4) +
      loadingCalibrationFunctional N s k p (z (3 / 4)) ≤ 0 := by
    linarith
  have hf_lo_eq : f (3 / 4) =
      (xi0 (3 / 4) + loadingCalibrationFunctional N s k p (z (3 / 4))) * R := by
    apply (div_eq_iff hRne).mp
    simpa [f, R] using hspec_lo
  have hf_lo : f (3 / 4) ≤ D / 8 := by
    rw [hf_lo_eq]
    have hRnonneg : 0 ≤ R := (by simpa [R] using href_pos.le)
    have : (xi0 (3 / 4) +
        loadingCalibrationFunctional N s k p (z (3 / 4))) * R ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hlo_sum hRnonneg
    linarith
  have hxi_hi' : 7 * D / 32 ≤ xi0 (5 / 4) := by
    have := (abs_le.mp hxi_hi).1
    norm_num at this ⊢
    linarith
  have hpsi_hi' : -D / 32 ≤
      loadingCalibrationFunctional N s k p (z (5 / 4)) :=
    by simpa only [neg_div] using (abs_le.mp hpsi_hi).1
  have hhi_sum : D / 8 ≤ xi0 (5 / 4) +
      loadingCalibrationFunctional N s k p (z (5 / 4)) := by
    linarith
  have hf_hi_eq : f (5 / 4) =
      (xi0 (5 / 4) + loadingCalibrationFunctional N s k p (z (5 / 4))) * R := by
    apply (div_eq_iff hRne).mp
    simpa [f, R] using hspec_hi
  have hf_hi : D / 8 ≤ f (5 / 4) := by
    rw [hf_hi_eq]
    have hsum_nonneg : 0 ≤ xi0 (5 / 4) +
        loadingCalibrationFunctional N s k p (z (5 / 4)) := by
      linarith
    calc
      D / 8 ≤ xi0 (5 / 4) +
          loadingCalibrationFunctional N s k p (z (5 / 4)) := hhi_sum
      _ ≤ (xi0 (5 / 4) +
          loadingCalibrationFunctional N s k p (z (5 / 4))) * R :=
        le_mul_of_one_le_right hsum_nonneg (by simpa [R] using href_one)
  have htarget : D / 8 ∈ Set.Icc (f (3 / 4)) (f (5 / 4)) :=
    ⟨hf_lo, hf_hi⟩
  obtain ⟨a, ha, hfa⟩ :=
    intermediate_value_Icc (by norm_num : (3 / 4 : ℝ) ≤ 5 / 4)
      hcont.continuousOn htarget
  exact ⟨a, ha, by simpa [f] using hfa⟩

/-- Source equation (26): the branch-independent formal center has the exact
normalized calibration identity, and its functional is uniformly `C₂ s`
bounded for arbitrary waiting length. -/
theorem loading_calibration_functional_spec
    (N : NetworkSetup n) (M s Cp : ℝ) (k : ℕ)
    (hM : 1 ≤ M) (hs : 0 ≤ s) (hCp : 0 ≤ Cp)
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
          (nodeSupNorm E + nodeL1Norm K))
    (hcap : loadingFastRate N +
      M * (s * (2 * ((n : ℝ) + 1)) + Cp * s ^ 2) ≤
        loadingTransverseRate N)
    (href_pos : ∀ m,
      0 < (loadingUnitCenterReferenceOrbit N s k m).1)
    (href_one : ∀ m,
      1 ≤ (loadingUnitCenterReferenceOrbit N s k m).1)
    (href_fast : ∀ m,
      nodeSupNorm (loadingUnitCenterReferenceOrbit N s k m).2.1 +
        nodeL1Norm (loadingUnitCenterReferenceOrbit N s k m).2.2 ≤
      Cp * s * (loadingUnitCenterReferenceOrbit N s k m).1)
    (xi0 : ℝ) (z : (Fin n → ℝ) × (Fin n → ℝ))
    (hE : dotProduct (absoluteProbability N k) z.1 = 0)
    (hK : (∑ q, z.2 q) = 0) :
    ∀ m,
      loadingFormalCorrectedCenter N s k xi0 z m /
          (loadingUnitCenterReferenceOrbit N s k m).1 =
        xi0 + loadingCalibrationFunctional N s k m z ∧
      |loadingCalibrationFunctional N s k m z| ≤
        (M / (1 - loadingTransverseRate N)) * s *
          (nodeSupNorm z.1 + nodeL1Norm z.2) := by
  let R := loadingUnitCenterReferenceOrbit N s k
  let G := loadingCorrectedTransverseOrbit N s k z
  have hG := loading_corrected_transverse_product_geometric
    N M s Cp k hM hs hCp htriangular hcap href_pos href_fast z hE hK
  have hrate_nonneg : 0 ≤ loadingTransverseRate N := by
    unfold loadingTransverseRate loadingFastRate loadingTriangularRate
    linarith [mixingRate_nonneg N]
  have hrate_lt : loadingTransverseRate N < 1 := by
    unfold loadingTransverseRate loadingFastRate loadingTriangularRate
    linarith [mixingRate_lt_one N]
  have hidentity : ∀ m,
      loadingFormalCorrectedCenter N s k xi0 z m / (R m).1 =
        xi0 + loadingCalibrationFunctional N s k m z := by
    intro m
    induction m with
    | zero => simp [R, loadingCalibrationFunctional,
        loadingFormalCorrectedCenter]
    | succ m ih =>
        have hmne : (R m).1 ≠ 0 := ne_of_gt (by simpa [R] using href_pos m)
        have hnextne : (R (m + 1)).1 ≠ 0 :=
          ne_of_gt (by simpa [R] using href_pos (m + 1))
        have hnormalize (x ell : ℝ) :
            (((R (m + 1)).1 / (R m).1) * x + s * ell) /
                (R (m + 1)).1 =
              x / (R m).1 + s * ell / (R (m + 1)).1 := by
          field_simp [hmne, hnextne]
        simp only [loadingFormalCorrectedCenter,
          loadingCalibrationFunctional, Finset.sum_range_succ]
        change (((R (m + 1)).1 / (R m).1) *
              loadingFormalCorrectedCenter N s k xi0 z m +
            s * dotProduct (absoluteProbability N (k + m + 1))
              ((G m).1 + (G m).2)) / (R (m + 1)).1 = _
        rw [hnormalize, ih]
        simp only [loadingCalibrationFunctional]
        ring
  intro m
  refine ⟨by simpa [R] using hidentity m, ?_⟩
  have hterm (q : ℕ) :
      |dotProduct (absoluteProbability N (k + q + 1))
          ((G q).1 + (G q).2) / (R (q + 1)).1| ≤
        M * loadingTransverseRate N ^ q *
          (nodeSupNorm z.1 + nodeL1Norm z.2) := by
    have hRpos : 0 < (R (q + 1)).1 := by simpa [R] using href_pos (q + 1)
    have hRone : 1 ≤ (R (q + 1)).1 := by simpa [R] using href_one (q + 1)
    rw [abs_div, abs_of_pos hRpos]
    apply (div_le_iff₀ hRpos).2
    have hell := loadingCenterFeedback_abs_le_gauge
      N (k + q + 1) (G q).1 (G q).2
    have hbound := hG q
    have hcoef_nonneg :
        0 ≤ M * loadingTransverseRate N ^ q *
          (nodeSupNorm z.1 + nodeL1Norm z.2) := by
      exact mul_nonneg
        (mul_nonneg (by linarith) (pow_nonneg hrate_nonneg _))
        (add_nonneg (nodeSupNorm_nonneg N _)
          (Finset.sum_nonneg fun i _ => abs_nonneg _))
    calc
      |dotProduct (absoluteProbability N (k + q + 1))
          ((G q).1 + (G q).2)| ≤
          nodeSupNorm (G q).1 + nodeL1Norm (G q).2 := hell
      _ ≤ M * loadingTransverseRate N ^ q *
          (nodeSupNorm z.1 + nodeL1Norm z.2) := hbound
      _ ≤ (M * loadingTransverseRate N ^ q *
          (nodeSupNorm z.1 + nodeL1Norm z.2)) * (R (q + 1)).1 :=
        le_mul_of_one_le_right hcoef_nonneg hRone
  have hsum_abs :
      |(∑ q ∈ Finset.range m,
          dotProduct (absoluteProbability N (k + q + 1))
            ((G q).1 + (G q).2) / (R (q + 1)).1)| ≤
        ∑ q ∈ Finset.range m,
          M * loadingTransverseRate N ^ q *
            (nodeSupNorm z.1 + nodeL1Norm z.2) := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun q _ => hterm q)
  have hgeom :
      (∑ q ∈ Finset.range m, loadingTransverseRate N ^ q) ≤
        1 / (1 - loadingTransverseRate N) := by
    simpa using (geom_sum_Ico_le_of_lt_one
      (x := loadingTransverseRate N) (m := 0) (n := m)
        hrate_nonneg hrate_lt)
  have hgauge_nonneg : 0 ≤ nodeSupNorm z.1 + nodeL1Norm z.2 :=
    add_nonneg (nodeSupNorm_nonneg N _)
      (Finset.sum_nonneg fun i _ => abs_nonneg _)
  have hfactor :
      (∑ q ∈ Finset.range m,
          M * loadingTransverseRate N ^ q *
            (nodeSupNorm z.1 + nodeL1Norm z.2)) =
        (M * (nodeSupNorm z.1 + nodeL1Norm z.2)) *
          ∑ q ∈ Finset.range m, loadingTransverseRate N ^ q := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  have hsum :
      (∑ q ∈ Finset.range m,
          M * loadingTransverseRate N ^ q *
            (nodeSupNorm z.1 + nodeL1Norm z.2)) ≤
        (M * (nodeSupNorm z.1 + nodeL1Norm z.2)) /
          (1 - loadingTransverseRate N) := by
    rw [hfactor]
    calc
      (M * (nodeSupNorm z.1 + nodeL1Norm z.2)) *
          ∑ q ∈ Finset.range m, loadingTransverseRate N ^ q ≤
        (M * (nodeSupNorm z.1 + nodeL1Norm z.2)) *
          (1 / (1 - loadingTransverseRate N)) :=
        mul_le_mul_of_nonneg_left hgeom
          (mul_nonneg (by linarith) hgauge_nonneg)
      _ = (M * (nodeSupNorm z.1 + nodeL1Norm z.2)) /
          (1 - loadingTransverseRate N) := by ring
  rw [loadingCalibrationFunctional, abs_mul, abs_of_nonneg hs]
  calc
    s * |(∑ q ∈ Finset.range m,
        dotProduct (absoluteProbability N (k + q + 1))
          ((G q).1 + (G q).2) / (R (q + 1)).1)| ≤
      s * (∑ q ∈ Finset.range m,
        M * loadingTransverseRate N ^ q *
          (nodeSupNorm z.1 + nodeL1Norm z.2)) :=
      mul_le_mul_of_nonneg_left hsum_abs hs
    _ ≤ s * ((M * (nodeSupNorm z.1 + nodeL1Norm z.2)) /
          (1 - loadingTransverseRate N)) :=
      mul_le_mul_of_nonneg_left hsum hs
    _ = (M / (1 - loadingTransverseRate N)) * s *
          (nodeSupNorm z.1 + nodeL1Norm z.2) := by ring

/-- The paper's formal fast state reconstructed from the corrected transverse
state and the normalized unit-center reference orbit.  This is the identity
`F_t = G_t^f + H_t^a ξ_t` used in equations (27)--(28). -/
def loadingFormalFastState
    (N : NetworkSetup n) (s : ℝ) (k : ℕ) (xi0 : ℝ)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) (m : ℕ) :
    (Fin n → ℝ) × (Fin n → ℝ) :=
  let R := loadingUnitCenterReferenceOrbit N s k
  let G := loadingCorrectedTransverseOrbit N s k z
  G m + loadingFastScale (loadingFormalCorrectedCenter N s k xi0 z m)
    (loadingFastScale ((R m).1)⁻¹ (R m).2)

/-- The fast-state half of equation (27), obtained from the literal
reconstruction `F=G+H^a ξ`. -/
theorem loading_formal_fast_state_bound
    (N : NetworkSetup n) (M s Cp : ℝ) (k : ℕ)
    (hM : 1 ≤ M) (hs : 0 ≤ s) (hCp : 0 ≤ Cp)
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
          (nodeSupNorm E + nodeL1Norm K))
    (hcap : loadingFastRate N +
      M * (s * (2 * ((n : ℝ) + 1)) + Cp * s ^ 2) ≤
        loadingTransverseRate N)
    (href_pos : ∀ m,
      0 < (loadingUnitCenterReferenceOrbit N s k m).1)
    (href_fast : ∀ m,
      nodeSupNorm (loadingUnitCenterReferenceOrbit N s k m).2.1 +
        nodeL1Norm (loadingUnitCenterReferenceOrbit N s k m).2.2 ≤
      Cp * s * (loadingUnitCenterReferenceOrbit N s k m).1)
    (xi0 : ℝ) (z : (Fin n → ℝ) × (Fin n → ℝ))
    (hE : dotProduct (absoluteProbability N k) z.1 = 0)
    (hK : (∑ q, z.2 q) = 0) (m : ℕ) :
    nodeSupNorm (loadingFormalFastState N s k xi0 z m).1 +
        nodeL1Norm (loadingFormalFastState N s k xi0 z m).2 ≤
      Cp * s * |loadingFormalCorrectedCenter N s k xi0 z m| +
        M * loadingTransverseRate N ^ m *
          (nodeSupNorm z.1 + nodeL1Norm z.2) := by
  let R := loadingUnitCenterReferenceOrbit N s k
  let G := loadingCorrectedTransverseOrbit N s k z
  let H := loadingFastScale ((R m).1)⁻¹ (R m).2
  let xi := loadingFormalCorrectedCenter N s k xi0 z m
  have hG := loading_corrected_transverse_product_geometric
    N M s Cp k hM hs hCp htriangular hcap href_pos href_fast z hE hK m
  have hRpos : 0 < (R m).1 := by simpa [R] using href_pos m
  have hRne : (R m).1 ≠ 0 := ne_of_gt hRpos
  have hH : nodeSupNorm H.1 + nodeL1Norm H.2 ≤ Cp * s := by
    have hscale := loadingFastScale_gauge_le_abs N ((R m).1)⁻¹ (R m).2
    rw [abs_of_pos (inv_pos.mpr hRpos)] at hscale
    calc
      nodeSupNorm H.1 + nodeL1Norm H.2 ≤
          ((R m).1)⁻¹ *
            (nodeSupNorm (R m).2.1 + nodeL1Norm (R m).2.2) := by
        simpa [H] using hscale
      _ ≤ ((R m).1)⁻¹ * (Cp * s * (R m).1) :=
        mul_le_mul_of_nonneg_left (by simpa [R] using href_fast m)
          (inv_nonneg.mpr hRpos.le)
      _ = Cp * s := by field_simp [hRne]
  have hscaled := loadingFastScale_gauge_le_abs N xi H
  have hadd := loadingFastGauge_add_le N (G m) (loadingFastScale xi H)
  calc
    nodeSupNorm (loadingFormalFastState N s k xi0 z m).1 +
        nodeL1Norm (loadingFormalFastState N s k xi0 z m).2 ≤
      (nodeSupNorm (G m).1 + nodeL1Norm (G m).2) +
        (nodeSupNorm (loadingFastScale xi H).1 +
          nodeL1Norm (loadingFastScale xi H).2) := by
            simpa [loadingFormalFastState, R, G, H, xi] using hadd
    _ ≤ M * loadingTransverseRate N ^ m *
          (nodeSupNorm z.1 + nodeL1Norm z.2) +
        |xi| * (Cp * s) :=
      add_le_add hG (hscaled.trans
        (mul_le_mul_of_nonneg_left hH (abs_nonneg xi)))
    _ = Cp * s * |loadingFormalCorrectedCenter N s k xi0 z m| +
        M * loadingTransverseRate N ^ m *
          (nodeSupNorm z.1 + nodeL1Norm z.2) := by
      dsimp [xi]
      ring

/-- A weighted tail of the calibration functional.  The reference factor at
the left endpoint cancels the denominators because the reference center is
positive and nondecreasing. -/
theorem loading_calibration_weighted_tail_bound
    (N : NetworkSetup n) (M s Cp : ℝ) (k : ℕ)
    (hM : 1 ≤ M) (hs : 0 ≤ s) (hCp : 0 ≤ Cp)
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
          (nodeSupNorm E + nodeL1Norm K))
    (hcap : loadingFastRate N +
      M * (s * (2 * ((n : ℝ) + 1)) + Cp * s ^ 2) ≤
        loadingTransverseRate N)
    (href_pos : ∀ m,
      0 < (loadingUnitCenterReferenceOrbit N s k m).1)
    (href_mono : ∀ u v, u ≤ v →
      (loadingUnitCenterReferenceOrbit N s k u).1 ≤
        (loadingUnitCenterReferenceOrbit N s k v).1)
    (href_fast : ∀ m,
      nodeSupNorm (loadingUnitCenterReferenceOrbit N s k m).2.1 +
        nodeL1Norm (loadingUnitCenterReferenceOrbit N s k m).2.2 ≤
      Cp * s * (loadingUnitCenterReferenceOrbit N s k m).1)
    (z : (Fin n → ℝ) × (Fin n → ℝ))
    (hE : dotProduct (absoluteProbability N k) z.1 = 0)
    (hK : (∑ q, z.2 q) = 0) (m p : ℕ) (hmp : m ≤ p) :
    |(loadingUnitCenterReferenceOrbit N s k m).1 *
        (loadingCalibrationFunctional N s k p z -
          loadingCalibrationFunctional N s k m z)| ≤
      (M / (1 - loadingTransverseRate N)) * s *
        loadingTransverseRate N ^ m *
          (nodeSupNorm z.1 + nodeL1Norm z.2) := by
  let R := loadingUnitCenterReferenceOrbit N s k
  let G := loadingCorrectedTransverseOrbit N s k z
  let f : ℕ → ℝ := fun q =>
    dotProduct (absoluteProbability N (k + q + 1))
      ((G q).1 + (G q).2) / (R (q + 1)).1
  have hG := loading_corrected_transverse_product_geometric
    N M s Cp k hM hs hCp htriangular hcap href_pos href_fast z hE hK
  have hrate_nonneg : 0 ≤ loadingTransverseRate N := by
    unfold loadingTransverseRate loadingFastRate loadingTriangularRate
    linarith [mixingRate_nonneg N]
  have hrate_lt : loadingTransverseRate N < 1 := by
    unfold loadingTransverseRate loadingFastRate loadingTriangularRate
    linarith [mixingRate_lt_one N]
  have hgauge_nonneg : 0 ≤ nodeSupNorm z.1 + nodeL1Norm z.2 :=
    add_nonneg (nodeSupNorm_nonneg N _)
      (Finset.sum_nonneg fun i _ => abs_nonneg _)
  have hterm (q : ℕ) (hq : q ∈ Finset.Ico m p) :
      |(R m).1 * f q| ≤
        M * loadingTransverseRate N ^ q *
          (nodeSupNorm z.1 + nodeL1Norm z.2) := by
    have hmq : m ≤ q + 1 :=
      (Finset.mem_Ico.mp hq).1.trans (Nat.le_succ q)
    have hRmpos : 0 < (R m).1 := by simpa [R] using href_pos m
    have hRqpos : 0 < (R (q + 1)).1 := by
      simpa [R] using href_pos (q + 1)
    have hRle : (R m).1 ≤ (R (q + 1)).1 := by
      simpa [R] using href_mono m (q + 1) hmq
    have hell := loadingCenterFeedback_abs_le_gauge
      N (k + q + 1) (G q).1 (G q).2
    have hbound := hG q
    have hcoef_nonneg :
        0 ≤ M * loadingTransverseRate N ^ q *
          (nodeSupNorm z.1 + nodeL1Norm z.2) :=
      mul_nonneg (mul_nonneg (by linarith) (pow_nonneg hrate_nonneg _))
        hgauge_nonneg
    rw [abs_mul, abs_of_pos hRmpos]
    dsimp [f]
    rw [abs_div, abs_of_pos hRqpos]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hRqpos).2
    calc
      (R m).1 *
          |dotProduct (absoluteProbability N (k + q + 1))
            ((G q).1 + (G q).2)| ≤
        (R m).1 *
          (M * loadingTransverseRate N ^ q *
            (nodeSupNorm z.1 + nodeL1Norm z.2)) :=
          mul_le_mul_of_nonneg_left (hell.trans hbound) hRmpos.le
      _ ≤ (R (q + 1)).1 *
          (M * loadingTransverseRate N ^ q *
            (nodeSupNorm z.1 + nodeL1Norm z.2)) :=
          mul_le_mul_of_nonneg_right hRle hcoef_nonneg
      _ = (M * loadingTransverseRate N ^ q *
          (nodeSupNorm z.1 + nodeL1Norm z.2)) * (R (q + 1)).1 := by ring
  have hsplit := Finset.sum_range_add_sum_Ico f hmp
  have hfunctional :
      (R m).1 * (loadingCalibrationFunctional N s k p z -
        loadingCalibrationFunctional N s k m z) =
      s * ∑ q ∈ Finset.Ico m p, (R m).1 * f q := by
    rw [loadingCalibrationFunctional, loadingCalibrationFunctional]
    change (R m).1 *
        (s * ∑ q ∈ Finset.range p, f q -
          s * ∑ q ∈ Finset.range m, f q) = _
    rw [← hsplit]
    rw [← Finset.mul_sum]
    ring
  rw [hfunctional, abs_mul, abs_of_nonneg hs]
  have hsum_abs :
      |∑ q ∈ Finset.Ico m p, (R m).1 * f q| ≤
        ∑ q ∈ Finset.Ico m p,
          M * loadingTransverseRate N ^ q *
            (nodeSupNorm z.1 + nodeL1Norm z.2) :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun q hq => hterm q hq)
  have hgeom := geom_sum_Ico_le_of_lt_one
    (x := loadingTransverseRate N) (m := m) (n := p)
      hrate_nonneg hrate_lt
  calc
    s * |∑ q ∈ Finset.Ico m p, (R m).1 * f q| ≤
      s * ∑ q ∈ Finset.Ico m p,
        M * loadingTransverseRate N ^ q *
          (nodeSupNorm z.1 + nodeL1Norm z.2) :=
        mul_le_mul_of_nonneg_left hsum_abs hs
    _ = s * (M * (nodeSupNorm z.1 + nodeL1Norm z.2) *
          ∑ q ∈ Finset.Ico m p, loadingTransverseRate N ^ q) := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        ring
    _ ≤ s * (M * (nodeSupNorm z.1 + nodeL1Norm z.2) *
          (loadingTransverseRate N ^ m /
            (1 - loadingTransverseRate N))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hgeom
            (mul_nonneg (by linarith) hgauge_nonneg)) hs
    _ = (M / (1 - loadingTransverseRate N)) * s *
          loadingTransverseRate N ^ m *
            (nodeSupNorm z.1 + nodeL1Norm z.2) := by ring

/-- Source equation (27): before the calibrated endpoint, the formal center
has a geometrically decaying backward error, and the reconstructed formal fast
state has the printed `C_p s |ξ_t| + M_2 r_2^{t-k}‖F_k‖` bound. -/
theorem loading_calibrated_backward_propagation
    (N : NetworkSetup n) (M s Cp : ℝ) (k : ℕ)
    (hM : 1 ≤ M) (hs : 0 ≤ s) (hCp : 0 ≤ Cp)
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
          (nodeSupNorm E + nodeL1Norm K))
    (hcap : loadingFastRate N +
      M * (s * (2 * ((n : ℝ) + 1)) + Cp * s ^ 2) ≤
        loadingTransverseRate N)
    (href_pos : ∀ m,
      0 < (loadingUnitCenterReferenceOrbit N s k m).1)
    (href_one : ∀ m,
      1 ≤ (loadingUnitCenterReferenceOrbit N s k m).1)
    (href_mono : ∀ u v, u ≤ v →
      (loadingUnitCenterReferenceOrbit N s k u).1 ≤
        (loadingUnitCenterReferenceOrbit N s k v).1)
    (href_fast : ∀ m,
      nodeSupNorm (loadingUnitCenterReferenceOrbit N s k m).2.1 +
        nodeL1Norm (loadingUnitCenterReferenceOrbit N s k m).2.2 ≤
      Cp * s * (loadingUnitCenterReferenceOrbit N s k m).1)
    (xi0 zeta : ℝ) (z : (Fin n → ℝ) × (Fin n → ℝ))
    (hE : dotProduct (absoluteProbability N k) z.1 = 0)
    (hK : (∑ q, z.2 q) = 0) (p : ℕ)
    (hcal : loadingFormalCorrectedCenter N s k xi0 z p = zeta) :
    ∀ m, m ≤ p →
      |loadingFormalCorrectedCenter N s k xi0 z m -
          (loadingUnitCenterReferenceOrbit N s k m).1 /
            (loadingUnitCenterReferenceOrbit N s k p).1 * zeta| ≤
        (M / (1 - loadingTransverseRate N)) * s *
          loadingTransverseRate N ^ m *
            (nodeSupNorm z.1 + nodeL1Norm z.2) ∧
      nodeSupNorm (loadingFormalFastState N s k xi0 z m).1 +
          nodeL1Norm (loadingFormalFastState N s k xi0 z m).2 ≤
        Cp * s * |loadingFormalCorrectedCenter N s k xi0 z m| +
          M * loadingTransverseRate N ^ m *
            (nodeSupNorm z.1 + nodeL1Norm z.2) := by
  let R := loadingUnitCenterReferenceOrbit N s k
  let xi := loadingFormalCorrectedCenter N s k xi0 z
  have hspec := loading_calibration_functional_spec
    N M s Cp k hM hs hCp htriangular hcap href_pos href_one href_fast
      xi0 z hE hK
  have hfast := loading_formal_fast_state_bound
    N M s Cp k hM hs hCp htriangular hcap href_pos href_fast
      xi0 z hE hK
  intro m hmp
  constructor
  · have hRmpos : 0 < (R m).1 := by simpa [R] using href_pos m
    have hRppos : 0 < (R p).1 := by simpa [R] using href_pos p
    have hxim : xi m = (R m).1 *
        (xi0 + loadingCalibrationFunctional N s k m z) := by
      have h := (div_eq_iff (ne_of_gt hRmpos)).mp (by
        simpa [R, xi] using (hspec m).1)
      simpa [mul_comm] using h
    have hxip : zeta = (R p).1 *
        (xi0 + loadingCalibrationFunctional N s k p z) := by
      rw [← hcal]
      have h := (div_eq_iff (ne_of_gt hRppos)).mp (by
        simpa [R, xi] using (hspec p).1)
      simpa [mul_comm] using h
    have hid : xi m - (R m).1 / (R p).1 * zeta =
        -(R m).1 *
          (loadingCalibrationFunctional N s k p z -
            loadingCalibrationFunctional N s k m z) := by
      rw [hxim, hxip]
      field_simp [ne_of_gt hRppos]
      ring
    rw [hid, abs_mul, abs_neg]
    simpa [R] using loading_calibration_weighted_tail_bound
      N M s Cp k hM hs hCp htriangular hcap href_pos href_mono href_fast
        z hE hK m p hmp
  · simpa [xi] using hfast m

/-- Source equation (28): after the calibrated endpoint, the normalized
center error is the forward tail beginning at that endpoint, with no bound on
the waiting length. -/
theorem loading_calibrated_forward_propagation
    (N : NetworkSetup n) (M s Cp : ℝ) (k : ℕ)
    (hM : 1 ≤ M) (hs : 0 ≤ s) (hCp : 0 ≤ Cp)
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
          (nodeSupNorm E + nodeL1Norm K))
    (hcap : loadingFastRate N +
      M * (s * (2 * ((n : ℝ) + 1)) + Cp * s ^ 2) ≤
        loadingTransverseRate N)
    (href_pos : ∀ m,
      0 < (loadingUnitCenterReferenceOrbit N s k m).1)
    (href_one : ∀ m,
      1 ≤ (loadingUnitCenterReferenceOrbit N s k m).1)
    (href_mono : ∀ u v, u ≤ v →
      (loadingUnitCenterReferenceOrbit N s k u).1 ≤
        (loadingUnitCenterReferenceOrbit N s k v).1)
    (href_fast : ∀ m,
      nodeSupNorm (loadingUnitCenterReferenceOrbit N s k m).2.1 +
        nodeL1Norm (loadingUnitCenterReferenceOrbit N s k m).2.2 ≤
      Cp * s * (loadingUnitCenterReferenceOrbit N s k m).1)
    (xi0 zeta : ℝ) (z : (Fin n → ℝ) × (Fin n → ℝ))
    (hE : dotProduct (absoluteProbability N k) z.1 = 0)
    (hK : (∑ q, z.2 q) = 0) (p : ℕ)
    (hcal : loadingFormalCorrectedCenter N s k xi0 z p = zeta) :
    ∀ m, p ≤ m →
      |loadingFormalCorrectedCenter N s k xi0 z m -
          (loadingUnitCenterReferenceOrbit N s k m).1 /
            (loadingUnitCenterReferenceOrbit N s k p).1 * zeta| ≤
        (loadingUnitCenterReferenceOrbit N s k m).1 /
          (loadingUnitCenterReferenceOrbit N s k p).1 *
            ((M / (1 - loadingTransverseRate N)) * s *
              loadingTransverseRate N ^ p *
                (nodeSupNorm z.1 + nodeL1Norm z.2)) := by
  let R := loadingUnitCenterReferenceOrbit N s k
  let xi := loadingFormalCorrectedCenter N s k xi0 z
  have hspec := loading_calibration_functional_spec
    N M s Cp k hM hs hCp htriangular hcap href_pos href_one href_fast
      xi0 z hE hK
  intro m hpm
  have hRmpos : 0 < (R m).1 := by simpa [R] using href_pos m
  have hRppos : 0 < (R p).1 := by simpa [R] using href_pos p
  have hxim : xi m = (R m).1 *
      (xi0 + loadingCalibrationFunctional N s k m z) := by
    have h := (div_eq_iff (ne_of_gt hRmpos)).mp (by
      simpa [R, xi] using (hspec m).1)
    simpa [mul_comm] using h
  have hxip : zeta = (R p).1 *
      (xi0 + loadingCalibrationFunctional N s k p z) := by
    rw [← hcal]
    have h := (div_eq_iff (ne_of_gt hRppos)).mp (by
      simpa [R, xi] using (hspec p).1)
    simpa [mul_comm] using h
  have hid : xi m - (R m).1 / (R p).1 * zeta =
      (R m).1 / (R p).1 *
        ((R p).1 *
          (loadingCalibrationFunctional N s k m z -
            loadingCalibrationFunctional N s k p z)) := by
    rw [hxim, hxip]
    field_simp [ne_of_gt hRppos]
    ring
  rw [hid, abs_mul, abs_div, abs_of_pos hRmpos, abs_of_pos hRppos]
  have hratio_nonneg : 0 ≤ (R m).1 / (R p).1 :=
    div_nonneg hRmpos.le hRppos.le
  apply mul_le_mul_of_nonneg_left _ hratio_nonneg
  rw [abs_mul, abs_of_pos hRppos]
  have htail := loading_calibration_weighted_tail_bound
    N M s Cp k hM hs hCp htriangular hcap href_pos href_mono href_fast
      z hE hK p m hpm
  rw [abs_mul, abs_of_pos hRppos] at htail
  simpa [abs_sub_comm, R] using htail

/-- Column-product transport bundled with its preserved zero-sum certificate. -/
def transportZeroSum (N : NetworkSetup n) (t k : ℕ)
    (z : ZeroSumNodeVector n) : ZeroSumNodeVector n :=
  ⟨forwardProduct N.colMix t k *ᵥ z.1, by
    have hproduct :
        FiniteNetwork.consecutiveProduct N.colMix k (t - k) ∈
          Matrix.colStochastic ℝ (Fin n) := by
      induction (t - k) with
      | zero => exact (Matrix.colStochastic ℝ (Fin n)).one_mem
      | succ q ih =>
          rw [FiniteNetwork.consecutiveProduct_succ]
          exact (Matrix.colStochastic ℝ (Fin n)).mul_mem
            (N.col_stochastic (k + q)) ih
    rw [forwardProduct,
      Matrix.sum_mulVec_of_mem_colStochastic hproduct, z.2]⟩

theorem transportZeroSum_succ (N : NetworkSetup n)
    (t k : ℕ) (hkt : k ≤ t) (z : ZeroSumNodeVector n) :
    transportZeroSum N (t + 1) k z =
      advanceZeroSum N t (transportZeroSum N t k z) := by
  apply Subtype.ext
  simp only [transportZeroSum, advanceZeroSum]
  rw [forwardProduct, forwardProduct,
    show t + 1 - k = (t - k) + 1 by omega,
    FiniteNetwork.consecutiveProduct_succ,
    show k + (t - k) = t by omega,
    Matrix.mulVec_mulVec]

/-- Finite-prefix iteration of the source resolvent identity, retaining the
terminal corrected-lift tail at the exactly transported zero-sum state. -/
theorem influenceOperator_iterated_resolvent
    (N : NetworkSetup n) (t k : ℕ) (hkt : k ≤ t)
    (z : ZeroSumNodeVector n) :
    influenceOperator N k z =
      (∑ r ∈ Finset.Ico k t,
        dotProduct (absoluteProbability N (r + 1))
          (forwardProduct N.colMix r k *ᵥ z.1)) +
        influenceOperator N t (transportZeroSum N t k z) := by
  induction t with
  | zero =>
      have hk : k = 0 := by omega
      subst k
      simp [transportZeroSum, forwardProduct]
  | succ t ih =>
      by_cases hEq : k = t + 1
      · subst k
        simp [transportZeroSum, forwardProduct]
      · have hkt' : k ≤ t := by omega
        rw [ih hkt']
        rw [influenceOperator_resolvent N t (transportZeroSum N t k z)]
        rw [Finset.sum_Ico_succ_top hkt']
        rw [transportZeroSum_succ N t k hkt' z]
        simp only [transportZeroSum]
        ring

/-- The retained-tracker flat kernel `T_{t,j}`. Book
`#/key_lemmas/3/proof/17/math`:
“`{\mathsf T}_{t,j}=C(t,j+1)(C_j-I)`”. -/
def flatTrackerKernel (N : NetworkSetup n) (t j : ℕ) : NetworkMatrix n :=
  forwardProduct N.colMix t (j + 1) * (N.colMix j - 1)

/-- The flat primal kernel `P_{t,j}`. Book
`#/key_lemmas/3/proof/17/math`:
“`{\mathsf P}_{t,j}=-R(t,j+1)-\sum_{r=j+1}^{t-1}R(t,r+1)C(r,j+1)(C_j-I)`”. -/
def flatPrimalKernel (N : NetworkSetup n) (t j : ℕ) : NetworkMatrix n :=
  -forwardProduct N.rowMix t (j + 1) -
    ∑ r ∈ Finset.Ico (j + 1) t,
      forwardProduct N.rowMix t (r + 1) *
        forwardProduct N.colMix r (j + 1) * (N.colMix j - 1)

/-- After the pulse time, the flat primal kernel is driven by the flat
retained-tracker kernel through the same row-mixing recurrence. -/
theorem flatPrimalKernel_succ
    (N : NetworkSetup n) (j t : ℕ) (hjt : j + 1 ≤ t) :
    flatPrimalKernel N (t + 1) j =
      N.rowMix t * flatPrimalKernel N t j - flatTrackerKernel N t j := by
  have hforward (k : ℕ) (hkt : k ≤ t) :
      forwardProduct N.rowMix (t + 1) k =
        N.rowMix t * forwardProduct N.rowMix t k := by
    unfold forwardProduct
    rw [show t + 1 - k = (t - k) + 1 by omega,
      FiniteNetwork.consecutiveProduct_succ,
      show k + (t - k) = t by omega]
  have hend : forwardProduct N.rowMix (t + 1) (t + 1) = 1 := by
    simp [forwardProduct]
  have hsum :
      (∑ r ∈ Finset.Ico (j + 1) t,
        forwardProduct N.rowMix (t + 1) (r + 1) *
          forwardProduct N.colMix r (j + 1) * (N.colMix j - 1)) =
      N.rowMix t *
        (∑ r ∈ Finset.Ico (j + 1) t,
          forwardProduct N.rowMix t (r + 1) *
            forwardProduct N.colMix r (j + 1) * (N.colMix j - 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    have hrt : r + 1 ≤ t := by
      exact Nat.succ_le_of_lt (Finset.mem_Ico.mp hr).2
    rw [hforward (r + 1) hrt]
    simp only [mul_assoc]
  unfold flatPrimalKernel flatTrackerKernel
  rw [hforward (j + 1) hjt, Finset.sum_Ico_succ_top hjt, hsum, hend,
    one_mul]
  noncomm_ring

/-- At the first time after the pulse, the true and flat primal responses
coincide exactly. -/
theorem loadingTrajectory_primal_eq_flat_at_pulse_exit
    (N : NetworkSetup n) (L D s : ℝ) (j : ℕ) (i : Fin n) (e : ℝ) :
    (loadingTrajectory N L D s j i e (j + 1)).primal =
      fun q => (s / L) *
        (flatPrimalKernel N (j + 1) j *ᵥ
          (fun r => if r = i then 1 else 0)) q * e := by
  classical
  obtain ⟨hX, hV⟩ :=
    loadingTrajectory_primal_retained_zero_before_pulse
      N L D s j i e j le_rfl
  have horacle :
      loadingOracle L D j i e j
        (loadingTrajectory N L D s j i e j).primal =
        loadingPulse j i e j := by
    rw [hX]
    funext q
    simp [loadingOracle, negativeCurvatureDerivative_zero]
  have htracker :
      (loadingTrajectory N L D s j i e j).tracker =
        loadingPulse j i e j := by
    rw [retainedLoadingTracker, horacle, sub_eq_zero] at hV
    exact hV
  funext q
  simp [loadingTrajectory, SOptLib.pushPullStep, hX, htracker,
    flatPrimalKernel, forwardProduct, loadingPulse, Matrix.mulVec, dotProduct,
    Matrix.one_apply]

/-- The true retained tracker differs from its flat pulse response by a
uniform pure-network multiple of `D`.  This is the completed tracker estimate
in equation (34), including the exact flat-pulse identification. -/
theorem nonlinear_loading_tracker_difference_bound
    (N : NetworkSetup n) (L D s : ℝ) (j : ℕ) (i : Fin n) (e : ℝ) (t : ℕ)
    (hL : 0 < L) (hD : 0 < D) (hjt : j + 1 ≤ t) :
    nodeL1Norm (fun q =>
        (retainedLoadingTracker N L D s j i e t q -
          (flatTrackerKernel N t j *ᵥ
            (fun r => if r = i then 1 else 0)) q * e) / L) ≤
      (((blockContraction N)⁻¹ * (n : ℝ)) / (1 - mixingRate N)) * D := by
  let U : ℕ → Fin n → ℝ := fun r q =>
    negativeCurvatureDerivative L D
      ((loadingTrajectory N L D s j i e r).primal q)
  let W : Fin n → ℝ := FiniteNetwork.trackerInnovationResponse N.colMix U t
  have hM : 0 ≤ L * D / 2 := by positivity
  have hU : ∀ r q, |U r q| ≤ L * D / 2 := by
    intro r q
    dsimp [U]
    exact abs_negativeCurvatureDerivative_le L D _ hL.le hD.le
  have hW := trackerInnovationResponse_nodeL1_le_of_uniform
    N U (L * D / 2) hM hU t
  have hpulse := trackerInnovationResponse_loadingPulse_eq_flatTrackerKernel
    N j i e t hjt
  have hdiff :
      (fun q =>
        retainedLoadingTracker N L D s j i e t q -
          (flatTrackerKernel N t j *ᵥ
            (fun r => if r = i then 1 else 0)) q * e) = W := by
    rw [retainedLoadingTracker_eq_nonlinearResponse_add_pulseResponse]
    rw [hpulse]
    funext q
    simp only [Pi.add_apply, Pi.sub_apply]
    dsimp [W, U]
    unfold flatTrackerKernel
    ring
  have hscaled :
      (fun q =>
        (retainedLoadingTracker N L D s j i e t q -
          (flatTrackerKernel N t j *ᵥ
            (fun r => if r = i then 1 else 0)) q * e) / L) =
        (fun q => W q / L) := by
    funext q
    rw [congrFun hdiff q]
  rw [hscaled]
  have hscale :
      nodeL1Norm (fun q => W q / L) =
        FiniteNetwork.stateL1Norm W / L := by
    unfold nodeL1Norm FiniteNetwork.stateL1Norm
    simp_rw [Real.norm_eq_abs, abs_div, abs_of_pos hL]
    exact (Finset.sum_div _ _ L).symm
  rw [hscale]
  have hden : 0 < 1 - mixingRate N := by
    linarith [mixingRate_lt_one N]
  have hLnonneg : 0 ≤ L := hL.le
  have hright :
      (((blockContraction N)⁻¹ * (2 * (n : ℝ) * (L * D / 2))) /
          (1 - mixingRate N)) / L =
        (((blockContraction N)⁻¹ * (n : ℝ)) /
          (1 - mixingRate N)) * D := by
    field_simp
  rw [← hright]
  exact div_le_div_of_nonneg_right hW hLnonneg

/-- Exact one-step recurrence for the primal error after subtracting the flat
pulse response.  Only the nonlinear tracker response and bounded storage
gradient remain as forcing terms. -/
theorem loading_primal_flat_error_succ
    (N : NetworkSetup n) (L D s : ℝ) (j : ℕ) (i : Fin n) (e : ℝ) (t : ℕ)
    (hjt : j + 1 ≤ t) :
    (fun q =>
      (loadingTrajectory N L D s j i e (t + 1)).primal q -
        (s / L) * (flatPrimalKernel N (t + 1) j *ᵥ
          (fun r => if r = i then 1 else 0)) q * e) =
      (fun q =>
        (N.rowMix t *ᵥ (fun r =>
          (loadingTrajectory N L D s j i e t).primal r -
            (s / L) * (flatPrimalKernel N t j *ᵥ
              (fun u => if u = i then 1 else 0)) r * e)) q -
          (s / L) *
            (FiniteNetwork.trackerInnovationResponse N.colMix
                (fun r k => negativeCurvatureDerivative L D
                  ((loadingTrajectory N L D s j i e r).primal k)) t q +
              negativeCurvatureDerivative L D
                ((loadingTrajectory N L D s j i e t).primal q))) := by
  classical
  let W : Fin n → ℝ :=
    FiniteNetwork.trackerInnovationResponse N.colMix
      (fun r k => negativeCurvatureDerivative L D
        ((loadingTrajectory N L D s j i e r).primal k)) t
  have hpulse_resp :=
    trackerInnovationResponse_loadingPulse_eq_flatTrackerKernel
      N j i e t hjt
  have hret := retainedLoadingTracker_eq_nonlinearResponse_add_pulseResponse
    N L D s j i e t
  rw [hpulse_resp] at hret
  have htne : t ≠ j := by omega
  have hpulse : loadingPulse j i e t = 0 := by
    funext q
    simp [loadingPulse, htne]
  have htracker :
      (loadingTrajectory N L D s j i e t).tracker =
        fun q => W q +
          (flatTrackerKernel N t j *ᵥ
            (fun r => if r = i then 1 else 0)) q * e +
          negativeCurvatureDerivative L D
            ((loadingTrajectory N L D s j i e t).primal q) := by
    funext q
    have hd := congrFun hret q
    unfold retainedLoadingTracker at hd
    simp only [Pi.sub_apply, Pi.add_apply] at hd
    unfold loadingOracle at hd
    rw [show loadingPulse j i e t q = 0 by simp [loadingPulse, htne]] at hd
    change (loadingTrajectory N L D s j i e t).tracker q = _
    dsimp [W]
    unfold flatTrackerKernel
    linarith
  rw [flatPrimalKernel_succ N j t hjt]
  funext q
  simp only [loadingTrajectory, SOptLib.pushPullStep, htracker,
    Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.smulVec_apply,
    smul_eq_mul, Pi.sub_apply, Pi.add_apply]
  simp only [Matrix.mulVec, dotProduct]
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_sub,
    Finset.sum_sub_distrib]
  dsimp [W]
  have htracker_sum :
      s * L⁻¹ *
          (∑ x, (flatTrackerKernel N t j q x *
            (if x = i then 1 else 0)) * e) =
        e * ∑ x, s * L⁻¹ * flatTrackerKernel N t j q x *
          (if x = i then 1 else 0) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hprimal_sum :
      e * ∑ x, ∑ y, s * L⁻¹ * N.rowMix t q y *
          flatPrimalKernel N t j y x * (if x = i then 1 else 0) =
        ∑ x, ∑ y, s * L⁻¹ * e * N.rowMix t q x *
          flatPrimalKernel N t j x y * (if y = i then 1 else 0) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  simp only [div_eq_mul_inv]
  ring_nf
  rw [htracker_sum, hprimal_sum]
  ring

/-- Accumulating the exact primal-error recurrence with row-stochastic
nonexpansiveness gives the primal half of equation (34). -/
theorem nonlinear_loading_primal_difference_bound
    (N : NetworkSetup n) (L D s : ℝ) (j : ℕ) (i : Fin n) (e : ℝ)
    (hL : 0 < L) (hD : 0 < D) (hs : 0 < s) :
    ∀ t : ℕ, j + 1 ≤ t →
      nodeSupNorm (fun q =>
        (loadingTrajectory N L D s j i e t).primal q -
          (s / L) * (flatPrimalKernel N t j *ᵥ
            (fun r => if r = i then 1 else 0)) q * e) ≤
        (t - j - 1 : ℕ) * s *
          ((((blockContraction N)⁻¹ * (n : ℝ)) /
            (1 - mixingRate N)) + 1 / 2) * D := by
  let K : ℝ := ((blockContraction N)⁻¹ * (n : ℝ)) /
    (1 - mixingRate N)
  have hdelta : 0 ≤ (blockContraction N)⁻¹ := by
    exact inv_nonneg.mpr (blockContraction_pos N).le
  have hden : 0 < 1 - mixingRate N := by
    linarith [mixingRate_lt_one N]
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hstep_nonneg : 0 ≤ s * (K + 1 / 2) * D := by positivity
  intro t hjt
  induction t using Nat.strong_induction_on with
  | h t ih =>
      by_cases ht0 : t = j + 1
      · subst t
        rw [loadingTrajectory_primal_eq_flat_at_pulse_exit]
        simp [nodeSupNorm]
      · let p : ℕ := t - 1
        have hpt : p + 1 = t := by
          dsimp [p]
          omega
        have hjp : j + 1 ≤ p := by
          dsimp [p]
          omega
        have hplt : p < t := by omega
        have ihp := ih p hplt hjp
        let E : Fin n → ℝ := fun q =>
          (loadingTrajectory N L D s j i e p).primal q -
            (s / L) * (flatPrimalKernel N p j *ᵥ
              (fun r => if r = i then 1 else 0)) q * e
        change nodeSupNorm E ≤
          (p - j - 1 : ℕ) * s * (K + 1 / 2) * D at ihp
        let W : Fin n → ℝ :=
          FiniteNetwork.trackerInnovationResponse N.colMix
            (fun r k => negativeCurvatureDerivative L D
              ((loadingTrajectory N L D s j i e r).primal k)) p
        have hrec := loading_primal_flat_error_succ
          N L D s j i e p hjp
        have hU : ∀ r q,
            |negativeCurvatureDerivative L D
              ((loadingTrajectory N L D s j i e r).primal q)| ≤
              L * D / 2 := by
          intro r q
          exact abs_negativeCurvatureDerivative_le L D _ hL.le hD.le
        have hWraw := trackerInnovationResponse_nodeL1_le_of_uniform
          N (fun r q => negativeCurvatureDerivative L D
            ((loadingTrajectory N L D s j i e r).primal q))
          (L * D / 2) (by positivity) hU p
        have hWbound : FiniteNetwork.stateL1Norm W ≤ K * L * D := by
          dsimp [W] at hWraw ⊢
          have heq :
              ((blockContraction N)⁻¹ *
                  (2 * (n : ℝ) * (L * D / 2))) /
                    (1 - mixingRate N) = K * L * D := by
            dsimp [K]
            field_simp
          rw [← heq]
          exact hWraw
        have hWcoord (q : Fin n) : |W q| ≤ K * L * D := by
          calc
            |W q| ≤ FiniteNetwork.stateL1Norm W := by
              rw [FiniteNetwork.stateL1Norm_def]
              simpa [Real.norm_eq_abs] using
                (Finset.single_le_sum (fun r _ => norm_nonneg (W r))
                  (Finset.mem_univ q))
            _ ≤ K * L * D := hWbound
        have hpoint (q : Fin n) :
            |(loadingTrajectory N L D s j i e t).primal q -
                (s / L) * (flatPrimalKernel N t j *ᵥ
                  (fun r => if r = i then 1 else 0)) q * e| ≤
              ((p - j - 1 : ℕ) + 1) * s * (K + 1 / 2) * D := by
          have hrecq := congrFun hrec q
          rw [hpt] at hrecq
          change _ = (N.rowMix p *ᵥ E) q -
            (s / L) * (W q + negativeCurvatureDerivative L D
              ((loadingTrajectory N L D s j i e p).primal q)) at hrecq
          rw [hrecq]
          have hrowcoord : |(N.rowMix p *ᵥ E) q| ≤ nodeSupNorm E :=
            (abs_le_nodeSupNorm _ q).trans (rowMix_nodeSupNorm_le N p E)
          have hforce :
              |(s / L) * (W q + negativeCurvatureDerivative L D
                ((loadingTrajectory N L D s j i e p).primal q))| ≤
                s * (K + 1 / 2) * D := by
            rw [abs_mul, abs_of_pos (div_pos hs hL)]
            calc
              (s / L) * |W q + negativeCurvatureDerivative L D
                  ((loadingTrajectory N L D s j i e p).primal q)| ≤
                  (s / L) * (K * L * D + L * D / 2) := by
                gcongr
                exact (abs_add_le _ _).trans
                  (add_le_add (hWcoord q) (hU p q))
              _ = s * (K + 1 / 2) * D := by field_simp
          calc
            |(N.rowMix p *ᵥ E) q -
                (s / L) * (W q + negativeCurvatureDerivative L D
                  ((loadingTrajectory N L D s j i e p).primal q))| ≤
                |(N.rowMix p *ᵥ E) q| +
                  |(s / L) * (W q + negativeCurvatureDerivative L D
                    ((loadingTrajectory N L D s j i e p).primal q))| :=
              abs_sub _ _
            _ ≤ nodeSupNorm E + s * (K + 1 / 2) * D :=
              add_le_add hrowcoord hforce
            _ ≤ (p - j - 1 : ℕ) * s * (K + 1 / 2) * D +
                s * (K + 1 / 2) * D := by
              exact add_le_add ihp le_rfl
            _ = ((p - j - 1 : ℕ) + 1) * s * (K + 1 / 2) * D := by
              push_cast
              ring
        have hsup :
            nodeSupNorm (fun q =>
              (loadingTrajectory N L D s j i e t).primal q -
                (s / L) * (flatPrimalKernel N t j *ᵥ
                  (fun r => if r = i then 1 else 0)) q * e) ≤
              ((p - j - 1 : ℕ) + 1) * s * (K + 1 / 2) * D := by
          letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp N.hn
          unfold nodeSupNorm
          exact ciSup_le hpoint
        have hlag : t - j - 1 = (p - j - 1) + 1 := by
          dsimp [p]
          omega
        simpa [K, hlag] using hsup

/-- The paired nonlinear-response estimate (34), with explicit pure-network
constants, on every loading segment of length at most `2m`. -/
theorem bounded_nonlinear_loading_response
    (N : NetworkSetup n) (L D s : ℝ) (j : ℕ) (i : Fin n) (e : ℝ)
    (m t : ℕ) (hL : 0 < L) (hD : 0 < D) (hs : 0 < s)
    (hjt : j + 1 ≤ t) (ht : t ≤ j + 2 * m + 1) :
    nodeL1Norm (fun q =>
        (retainedLoadingTracker N L D s j i e t q -
          (flatTrackerKernel N t j *ᵥ
            (fun r => if r = i then 1 else 0)) q * e) / L) ≤
        (((blockContraction N)⁻¹ * (n : ℝ)) /
          (1 - mixingRate N)) * D ∧
    nodeSupNorm (fun q =>
        (loadingTrajectory N L D s j i e t).primal q -
          (s / L) * (flatPrimalKernel N t j *ᵥ
            (fun r => if r = i then 1 else 0)) q * e) ≤
        (2 * ((((blockContraction N)⁻¹ * (n : ℝ)) /
          (1 - mixingRate N)) + 1 / 2)) * s * (m + 1) * D := by
  constructor
  · exact nonlinear_loading_tracker_difference_bound
      N L D s j i e t hL hD hjt
  · have hp := nonlinear_loading_primal_difference_bound
      N L D s j i e hL hD hs t hjt
    have hK : 0 ≤ ((blockContraction N)⁻¹ * (n : ℝ)) /
        (1 - mixingRate N) := by
      have hden : 0 < 1 - mixingRate N := by
        linarith [mixingRate_lt_one N]
      exact div_nonneg
        (mul_nonneg (inv_nonneg.mpr (blockContraction_pos N).le)
          (Nat.cast_nonneg n)) hden.le
    have hlag : t - j - 1 ≤ 2 * m := by omega
    have hlagR : ((t - j - 1 : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by
      exact_mod_cast hlag
    calc
      nodeSupNorm (fun q =>
          (loadingTrajectory N L D s j i e t).primal q -
            (s / L) * (flatPrimalKernel N t j *ᵥ
              (fun r => if r = i then 1 else 0)) q * e) ≤
          (t - j - 1 : ℕ) * s *
            ((((blockContraction N)⁻¹ * (n : ℝ)) /
              (1 - mixingRate N)) + 1 / 2) * D := hp
      _ ≤ (2 * (m : ℝ)) * s *
            ((((blockContraction N)⁻¹ * (n : ℝ)) /
              (1 - mixingRate N)) + 1 / 2) * D := by
        gcongr
      _ ≤ (2 * ((((blockContraction N)⁻¹ * (n : ℝ)) /
            (1 - mixingRate N)) + 1 / 2)) * s * (m + 1) * D := by
        push_cast
        have hm : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
        have hc : 0 ≤ ((blockContraction N)⁻¹ * (n : ℝ)) /
            (1 - mixingRate N) + 1 / 2 := by linarith
        calc
          2 * (m : ℝ) * s *
              (((blockContraction N)⁻¹ * (n : ℝ)) /
                (1 - mixingRate N) + 1 / 2) * D ≤
              2 * ((m : ℝ) + 1) * s *
                (((blockContraction N)⁻¹ * (n : ℝ)) /
                  (1 - mixingRate N) + 1 / 2) * D := by gcongr
          _ = 2 * (((blockContraction N)⁻¹ * (n : ℝ)) /
                (1 - mixingRate N) + 1 / 2) * s * ((m : ℝ) + 1) * D := by
              ring

/-- Exact corrected-center decomposition of the flat primal kernel.  Each
finite term is a row-product disagreement around its propagated absolute-
probability center, and the only remainder is the terminal resolvent tail. -/
theorem flatPrimalKernel_corrected_identity
    (N : NetworkSetup n) (j : ℕ) (i : Fin n) (t : ℕ) (hjt : j + 1 ≤ t) :
    (fun q =>
      (flatPrimalKernel N t j *ᵥ (fun r => if r = i then 1 else 0)) q +
        influenceRow N j i) =
      (fun q =>
        -((forwardProduct N.rowMix t (j + 1) *ᵥ
              (fun r => if r = i then 1 else 0)) q -
            dotProduct (absoluteProbability N (j + 1))
              (fun r => if r = i then 1 else 0)) -
          (∑ r ∈ Finset.Ico (j + 1) t,
            ((forwardProduct N.rowMix t (r + 1) *ᵥ
                (forwardProduct N.colMix r (j + 1) *ᵥ
                  (columnInnovation N j i).1)) q -
              dotProduct (absoluteProbability N (r + 1))
                (forwardProduct N.colMix r (j + 1) *ᵥ
                  (columnInnovation N j i).1))) +
          influenceOperator N t
            (transportZeroSum N t (j + 1) (columnInnovation N j i))) := by
  classical
  funext q
  rw [influenceRow]
  rw [influenceOperator_iterated_resolvent N t (j + 1) hjt
    (columnInnovation N j i)]
  simp only [flatPrimalKernel, Matrix.sub_mulVec, Matrix.neg_mulVec,
    Matrix.sum_mulVec, Matrix.mulVec_mulVec, Pi.sub_apply, Pi.neg_apply]
  have hinnovation :
      (N.colMix j - 1) *ᵥ (fun r => if r = i then 1 else 0) =
        (columnInnovation N j i).1 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    funext r
    simp [Matrix.mulVec, dotProduct, columnInnovation]
  have hterm_action (r : ℕ) :
      (forwardProduct N.rowMix t (r + 1) *
          forwardProduct N.colMix r (j + 1) * (N.colMix j - 1)) *ᵥ
            (fun r => if r = i then 1 else 0) =
        (forwardProduct N.rowMix t (r + 1) *
          forwardProduct N.colMix r (j + 1)) *ᵥ
            (columnInnovation N j i).1 := by
    rw [← Matrix.mulVec_mulVec, hinnovation]
  simp_rw [hterm_action]
  have hselect :
      dotProduct (absoluteProbability N (j + 1))
          (fun r => if r = i then 1 else 0) =
        absoluteProbability N (j + 1) i := by
    simp [dotProduct]
  rw [hselect]
  simp only [Finset.sum_apply]
  rw [Finset.sum_sub_distrib]
  ring

/-- A stochastic column minus its coordinate atom has total variation at
most two; the Euclidean estimate is recorded simultaneously for later use. -/
theorem columnInnovation_norms_le_two
    (N : NetworkSetup n) (j : ℕ) (i : Fin n) :
    nodeL1Norm (columnInnovation N j i).1 ≤ 2 ∧
      nodeL2Norm (columnInnovation N j i).1 ≤ 2 := by
  classical
  have hL1 : nodeL1Norm (columnInnovation N j i).1 ≤ 2 := by
    unfold nodeL1Norm columnInnovation
    calc
      (∑ r : Fin n, |N.colMix j r i - if r = i then 1 else 0|) ≤
          ∑ r : Fin n, (|N.colMix j r i| + |if r = i then (1 : ℝ) else 0|) := by
        exact Finset.sum_le_sum fun r _ => abs_sub _ _
      _ = (∑ r : Fin n, N.colMix j r i) + 1 := by
        rw [Finset.sum_add_distrib]
        have hnonneg : ∀ r : Fin n, 0 ≤ N.colMix j r i := fun r =>
          Matrix.nonneg_of_mem_colStochastic (N.col_stochastic j)
        simp_rw [abs_of_nonneg (hnonneg _)]
        simp only [abs_ite, abs_one, abs_zero]
        simp
      _ = 2 := by
        rw [Matrix.sum_col_of_mem_colStochastic (N.col_stochastic j)]
        norm_num
  refine ⟨hL1, ?_⟩
  calc
    nodeL2Norm (columnInnovation N j i).1 =
        ‖WithLp.toLp 2 (columnInnovation N j i).1‖ := by
      simp [PiLp.norm_eq_of_L2, nodeL2Norm, Real.norm_eq_abs, sq_abs]
    _ ≤ ∑ r, ‖(columnInnovation N j i).1 r‖ :=
      dependentProductL2Seminorm_le_sum_norm _
    _ = nodeL1Norm (columnInnovation N j i).1 := by
      simp [nodeL1Norm, Real.norm_eq_abs]
    _ ≤ 2 := hL1

/-- The tracker half of equation (33).  It is the completed column-product
estimate specialized to the zero-sum innovation column `(C_j-I)e_i`. -/
theorem flatTrackerKernel_nodeL1_geometric (N : NetworkSetup n) :
    ∃ Ktr : ℝ, 0 ≤ Ktr ∧
      ∀ (j : ℕ) (i : Fin n) (t : ℕ), j + 1 ≤ t →
        nodeL1Norm
            (flatTrackerKernel N t j *ᵥ
              (fun r => if r = i then 1 else 0)) ≤
          Ktr * loadingFlatRate N ^ (t - j - 1) := by
  classical
  let Ktr : ℝ := 2 * (blockContraction N)⁻¹
  have hdelta_pos : 0 < blockContraction N := blockContraction_pos N
  have hKtr : 0 ≤ Ktr := by
    dsimp [Ktr]
    positivity
  refine ⟨Ktr, hKtr, ?_⟩
  intro j i t hjt
  have hinnovation :
      nodeL1Norm (columnInnovation N j i).1 ≤ 2 :=
    (columnInnovation_norms_le_two N j i).1
  have hkernel :
      flatTrackerKernel N t j *ᵥ (fun r => if r = i then 1 else 0) =
        forwardProduct N.colMix t (j + 1) *ᵥ (columnInnovation N j i).1 := by
    rw [flatTrackerKernel, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec,
      Matrix.one_mulVec]
    congr 1
    funext r
    simp [Matrix.mulVec, dotProduct, columnInnovation]
  rw [hkernel]
  have hcol := colMix_stateL1_geometric N (j + 1) (t - (j + 1))
    (columnInnovation N j i)
  have hrho_flat : mixingRate N ≤ loadingFlatRate N := by
    unfold loadingFlatRate
    linarith [mixingRate_lt_one N]
  have hpowers :
      mixingRate N ^ (t - (j + 1)) ≤
        loadingFlatRate N ^ (t - (j + 1)) :=
    pow_le_pow_left₀ (mixingRate_nonneg N) hrho_flat _
  have hcoeff_nonneg : 0 ≤ (blockContraction N)⁻¹ := by positivity
  calc
    nodeL1Norm
        (forwardProduct N.colMix t (j + 1) *ᵥ (columnInnovation N j i).1) =
        FiniteNetwork.stateL1Norm
          (Matrix.smulVec
            (FiniteNetwork.consecutiveProduct N.colMix (j + 1) (t - (j + 1)))
            (columnInnovation N j i).1) := by
      simp [nodeL1Norm, forwardProduct, FiniteNetwork.stateL1Norm_def,
        Matrix.mulVec, dotProduct, Matrix.smulVec, Real.norm_eq_abs]
    _ ≤ (blockContraction N)⁻¹ * mixingRate N ^ (t - (j + 1)) *
          FiniteNetwork.stateL1Norm (columnInnovation N j i).1 := hcol
    _ ≤ (blockContraction N)⁻¹ * mixingRate N ^ (t - (j + 1)) * 2 := by
      exact mul_le_mul_of_nonneg_left hinnovation
        (mul_nonneg hcoeff_nonneg (pow_nonneg (mixingRate_nonneg N) _))
    _ ≤ (blockContraction N)⁻¹ * loadingFlatRate N ^ (t - (j + 1)) * 2 := by
      gcongr
    _ = Ktr * loadingFlatRate N ^ (t - j - 1) := by
      dsimp [Ktr]
      rw [show t - (j + 1) = t - j - 1 by omega]
      ring

/-- The corrected primal half of equation (33), obtained from the exact
corrected-center identity, row/column geometric convolution, and absorption
of the linear lag into the strictly larger flat rate. -/
theorem flatPrimalKernel_corrected_geometric (N : NetworkSetup n) :
    ∃ Kpr : ℝ, 0 ≤ Kpr ∧
      ∀ (j : ℕ) (i : Fin n) (t : ℕ), j + 1 ≤ t →
        nodeSupNorm
            (fun q => (flatPrimalKernel N t j *ᵥ
              (fun r => if r = i then 1 else 0)) q + influenceRow N j i) ≤
          Kpr * loadingFlatRate N ^ (t - j - 1) := by
  classical
  have hρpos : 0 < mixingRate N := (uniform_mixing_and_influence N).1
  have hρnonneg : 0 ≤ mixingRate N := hρpos.le
  have hρlt : mixingRate N < loadingFlatRate N := by
    unfold loadingFlatRate
    linarith [mixingRate_lt_one N]
  have hRpos : 0 < loadingFlatRate N := hρpos.trans hρlt
  obtain ⟨Cconv, hCconv, hconv⟩ :=
    exists_const_one_add_natCast_mul_pow_le_pow_of_lt hρnonneg hρlt
  have hrowC : 0 ≤ rowMixingConstant N := by
    unfold rowMixingConstant
    exact div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (blockContraction_pos N).le
  have hcolC : 0 ≤ columnMixingConstant N := by
    unfold columnMixingConstant
    exact div_nonneg (Real.sqrt_nonneg _) (blockContraction_pos N).le
  have hD : 0 ≤ influenceOperatorBound N := by
    unfold influenceOperatorBound
    have : 0 < 1 - mixingRate N := by linarith [mixingRate_lt_one N]
    positivity
  let A : ℝ := 2 * rowMixingConstant N
  let B : ℝ := 4 * rowMixingConstant N * columnMixingConstant N
  let Ttail : ℝ := 2 * influenceOperatorBound N * columnMixingConstant N
  let Kpr : ℝ := A + Ttail + B * (Cconv / loadingFlatRate N)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hTtail : 0 ≤ Ttail := by dsimp [Ttail]; positivity
  have hKpr : 0 ≤ Kpr := by
    dsimp [Kpr]
    positivity
  refine ⟨Kpr, hKpr, ?_⟩
  intro j i t hjt
  let e : Fin n → ℝ := fun r => if r = i then 1 else 0
  let z : ZeroSumNodeVector n := columnInnovation N j i
  let m : ℕ := t - j - 1
  have hm_eq : m = t - (j + 1) := by dsimp [m]; omega
  have he_norm : nodeL2Norm e = 1 := by
    dsimp [e]
    simp [nodeL2Norm]
  have hz_norm : nodeL2Norm z.1 ≤ 2 := by
    dsimp [z]
    exact (columnInnovation_norms_le_two N j i).2
  have hinitial :
      nodeSupNorm (fun q =>
          (forwardProduct N.rowMix t (j + 1) *ᵥ e) q -
            dotProduct (absoluteProbability N (j + 1)) e) ≤
        A * mixingRate N ^ m := by
    have hrow := rowProduct_sub_absoluteConsensus_sup_geometric
      N t (j + 1) hjt e
    have hdis := disagreement_nodeL2_le N e
    rw [he_norm] at hdis
    calc
      _ ≤ (2 * rowMixingConstant N) * mixingRate N ^ (t - (j + 1)) *
          nodeL2Norm (disagreement e) := hrow
      _ ≤ (2 * rowMixingConstant N) * mixingRate N ^ (t - (j + 1)) * 1 := by
        exact mul_le_mul_of_nonneg_left hdis
          (mul_nonneg (mul_nonneg (by positivity) hrowC)
            (pow_nonneg hρnonneg _))
      _ = A * mixingRate N ^ m := by rw [hm_eq]; simp [A]
  have hterm : ∀ r ∈ Finset.Ico (j + 1) t,
      nodeSupNorm (fun q =>
          (forwardProduct N.rowMix t (r + 1) *ᵥ
            (forwardProduct N.colMix r (j + 1) *ᵥ z.1)) q -
          dotProduct (absoluteProbability N (r + 1))
            (forwardProduct N.colMix r (j + 1) *ᵥ z.1)) ≤
        B * (mixingRate N ^ (t - r - 1) *
          mixingRate N ^ (r - j - 1)) := by
    intro r hr
    have hrange := Finset.mem_Ico.mp hr
    have hrj : j + 1 ≤ r := hrange.1
    have hrt : r + 1 ≤ t := by omega
    have hrow := rowProduct_sub_absoluteConsensus_sup_geometric N t (r + 1)
      hrt (forwardProduct N.colMix r (j + 1) *ᵥ z.1)
    have hdis := disagreement_nodeL2_le N
      (forwardProduct N.colMix r (j + 1) *ᵥ z.1)
    have hcol := scalar_colMix_nodeL2_geometric N r (j + 1) hrj z.1 z.2
    calc
      _ ≤ (2 * rowMixingConstant N) * mixingRate N ^ (t - (r + 1)) *
          nodeL2Norm (disagreement
            (forwardProduct N.colMix r (j + 1) *ᵥ z.1)) := hrow
      _ ≤ (2 * rowMixingConstant N) * mixingRate N ^ (t - (r + 1)) *
          nodeL2Norm (forwardProduct N.colMix r (j + 1) *ᵥ z.1) := by
        exact mul_le_mul_of_nonneg_left hdis
          (mul_nonneg (mul_nonneg (by positivity) hrowC)
            (pow_nonneg hρnonneg _))
      _ ≤ (2 * rowMixingConstant N) * mixingRate N ^ (t - (r + 1)) *
          (columnMixingConstant N * mixingRate N ^ (r - (j + 1)) *
            nodeL2Norm z.1) := by
        exact mul_le_mul_of_nonneg_left hcol
          (mul_nonneg (mul_nonneg (by positivity) hrowC)
            (pow_nonneg hρnonneg _))
      _ ≤ (2 * rowMixingConstant N) * mixingRate N ^ (t - (r + 1)) *
          (columnMixingConstant N * mixingRate N ^ (r - (j + 1)) * 2) := by
        gcongr
      _ = B * (mixingRate N ^ (t - r - 1) *
          mixingRate N ^ (r - j - 1)) := by
        dsimp [B]
        rw [show t - (r + 1) = t - r - 1 by omega,
          show r - (j + 1) = r - j - 1 by omega]
        ring
  have htail :
      |influenceOperator N t (transportZeroSum N t (j + 1) z)| ≤
        Ttail * mixingRate N ^ m := by
    have hop := influenceOperator_norm_le N t
      (transportZeroSum N t (j + 1) z)
    have hcol := scalar_colMix_nodeL2_geometric N t (j + 1) hjt z.1 z.2
    change nodeL2Norm
      (forwardProduct N.colMix t (j + 1) *ᵥ z.1) ≤ _ at hcol
    calc
      _ ≤ influenceOperatorBound N *
          nodeL2Norm (transportZeroSum N t (j + 1) z).1 := hop
      _ ≤ influenceOperatorBound N *
          (columnMixingConstant N * mixingRate N ^ (t - (j + 1)) *
            nodeL2Norm z.1) := by
        exact mul_le_mul_of_nonneg_left hcol hD
      _ ≤ influenceOperatorBound N *
          (columnMixingConstant N * mixingRate N ^ (t - (j + 1)) * 2) := by
        gcongr
      _ = Ttail * mixingRate N ^ m := by
        dsimp [Ttail]
        rw [hm_eq]
        ring
  have hpoint (q : Fin n) :
      |(flatPrimalKernel N t j *ᵥ e) q + influenceRow N j i| ≤
        A * mixingRate N ^ m +
          B * ((m : ℝ) * mixingRate N ^ (m - 1)) +
          Ttail * mixingRate N ^ m := by
    have hid := congrFun (flatPrimalKernel_corrected_identity N j i t hjt) q
    change (flatPrimalKernel N t j *ᵥ e) q + influenceRow N j i = _ at hid
    let a0 : ℝ := (forwardProduct N.rowMix t (j + 1) *ᵥ e) q -
      dotProduct (absoluteProbability N (j + 1)) e
    let f : ℕ → ℝ := fun r =>
      (forwardProduct N.rowMix t (r + 1) *ᵥ
        (forwardProduct N.colMix r (j + 1) *ᵥ z.1)) q -
      dotProduct (absoluteProbability N (r + 1))
        (forwardProduct N.colMix r (j + 1) *ᵥ z.1)
    let tail : ℝ := influenceOperator N t (transportZeroSum N t (j + 1) z)
    have hid' :
        (flatPrimalKernel N t j *ᵥ e) q + influenceRow N j i =
          -a0 - (∑ r ∈ Finset.Ico (j + 1) t, f r) + tail := by
      simpa [a0, f, tail, e, z] using hid
    rw [hid']
    calc
      |-a0 - (∑ r ∈ Finset.Ico (j + 1) t, f r) + tail| ≤
          |a0| + (∑ r ∈ Finset.Ico (j + 1) t, |f r|) + |tail| := by
        calc
          _ ≤ |-a0 - (∑ r ∈ Finset.Ico (j + 1) t, f r)| + |tail| :=
            abs_add_le _ _
          _ ≤ (|a0| + |∑ r ∈ Finset.Ico (j + 1) t, f r|) + |tail| := by
            gcongr
            simpa only [abs_neg] using
              (abs_sub (-a0) (∑ r ∈ Finset.Ico (j + 1) t, f r))
          _ ≤ |a0| + (∑ r ∈ Finset.Ico (j + 1) t, |f r|) + |tail| := by
            gcongr
            exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ A * mixingRate N ^ m +
          (∑ r ∈ Finset.Ico (j + 1) t,
            B * (mixingRate N ^ (t - r - 1) *
              mixingRate N ^ (r - j - 1))) +
          Ttail * mixingRate N ^ m := by
        exact add_le_add
          (add_le_add
            (by
              dsimp [a0]
              exact (abs_le_nodeSupNorm _ q).trans hinitial)
            (Finset.sum_le_sum fun r hr => by
              dsimp [f]
              exact (abs_le_nodeSupNorm _ q).trans (hterm r hr)))
          (by simpa [tail] using htail)
      _ = A * mixingRate N ^ m +
          B * ((m : ℝ) * mixingRate N ^ (m - 1)) +
          Ttail * mixingRate N ^ m := by
        rw [← Finset.mul_sum]
        rw [sum_Ico_split_geometric_powers (mixingRate N) j t hjt]
        rw [show t - j - 2 = (t - j - 1) - 1 by omega]
  have hsup :
      nodeSupNorm (fun q =>
        (flatPrimalKernel N t j *ᵥ e) q + influenceRow N j i) ≤
        A * mixingRate N ^ m +
          B * ((m : ℝ) * mixingRate N ^ (m - 1)) +
          Ttail * mixingRate N ^ m := by
    letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp N.hn
    unfold nodeSupNorm
    exact ciSup_le (fun q => hpoint q)
  have hρRpow : mixingRate N ^ m ≤ loadingFlatRate N ^ m :=
    pow_le_pow_left₀ hρnonneg hρlt.le _
  by_cases hm0 : m = 0
  · have hm0' : t - j - 1 = 0 := by simpa [m] using hm0
    refine hsup.trans ?_
    dsimp [Kpr]
    simp [hm0, hm0']
    have hBC : 0 ≤ B * (Cconv / loadingFlatRate N) := by positivity
    linarith
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    have hlag :
        (m : ℝ) * mixingRate N ^ (m - 1) ≤
          (Cconv / loadingFlatRate N) * loadingFlatRate N ^ m := by
      have hc := hconv (m - 1)
      have hmcast : (((m - 1 : ℕ) : ℝ) + 1) = (m : ℝ) := by
        norm_cast
        omega
      rw [hmcast] at hc
      calc
        (m : ℝ) * mixingRate N ^ (m - 1) ≤
            Cconv * loadingFlatRate N ^ (m - 1) := hc
        _ = (Cconv / loadingFlatRate N) *
            (loadingFlatRate N ^ (m - 1) * loadingFlatRate N) := by
          field_simp
        _ = (Cconv / loadingFlatRate N) * loadingFlatRate N ^ m := by
          rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm0)]
    refine hsup.trans ?_
    calc
      A * mixingRate N ^ m +
          B * ((m : ℝ) * mixingRate N ^ (m - 1)) +
          Ttail * mixingRate N ^ m ≤
        A * loadingFlatRate N ^ m +
          B * ((Cconv / loadingFlatRate N) * loadingFlatRate N ^ m) +
          Ttail * loadingFlatRate N ^ m := by gcongr
      _ = Kpr * loadingFlatRate N ^ m := by
        dsimp [Kpr]
        ring

/-- The full source specification of a finite flat-response constant `K_f`.
It records both estimates in (33), not merely the fact that a number exists.
Book `#/key_lemmas/3/proof/19/math`:
“`\|X_t^{(0)}-d1\|_\infty\le K_f\alpha|e|\rho_{flat}^{t-j-1},\qquad
\|V_t^{tr,(0)}\|_1\le K_f|e|\rho_{flat}^{t-j-1}`”. -/
def IsFlatKernelConstant (N : NetworkSetup n) (Kf : ℝ) : Prop :=
  1 ≤ Kf ∧
  ∀ (j : ℕ) (i : Fin n) (t : ℕ), j + 1 ≤ t →
    nodeSupNorm
        (fun k => (flatPrimalKernel N t j *ᵥ
          (fun r => if r = i then 1 else 0)) k + influenceRow N j i) ≤
      Kf * loadingFlatRate N ^ (t - j - 1) ∧
    nodeL1Norm
        (flatTrackerKernel N t j *ᵥ (fun r => if r = i then 1 else 0)) ≤
      Kf * loadingFlatRate N ^ (t - j - 1)

/-- Geometric row/column convolution supplies the finite pure-network
constant promised immediately before equation (34). Book
`#/key_lemmas/3/proof/18/math`: “`K_f\ge1`”. -/
theorem exists_flatKernelConstant (N : NetworkSetup n) :
    ∃ Kf : ℝ, IsFlatKernelConstant N Kf := by
  obtain ⟨Ktr, hKtr, htracker⟩ := flatTrackerKernel_nodeL1_geometric N
  obtain ⟨Kpr, hKpr, hprimal⟩ := flatPrimalKernel_corrected_geometric N
  let Kf : ℝ := max 1 (max Kpr Ktr)
  refine ⟨Kf, ?_⟩
  unfold IsFlatKernelConstant
  refine ⟨?_, ?_⟩
  · dsimp [Kf]
    exact le_max_left _ _
  · intro j i t hjt
    constructor
    · refine (hprimal j i t hjt).trans ?_
      exact mul_le_mul_of_nonneg_right
        (le_trans (le_max_left Kpr Ktr) (le_max_right 1 (max Kpr Ktr)))
        (pow_nonneg (by
          unfold loadingFlatRate
          linarith [(uniform_mixing_and_influence N).1]) _)
    · refine (htracker j i t hjt).trans ?_
      exact mul_le_mul_of_nonneg_right
        (le_trans (le_max_right Kpr Ktr) (le_max_right 1 (max Kpr Ktr)))
        (pow_nonneg (by
          unfold loadingFlatRate
          linarith [(uniform_mixing_and_influence N).1]) _)

/-- Canonical choice of the source constant `K_f`, backed by the complete
kernel specification above. Book `#/key_lemmas/3/proof/18/math`:
“`K_f\ge1`”. -/
def loadingFlatConstant (N : NetworkSetup n) : ℝ :=
  Classical.choose (exists_flatKernelConstant N)

/-- The canonical choice satisfies both equation-(33) kernel bounds. Book
`#/key_lemmas/3/proof/19/math`:
“`\|X_t^{(0)}-d1\|_\infty\le K_f\alpha|e|\rho_{flat}^{t-j-1},\qquad
\|V_t^{tr,(0)}\|_1\le K_f|e|\rho_{flat}^{t-j-1}`”. -/
theorem loadingFlatConstant_spec (N : NetworkSetup n) :
    IsFlatKernelConstant N (loadingFlatConstant N) :=
  Classical.choose_spec (exists_flatKernelConstant N)

/-- `ρ₀`. Book `#/key_lemmas/3/proof/21/description`:
“Choose rho_0 with max{rho_flat,r_f,r_2}<rho_0<1 and
K_load>=max{1,K_f,M}, then define the logarithmic two-stage loading delay.” -/
def loadingRate (N : NetworkSetup n) : ℝ :=
  (1 + max (loadingFlatRate N)
    (max (loadingFastRate N) (loadingTransverseRate N))) / 2

/-- `K_load`. Book `#/key_lemmas/3/proof/21/description`:
“Choose rho_0 with max{rho_flat,r_f,r_2}<rho_0<1 and
K_load>=max{1,K_f,M}, then define the logarithmic two-stage loading delay.” -/
def loadingConstant (N : NetworkSetup n) : ℝ :=
  max 1 (max (loadingFlatConstant N) (loadingTriangularConstant N))

/-- All domination and positivity facts demanded by the equation-(35)
construction are derived from `NetworkSetup`; none is a public assumption.
Book `#/key_lemmas/3/proof/21/description`:
“Choose rho_0 with max{rho_flat,r_f,r_2}<rho_0<1 and
K_load>=max{1,K_f,M}, then define the logarithmic two-stage loading delay.” -/
theorem loading_constants_spec (N : NetworkSetup n) :
    0 < loadingRate N ∧ loadingRate N < 1 ∧
    loadingFlatRate N < loadingRate N ∧
    loadingFastRate N < loadingRate N ∧
    loadingTransverseRate N < loadingRate N ∧
    1 ≤ loadingConstant N ∧
    loadingFlatConstant N ≤ loadingConstant N ∧
    loadingTriangularConstant N ≤ loadingConstant N ∧
    0 < Real.log (1 / loadingRate N) := by
  have hρ_nonneg := mixingRate_nonneg N
  have hρ_lt := mixingRate_lt_one N
  have hflat_pos : 0 < loadingFlatRate N := by
    unfold loadingFlatRate
    linarith
  have hflat_lt : loadingFlatRate N < 1 := by
    unfold loadingFlatRate
    linarith
  have htri_pos : 0 < loadingTriangularRate N := by
    unfold loadingTriangularRate
    linarith
  have htri_lt : loadingTriangularRate N < 1 := by
    unfold loadingTriangularRate
    linarith
  have hfast_pos : 0 < loadingFastRate N := by
    unfold loadingFastRate
    linarith
  have hfast_lt : loadingFastRate N < 1 := by
    unfold loadingFastRate
    linarith
  have htrans_pos : 0 < loadingTransverseRate N := by
    unfold loadingTransverseRate
    linarith
  have htrans_lt : loadingTransverseRate N < 1 := by
    unfold loadingTransverseRate
    linarith
  let m : ℝ := max (loadingFlatRate N)
    (max (loadingFastRate N) (loadingTransverseRate N))
  have hm_lt : m < 1 := by
    dsimp [m]
    rw [max_lt_iff, max_lt_iff]
    exact ⟨hflat_lt, hfast_lt, htrans_lt⟩
  have hflat_le : loadingFlatRate N ≤ m := by
    dsimp [m]
    exact le_max_left _ _
  have hfast_le : loadingFastRate N ≤ m := by
    dsimp [m]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have htrans_le : loadingTransverseRate N ≤ m := by
    dsimp [m]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hload_eq : loadingRate N = (1 + m) / 2 := by
    rfl
  have hload_pos : 0 < loadingRate N := by
    rw [hload_eq]
    linarith
  have hload_lt : loadingRate N < 1 := by
    rw [hload_eq]
    linarith
  have hflat_dom : loadingFlatRate N < loadingRate N := by
    rw [hload_eq]
    linarith
  have hfast_dom : loadingFastRate N < loadingRate N := by
    rw [hload_eq]
    linarith
  have htrans_dom : loadingTransverseRate N < loadingRate N := by
    rw [hload_eq]
    linarith
  have hK_flat : loadingFlatConstant N ≤ loadingConstant N := by
    unfold loadingConstant
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hK_one : 1 ≤ loadingConstant N := by
    exact le_trans (loadingFlatConstant_spec N).1 hK_flat
  have hK_tri : loadingTriangularConstant N ≤ loadingConstant N := by
    unfold loadingConstant
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hinv : 1 < 1 / loadingRate N := by
    rw [one_lt_div hload_pos]
    exact hload_lt
  exact ⟨hload_pos, hload_lt, hflat_dom, hfast_dom, htrans_dom,
    hK_one, hK_flat, hK_tri, Real.log_pos hinv⟩

/-- The source half-delay `m(s)`. Book `#/key_lemmas/3/proof/21/math`:
“`m(s)=\max\{1,\lceil\log(K_{load}/s^3)/\log(1/\rho_0)\rceil\}`”. -/
def loadingHalfDelay (N : NetworkSetup n) (s : ℝ) : ℕ :=
  max 1 (Nat.ceil (Real.log (loadingConstant N / s ^ 3) /
    Real.log (1 / loadingRate N)))

/-- Equation (35): `τ(s)=2 max{1,ceil(log(K_load/s^3)/log(1/ρ₀))}+1`.
Book `#/key_lemmas/3/proof/21/math`: “`\tau(s)=2m(s)+1`”. -/
def loadingDelay (N : NetworkSetup n) (s : ℝ) : ℕ :=
  2 * loadingHalfDelay N s + 1

/-- The logarithmic half-delay pays for the three inverse powers of the
loading scale which occur in the calibrated pulse.  This is the scalar
geometric-tail part of the source construction following equation (35). -/
theorem loading_half_delay_geometric_budget
    (N : NetworkSetup n) :
    ∃ sLoad : ℝ, 0 < sLoad ∧ sLoad ≤ 1 / (64 * (n : ℝ)) ∧
      ∀ s : ℝ, 0 < s → s ≤ sLoad →
        loadingConstant N * loadingRate N ^ loadingHalfDelay N s ≤ s ^ 3 := by
  let sLoad : ℝ := 1 / (64 * (n : ℝ))
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr N.hn
  have hdenpos : 0 < 64 * (n : ℝ) := mul_pos (by norm_num) hnpos
  have hsLoad_pos : 0 < sLoad := by
    dsimp [sLoad]
    exact div_pos (by norm_num) hdenpos
  refine ⟨sLoad, hsLoad_pos, le_rfl, ?_⟩
  intro s hs hsLoad
  obtain ⟨hρpos, hρlt, _hflat, _hfast, _htrans, hKone,
      _hKflat, _hKtri, hlogInv⟩ := loading_constants_spec N
  have hKpos : 0 < loadingConstant N := lt_of_lt_of_le zero_lt_one hKone
  have hsLoad_one : sLoad ≤ 1 := by
    apply (div_le_iff₀ hdenpos).2
    dsimp [sLoad]
    have hn_one : (1 : ℝ) ≤ n := by exact_mod_cast N.hn
    nlinarith
  have hs_one : s ≤ 1 := hsLoad.trans hsLoad_one
  have hs3pos : 0 < s ^ 3 := pow_pos hs _
  have hs3one : s ^ 3 ≤ 1 := by
    nlinarith [sq_nonneg s, mul_self_le_mul_self (le_of_lt hs) hs_one]
  let B : ℝ := loadingConstant N / s ^ 3
  have hBpos : 0 < B := by
    dsimp [B]
    exact div_pos hKpos hs3pos
  have hBone : 1 ≤ B := by
    apply (le_div_iff₀ hs3pos).2
    dsimp [B]
    nlinarith
  have hratio_nonneg :
      0 ≤ Real.log B / Real.log (1 / loadingRate N) :=
    div_nonneg (Real.log_nonneg hBone) hlogInv.le
  have hratio_ceil :
      Real.log B / Real.log (1 / loadingRate N) ≤
        (Nat.ceil (Real.log B / Real.log (1 / loadingRate N)) : ℝ) :=
    Nat.le_ceil _
  have hceil_half :
      Nat.ceil (Real.log B / Real.log (1 / loadingRate N)) ≤
        loadingHalfDelay N s := by
    unfold loadingHalfDelay
    dsimp [B]
    exact le_max_right _ _
  have hratio_half :
      Real.log B / Real.log (1 / loadingRate N) ≤
        (loadingHalfDelay N s : ℝ) :=
    hratio_ceil.trans (by exact_mod_cast hceil_half)
  have hlog_inv :
      Real.log (1 / loadingRate N) = -Real.log (loadingRate N) := by
    rw [one_div, Real.log_inv]
  have hschedule :
      -Real.log B / Real.log (loadingRate N) ≤
        (loadingHalfDelay N s : ℝ) := by
    rw [hlog_inv] at hratio_half
    convert hratio_half using 1 <;> ring
  have hpow :
      loadingRate N ^ loadingHalfDelay N s ≤ B⁻¹ :=
    pow_nat_le_inv_of_neg_log_div_log_le hρpos hρlt hBpos hschedule
  calc
    loadingConstant N * loadingRate N ^ loadingHalfDelay N s ≤
        loadingConstant N * B⁻¹ :=
      mul_le_mul_of_nonneg_left hpow hKpos.le
    _ = s ^ 3 := by
      dsimp [B]
      field_simp

/-- Once one half-delay has elapsed, the calibrated flat pulse is within the
source `O(D s^2)` envelope of its exact consensus displacement `aD`. -/
theorem calibrated_flat_primal_response_pointwise
    (N : NetworkSetup n) (L D s a : ℝ) (j : ℕ) (i : Fin n) (t : ℕ)
    (hL : 0 < L) (hD : 0 < D) (hs : 0 < s)
    (hrow : s ≤ |influenceRow N j i|)
    (ha_lo : 3 / 4 ≤ a) (ha_hi : a ≤ 5 / 4)
    (hjt : j + loadingHalfDelay N s + 1 ≤ t)
    (hgeom : loadingConstant N *
      loadingRate N ^ loadingHalfDelay N s ≤ s ^ 3) :
    ∀ q : Fin n,
      |(s / L) *
          (flatPrimalKernel N t j *ᵥ (fun r => if r = i then 1 else 0)) q *
          (-a * D / ((s / L) * influenceRow N j i)) - a * D| ≤
        5 * D * s ^ 2 / 4 := by
  intro q
  obtain ⟨hload_pos, hload_lt, hflat_lt, _hfast_lt, _htrans_lt,
      hKone, hKflat, _hKtri, _hlogInv⟩ := loading_constants_spec N
  let b : ℝ := influenceRow N j i
  let alpha : ℝ := s / L
  let e : ℝ := -a * D / (alpha * b)
  have hαpos : 0 < alpha := div_pos hs hL
  have hbabspos : 0 < |b| := hs.trans_le (by simpa [b] using hrow)
  have hbne : b ≠ 0 := abs_pos.mp hbabspos
  have hαne : alpha ≠ 0 := ne_of_gt hαpos
  have hcal : alpha * e * b = -a * D := by
    dsimp [e]
    field_simp [hαne, hbne]
  have ha_pos : 0 < a := by norm_num at ha_lo ⊢; linarith
  have hscale_eq : |alpha * e| = a * D / |b| := by
    have halpha_e : alpha * e = -a * D / b := by
      apply (mul_right_cancel₀ hbne)
      rw [div_mul_cancel₀ _ hbne]
      exact hcal
    rw [halpha_e, abs_div, abs_mul, abs_neg, abs_of_pos ha_pos,
      abs_of_pos hD]
  have hscale : |alpha * e| ≤ 5 * D / (4 * s) := by
    rw [hscale_eq]
    calc
      a * D / |b| ≤ (5 / 4 * D) / |b| := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right ha_hi hD.le) (abs_nonneg b)
      _ ≤ (5 / 4 * D) / s := by
        exact div_le_div_of_nonneg_left (by positivity) hs
          (by simpa [b] using hrow)
      _ = 5 * D / (4 * s) := by ring
  have hjt' : j + 1 ≤ t := by omega
  have hlag : loadingHalfDelay N s ≤ t - j - 1 := by omega
  have hflat_nonneg : 0 ≤ loadingFlatRate N := by
    unfold loadingFlatRate
    linarith [mixingRate_nonneg N]
  have hload_nonneg : 0 ≤ loadingRate N := hload_pos.le
  have hload_le_one : loadingRate N ≤ 1 := hload_lt.le
  have hpowers :
      loadingFlatRate N ^ (t - j - 1) ≤
        loadingRate N ^ loadingHalfDelay N s := by
    calc
      loadingFlatRate N ^ (t - j - 1) ≤
          loadingRate N ^ (t - j - 1) :=
        pow_le_pow_left₀ hflat_nonneg hflat_lt.le _
      _ ≤ loadingRate N ^ loadingHalfDelay N s :=
        pow_le_pow_of_le_one hload_nonneg hload_le_one hlag
  have hkernel := (loadingFlatConstant_spec N).2 j i t hjt'
  have hcoord :
      |(flatPrimalKernel N t j *ᵥ (fun r => if r = i then 1 else 0)) q + b| ≤
        loadingFlatConstant N * loadingFlatRate N ^ (t - j - 1) := by
    exact (abs_le_nodeSupNorm _ q).trans (by simpa [b] using hkernel.1)
  have htail :
      loadingFlatConstant N * loadingFlatRate N ^ (t - j - 1) ≤ s ^ 3 := by
    calc
      loadingFlatConstant N * loadingFlatRate N ^ (t - j - 1) ≤
          loadingConstant N * loadingRate N ^ loadingHalfDelay N s := by
        exact mul_le_mul hKflat hpowers
          (pow_nonneg hflat_nonneg _) (by linarith [hKone])
      _ ≤ s ^ 3 := hgeom
  have hpoint_tail :
      |(flatPrimalKernel N t j *ᵥ (fun r => if r = i then 1 else 0)) q + b| ≤
        s ^ 3 := hcoord.trans htail
  change |alpha * _ * e - a * D| ≤ _
  have hrearrange :
      alpha *
          (flatPrimalKernel N t j *ᵥ (fun r => if r = i then 1 else 0)) q * e -
          a * D =
        (alpha * e) *
          ((flatPrimalKernel N t j *ᵥ (fun r => if r = i then 1 else 0)) q + b) := by
    calc
      alpha *
            (flatPrimalKernel N t j *ᵥ (fun r => if r = i then 1 else 0)) q * e -
            a * D =
          alpha * e *
            (flatPrimalKernel N t j *ᵥ (fun r => if r = i then 1 else 0)) q +
            (-a * D) := by ring
      _ = alpha * e *
            (flatPrimalKernel N t j *ᵥ (fun r => if r = i then 1 else 0)) q +
            alpha * e * b := by rw [hcal]
      _ = _ := by ring
  rw [hrearrange, abs_mul]
  calc
    |alpha * e| *
        |(flatPrimalKernel N t j *ᵥ (fun r => if r = i then 1 else 0)) q + b| ≤
        (5 * D / (4 * s)) * s ^ 3 :=
      mul_le_mul hscale hpoint_tail (abs_nonneg _)
        (by positivity)
    _ = 5 * D * s ^ 2 / 4 := by field_simp

/-- The same half-delay suppresses the retained flat tracker to `O(Ds)`;
this is the second estimate in (33) after pulse calibration. -/
theorem calibrated_flat_tracker_response_l1
    (N : NetworkSetup n) (L D s a : ℝ) (j : ℕ) (i : Fin n) (t : ℕ)
    (hL : 0 < L) (hD : 0 < D) (hs : 0 < s)
    (hrow : s ≤ |influenceRow N j i|)
    (ha_lo : 3 / 4 ≤ a) (ha_hi : a ≤ 5 / 4)
    (hjt : j + loadingHalfDelay N s + 1 ≤ t)
    (hgeom : loadingConstant N *
      loadingRate N ^ loadingHalfDelay N s ≤ s ^ 3) :
    nodeL1Norm
        (fun q =>
          (flatTrackerKernel N t j *ᵥ (fun r => if r = i then 1 else 0)) q *
            ((-a * D / ((s / L) * influenceRow N j i)) / L)) ≤
      5 * D * s / 4 := by
  obtain ⟨hload_pos, hload_lt, hflat_lt, _hfast_lt, _htrans_lt,
      hKone, hKflat, _hKtri, _hlogInv⟩ := loading_constants_spec N
  let b : ℝ := influenceRow N j i
  let e : ℝ := -a * D / ((s / L) * b)
  have hbabspos : 0 < |b| := hs.trans_le (by simpa [b] using hrow)
  have hbne : b ≠ 0 := abs_pos.mp hbabspos
  have hLne : L ≠ 0 := ne_of_gt hL
  have ha_pos : 0 < a := by norm_num at ha_lo ⊢; linarith
  have he_div : e / L = -a * D / (s * b) := by
    dsimp [e]
    field_simp [hLne, hbne]
  have hscale_eq : |e / L| = a * D / (s * |b|) := by
    rw [he_div, abs_div, abs_mul, abs_neg, abs_of_pos ha_pos,
      abs_of_pos hD, abs_mul, abs_of_pos hs]
  have hden_le : s * s ≤ s * |b| :=
    mul_le_mul_of_nonneg_left (by simpa [b] using hrow) hs.le
  have hscale : |e / L| ≤ 5 * D / (4 * s ^ 2) := by
    rw [hscale_eq]
    calc
      a * D / (s * |b|) ≤ (5 / 4 * D) / (s * |b|) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right ha_hi hD.le) (by positivity)
      _ ≤ (5 / 4 * D) / (s * s) := by
        exact div_le_div_of_nonneg_left (by positivity) (mul_pos hs hs) hden_le
      _ = 5 * D / (4 * s ^ 2) := by ring
  have hjt' : j + 1 ≤ t := by omega
  have hlag : loadingHalfDelay N s ≤ t - j - 1 := by omega
  have hflat_nonneg : 0 ≤ loadingFlatRate N := by
    unfold loadingFlatRate
    linarith [mixingRate_nonneg N]
  have hpowers :
      loadingFlatRate N ^ (t - j - 1) ≤
        loadingRate N ^ loadingHalfDelay N s := by
    calc
      loadingFlatRate N ^ (t - j - 1) ≤
          loadingRate N ^ (t - j - 1) :=
        pow_le_pow_left₀ hflat_nonneg hflat_lt.le _
      _ ≤ loadingRate N ^ loadingHalfDelay N s :=
        pow_le_pow_of_le_one hload_pos.le hload_lt.le hlag
  have hkernel := (loadingFlatConstant_spec N).2 j i t hjt'
  have htail :
      loadingFlatConstant N * loadingFlatRate N ^ (t - j - 1) ≤ s ^ 3 := by
    calc
      loadingFlatConstant N * loadingFlatRate N ^ (t - j - 1) ≤
          loadingConstant N * loadingRate N ^ loadingHalfDelay N s := by
        exact mul_le_mul hKflat hpowers (pow_nonneg hflat_nonneg _)
          (by linarith [hKone])
      _ ≤ s ^ 3 := hgeom
  have hnorm_scale :
      nodeL1Norm
          (fun q =>
            (flatTrackerKernel N t j *ᵥ (fun r => if r = i then 1 else 0)) q *
              (e / L)) =
        |e / L| * nodeL1Norm
          (flatTrackerKernel N t j *ᵥ (fun r => if r = i then 1 else 0)) := by
    unfold nodeL1Norm
    simp_rw [abs_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  change nodeL1Norm (fun q => _ * (e / L)) ≤ _
  rw [hnorm_scale]
  have htracker_nonneg :
      0 ≤ nodeL1Norm (flatTrackerKernel N t j *ᵥ
        (fun r => if r = i then 1 else 0)) := by
    unfold nodeL1Norm
    exact Finset.sum_nonneg fun q _ => abs_nonneg _
  calc
    |e / L| *
        nodeL1Norm (flatTrackerKernel N t j *ᵥ
          (fun r => if r = i then 1 else 0)) ≤
        (5 * D / (4 * s ^ 2)) * s ^ 3 :=
      mul_le_mul hscale (hkernel.2.trans htail) htracker_nonneg
        (by positivity)
    _ = 5 * D * s / 4 := by field_simp

/-- Equation (34) combined with the calibrated flat estimates at the first
half-delay.  These are the true-trajectory bounds used to start the source's
second slow--fast loading segment. -/
theorem calibrated_true_first_segment_bounds
    (N : NetworkSetup n) (L D s a : ℝ) (j : ℕ) (i : Fin n)
    (hL : 0 < L) (hD : 0 < D) (hs : 0 < s)
    (hrow : s ≤ |influenceRow N j i|)
    (ha_lo : 3 / 4 ≤ a) (ha_hi : a ≤ 5 / 4)
    (hgeom : loadingConstant N *
      loadingRate N ^ loadingHalfDelay N s ≤ s ^ 3) :
    let e := -a * D / ((s / L) * influenceRow N j i)
    let m := loadingHalfDelay N s
    let t := j + m + 1
    nodeSupNorm (fun q =>
        (loadingTrajectory N L D s j i e t).primal q - a * D) ≤
      ((5 / 4) * s ^ 2 +
        (2 * ((((blockContraction N)⁻¹ * (n : ℝ)) /
          (1 - mixingRate N)) + 1 / 2)) * s * (m + 1)) * D ∧
    nodeL1Norm (fun q =>
        retainedLoadingTracker N L D s j i e t q / L) ≤
      ((((blockContraction N)⁻¹ * (n : ℝ)) /
        (1 - mixingRate N)) + 5 * s / 4) * D := by
  dsimp only
  let e : ℝ := -a * D / ((s / L) * influenceRow N j i)
  let m : ℕ := loadingHalfDelay N s
  let t : ℕ := j + m + 1
  change nodeSupNorm (fun q =>
      (loadingTrajectory N L D s j i e t).primal q - a * D) ≤ _ ∧
    nodeL1Norm (fun q =>
      retainedLoadingTracker N L D s j i e t q / L) ≤ _
  have hjt : j + 1 ≤ t := by dsimp [t]; omega
  have ht : t ≤ j + 2 * m + 1 := by dsimp [t]; omega
  have hpair := bounded_nonlinear_loading_response
    N L D s j i e m t hL hD hs hjt ht
  have hflatP := calibrated_flat_primal_response_pointwise
    N L D s a j i t hL hD hs hrow ha_lo ha_hi
      (by simpa [m, t] using hjt) hgeom
  have hflatT := calibrated_flat_tracker_response_l1
    N L D s a j i t hL hD hs hrow ha_lo ha_hi
      (by simpa [m, t] using hjt) hgeom
  have he : e = -a * D / ((s / L) * influenceRow N j i) := rfl
  constructor
  · have hpoint (q : Fin n) :
        |(loadingTrajectory N L D s j i e t).primal q - a * D| ≤
          (2 * ((((blockContraction N)⁻¹ * (n : ℝ)) /
            (1 - mixingRate N)) + 1 / 2)) * s * (m + 1) * D +
            5 * D * s ^ 2 / 4 := by
      let E : Fin n → ℝ := fun r =>
        (loadingTrajectory N L D s j i e t).primal r -
          (s / L) * (flatPrimalKernel N t j *ᵥ
            (fun u => if u = i then 1 else 0)) r * e
      have herr : |E q| ≤
          2 * ((((blockContraction N)⁻¹ * (n : ℝ)) /
            (1 - mixingRate N)) + 1 / 2) * s * (m + 1) * D :=
        (abs_le_nodeSupNorm E q).trans hpair.2
      have hflat :
          |(s / L) * (flatPrimalKernel N t j *ᵥ
              (fun u => if u = i then 1 else 0)) q * e - a * D| ≤
            5 * D * s ^ 2 / 4 := by
        rw [he]
        exact hflatP q
      have hid :
          (loadingTrajectory N L D s j i e t).primal q - a * D =
            E q + ((s / L) * (flatPrimalKernel N t j *ᵥ
              (fun u => if u = i then 1 else 0)) q * e - a * D) := by
        dsimp [E]
        ring
      rw [hid]
      exact (abs_add_le _ _).trans (add_le_add herr hflat)
    have hsup : nodeSupNorm (fun q =>
        (loadingTrajectory N L D s j i e t).primal q - a * D) ≤
          2 * ((((blockContraction N)⁻¹ * (n : ℝ)) /
            (1 - mixingRate N)) + 1 / 2) * s * (m + 1) * D +
            5 * D * s ^ 2 / 4 := by
      letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp N.hn
      unfold nodeSupNorm
      exact ciSup_le hpoint
    calc
      nodeSupNorm (fun q =>
          (loadingTrajectory N L D s j i e t).primal q - a * D) ≤
          2 * ((((blockContraction N)⁻¹ * (n : ℝ)) /
            (1 - mixingRate N)) + 1 / 2) * s * (m + 1) * D +
            5 * D * s ^ 2 / 4 := hsup
      _ = ((5 / 4) * s ^ 2 +
          (2 * ((((blockContraction N)⁻¹ * (n : ℝ)) /
            (1 - mixingRate N)) + 1 / 2)) * s * (m + 1)) * D := by ring
  · have htriangle :
        nodeL1Norm (fun q =>
            retainedLoadingTracker N L D s j i e t q / L) ≤
          nodeL1Norm (fun q =>
            (retainedLoadingTracker N L D s j i e t q -
              (flatTrackerKernel N t j *ᵥ
                (fun r => if r = i then 1 else 0)) q * e) / L) +
          nodeL1Norm (fun q =>
            (flatTrackerKernel N t j *ᵥ
              (fun r => if r = i then 1 else 0)) q * (e / L)) := by
      unfold nodeL1Norm
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro q _
      have hid :
          retainedLoadingTracker N L D s j i e t q / L =
            (retainedLoadingTracker N L D s j i e t q -
              (flatTrackerKernel N t j *ᵥ
                (fun r => if r = i then 1 else 0)) q * e) / L +
            (flatTrackerKernel N t j *ᵥ
              (fun r => if r = i then 1 else 0)) q * (e / L) := by ring
      change |retainedLoadingTracker N L D s j i e t q / L| ≤
        |(retainedLoadingTracker N L D s j i e t q -
            (flatTrackerKernel N t j *ᵥ
              (fun r => if r = i then 1 else 0)) q * e) / L| +
          |(flatTrackerKernel N t j *ᵥ
            (fun r => if r = i then 1 else 0)) q * (e / L)|
      rw [hid]
      exact abs_add_le _ _
    calc
      nodeL1Norm (fun q =>
          retainedLoadingTracker N L D s j i e t q / L) ≤
          nodeL1Norm (fun q =>
            (retainedLoadingTracker N L D s j i e t q -
              (flatTrackerKernel N t j *ᵥ
                (fun r => if r = i then 1 else 0)) q * e) / L) +
          nodeL1Norm (fun q =>
            (flatTrackerKernel N t j *ᵥ
              (fun r => if r = i then 1 else 0)) q * (e / L)) := htriangle
      _ ≤ (((blockContraction N)⁻¹ * (n : ℝ)) /
            (1 - mixingRate N)) * D + 5 * D * s / 4 := by
        apply add_le_add hpair.1
        rw [he]
        exact hflatT
      _ = ((((blockContraction N)⁻¹ * (n : ℝ)) /
          (1 - mixingRate N)) + 5 * s / 4) * D := by ring

/-- The complete position residual in (34) tends to zero despite the
logarithmic half-delay.  This is the scalar small-step part of equation (37):
the `s * (m(s)+1)` term is controlled using the ceiling formula defining
`loadingHalfDelay`, rather than by postulating a delay cap. -/
theorem loading_half_delay_residual_cap
    (N : NetworkSetup n) :
    let KX : ℝ :=
      2 * ((((blockContraction N)⁻¹ * (n : ℝ)) /
        (1 - mixingRate N)) + 1 / 2)
    ∃ sResidual : ℝ, 0 < sResidual ∧
      ∀ s : ℝ, 0 < s → s ≤ sResidual →
        (5 / 4) * s ^ 2 +
            KX * s * ((loadingHalfDelay N s : ℝ) + 1) ≤ 1 / 32 := by
  dsimp only
  let K : ℝ := loadingConstant N
  let c : ℝ := Real.log (1 / loadingRate N)
  let R : ℝ → ℝ := fun s => Real.log (K / s ^ 3) / c
  let KX : ℝ :=
    2 * ((((blockContraction N)⁻¹ * (n : ℝ)) /
      (1 - mixingRate N)) + 1 / 2)
  obtain ⟨hρpos, hρlt, _hflat, _hfast, _htrans, hKone,
      _hKflat, _hKtri, hlogInv⟩ := loading_constants_spec N
  have hKpos : 0 < K := by
    dsimp [K]
    exact lt_of_lt_of_le zero_lt_one hKone
  have hcpos : 0 < c := by simpa [c] using hlogInv
  have hs_id : Filter.Tendsto (fun s : ℝ => s)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    (Filter.tendsto_id.mono_left nhdsWithin_le_nhds)
  have hs_log :
      Filter.Tendsto (fun s : ℝ => s * Real.log s)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa [Real.rpow_one, mul_comm] using
      (tendsto_log_mul_rpow_nhdsGT_zero (r := (1 : ℝ)) zero_lt_one)
  have hupper_tendsto :
      Filter.Tendsto (fun s : ℝ => s * (R s + 3))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hformula :
        Filter.Tendsto (fun s : ℝ =>
          (Real.log K / c) * s - (3 / c) * (s * Real.log s) + 3 * s)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have h1 : Filter.Tendsto (fun s : ℝ => (Real.log K / c) * s)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        simpa using hs_id.const_mul (Real.log K / c)
      have h2 : Filter.Tendsto (fun s : ℝ => (3 / c) * (s * Real.log s))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        simpa using hs_log.const_mul (3 / c)
      have h3 : Filter.Tendsto (fun s : ℝ => 3 * s)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        simpa using hs_id.const_mul 3
      simpa only [sub_zero, zero_add] using (h1.sub h2).add h3
    apply hformula.congr'
    filter_upwards [eventually_mem_nhdsWithin] with s hs
    have hspos : 0 < s := hs
    have hsne : s ≠ 0 := ne_of_gt hspos
    have hlog : Real.log (K / s ^ 3) = Real.log K - 3 * Real.log s := by
      rw [Real.log_div (ne_of_gt hKpos) (pow_ne_zero _ hsne), Real.log_pow]
      norm_num
    dsimp [R]
    rw [hlog]
    field_simp [ne_of_gt hcpos]
    <;> ring
  have hdelay_tendsto :
      Filter.Tendsto
        (fun s : ℝ => s * ((loadingHalfDelay N s : ℝ) + 1))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (g := fun _ : ℝ => 0) (h := fun s : ℝ => s * (R s + 3))
      tendsto_const_nhds hupper_tendsto
    · filter_upwards [eventually_mem_nhdsWithin] with s hs
      exact mul_nonneg hs.le (by positivity)
    · filter_upwards [Icc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num),
        eventually_mem_nhdsWithin] with s hsRange hsMem
      have hspos : 0 < s := hsMem
      have hsone : s ≤ 1 := hsRange.2
      have hs3pos : 0 < s ^ 3 := pow_pos hspos _
      have hs3one : s ^ 3 ≤ 1 := by
        exact pow_le_one₀ hspos.le hsone
      have hKone' : 1 ≤ K := by simpa [K] using hKone
      have hBone : 1 ≤ K / s ^ 3 := by
        apply (le_div_iff₀ hs3pos).2
        simpa using hs3one.trans hKone'
      have hRnonneg : 0 ≤ R s := by
        dsimp [R]
        exact div_nonneg (Real.log_nonneg hBone) hcpos.le
      have hceil :
          ((Nat.ceil (R s) : ℕ) : ℝ) < R s + 1 :=
        Nat.ceil_lt_add_one hRnonneg
      have hm : (loadingHalfDelay N s : ℝ) ≤ R s + 2 := by
        unfold loadingHalfDelay
        change ((max 1 (Nat.ceil (R s)) : ℕ) : ℝ) ≤ R s + 2
        have hchoice :
            ((max 1 (Nat.ceil (R s)) : ℕ) : ℝ) ≤
              (Nat.ceil (R s) : ℝ) + 1 := by
          exact_mod_cast
            (max_le (Nat.succ_le_succ (Nat.zero_le (Nat.ceil (R s))))
              (Nat.le_succ (Nat.ceil (R s))))
        linarith
      exact mul_le_mul_of_nonneg_left (by linarith) hspos.le
  have hresidual_tendsto :
      Filter.Tendsto (fun s : ℝ =>
        (5 / 4) * s ^ 2 +
          KX * s * ((loadingHalfDelay N s : ℝ) + 1))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hquad : Filter.Tendsto (fun s : ℝ => (5 / 4) * s ^ 2)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      by simpa using (hs_id.pow 2).const_mul (5 / 4)
    have hdelay : Filter.Tendsto (fun s : ℝ =>
        KX * (s * ((loadingHalfDelay N s : ℝ) + 1)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      by simpa using hdelay_tendsto.const_mul KX
    simpa [mul_assoc] using hquad.add hdelay
  have heventually :
      ∀ᶠ s : ℝ in nhdsWithin 0 (Set.Ioi 0),
        (5 / 4) * s ^ 2 +
            KX * s * ((loadingHalfDelay N s : ℝ) + 1) < 1 / 32 :=
    hresidual_tendsto (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 32))
  have heventually' :
      ∀ᶠ s : ℝ in nhds 0, 0 < s →
        (5 / 4) * s ^ 2 +
            KX * s * ((loadingHalfDelay N s : ℝ) + 1) < 1 / 32 :=
    eventually_nhdsWithin_iff.mp heventually
  obtain ⟨eps, heps, hbound⟩ := Metric.eventually_nhds_iff.mp heventually'
  let sResidual : ℝ := eps / 2
  have hsResidual : 0 < sResidual := by dsimp [sResidual]; positivity
  refine ⟨sResidual, hsResidual, ?_⟩
  intro s hs hsCap
  apply (hbound (by
    simp only [Real.dist_eq, sub_zero, abs_of_pos hs]
    dsimp [sResidual] at hsCap
    linarith) hs).le

/-- A further scalar cap makes the geometrically contracted first-segment fast
seed negligible at the loaded endpoint. -/
theorem loading_fast_seed_contraction_cap
    (N : NetworkSetup n) (A : ℝ) :
    ∃ sFast : ℝ, 0 < sFast ∧
      ∀ s : ℝ, 0 < s → s ≤ sFast →
        A * s ^ 3 *
          (1 / 16 +
            (((blockContraction N)⁻¹ * (n : ℝ)) /
              (1 - mixingRate N) + 5 * s / 4) +
            9 * (n : ℝ) / 16) ≤ 1 / 64 := by
  have hs_id : Filter.Tendsto (fun s : ℝ => s)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    Filter.tendsto_id.mono_left nhdsWithin_le_nhds
  have htendsto : Filter.Tendsto (fun s : ℝ =>
      A * s ^ 3 *
        (1 / 16 +
          (((blockContraction N)⁻¹ * (n : ℝ)) /
            (1 - mixingRate N) + 5 * s / 4) +
          9 * (n : ℝ) / 16))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hfactor : Filter.Tendsto (fun s : ℝ =>
        1 / 16 +
          (((blockContraction N)⁻¹ * (n : ℝ)) /
            (1 - mixingRate N) + 5 * s / 4) +
          9 * (n : ℝ) / 16)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (1 / 16 +
          (((blockContraction N)⁻¹ * (n : ℝ)) /
            (1 - mixingRate N) + 5 * 0 / 4) +
          9 * (n : ℝ) / 16)) := by
      have hlin : Filter.Tendsto (fun s : ℝ => 5 * s / 4)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        convert hs_id.const_mul (5 / 4) using 1 <;> ring
      have h16 : Filter.Tendsto (fun _ : ℝ => (1 / 16 : ℝ))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 16)) := tendsto_const_nhds
      have hA : Filter.Tendsto (fun _ : ℝ =>
          ((blockContraction N)⁻¹ * (n : ℝ)) / (1 - mixingRate N))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (((blockContraction N)⁻¹ * (n : ℝ)) /
            (1 - mixingRate N))) := tendsto_const_nhds
      have hn : Filter.Tendsto (fun _ : ℝ => 9 * (n : ℝ) / 16)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (9 * (n : ℝ) / 16)) :=
        tendsto_const_nhds
      simpa only [mul_zero, zero_div, add_zero] using
        (h16.add (hA.add hlin)).add hn
    have hzero : Filter.Tendsto (fun s : ℝ => s ^ 3 *
        (1 / 16 +
          (((blockContraction N)⁻¹ * (n : ℝ)) /
            (1 - mixingRate N) + 5 * s / 4) +
          9 * (n : ℝ) / 16))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      convert (hs_id.pow 3).mul hfactor using 1 <;> norm_num
    simpa [mul_assoc] using hzero.const_mul A
  have heventually : ∀ᶠ s : ℝ in nhdsWithin 0 (Set.Ioi 0),
      A * s ^ 3 *
        (1 / 16 +
          (((blockContraction N)⁻¹ * (n : ℝ)) /
            (1 - mixingRate N) + 5 * s / 4) +
          9 * (n : ℝ) / 16) < 1 / 64 :=
    htendsto (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 64))
  have heventually' : ∀ᶠ s : ℝ in nhds 0, 0 < s →
      A * s ^ 3 *
        (1 / 16 +
          (((blockContraction N)⁻¹ * (n : ℝ)) /
            (1 - mixingRate N) + 5 * s / 4) +
          9 * (n : ℝ) / 16) < 1 / 64 :=
    eventually_nhdsWithin_iff.mp heventually
  obtain ⟨eps, heps, hbound⟩ := Metric.eventually_nhds_iff.mp heventually'
  let sFast : ℝ := eps / 2
  have hsFast : 0 < sFast := by dsimp [sFast]; positivity
  refine ⟨sFast, hsFast, ?_⟩
  intro s hs hsCap
  apply (hbound (by
    simp only [Real.dist_eq, sub_zero, abs_of_pos hs]
    dsimp [sFast] at hsCap
    linarith) hs).le

/-- The equation-(34) residual cap starts the genuine negative-curvature
recursion: every node is on the printed branch at the first half-delay, and
the Perron slow center is within the same residual of `(a-1)D`. -/
theorem loading_first_segment_branch_center_bounds
    (N : NetworkSetup n) (L D s a : ℝ) (j : ℕ) (i : Fin n)
    (hL : 0 < L) (hD : 0 < D) (hs : 0 < s)
    (hrow : s ≤ |influenceRow N j i|)
    (ha_lo : 3 / 4 ≤ a) (ha_hi : a ≤ 5 / 4)
    (hgeom : loadingConstant N *
      loadingRate N ^ loadingHalfDelay N s ≤ s ^ 3)
    (hδ :
      (5 / 4) * s ^ 2 +
          (2 * ((((blockContraction N)⁻¹ * (n : ℝ)) /
            (1 - mixingRate N)) + 1 / 2)) * s *
            ((loadingHalfDelay N s : ℝ) + 1) ≤ 1 / 32) :
    let e := -a * D / ((s / L) * influenceRow N j i)
    let t := j + loadingHalfDelay N s + 1
    let X : ℕ → Fin n → ℝ := fun r q =>
      (loadingTrajectory N L D s j i e r).primal q - D
    (∀ q,
      D / 2 ≤ (loadingTrajectory N L D s j i e t).primal q ∧
      (loadingTrajectory N L D s j i e t).primal q ≤ 3 * D / 2) ∧
    |loadingSlowCenter N X t - (a - 1) * D| ≤ D / 32 := by
  dsimp only
  let e : ℝ := -a * D / ((s / L) * influenceRow N j i)
  let t : ℕ := j + loadingHalfDelay N s + 1
  let X : ℕ → Fin n → ℝ := fun r q =>
    (loadingTrajectory N L D s j i e r).primal q - D
  change (∀ q,
      D / 2 ≤ (loadingTrajectory N L D s j i e t).primal q ∧
      (loadingTrajectory N L D s j i e t).primal q ≤ 3 * D / 2) ∧
    |loadingSlowCenter N X t - (a - 1) * D| ≤ D / 32
  have hfirst := calibrated_true_first_segment_bounds
    N L D s a j i hL hD hs hrow ha_lo ha_hi hgeom
  have hprimal :
      nodeSupNorm (fun q =>
        (loadingTrajectory N L D s j i e t).primal q - a * D) ≤ D / 32 := by
    have hraw := hfirst.1
    have hscaled := mul_le_mul_of_nonneg_right hδ hD.le
    have hbound : nodeSupNorm (fun q =>
        (loadingTrajectory N L D s j i e t).primal q - a * D) ≤
          (1 / 32) * D := by
      simpa [e, t, mul_assoc] using hraw.trans hscaled
    convert hbound using 1 <;> ring
  have hpoint (q : Fin n) :
      |(loadingTrajectory N L D s j i e t).primal q - a * D| ≤ D / 32 :=
    (abs_le_nodeSupNorm _ q).trans hprimal
  constructor
  · intro q
    have habs := (abs_le.mp (hpoint q))
    constructor <;> nlinarith
  · let p : Fin n → ℝ := absoluteProbability N t
    have hp := absoluteProbability_mem_stdSimplex N t
    have hcenter_eq :
        loadingSlowCenter N X t - (a - 1) * D =
          ∑ q, p q *
            ((loadingTrajectory N L D s j i e t).primal q - a * D) := by
      unfold loadingSlowCenter dotProduct
      dsimp [X, p]
      calc
        (∑ q, absoluteProbability N t q *
              ((loadingTrajectory N L D s j i e t).primal q - D)) -
              (a - 1) * D =
              (∑ q, absoluteProbability N t q *
              (loadingTrajectory N L D s j i e t).primal q) -
              (∑ q, absoluteProbability N t q) * D - (a - 1) * D := by
                simp_rw [mul_sub]
                rw [Finset.sum_sub_distrib, Finset.sum_mul]
        _ = (∑ q, absoluteProbability N t q *
              (loadingTrajectory N L D s j i e t).primal q) -
              D - (a - 1) * D := by rw [hp.2, one_mul]
        _ = ∑ q, absoluteProbability N t q *
              ((loadingTrajectory N L D s j i e t).primal q - a * D) := by
                rw [show (∑ q, absoluteProbability N t q *
                    ((loadingTrajectory N L D s j i e t).primal q - a * D)) =
                  (∑ q, absoluteProbability N t q *
                    (loadingTrajectory N L D s j i e t).primal q) -
                    (∑ q, absoluteProbability N t q) * (a * D) by
                      simp_rw [mul_sub]
                      rw [Finset.sum_sub_distrib, Finset.sum_mul]]
                rw [hp.2, one_mul]
                ring
    rw [hcenter_eq]
    calc
      |∑ q, p q *
          ((loadingTrajectory N L D s j i e t).primal q - a * D)| ≤
          ∑ q, |p q *
            ((loadingTrajectory N L D s j i e t).primal q - a * D)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ q, p q *
            |(loadingTrajectory N L D s j i e t).primal q - a * D| := by
        apply Finset.sum_congr rfl
        intro q _
        rw [abs_mul, abs_of_nonneg (hp.1 q)]
      _ ≤ ∑ q, p q * (D / 32) := by
        exact Finset.sum_le_sum fun q _ =>
          mul_le_mul_of_nonneg_left (hpoint q) (hp.1 q)
      _ = D / 32 := by rw [← Finset.sum_mul, hp.2, one_mul]

/-- The equation-(34) estimate is uniform on the whole second half of the
loading interval.  In particular, branch membership does not have to be
assumed at a putative first exit: it follows directly from the flat response
and the bounded nonlinear response at that time. -/
theorem loading_second_half_branch_center_bounds
    (N : NetworkSetup n) (L D s a : ℝ) (j : ℕ) (i : Fin n) (t : ℕ)
    (hL : 0 < L) (hD : 0 < D) (hs : 0 < s)
    (hrow : s ≤ |influenceRow N j i|)
    (ha_lo : 3 / 4 ≤ a) (ha_hi : a ≤ 5 / 4)
    (ht0 : j + loadingHalfDelay N s + 1 ≤ t)
    (htRef : t ≤ j + loadingDelay N s)
    (hgeom : loadingConstant N *
      loadingRate N ^ loadingHalfDelay N s ≤ s ^ 3)
    (hδ :
      (5 / 4) * s ^ 2 +
          (2 * ((((blockContraction N)⁻¹ * (n : ℝ)) /
            (1 - mixingRate N)) + 1 / 2)) * s *
            ((loadingHalfDelay N s : ℝ) + 1) ≤ 1 / 32) :
    let e := -a * D / ((s / L) * influenceRow N j i)
    let X : ℕ → Fin n → ℝ := fun r q =>
      (loadingTrajectory N L D s j i e r).primal q - D
    (∀ q,
      D / 2 ≤ (loadingTrajectory N L D s j i e t).primal q ∧
      (loadingTrajectory N L D s j i e t).primal q ≤ 3 * D / 2) ∧
    |loadingSlowCenter N X t - (a - 1) * D| ≤ D / 32 := by
  dsimp only
  let e : ℝ := -a * D / ((s / L) * influenceRow N j i)
  let m : ℕ := loadingHalfDelay N s
  let X : ℕ → Fin n → ℝ := fun r q =>
    (loadingTrajectory N L D s j i e r).primal q - D
  have hjt : j + 1 ≤ t := by omega
  have ht : t ≤ j + 2 * m + 1 := by
    simpa [m, loadingDelay] using htRef
  have hpair := bounded_nonlinear_loading_response
    N L D s j i e m t hL hD hs hjt ht
  have hflat := calibrated_flat_primal_response_pointwise
    N L D s a j i t hL hD hs hrow ha_lo ha_hi
      (by simpa [m] using ht0) hgeom
  have hpoint (q : Fin n) :
      |(loadingTrajectory N L D s j i e t).primal q - a * D| ≤ D / 32 := by
    let E : Fin n → ℝ := fun r =>
      (loadingTrajectory N L D s j i e t).primal r -
        (s / L) * (flatPrimalKernel N t j *ᵥ
          (fun u => if u = i then 1 else 0)) r * e
    have herr : |E q| ≤
        2 * ((((blockContraction N)⁻¹ * (n : ℝ)) /
          (1 - mixingRate N)) + 1 / 2) * s * (m + 1) * D :=
      (abs_le_nodeSupNorm E q).trans hpair.2
    have hflatq :
        |(s / L) * (flatPrimalKernel N t j *ᵥ
            (fun u => if u = i then 1 else 0)) q * e - a * D| ≤
          5 * D * s ^ 2 / 4 := by
      dsimp [e]
      exact hflat q
    have hid :
        (loadingTrajectory N L D s j i e t).primal q - a * D =
          E q + ((s / L) * (flatPrimalKernel N t j *ᵥ
            (fun u => if u = i then 1 else 0)) q * e - a * D) := by
      dsimp [E]
      ring
    have hraw := (abs_add_le _ _).trans (add_le_add herr hflatq)
    rw [← hid] at hraw
    have hscaled := mul_le_mul_of_nonneg_right hδ hD.le
    have hcap :
        2 * ((((blockContraction N)⁻¹ * (n : ℝ)) /
              (1 - mixingRate N)) + 1 / 2) * s * (m + 1) * D +
            5 * D * s ^ 2 / 4 ≤ D / 32 := by
      dsimp [m]
      convert hscaled using 1 <;> ring
    exact hraw.trans hcap
  constructor
  · intro q
    have habs := abs_le.mp (hpoint q)
    constructor <;> nlinarith
  · let p : Fin n → ℝ := absoluteProbability N t
    have hp := absoluteProbability_mem_stdSimplex N t
    have hcenter_eq :
        loadingSlowCenter N X t - (a - 1) * D =
          ∑ q, p q *
            ((loadingTrajectory N L D s j i e t).primal q - a * D) := by
      unfold loadingSlowCenter dotProduct
      dsimp [X, p]
      calc
        (∑ q, absoluteProbability N t q *
              ((loadingTrajectory N L D s j i e t).primal q - D)) -
              (a - 1) * D =
            (∑ q, absoluteProbability N t q *
              (loadingTrajectory N L D s j i e t).primal q) -
              (∑ q, absoluteProbability N t q) * D - (a - 1) * D := by
                simp_rw [mul_sub]
                rw [Finset.sum_sub_distrib, Finset.sum_mul]
        _ = (∑ q, absoluteProbability N t q *
              (loadingTrajectory N L D s j i e t).primal q) -
              D - (a - 1) * D := by rw [hp.2, one_mul]
        _ = ∑ q, absoluteProbability N t q *
              ((loadingTrajectory N L D s j i e t).primal q - a * D) := by
                rw [show (∑ q, absoluteProbability N t q *
                    ((loadingTrajectory N L D s j i e t).primal q - a * D)) =
                  (∑ q, absoluteProbability N t q *
                    (loadingTrajectory N L D s j i e t).primal q) -
                    (∑ q, absoluteProbability N t q) * (a * D) by
                      simp_rw [mul_sub]
                      rw [Finset.sum_sub_distrib, Finset.sum_mul]]
                rw [hp.2, one_mul]
                ring
    rw [hcenter_eq]
    calc
      |∑ q, p q *
          ((loadingTrajectory N L D s j i e t).primal q - a * D)| ≤
          ∑ q, |p q *
            ((loadingTrajectory N L D s j i e t).primal q - a * D)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ q, p q *
            |(loadingTrajectory N L D s j i e t).primal q - a * D| := by
        apply Finset.sum_congr rfl
        intro q _
        rw [abs_mul, abs_of_nonneg (hp.1 q)]
      _ ≤ ∑ q, p q * (D / 32) := by
        exact Finset.sum_le_sum fun q _ =>
          mul_le_mul_of_nonneg_left (hpoint q) (hp.1 q)
      _ = D / 32 := by rw [← Finset.sum_mul, hp.2, one_mul]

/-- Quantitative fast-coordinate seed at the first half-delay.  This exposes
the finite `C_{F,0}D` datum which the triangular product contracts during the
second loading segment. -/
theorem loading_first_segment_fast_seed_bound
    (N : NetworkSetup n) (L D s a : ℝ) (j : ℕ) (i : Fin n)
    (hL : 0 < L) (hD : 0 < D) (hs : 0 < s)
    (hrow : s ≤ |influenceRow N j i|)
    (ha_lo : 3 / 4 ≤ a) (ha_hi : a ≤ 5 / 4)
    (hgeom : loadingConstant N *
      loadingRate N ^ loadingHalfDelay N s ≤ s ^ 3)
    (hδ :
      (5 / 4) * s ^ 2 +
          (2 * ((((blockContraction N)⁻¹ * (n : ℝ)) /
            (1 - mixingRate N)) + 1 / 2)) * s *
            ((loadingHalfDelay N s : ℝ) + 1) ≤ 1 / 32) :
    let e := -a * D / ((s / L) * influenceRow N j i)
    let t := j + loadingHalfDelay N s + 1
    let X : ℕ → Fin n → ℝ := fun r q =>
      (loadingTrajectory N L D s j i e r).primal q - D
    let U : ℕ → Fin n → ℝ := fun r q =>
      -retainedLoadingTracker N L D s j i e r q / L
    let F := loadingFastCoordinates N X U
    nodeSupNorm (F t).1 + nodeL1Norm (F t).2 ≤
      (1 / 16 +
        (((blockContraction N)⁻¹ * (n : ℝ)) /
          (1 - mixingRate N) + 5 * s / 4) +
        9 * (n : ℝ) / 16) * D := by
  dsimp only
  let e : ℝ := -a * D / ((s / L) * influenceRow N j i)
  let t : ℕ := j + loadingHalfDelay N s + 1
  let X : ℕ → Fin n → ℝ := fun r q =>
    (loadingTrajectory N L D s j i e r).primal q - D
  let U : ℕ → Fin n → ℝ := fun r q =>
    -retainedLoadingTracker N L D s j i e r q / L
  let F := loadingFastCoordinates N X U
  change nodeSupNorm (F t).1 + nodeL1Norm (F t).2 ≤ _
  have hfirst := calibrated_true_first_segment_bounds
    N L D s a j i hL hD hs hrow ha_lo ha_hi hgeom
  have hseed := loading_first_segment_branch_center_bounds
    N L D s a j i hL hD hs hrow ha_lo ha_hi hgeom hδ
  have hprimal :
      nodeSupNorm (fun q =>
        (loadingTrajectory N L D s j i e t).primal q - a * D) ≤ D / 32 := by
    have hscaled := mul_le_mul_of_nonneg_right hδ hD.le
    have hbound : nodeSupNorm (fun q =>
        (loadingTrajectory N L D s j i e t).primal q - a * D) ≤
          (1 / 32) * D := by
      simpa [e, t, mul_assoc] using hfirst.1.trans hscaled
    convert hbound using 1 <;> ring
  have hcenter :
      |loadingSlowCenter N X t - (a - 1) * D| ≤ D / 32 := by
    simpa [e, t, X] using hseed.2
  have ha_abs : |a - 1| ≤ 1 / 4 := by
    rw [abs_le]
    constructor <;> linarith
  have htarget_abs : |(a - 1) * D| ≤ D / 4 := by
    rw [abs_mul, abs_of_pos hD]
    nlinarith
  have hxi_abs : |loadingSlowCenter N X t| ≤ 9 * D / 32 := by
    calc
      |loadingSlowCenter N X t| =
          |(loadingSlowCenter N X t - (a - 1) * D) + (a - 1) * D| := by ring_nf
      _ ≤ |loadingSlowCenter N X t - (a - 1) * D| + |(a - 1) * D| :=
        abs_add_le _ _
      _ ≤ D / 32 + D / 4 := add_le_add hcenter htarget_abs
      _ = 9 * D / 32 := by ring
  have hEpoint (q : Fin n) : |(F t).1 q| ≤ D / 16 := by
    have hp := (abs_le_nodeSupNorm
      (fun r => (loadingTrajectory N L D s j i e t).primal r - a * D) q).trans
        hprimal
    dsimp [F, loadingFastCoordinates, X]
    have hid :
        (loadingTrajectory N L D s j i e t).primal q - D -
            loadingSlowCenter N X t =
          ((loadingTrajectory N L D s j i e t).primal q - a * D) -
            (loadingSlowCenter N X t - (a - 1) * D) := by ring
    rw [hid]
    exact (abs_sub _ _).trans (by nlinarith)
  have hE : nodeSupNorm (F t).1 ≤ D / 16 := by
    letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp N.hn
    unfold nodeSupNorm
    exact ciSup_le hEpoint
  have hU : nodeL1Norm (U t) ≤
      ((((blockContraction N)⁻¹ * (n : ℝ)) /
        (1 - mixingRate N)) + 5 * s / 4) * D := by
    have hraw : nodeL1Norm (fun q =>
        retainedLoadingTracker N L D s j i e t q / L) ≤
          ((((blockContraction N)⁻¹ * (n : ℝ)) /
            (1 - mixingRate N)) + 5 * s / 4) * D := by
      simpa [e, t] using hfirst.2
    unfold nodeL1Norm at hraw ⊢
    simpa only [U, neg_div, abs_neg] using hraw
  have hw_abs :
      (∑ q, |pushMass N t q - 1|) ≤ 2 * (n : ℝ) := by
    calc
      (∑ q, |pushMass N t q - 1|) ≤
          ∑ q, (pushMass N t q + 1) := by
        apply Finset.sum_le_sum
        intro q _
        calc
          |pushMass N t q - 1| ≤ |pushMass N t q| + |(1 : ℝ)| := abs_sub _ _
          _ = pushMass N t q + 1 := by
            rw [abs_of_nonneg (pushMass_nonneg N t q), abs_one]
      _ = 2 * (n : ℝ) := by
        rw [Finset.sum_add_distrib, pushMass_sum_eq_n]
        simp
        ring
  have hmass_center :
      nodeL1Norm (fun q =>
        (pushMass N t q - 1) * loadingSlowCenter N X t) ≤
          9 * (n : ℝ) * D / 16 := by
    unfold nodeL1Norm
    simp_rw [abs_mul]
    rw [← Finset.sum_mul]
    calc
      (∑ q, |pushMass N t q - 1|) * |loadingSlowCenter N X t| ≤
          (2 * (n : ℝ)) * (9 * D / 32) :=
        mul_le_mul hw_abs hxi_abs (abs_nonneg _) (by positivity)
      _ = 9 * (n : ℝ) * D / 16 := by ring
  have hK : nodeL1Norm (F t).2 ≤
      ((((blockContraction N)⁻¹ * (n : ℝ)) /
          (1 - mixingRate N)) + 5 * s / 4) * D +
        9 * (n : ℝ) * D / 16 := by
    unfold nodeL1Norm
    calc
      (∑ q, |(F t).2 q|) ≤
          ∑ q, (|U t q| +
            |(pushMass N t q - 1) * loadingSlowCenter N X t|) := by
        apply Finset.sum_le_sum
        intro q _
        dsimp [F, loadingFastCoordinates]
        exact abs_sub _ _
      _ = nodeL1Norm (U t) +
          nodeL1Norm (fun q =>
            (pushMass N t q - 1) * loadingSlowCenter N X t) := by
        rw [Finset.sum_add_distrib]
        rfl
      _ ≤ ((((blockContraction N)⁻¹ * (n : ℝ)) /
            (1 - mixingRate N)) + 5 * s / 4) * D +
          9 * (n : ℝ) * D / 16 := add_le_add hU hmass_center
  calc
    nodeSupNorm (F t).1 + nodeL1Norm (F t).2 ≤
        D / 16 +
          (((((blockContraction N)⁻¹ * (n : ℝ)) /
              (1 - mixingRate N)) + 5 * s / 4) * D +
            9 * (n : ℝ) * D / 16) := add_le_add hE hK
    _ = (1 / 16 +
        (((blockContraction N)⁻¹ * (n : ℝ)) /
          (1 - mixingRate N) + 5 * s / 4) +
        9 * (n : ℝ) / 16) * D := by ring

/-- The second loading half stays on the negative branch, and the restricted
forced slow--fast evolution gives the equation-(37) endpoint bounds.  The
branch premise used by the recurrence is established independently at every
consumed time by `loading_second_half_branch_center_bounds`, so the argument
does not assume the putative first-exit time is already safe. -/
theorem loading_second_half_loaded_endpoint_source_bound
    (N : NetworkSetup n) (L D s a M : ℝ) (j : ℕ) (i : Fin n)
    (hL : 0 < L) (hD : 0 < D) (hs : 0 < s)
    (hs_one : s ≤ 1)
    (hrow : s ≤ |influenceRow N j i|)
    (ha_lo : 3 / 4 ≤ a) (ha_hi : a ≤ 5 / 4)
    (hM : 1 ≤ M)
    (hgeom : loadingConstant N *
      loadingRate N ^ loadingHalfDelay N s ≤ s ^ 3)
    (hδ :
      (5 / 4) * s ^ 2 +
          (2 * ((((blockContraction N)⁻¹ * (n : ℝ)) /
            (1 - mixingRate N)) + 1 / 2)) * s *
            ((loadingHalfDelay N s : ℝ) + 1) ≤ 1 / 32)
    (htriangular : ∀ (k t : ℕ), k ≤ t → ∀ (E K : Fin n → ℝ),
      dotProduct (absoluteProbability N k) E = 0 →
      (∑ q, K q) = 0 →
      nodeSupNorm (forwardProduct N.rowMix t k *ᵥ E) +
          nodeL1Norm
            (forwardProduct N.colMix t k *ᵥ K +
              ∑ q ∈ Finset.Ico k t,
                forwardProduct N.colMix t (q + 1) *ᵥ
                  ((N.colMix q - 1) *ᵥ
                    (forwardProduct N.rowMix q k *ᵥ E))) ≤
        M * loadingFastRate N ^ (t - k) *
          (nodeSupNorm E + nodeL1Norm K))
    (hperturbation : loadingFastRate N +
      M * (s * (2 * ((n : ℝ) + 1))) ≤ loadingTransverseRate N)
    :
    let e := -a * D / ((s / L) * influenceRow N j i)
    let X : ℕ → Fin n → ℝ := fun r q =>
      (loadingTrajectory N L D s j i e r).primal q - D
    let U : ℕ → Fin n → ℝ := fun r q =>
      -retainedLoadingTracker N L D s j i e r q / L
    let xi := loadingSlowCenter N X
    let F := loadingFastCoordinates N X U
    let t0 := j + loadingHalfDelay N s + 1
    let kRef := j + loadingDelay N s
    let Cseed := 1 / 16 +
      (((blockContraction N)⁻¹ * (n : ℝ)) /
        (1 - mixingRate N) + 5 / 4) + 9 * (n : ℝ) / 16
    let Cp := M * (2 * (n : ℝ) * ((n : ℝ) + 1)) /
      (1 - loadingTransverseRate N)
    let C3 := (M / loadingConstant N) * Cseed + (9 / 32) * Cp
    (∀ t, t0 ≤ t → t ≤ kRef → ∀ q,
      D / 2 ≤ (loadingTrajectory N L D s j i e t).primal q ∧
      (loadingTrajectory N L D s j i e t).primal q ≤ 3 * D / 2) ∧
    (∀ t, t0 ≤ t → t < kRef →
      |xi (t + 1) - xi t| ≤
        s * (gain N t * |xi t| +
          (nodeSupNorm (F t).1 + nodeL1Norm (F t).2))) ∧
    |xi kRef - (a - 1) * D| ≤ D / 32 ∧
    nodeSupNorm (F kRef).1 + nodeL1Norm (F kRef).2 ≤ C3 * s * D := by
  dsimp only
  let e : ℝ := -a * D / ((s / L) * influenceRow N j i)
  let X : ℕ → Fin n → ℝ := fun r q =>
    (loadingTrajectory N L D s j i e r).primal q - D
  let U : ℕ → Fin n → ℝ := fun r q =>
    -retainedLoadingTracker N L D s j i e r q / L
  let xi := loadingSlowCenter N X
  let F := loadingFastCoordinates N X U
  let t0 : ℕ := j + loadingHalfDelay N s + 1
  let kRef : ℕ := j + loadingDelay N s
  let Cseed : ℝ := 1 / 16 +
    (((blockContraction N)⁻¹ * (n : ℝ)) /
      (1 - mixingRate N) + 5 / 4) + 9 * (n : ℝ) / 16
  let Cp : ℝ := M * (2 * (n : ℝ) * ((n : ℝ) + 1)) /
    (1 - loadingTransverseRate N)
  let C3 : ℝ := (M / loadingConstant N) * Cseed + (9 / 32) * Cp
  have ht0Ref : t0 ≤ kRef := by
    dsimp [t0, kRef, loadingDelay]
    omega
  have hbranch_center (t : ℕ) (ht0 : t0 ≤ t) (htRef : t ≤ kRef) :
      (∀ q,
        D / 2 ≤ (loadingTrajectory N L D s j i e t).primal q ∧
        (loadingTrajectory N L D s j i e t).primal q ≤ 3 * D / 2) ∧
      |xi t - (a - 1) * D| ≤ D / 32 := by
    simpa [e, X, xi, t0, kRef] using
      (loading_second_half_branch_center_bounds
        N L D s a j i t hL hD hs hrow ha_lo ha_hi
          (by simpa [t0] using ht0) (by simpa [kRef] using htRef) hgeom hδ)
  have hbranch : ∀ t, t0 ≤ t → t ≤ kRef → ∀ q,
      D / 2 ≤ (loadingTrajectory N L D s j i e t).primal q ∧
      (loadingTrajectory N L D s j i e t).primal q ≤ 3 * D / 2 :=
    fun t ht0 htRef => (hbranch_center t ht0 htRef).1
  have hcenter_endpoint : |xi kRef - (a - 1) * D| ≤ D / 32 :=
    (hbranch_center kRef ht0Ref le_rfl).2
  have hseed := loading_first_segment_branch_center_bounds
    N L D s a j i hL hD hs hrow ha_lo ha_hi hgeom hδ
  have hseed_branch : ∀ q,
      D / 2 ≤ (loadingTrajectory N L D s j i e t0).primal q ∧
      (loadingTrajectory N L D s j i e t0).primal q ≤ 3 * D / 2 := by
    simpa [e, t0] using hseed.1
  have hseed_recurrence := loading_negative_branch_slow_fast_coordinates
    N L D s a j i t0 (by
      dsimp only
      exact loading_negative_branch_shifted_recurrence
        N L D s j i e t0 hL hD (by dsimp [t0]; omega) hseed_branch)
  have hseed_carrier :
      dotProduct (absoluteProbability N t0) (F t0).1 = 0 ∧
      (∑ q, (F t0).2 q) = 0 := by
    simpa [e, X, U, xi, F, t0] using hseed_recurrence.1
  have hstep (r : ℕ) (htr : t0 ≤ r) (hrRef : r < kRef) :
      F (r + 1) =
        loadingFastStep N r (F r) +
          loadingFastScale s
            (loadingFastPerturbationInput N r (F r).1 (F r).2) +
          loadingFastScale s (loadingFastCenterInput N r (xi r)) := by
    have hrbranch := hbranch r htr (by omega)
    have hsf := loading_negative_branch_slow_fast_coordinates
      N L D s a j i r (by
        dsimp only
        exact loading_negative_branch_shifted_recurrence
          N L D s j i e r hL hD (by dsimp [t0] at htr; omega) hrbranch)
    simpa [e, X, U, xi, F] using hsf.2.2
  have hcenter_step (t : ℕ) (ht0 : t0 ≤ t) (htRef : t < kRef) :
      |xi (t + 1) - xi t| ≤
        s * (gain N t * |xi t| +
          (nodeSupNorm (F t).1 + nodeL1Norm (F t).2)) := by
    have htbranch := hbranch t ht0 (Nat.le_of_lt htRef)
    have hsf := loading_negative_branch_slow_fast_coordinates
      N L D s a j i t (by
        dsimp only
        exact loading_negative_branch_shifted_recurrence
          N L D s j i e t hL hD (by dsimp [t0] at ht0; omega) htbranch)
    have hrec :
        xi (t + 1) =
          (1 + s * gain N t) * xi t +
            s * dotProduct (absoluteProbability N (t + 1))
              ((F t).1 + (F t).2) := by
      simpa [e, X, U, xi, F] using hsf.2.1
    have hgain_nonneg : 0 ≤ gain N t := by
      unfold gain dotProduct
      exact Finset.sum_nonneg fun q _ =>
        mul_nonneg ((absoluteProbability_mem_stdSimplex N (t + 1)).1 q)
          (pushMass_nonneg N t q)
    have hell := loadingCenterFeedback_abs_le_gauge
      N (t + 1) (F t).1 (F t).2
    calc
      |xi (t + 1) - xi t| =
          |s * gain N t * xi t +
            s * dotProduct (absoluteProbability N (t + 1))
              ((F t).1 + (F t).2)| := by rw [hrec]; congr 1 <;> ring
      _ ≤ |s * gain N t * xi t| +
          |s * dotProduct (absoluteProbability N (t + 1))
            ((F t).1 + (F t).2)| := abs_add_le _ _
      _ = s * gain N t * |xi t| +
          s * |dotProduct (absoluteProbability N (t + 1))
            ((F t).1 + (F t).2)| := by
              rw [abs_mul, abs_mul, abs_mul, abs_of_pos hs,
                abs_of_nonneg hgain_nonneg]
      _ ≤ s * gain N t * |xi t| +
          s * (nodeSupNorm (F t).1 + nodeL1Norm (F t).2) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hell hs.le)
      _ = s * (gain N t * |xi t| +
          (nodeSupNorm (F t).1 + nodeL1Norm (F t).2)) := by ring
  have hfast_raw := loading_center_forced_fast_gauge_le
    N M s hM hs.le htriangular hperturbation xi F t0 kRef ht0Ref
      hseed_carrier.1 hseed_carrier.2 hstep
  have hcenter_abs (r : ℕ) (hr : r ∈ Finset.Ico t0 kRef) :
      |xi r| ≤ 9 * D / 32 := by
    have hc := (hbranch_center r (Finset.mem_Ico.mp hr).1
      (Nat.le_of_lt (Finset.mem_Ico.mp hr).2)).2
    have ha_abs : |a - 1| ≤ 1 / 4 := by
      rw [abs_le]
      constructor <;> linarith
    have htarget : |(a - 1) * D| ≤ D / 4 := by
      rw [abs_mul, abs_of_pos hD]
      nlinarith
    calc
      |xi r| = |(xi r - (a - 1) * D) + (a - 1) * D| := by ring_nf
      _ ≤ |xi r - (a - 1) * D| + |(a - 1) * D| := abs_add_le _ _
      _ ≤ D / 32 + D / 4 := add_le_add hc htarget
      _ = 9 * D / 32 := by ring
  let rate : ℝ := loadingTransverseRate N
  let B0 : ℝ := 2 * (n : ℝ) * ((n : ℝ) + 1)
  have hrate_pos : 0 < rate := by
    dsimp [rate]
    unfold loadingTransverseRate loadingFastRate loadingTriangularRate
    linarith [mixingRate_nonneg N]
  have hrate_lt : rate < 1 := by
    dsimp [rate]
    unfold loadingTransverseRate loadingFastRate loadingTriangularRate
    linarith [mixingRate_lt_one N]
  have hsum :
      (∑ r ∈ Finset.Ico t0 kRef,
        M * rate ^ (kRef - r - 1) * (s * (B0 * |xi r|))) ≤
        (M * s * B0 * (9 * D / 32)) / (1 - rate) := by
    calc
      (∑ r ∈ Finset.Ico t0 kRef,
        M * rate ^ (kRef - r - 1) * (s * (B0 * |xi r|))) ≤
          ∑ r ∈ Finset.Ico t0 kRef,
            rate ^ (kRef - r - 1) * (M * s * B0 * (9 * D / 32)) := by
              apply Finset.sum_le_sum
              intro r hr
              have hp : 0 ≤ rate ^ (kRef - r - 1) :=
                pow_nonneg hrate_pos.le _
              calc
                M * rate ^ (kRef - r - 1) * (s * (B0 * |xi r|)) =
                    rate ^ (kRef - r - 1) * (M * s * B0 * |xi r|) := by ring
                _ ≤ rate ^ (kRef - r - 1) *
                    (M * s * B0 * (9 * D / 32)) := by
                      exact mul_le_mul_of_nonneg_left
                        (mul_le_mul_of_nonneg_left (hcenter_abs r hr)
                          (by positivity)) hp
      _ ≤ (M * s * B0 * (9 * D / 32)) / (1 - rate) := by
        rw [Finset.sum_Ico_eq_sum_range]
        have hraw := sum_range_geometric_reverse_mul_le_div_one_sub
          rate (M * s * B0 * (9 * D / 32)) (kRef - t0)
            hrate_pos.le hrate_lt (by positivity)
        convert hraw using 1
        apply Finset.sum_congr rfl
        intro q hq
        have hqRef : q < kRef - t0 := Finset.mem_range.mp hq
        rw [show kRef - (t0 + q) - 1 = kRef - t0 - 1 - q by omega]
  have hforcing :
      (∑ r ∈ Finset.Ico t0 kRef,
        M * rate ^ (kRef - r - 1) * (s * (B0 * |xi r|))) ≤
        (9 / 32 * Cp) * s * D := by
    calc
      (∑ r ∈ Finset.Ico t0 kRef,
        M * rate ^ (kRef - r - 1) * (s * (B0 * |xi r|))) ≤
          (M * s * B0 * (9 * D / 32)) / (1 - rate) := hsum
      _ = (9 / 32 * Cp) * s * D := by
        dsimp [Cp, B0, rate]
        ring
  have hseed_fast := loading_first_segment_fast_seed_bound
    N L D s a j i hL hD hs hrow ha_lo ha_hi hgeom hδ
  have hseed_bound :
      nodeSupNorm (F t0).1 + nodeL1Norm (F t0).2 ≤ Cseed * D := by
    have hraw :
        nodeSupNorm (F t0).1 + nodeL1Norm (F t0).2 ≤
          (1 / 16 +
            (((blockContraction N)⁻¹ * (n : ℝ)) /
              (1 - mixingRate N) + 5 * s / 4) +
            9 * (n : ℝ) / 16) * D := by
      simpa [e, X, U, F, t0] using hseed_fast
    refine hraw.trans (mul_le_mul_of_nonneg_right ?_ hD.le)
    dsimp [Cseed]
    nlinarith
  obtain ⟨_hload_pos, _hload_lt, _hflat_dom, _hfast_dom, htrans_dom,
      hKone, _hKflat, _hKtri, _hlogInv⟩ := loading_constants_spec N
  have hKpos : 0 < loadingConstant N :=
    lt_of_lt_of_le zero_lt_one hKone
  have hpowers :
      rate ^ (kRef - t0) ≤ loadingRate N ^ (kRef - t0) := by
    exact pow_le_pow_left₀ hrate_pos.le (by simpa [rate] using htrans_dom.le) _
  have hdiff : kRef - t0 = loadingHalfDelay N s := by
    dsimp [kRef, t0, loadingDelay]
    omega
  have hcoeff :
      M * rate ^ (kRef - t0) ≤ (M / loadingConstant N) * s ^ 3 := by
    have hratio_nonneg : 0 ≤ M / loadingConstant N :=
      div_nonneg (zero_le_one.trans hM) hKpos.le
    calc
      M * rate ^ (kRef - t0) =
          (M / loadingConstant N) *
            (loadingConstant N * rate ^ (kRef - t0)) := by
              field_simp [ne_of_gt hKpos]
      _ ≤ (M / loadingConstant N) *
            (loadingConstant N * loadingRate N ^ (kRef - t0)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hpowers hKpos.le) hratio_nonneg
      _ ≤ (M / loadingConstant N) * s ^ 3 := by
          apply mul_le_mul_of_nonneg_left _ hratio_nonneg
          simpa [hdiff] using hgeom
  have hCseed_nonneg : 0 ≤ Cseed := by
    dsimp [Cseed]
    have hblock : 0 ≤ (blockContraction N)⁻¹ :=
      inv_nonneg.mpr (blockContraction_pos N).le
    have hdenmix : 0 < 1 - mixingRate N :=
      sub_pos.mpr (mixingRate_lt_one N)
    positivity
  have hhomogeneous :
      M * rate ^ (kRef - t0) *
          (nodeSupNorm (F t0).1 + nodeL1Norm (F t0).2) ≤
        ((M / loadingConstant N) * Cseed) * s ^ 3 * D := by
    have hgauge_nonneg :
        0 ≤ nodeSupNorm (F t0).1 + nodeL1Norm (F t0).2 :=
      add_nonneg (nodeSupNorm_nonneg N _)
        (Finset.sum_nonneg fun q _ => abs_nonneg _)
    calc
      M * rate ^ (kRef - t0) *
          (nodeSupNorm (F t0).1 + nodeL1Norm (F t0).2) ≤
          ((M / loadingConstant N) * s ^ 3) * (Cseed * D) :=
        mul_le_mul hcoeff hseed_bound hgauge_nonneg
          (mul_nonneg (div_nonneg (zero_le_one.trans hM) hKpos.le)
            (pow_nonneg hs.le _))
      _ = ((M / loadingConstant N) * Cseed) * s ^ 3 * D := by ring
  have hs_cube : s ^ 3 ≤ s := by
    have hs_sq : s ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hs_one)]
    calc
      s ^ 3 = s ^ 2 * s := by ring
      _ ≤ 1 * s := mul_le_mul_of_nonneg_right hs_sq hs.le
      _ = s := one_mul s
  have hhomogeneous_linear :
      ((M / loadingConstant N) * Cseed) * s ^ 3 * D ≤
        ((M / loadingConstant N) * Cseed) * s * D := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hs_cube
        (mul_nonneg (div_nonneg (zero_le_one.trans hM) hKpos.le)
          hCseed_nonneg)) hD.le
  have hfast_endpoint :
      nodeSupNorm (F kRef).1 + nodeL1Norm (F kRef).2 ≤ C3 * s * D := by
    have hraw :
        nodeSupNorm (F kRef).1 + nodeL1Norm (F kRef).2 ≤
          M * rate ^ (kRef - t0) *
              (nodeSupNorm (F t0).1 + nodeL1Norm (F t0).2) +
            ∑ r ∈ Finset.Ico t0 kRef,
              M * rate ^ (kRef - r - 1) * (s * (B0 * |xi r|)) := by
      simpa [rate, B0] using hfast_raw
    calc
      nodeSupNorm (F kRef).1 + nodeL1Norm (F kRef).2 ≤
          M * rate ^ (kRef - t0) *
              (nodeSupNorm (F t0).1 + nodeL1Norm (F t0).2) +
            ∑ r ∈ Finset.Ico t0 kRef,
              M * rate ^ (kRef - r - 1) * (s * (B0 * |xi r|)) := hraw
      _ ≤ ((M / loadingConstant N) * Cseed) * s * D +
            (9 / 32 * Cp) * s * D :=
        add_le_add (hhomogeneous.trans hhomogeneous_linear) hforcing
      _ = C3 * s * D := by
        dsimp [C3]
        ring
  exact ⟨hbranch, hcenter_step, hcenter_endpoint, hfast_endpoint⟩

end Algorithms.Unverified.GeneralPushPull
end
