import Mathlib.Tactic
import SOptLib.Model.ParameterChoices.realSqrtSpec
import SOptLib.Glue.Analysis.sum_Icc_one_div_natCast_le_one_add_log
open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: weighted finite-history Cauchy-Schwarz logarithmic bound; orig was amsgrad_history_l1_over_sqrt_le_sqrt_log_l2.
-- generality used: natural horizon, real-valued scalar history, and paper-independent real square-root witnesses; no measure, filtration, optimization, oracle, or finite-dimensional assumptions are used.
-- portable call pattern: adaptive-gradient and normalized-history proofs instantiate the scalar history with a coordinate sequence and supply root witnesses for the logarithmic weight factor and accumulated squared history; the algorithm, coordinate index, and source recurrence change while the weighted l1-to-l2 conclusion stays fixed.
-- counterargument checked: this is not paper-local traceability or a caller-side expression because it packages finite Cauchy-Schwarz, reciprocal-square-root normalization, and the harmonic-log comparison into one reusable deterministic estimate; Mathlib's finite Cauchy theorem and the staged harmonic bridge are only partial components.
-- coverage search: searched `sum Icc absolute values divided by square root bounded by square root logarithm times square root sum squares` and `weighted finite Cauchy Schwarz reciprocal square root harmonic log`; Mathlib supplied `Real.sum_mul_le_sqrt_mul_sqrt`, while SOptLib and staging supplied only the harmonic bridge, so coverage is partial.
-- minimal hypotheses: replaced the algorithm-specific coordinate family and `IsScalarSqrt` alias with `(a : ℕ → ℝ)` and `realSqrtSpec`; the horizon lower bound is unnecessary because the harmonic estimate is valid for every natural horizon.

/-- A one-based finite history divided by reciprocal square-root time weights is
bounded by the logarithmic weight root times the root sum of squared history.

Layer: Glue | Gap: Level 1 (weighted finite-history l1-to-l2 logarithmic bound)
Proof: apply finite Cauchy-Schwarz to the absolute history and reciprocal
square-root weights, rewrite the squared weights as the one-based harmonic
sum, and use the harmonic-log bound together with the supplied root witnesses.
Source: Mathlib finite Cauchy-Schwarz, real square-root order and square
identities, finite sums, and the harmonic-number logarithmic estimate
Used in: adaptive-gradient coordinate-history estimates that convert
`∑ |g j i| / √j` into a logarithmic horizon factor times the accumulated
coordinate l2 history norm
Book citation: book/ICLR2018/AMSGrad.json#/main_theorem/proof/3
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond, AMSGrad Algorithm 2 -/
theorem sum_Icc_abs_div_sqrt_natCast_le_sqrt_one_add_log_mul_sqrt_sum_sq
    (T : ℕ) (a : ℕ → ℝ)
    (sqrtOnePlusLogT sqrtSumSq : ℝ)
    (hsqrtOnePlusLogT :
      realSqrtSpec (1 + Real.log (T : ℝ)) sqrtOnePlusLogT)
    (hsqrtSumSq :
      realSqrtSpec (∑ j ∈ Finset.Icc 1 T, (a j) ^ 2) sqrtSumSq) :
    (∑ j ∈ Finset.Icc 1 T, |a j| / Real.sqrt (j : ℝ)) ≤
      sqrtOnePlusLogT * sqrtSumSq := by
  let s := Finset.Icc 1 T
  have hsum_sq_nonneg :
      0 ≤ ∑ j ∈ s, (a j) ^ 2 := by
    refine Finset.sum_nonneg ?_
    intro j _hj
    exact sq_nonneg _
  have hhist_sqrt :
      Real.sqrt (∑ j ∈ s, |a j| ^ 2) = sqrtSumSq := by
    have habs_sq :
        (∑ j ∈ s, |a j| ^ 2) =
          ∑ j ∈ s, (a j) ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro j _hj
      rw [sq_abs]
    have hsqrt_sq :
        (Real.sqrt (∑ j ∈ s, |a j| ^ 2)) ^ 2 =
          sqrtSumSq ^ 2 := by
      rw [Real.sq_sqrt]
      · rw [habs_sq]
        exact hsqrtSumSq.2.symm
      · rw [habs_sq]
        exact hsum_sq_nonneg
    have hsqrt_nonneg :
        0 ≤ Real.sqrt (∑ j ∈ s, |a j| ^ 2) :=
      Real.sqrt_nonneg _
    nlinarith [hsqrtSumSq.1, hsqrt_nonneg, hsqrt_sq]
  have hweight_sq :
      (∑ j ∈ s, (1 / Real.sqrt (j : ℝ)) ^ 2) =
        ∑ j ∈ s, (1 : ℝ) / (j : ℝ) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hj_pos_nat : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hj_nonneg : 0 ≤ (j : ℝ) := by positivity
    have hj_sqrt_ne : Real.sqrt (j : ℝ) ≠ 0 := by
      have hj_pos : 0 < (j : ℝ) := by exact_mod_cast hj_pos_nat
      exact ne_of_gt (Real.sqrt_pos.2 hj_pos)
    field_simp [hj_sqrt_ne, Real.sq_sqrt hj_nonneg]
    exact (Real.sq_sqrt hj_nonneg).symm
  have hsqrt_log_eq :
      Real.sqrt (1 + Real.log (T : ℝ)) = sqrtOnePlusLogT := by
    have hvalue_nonneg : 0 ≤ 1 + Real.log (T : ℝ) := by
      nlinarith [sq_nonneg sqrtOnePlusLogT, hsqrtOnePlusLogT.2]
    have hsqrt_sq :
        (Real.sqrt (1 + Real.log (T : ℝ))) ^ 2 =
          sqrtOnePlusLogT ^ 2 := by
      calc
        (Real.sqrt (1 + Real.log (T : ℝ))) ^ 2
            = 1 + Real.log (T : ℝ) := Real.sq_sqrt hvalue_nonneg
        _ = sqrtOnePlusLogT ^ 2 := hsqrtOnePlusLogT.2.symm
    have hsqrt_nonneg :
        0 ≤ Real.sqrt (1 + Real.log (T : ℝ)) := Real.sqrt_nonneg _
    nlinarith [hsqrtOnePlusLogT.1, hsqrt_nonneg, hsqrt_sq]
  have hweight_sqrt_le :
      Real.sqrt (∑ j ∈ s, (1 / Real.sqrt (j : ℝ)) ^ 2) ≤
        sqrtOnePlusLogT := by
    calc
      Real.sqrt (∑ j ∈ s, (1 / Real.sqrt (j : ℝ)) ^ 2)
          = Real.sqrt (∑ j ∈ s, (1 : ℝ) / (j : ℝ)) := by
            rw [hweight_sq]
      _ ≤ Real.sqrt (1 + Real.log (T : ℝ)) := by
            exact Real.sqrt_le_sqrt
              (sum_Icc_one_div_natCast_le_one_add_log T)
      _ = sqrtOnePlusLogT := hsqrt_log_eq
  have hcauchy :=
    Real.sum_mul_le_sqrt_mul_sqrt s
      (fun j => |a j|) (fun j => 1 / Real.sqrt (j : ℝ))
  calc
    (∑ j ∈ Finset.Icc 1 T, |a j| / Real.sqrt (j : ℝ))
        = ∑ j ∈ s, |a j| * (1 / Real.sqrt (j : ℝ)) := by
          simp [s, div_eq_mul_inv]
    _ ≤ Real.sqrt (∑ j ∈ s, |a j| ^ 2) *
          Real.sqrt (∑ j ∈ s, (1 / Real.sqrt (j : ℝ)) ^ 2) := hcauchy
    _ = sqrtSumSq *
          Real.sqrt (∑ j ∈ s, (1 / Real.sqrt (j : ℝ)) ^ 2) := by
          rw [hhist_sqrt]
    _ ≤ sqrtSumSq * sqrtOnePlusLogT := by
          exact mul_le_mul_of_nonneg_left hweight_sqrt_le hsqrtSumSq.1
    _ = sqrtOnePlusLogT * sqrtSumSq := by
          ring
