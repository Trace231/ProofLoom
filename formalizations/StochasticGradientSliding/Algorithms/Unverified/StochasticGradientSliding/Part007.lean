import SOptLib.Model.Bregman
import SOptLib.Model.Filtration
import SOptLib.Model.Iterates
import SOptLib.Model.Norms
import SOptLib.Model.Objective
import SOptLib.Model.Prox
import SOptLib.Model.Subdifferential
import SOptLib.Glue.Probability
import SOptLib.Glue.Martingale
import SOptLib.Layer0.Oracle
import SOptLib.Layer1.Proximal
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Algorithms.Unverified.StochasticGradientSliding.Part006

/-!
Stochastic gradient sliding.

Phase 0 object layer for Lan's stochastic gradient sliding method.  The
declarations below encode the paper-facing mathematical objects as definitions:
the composite objective, Bregman prox geometry, stochastic oracle samples, SPS
inner update, and the outer SGS recursion.
-/

open scoped BigOperators Gradient InnerProductSpace
open MeasureTheory ProbabilityTheory

namespace StochasticGradientSliding


universe u v w z

variable {E : Type u} {Sample : Type v} {Ω : Type w}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (S : Setup.{u, v, w} E Sample)


/-- Harmonic factor bound for one compact linear SPS source row.

Aligns with Lan Corollary 8.3 proof step 7 / Eq. (8.1.79): after the exact
`2 + 2/(i+1)` row split, the normalized scalar factor is bounded by one using
only `∑_{i<t} 1/(i+1) ≤ t` and the elementary polynomial slack
`(t+1)^2(t+2) ≤ t(t+3)^2`. Candidate audit: checked
`compact_linear_sps_combined_row_eq_normalized_sum_form`,
`compact_linear_sps_normalized_q_minus_one_eq`, and SOptLib finite-sum
telescopes; they expose row normalization or different aggregate routes, but
not this literal positive-`t` source-row factor bound. -/
private theorem compact_linear_sps_harmonic_factor_le_one {t : ℕ} (ht : 0 < t) :
    ((((t : ℝ) + 1) * ((t : ℝ) + 2) / ((t : ℝ) + 3) ^ 2) *
        (1 + (Finset.range t).sum (fun i => 1 / ((i : ℝ) + 1))) /
        (t : ℝ)) ≤ 1 := by
  classical
  let H : ℝ := (Finset.range t).sum (fun i => 1 / ((i : ℝ) + 1))
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht
  have hH_le : H ≤ (t : ℝ) := by
    dsimp [H]
    calc
      (Finset.range t).sum (fun i => 1 / ((i : ℝ) + 1))
          ≤ (Finset.range t).sum (fun _ => (1 : ℝ)) := by
            refine Finset.sum_le_sum ?_
            intro i _hi
            have hden_pos : 0 < (i : ℝ) + 1 := by positivity
            have hden_ge : 1 ≤ (i : ℝ) + 1 := by
              have hi_nonneg : 0 ≤ (i : ℝ) := by positivity
              linarith
            exact (div_le_one hden_pos).2 hden_ge
      _ = (t : ℝ) := by
            simp [Finset.sum_const, nsmul_eq_mul]
  have hfactor_nonneg :
      0 ≤ ((t : ℝ) + 1) * ((t : ℝ) + 2) / ((t : ℝ) + 3) ^ 2 := by
    positivity
  have hmono :
      ((((t : ℝ) + 1) * ((t : ℝ) + 2) / ((t : ℝ) + 3) ^ 2) *
          (1 + H) / (t : ℝ)) ≤
        ((((t : ℝ) + 1) * ((t : ℝ) + 2) / ((t : ℝ) + 3) ^ 2) *
          (1 + (t : ℝ)) / (t : ℝ)) := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith) hfactor_nonneg) (le_of_lt htR)
  have hpoly :
      ((((t : ℝ) + 1) * ((t : ℝ) + 2) / ((t : ℝ) + 3) ^ 2) *
          (1 + (t : ℝ)) / (t : ℝ)) ≤ 1 := by
    have ht_ne : (t : ℝ) ≠ 0 := ne_of_gt htR
    have ht3_ne : (t : ℝ) + 3 ≠ 0 := by positivity
    have htR_ge_one : 1 ≤ (t : ℝ) := by exact_mod_cast ht
    field_simp [ht_ne, ht3_ne]
    nlinarith [sq_nonneg ((t : ℝ) + 3), sq_nonneg ((t : ℝ) - 1), htR_ge_one]
  calc
    ((((t : ℝ) + 1) * ((t : ℝ) + 2) / ((t : ℝ) + 3) ^ 2) *
        (1 + (Finset.range t).sum (fun i => 1 / ((i : ℝ) + 1))) /
        (t : ℝ))
        = ((((t : ℝ) + 1) * ((t : ℝ) + 2) / ((t : ℝ) + 3) ^ 2) *
            (1 + H) / (t : ℝ)) := by rfl
    _ ≤ ((((t : ℝ) + 1) * ((t : ℝ) + 2) / ((t : ℝ) + 3) ^ 2) *
          (1 + (t : ℝ)) / (t : ℝ)) := hmono
    _ ≤ 1 := hpoly

/-- The live source row cannot be discharged by the tempting pointwise
`q(T) ≤ 1` shortcut.

The preceding helper bounds
`factor * (1 + H_T) / T`.  The source row in
the previous arbitrary-`T` source-formula attempt used
`factor * (1 + H_T / T)`, which is already larger than one at `T = 9`.
This compiled obstruction keeps the remaining proof obligation at the aggregate
finite-sum level rather than silently reviving the pointwise shortcut. -/
private theorem compact_linear_sps_live_factor_not_pointwise_le_one :
    ¬ (((((9 : ℝ) + 1) * ((9 : ℝ) + 2) / ((9 : ℝ) + 3) ^ 2) *
        (1 + (Finset.range 9).sum (fun i => 1 / ((i : ℝ) + 1)) / (9 : ℝ))) ≤
      1) := by
  norm_num [Finset.sum_range_succ]

/-- The exact source SPS linear row is not bounded by the paper's aggregate
`4 / T` contribution pointwise.

This is the same obstruction in the source-formula coordinates consumed below:
at `T = 9`, the exact `2 + 2/(i+1)` row exceeds the rowwise `4/T` bound, so
the compact Corollary 8.3 linear term needs a finite-sum cancellation rather
than a pointwise replacement. -/
private theorem compact_linear_sps_source_row_not_pointwise_four_over_t :
    ¬ ((2 * ((9 : ℝ) + 1) * ((9 : ℝ) + 2) /
          ((9 : ℝ) ^ 2 * ((9 : ℝ) + 3) ^ 2)) *
        (Finset.range 9).sum (fun i => 2 + 2 / ((i : ℝ) + 1)) ≤
      4 / (9 : ℝ)) := by
  norm_num [Finset.sum_range_succ]

/-- Same-interface obstruction for the step-7 checked-summand bridge.

The exact checked Theorem 8.2(c) row at `T = 9` is already larger than the
source-displayed `4/T` row.  Thus the active bridge from the unhalved checked
linear summand to the Corollary 8.3 `4σ²/(9L)` formula is not a pure FILL leaf
under the current checked-scale realization; the source boundary needs either a
corrected checked probability-scale object or an explicitly different source
combination before this row can be consumed. -/
private theorem compact_probability_linear_step7_checked_row_bridge_false_at_T9 :
    ¬ ((Finset.range 9).sum (fun i =>
        (psWeightProduct spsP 9 *
          (1 - psWeightProduct spsP 9)⁻¹ *
            (1 - psWeightProduct spsP 9)⁻¹) *
        ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
          psWeightProduct spsP i)⁻¹) ≤
      4 / (9 : ℝ)) := by
  norm_num [psWeightProduct_spsP_eq, spsP, Finset.sum_range_succ]

/-- Quantified same-interface obstruction for the tempting checked-row bridge.

Any direct checked-row source bridge of the form
`row(T) ≤ 4 / T` is refuted by the compiled `T = 9` instance above.  This is
route evidence for the active step-7 boundary: proving the checked summand
against the displayed `4σ²/(9L)` source row requires a corrected source-scale
interface or additional source structure, not another pointwise row fill. -/
private theorem compact_probability_linear_step7_checked_row_bridge_not_universal :
    ¬ (∀ T : ℕ, 0 < T →
      (Finset.range T).sum (fun i =>
          (psWeightProduct spsP T *
            (1 - psWeightProduct spsP T)⁻¹ *
              (1 - psWeightProduct spsP T)⁻¹) *
          ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
            psWeightProduct spsP i)⁻¹) ≤
        4 / (T : ℝ)) := by
  intro h
  exact compact_probability_linear_step7_checked_row_bridge_false_at_T9
    (h 9 (by norm_num))

/-- Same-interface obstruction for the aggregate step-7 checked-summand bridge.

This targets the current source/coarser interface itself, not just a reusable
row lemma.  Under the concrete compact schedule
`T_k = ceil ((M^2 + sigmaSq) * (k+1)^3 / (Dtilde * L^2))`, the bridge from the
checked Theorem 8.2(c) linear summand to the displayed
`4 * sigmaSq / (9 * L) * sum k(k+1)^2/T_k` source contribution is false at
`N = 1`, `Dtilde = L = sigmaSq = 1`, `M = 1/100`, where the only aggregate row
has `T_1 = 9`. -/
theorem compact_probability_linear_step7_checked_summand_bridge_compact_schedule_false_at_N1 :
    ¬ (∀ N : PositiveTime, ∀ Dtilde L sigmaSq mGrowth : ℝ,
      0 < Dtilde → 0 < L → 0 ≤ sigmaSq → 0 < mGrowth →
      let T : PositiveTime → ℕ := fun κ =>
        Nat.ceil (((mGrowth ^ 2 + sigmaSq) * ((κ.1 : ℝ) + 1) ^ 3) /
          (Dtilde * L ^ 2))
      sigmaSq * compactGammaWeight N *
          (Finset.range N.1).sum (fun k =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
            (Finset.range (T κ)).sum (fun i =>
              (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (9 * L)) *
                (psWeightProduct spsP (T κ) *
                  (1 - psWeightProduct spsP (T κ))⁻¹ *
                    (1 - psWeightProduct spsP (T κ))⁻¹) *
                ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
                  psWeightProduct spsP i)⁻¹)) ≤
        sigmaSq * compactGammaWeight N *
          (Finset.range N.1).sum (fun k =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
            (4 / (9 * L)) *
              (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (T κ : ℝ)))) := by
  intro h
  have hceil0 : Nat.ceil (10001 / 1250 : ℝ) = 9 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    norm_num
  have hinst := h ⟨1, by omega⟩ 1 1 1 (1 / 100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [compactGammaWeight, psWeightProduct_spsP_eq, spsP,
    Finset.sum_range_succ, hceil0] at hinst

/-- Source-interface validity predicate for the Arbiter-selected compact
step-7 checked-summand bridge.

This is the same target shape as the active bridge below, with the compact
schedule exposed by its scalar source parameters.  It records the route-level
question without asserting the false bridge as a theorem. -/
def compactProbabilityLinearStep7CheckedSummandBridgeSourceInterface : Prop :=
  ∀ N : PositiveTime, ∀ Dtilde L sigmaSq mGrowth : ℝ,
    0 < Dtilde → 0 < L → 0 ≤ sigmaSq → 0 < mGrowth →
    let T : PositiveTime → ℕ := fun κ =>
      Nat.ceil (((mGrowth ^ 2 + sigmaSq) * ((κ.1 : ℝ) + 1) ^ 3) /
        (Dtilde * L ^ 2))
    sigmaSq * compactGammaWeight N *
        (Finset.range N.1).sum (fun k =>
          let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
          (Finset.range (T κ)).sum (fun i =>
            (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (9 * L)) *
              (psWeightProduct spsP (T κ) *
                (1 - psWeightProduct spsP (T κ))⁻¹ *
                  (1 - psWeightProduct spsP (T κ))⁻¹) *
              ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
                psWeightProduct spsP i)⁻¹)) ≤
      sigmaSq * compactGammaWeight N *
        (Finset.range N.1).sum (fun k =>
          let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
          (4 / (9 * L)) *
            (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (T κ : ℝ)))

/-- Typed same-interface block for the Arbiter-selected checked-summand bridge.

The compact step-7 source formula is represented and its budget/Gamma algebra
is proved below, but the checked-summand bridge from the current
`theorem82ProbabilityScale_checkedFormulaExtension` realization to the source
`4/(9L)` row is refuted at this interface. -/
theorem compact_probability_linear_step7_checked_summand_bridge_source_interface_typed_blocked :
    ¬ compactProbabilityLinearStep7CheckedSummandBridgeSourceInterface :=
  compact_probability_linear_step7_checked_summand_bridge_compact_schedule_false_at_N1

/-- Exact-interface dependency certificate for the arbitrary-`T` source formula.

If the pre-gamma source formula below were available for every admissible
`Dtilde`, `L`, `sigmaSq`, and `T`, then specializing it to `Dtilde = L = 1`
and `sigmaSq = c` gives the normalized overrun supplier for the same arbitrary
admissible compact budgets.  This is route evidence only: it is not consumed by
the public compact probability-linear theorem, and it avoids calling the older
normalized/common-ceiling declarations. -/
theorem compact_probability_linear_source_formula_supplier_implies_normalized_source
    (N : PositiveTime) (c : ℝ) (hc : 0 ≤ c)
    (hsource :
      ∀ (Dtilde L sigmaSq : ℝ),
        0 < Dtilde → 0 < L → 0 ≤ sigmaSq →
        ∀ (T : PositiveTime → ℕ), (∀ κ, 0 < T κ) →
          (∀ κ : PositiveTime,
            sigmaSq * (κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2 / (T κ : ℝ) ≤
              Dtilde * L ^ 2) →
          sigmaSq *
              (Finset.range N.1).sum (fun k =>
                let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
                (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (9 * L)) *
                  (2 * ((T κ : ℝ) + 1) * ((T κ : ℝ) + 2) /
                    ((T κ : ℝ) ^ 2 * ((T κ : ℝ) + 3) ^ 2)) *
                  (Finset.range (T κ)).sum (fun i => 2 + 2 / ((i : ℝ) + 1))) ≤
            Dtilde * L * (4 * ((N.1 : ℝ) + 1) / 9)) :
    ∀ (T : PositiveTime → ℕ), (∀ κ, 0 < T κ) →
      (∀ κ : PositiveTime,
        c * (κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2 ≤ (T κ : ℝ)) →
      (Finset.range N.1).sum (fun k =>
        let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
        (((c * ((((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (T κ : ℝ))) *
            (((T κ : ℝ) + 1) * ((T κ : ℝ) + 2) / ((T κ : ℝ) + 3) ^ 2)) *
            (1 + ((Finset.range (T κ)).sum (fun i => 1 / ((i : ℝ) + 1))) /
              (T κ : ℝ))) - 1)) ≤ 1 := by
  classical
  intro T hTpos hbudget_scale
  let sourceSum : ℝ :=
    (Finset.range N.1).sum (fun k =>
      let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
      (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (9 * (1 : ℝ))) *
        (2 * ((T κ : ℝ) + 1) * ((T κ : ℝ) + 2) /
          ((T κ : ℝ) ^ 2 * ((T κ : ℝ) + 3) ^ 2)) *
        (Finset.range (T κ)).sum (fun i => 2 + 2 / ((i : ℝ) + 1)))
  let scalarSum : ℝ :=
    (Finset.range N.1).sum (fun k =>
      let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
      (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / 9) *
        (2 * ((T κ : ℝ) + 1) * ((T κ : ℝ) + 2) /
          ((T κ : ℝ) ^ 2 * ((T κ : ℝ) + 3) ^ 2)) *
        (Finset.range (T κ)).sum (fun i => 2 + 2 / ((i : ℝ) + 1)))
  let normSum : ℝ :=
    (Finset.range N.1).sum (fun k =>
      let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
      ((c * (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (T κ : ℝ))) *
        (((T κ : ℝ) + 1) * ((T κ : ℝ) + 2) / ((T κ : ℝ) + 3) ^ 2)) *
        (1 + ((Finset.range (T κ)).sum (fun i => 1 / ((i : ℝ) + 1))) /
          (T κ : ℝ)))
  have hbudget_source : ∀ κ : PositiveTime,
      c * (κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2 / (T κ : ℝ) ≤
        (1 : ℝ) * (1 : ℝ) ^ 2 := by
    intro κ
    have hTκ_pos : 0 < (T κ : ℝ) := by exact_mod_cast hTpos κ
    have hbudget : c * ((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) ≤ (T κ : ℝ) := by
      simpa [mul_assoc] using hbudget_scale κ
    calc
      c * (κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2 / (T κ : ℝ)
          = c * ((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (T κ : ℝ) := by ring
      _ ≤ 1 := (div_le_one hTκ_pos).2 hbudget
      _ = (1 : ℝ) * (1 : ℝ) ^ 2 := by norm_num
  have hsource_bound :
      c * sourceSum ≤ (1 : ℝ) * (1 : ℝ) * (4 * ((N.1 : ℝ) + 1) / 9) := by
    simpa [sourceSum] using
      hsource 1 1 c (by norm_num) (by norm_num) hc T hTpos hbudget_source
  have hsource_scalar : sourceSum = scalarSum := by
    dsimp [sourceSum, scalarSum]
    refine Finset.sum_congr rfl ?_
    intro k _hk
    ring
  have hscalar_bound : c * scalarSum ≤ 4 * ((N.1 : ℝ) + 1) / 9 := by
    nlinarith [hsource_bound, hsource_scalar]
  have hrow_eq : c * scalarSum = (4 / 9) * normSum := by
    dsimp [scalarSum, normSum]
    conv_lhs => rw [Finset.mul_sum]
    conv_rhs => rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k _hk
    let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
    have hsplit :
        (Finset.range (T κ)).sum (fun i => 2 + 2 / ((i : ℝ) + 1)) =
          ((T κ : ℝ) * 2) +
            (Finset.range (T κ)).sum (fun i => 2 / ((i : ℝ) + 1)) := by
      calc
        (Finset.range (T κ)).sum (fun i => 2 + 2 / ((i : ℝ) + 1))
            =
          (Finset.range (T κ)).sum
            (fun i => (2 : ℝ) + 2 / ((i : ℝ) + 1)) := by rfl
        _ =
          (Finset.range (T κ)).sum (fun _ => (2 : ℝ)) +
            (Finset.range (T κ)).sum (fun i => 2 / ((i : ℝ) + 1)) := by
              rw [Finset.sum_add_distrib]
        _ =
          ((T κ : ℝ) * 2) +
            (Finset.range (T κ)).sum (fun i => 2 / ((i : ℝ) + 1)) := by
              simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
    let A : ℝ :=
      ((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2 / 9) *
        (2 * ((T κ : ℝ) + 1) * ((T κ : ℝ) + 2) /
          ((T κ : ℝ) ^ 2 * ((T κ : ℝ) + 3) ^ 2))
    let U : ℝ := (T κ : ℝ) * 2
    let V : ℝ := (Finset.range (T κ)).sum (fun i => 2 / ((i : ℝ) + 1))
    calc
      (c *
          ((((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2 / 9) *
              (2 * ((T κ : ℝ) + 1) * ((T κ : ℝ) + 2) /
                ((T κ : ℝ) ^ 2 * ((T κ : ℝ) + 3) ^ 2)) *
            (Finset.range (T κ)).sum (fun i => 2 + 2 / ((i : ℝ) + 1)))))
          =
        c * (A * U) + c * (A * V) := by
          rw [hsplit]
          dsimp [A, U, V]
          ring
      _ =
        (4 / 9) *
          (((c * (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (T κ : ℝ))) *
            (((T κ : ℝ) + 1) * ((T κ : ℝ) + 2) / ((T κ : ℝ) + 3) ^ 2)) *
            (1 + ((Finset.range (T κ)).sum (fun i => 1 / ((i : ℝ) + 1))) /
              (T κ : ℝ))) := by
            simpa [A, U, V, κ] using
              compact_linear_sps_combined_row_eq_normalized_sum_form c κ (hTpos κ)
  have hnorm_total : normSum ≤ (N.1 : ℝ) + 1 := by
    have hmul : (4 / 9) * normSum ≤ 4 * ((N.1 : ℝ) + 1) / 9 := by
      simpa [hrow_eq] using hscalar_bound
    nlinarith
  let row : ℕ → ℝ := fun k =>
    let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
    ((c * (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (T κ : ℝ))) *
      (((T κ : ℝ) + 1) * ((T κ : ℝ) + 2) / ((T κ : ℝ) + 3) ^ 2)) *
      (1 + ((Finset.range (T κ)).sum (fun i => 1 / ((i : ℝ) + 1))) /
        (T κ : ℝ))
  have hnorm_eq : normSum = (Finset.range N.1).sum row := by
    rfl
  have hsub :
      (Finset.range N.1).sum (fun k => row k - 1) =
        (Finset.range N.1).sum row - (Finset.range N.1).sum (fun _ => (1 : ℝ)) := by
    rw [Finset.sum_sub_distrib]
  have hconst : (Finset.range N.1).sum (fun _ => (1 : ℝ)) = (N.1 : ℝ) := by
    simp [Finset.sum_const, nsmul_eq_mul]
  change (Finset.range N.1).sum (fun k => row k - 1) ≤ 1
  nlinarith

/-- Coarse Eq. (8.1.52) expected-bound constants do not by themselves imply the
active probability-linear source target.

The already-compiled coarse source helper `compact_stochastic_outer_sum_le_public`
has the `16 * Dtilde / 3` numerator over `((N+1)*(N+2))`.  The active
probability-linear branch below has the sharper `8 * Dtilde / 3` numerator over
`N*(N+2)`.  At `N = 2` the coarse RHS is larger, so replacing the remaining
linear-row correction by that helper alone would be a constant mismatch rather
than a proof of the same formula-level interface. -/
theorem compact_probability_linear_coarse_eq8152_rhs_not_strong_enough :
    ¬ (∀ N : PositiveTime, ∀ Dtilde L : ℝ, 0 < Dtilde → 0 < L →
      L / (((N.1 : ℝ) + 1) * ((N.1 : ℝ) + 2)) * ((16 * Dtilde) / 3) ≤
        L / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) * ((8 * Dtilde) / 3)) := by
  intro h
  have htwo := h ⟨2, by omega⟩ 1 1 (by norm_num) (by norm_num)
  norm_num at htwo

/-- Same-interface obstruction for the coarse Eq. (8.1.52) bridge.

The source/coarser route requested by Phase 2b can use Eq. (8.1.52), but the
coarse expected-bound terminal constant alone is not strong enough for the
sharp probability-linear formula target.  This is stronger than comparing the
two closed RHS constants: it says that even a formula-level source aggregate
known only up to the coarse `16/3` bound cannot imply the active `8/3`
probability-linear target.  At `N = 2`, `sourceSum = 16/9` saturates the coarse
bound while violating the sharp target. -/
theorem compact_probability_linear_coarse_eq8152_source_interface_not_strong_enough :
    ¬ (∀ N : PositiveTime, ∀ Dtilde L sigmaSq sourceSum : ℝ,
      0 < Dtilde → 0 < L → 0 ≤ sigmaSq →
      sigmaSq * compactGammaWeight N * sourceSum ≤
        L / (((N.1 : ℝ) + 1) * ((N.1 : ℝ) + 2)) * ((16 * Dtilde) / 3) →
      sigmaSq * compactGammaWeight N * sourceSum ≤
        L / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) * ((8 * Dtilde) / 3)) := by
  intro h
  have htwo := h ⟨2, by omega⟩ 1 1 1 (16 / 9)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [compactGammaWeight])
  norm_num [compactGammaWeight] at htwo

/-- Same-interface obstruction for the `hbudget`-only formula algebra boundary.

The sharp high-probability linear target cannot be proved from only the
rowwise budget inequality used by
`compact_probability_linear_bp_linear_formula_algebra_bound_of_budget`.  At
`N = 2`, with every row saturating that inequality, the source-formula sum is
`4/9` after applying `compactGammaWeight`, while the requested RHS is `1/3`.
Any successful source/formula route therefore needs the sharper high-probability
linear coefficient or additional compact-budget structure, not this
`8/(9L)` Eq. (8.1.52)-row plus per-row budget abstraction alone. -/
theorem compact_probability_linear_bp_linear_hbudget_interface_not_strong_enough :
    ¬ (∀ N : PositiveTime, ∀ Dtilde L sigmaSq : ℝ,
      0 < Dtilde → 0 < L → 0 ≤ sigmaSq →
      ∀ T : PositiveTime → ℕ,
      (∀ κ : PositiveTime,
        sigmaSq * (κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2 / (T κ : ℝ) ≤
          Dtilde * L ^ 2) →
      sigmaSq * compactGammaWeight N *
          (Finset.range N.1).sum (fun k =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
            (8 / (9 * L)) *
              (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (T κ : ℝ))) ≤
        L / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) * ((8 * Dtilde) / 3)) := by
  intro h
  let T : PositiveTime → ℕ := fun κ => κ.1 * (κ.1 + 1) ^ 2
  have hbudget : ∀ κ : PositiveTime,
      (1 : ℝ) * (κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2 / (T κ : ℝ) ≤
        (1 : ℝ) * (1 : ℝ) ^ 2 := by
    intro κ
    have hk_pos : 0 < (κ.1 : ℝ) := by exact_mod_cast κ.2
    have hk1_pos : 0 < (κ.1 : ℝ) + 1 := by positivity
    have hrow :
        (1 : ℝ) * (κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2 / (T κ : ℝ) = 1 := by
      have hT_cast :
          (T κ : ℝ) = (κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2 := by
        dsimp [T]
        norm_num
      rw [hT_cast]
      field_simp [ne_of_gt hk_pos, ne_of_gt hk1_pos]
    rw [hrow]
    norm_num
  have htwo := h ⟨2, by omega⟩ 1 1 1
    (by norm_num) (by norm_num) (by norm_num) T hbudget
  norm_num [compactGammaWeight, T] at htwo

/-- Same-interface obstruction for the exact compact-schedule Eq. (8.1.52) route.

This targets the Arbiter-selected compact source/coarser formula interface, not
the arbitrary-`T` hbudget abstraction above.  Even after specializing the budget
to the paper's compact ceiling schedule
`ceil((M^2 + σ^2) * (k+1)^3 / (Dtilde * L^2))`, the Eq. (8.1.52) row with
coefficient `8/(9L)` is too weak to imply the active high-probability linear
target.  At `N = 4`, `Dtilde = L = σ² = 1`, and positive `M = 1/100`, the
formula sum still violates the requested `8/3` public RHS. -/
theorem compact_probability_linear_bp_linear_compact_schedule_eq8152_interface_not_strong_enough :
    ¬ (∀ N : PositiveTime, ∀ Dtilde L sigmaSq mGrowth : ℝ,
      0 < Dtilde → 0 < L → 0 ≤ sigmaSq →
      0 < mGrowth →
      let T : PositiveTime → ℕ := fun κ =>
        Nat.ceil (((mGrowth ^ 2 + sigmaSq) * ((κ.1 : ℝ) + 1) ^ 3) /
          (Dtilde * L ^ 2))
      sigmaSq * compactGammaWeight N *
          (Finset.range N.1).sum (fun k =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
            (8 / (9 * L)) *
              (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (T κ : ℝ))) ≤
        L / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) * ((8 * Dtilde) / 3)) := by
  intro h
  have hfour := h ⟨4, by omega⟩ 1 1 1 (1 / 100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hceil0 : Nat.ceil (10001 / 1250 : ℝ) = 9 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    norm_num
  have hceil1 : Nat.ceil (270027 / 10000 : ℝ) = 28 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    norm_num
  have hceil2 : Nat.ceil (40004 / 625 : ℝ) = 65 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    norm_num
  have hceil3 : Nat.ceil (10001 / 80 : ℝ) = 126 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    norm_num
  have hsum :
      (Finset.range 4).sum (fun x =>
        (8 / 9 : ℝ) * (((x : ℝ) + 1) * ((x : ℝ) + 1 + 1) ^ 2 /
          (Nat.ceil ((10001 / 10000 : ℝ) *
            ((x : ℝ) + 1 + 1) ^ 3) : ℝ))) =
          28604 / 12285 := by
    norm_num [Finset.sum_range_succ, hceil0, hceil1, hceil2, hceil3]
  norm_num [compactGammaWeight, hsum] at hfour

/-- Same-target dependency certificate for the concrete source formula.

The exact `compactInnerBudgetSource` formula target is not merely a wrapper
around the coarse Eq. (8.1.52) terminal constant: after factoring out
`Dtilde * L`, the theorem statement is equivalent to the sharp scalar
finite-grid estimate `c * scalarSum <= 4*(N+1)/9`.  This certificate is used
only as route evidence; it does not call the older normalized/common-ceiling
supplier family. -/
theorem compact_probability_linear_concrete_source_formula_requires_scalar_bound
    (N : PositiveTime) (Dtilde : ℝ) (hDtilde : 0 < Dtilde)
    (hsource :
      S.sigmaSq * compactGammaWeight N *
          (Finset.range N.1).sum (fun k =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
            (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (9 * S.lSmooth)) *
              (2 * ((innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ : ℝ) + 1) *
                  ((innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ : ℝ) + 2) /
                ((innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ : ℝ) ^ 2 *
                  ((innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ : ℝ) + 3) ^ 2)) *
              (Finset.range (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ)).sum
                (fun i => 2 + 2 / ((i : ℝ) + 1))) ≤
        S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) * ((8 * Dtilde) / 3)) :
    let T : PositiveTime → ℕ :=
      innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)
    let c : ℝ := S.sigmaSq / (Dtilde * S.lSmooth ^ 2)
    c * (Finset.range N.1).sum (fun k =>
          let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
          (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / 9) *
            (2 * ((T κ : ℝ) + 1) * ((T κ : ℝ) + 2) /
              ((T κ : ℝ) ^ 2 * ((T κ : ℝ) + 3) ^ 2)) *
            (Finset.range (T κ)).sum (fun i => 2 + 2 / ((i : ℝ) + 1))) ≤
      4 * ((N.1 : ℝ) + 1) / 9 := by
  classical
  let T : PositiveTime → ℕ :=
    innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)
  let c : ℝ := S.sigmaSq / (Dtilde * S.lSmooth ^ 2)
  let sourceSum : ℝ :=
    (Finset.range N.1).sum (fun k =>
      let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
      (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (9 * S.lSmooth)) *
        (2 * ((T κ : ℝ) + 1) * ((T κ : ℝ) + 2) /
          ((T κ : ℝ) ^ 2 * ((T κ : ℝ) + 3) ^ 2)) *
        (Finset.range (T κ)).sum (fun i => 2 + 2 / ((i : ℝ) + 1)))
  let scalarSum : ℝ :=
    (Finset.range N.1).sum (fun k =>
      let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
      (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / 9) *
        (2 * ((T κ : ℝ) + 1) * ((T κ : ℝ) + 2) /
          ((T κ : ℝ) ^ 2 * ((T κ : ℝ) + 3) ^ 2)) *
        (Finset.range (T κ)).sum (fun i => 2 + 2 / ((i : ℝ) + 1)))
  have hDL2_pos : 0 < Dtilde * S.lSmooth ^ 2 :=
    mul_pos hDtilde (sq_pos_of_ne_zero (ne_of_gt S.L_pos))
  have hsource_factor :
      S.sigmaSq * sourceSum = (Dtilde * S.lSmooth) * (c * scalarSum) := by
    have hcscalar :
        c * scalarSum =
          (Finset.range N.1).sum (fun k =>
            c *
              (let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
              (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / 9) *
                (2 * ((T κ : ℝ) + 1) * ((T κ : ℝ) + 2) /
                  ((T κ : ℝ) ^ 2 * ((T κ : ℝ) + 3) ^ 2)) *
                (Finset.range (T κ)).sum (fun i => 2 + 2 / ((i : ℝ) + 1)))) := by
      dsimp [scalarSum]
      rw [Finset.mul_sum]
    rw [hcscalar]
    dsimp [sourceSum, c]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k _hk
    let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
    field_simp [ne_of_gt S.L_pos, ne_of_gt hDL2_pos]
  have hsource' :
      compactGammaWeight N * ((Dtilde * S.lSmooth) * (c * scalarSum)) ≤
        S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) * ((8 * Dtilde) / 3) := by
    calc
      compactGammaWeight N * ((Dtilde * S.lSmooth) * (c * scalarSum))
          = S.sigmaSq * compactGammaWeight N * sourceSum := by
            rw [← hsource_factor]
            ring
      _ ≤ S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) * ((8 * Dtilde) / 3) := by
            simpa [sourceSum, T] using hsource
  have hN_pos : 0 < (N.1 : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one N.2)
  have hN1_pos : 0 < (N.1 : ℝ) + 1 := by positivity
  have hN2_pos : 0 < (N.1 : ℝ) + 2 := by positivity
  have hDL_pos : 0 < Dtilde * S.lSmooth := mul_pos hDtilde S.L_pos
  change c * scalarSum ≤ 4 * ((N.1 : ℝ) + 1) / 9
  unfold compactGammaWeight at hsource'
  field_simp [ne_of_gt hN_pos, ne_of_gt hN1_pos, ne_of_gt hN2_pos,
    ne_of_gt hDL_pos] at hsource' ⊢
  nlinarith [hsource']

/-- Specialized ceiling lower bound for the compact Eq. (8.1.75) schedule.

Aligns with Lan Corollary 8.3 proof step using Eq. (8.1.75): after writing
`T k = ceil (a * (k+2)^3)`, each concrete budget dominates its real
requirement. Candidate audit: checked the pre-searched probability/filtration
candidates (`iIndepFun.indep_prefixFiltration_future`, `filtration`,
`filtration_seq`, `measurable_sample_le_prefixFiltration`,
`generated_execution_bound_of_run_contract_bridge`, and
`generated_bound_of_carrier_objective_measurable`) and the older target
names `compact_linear_sps_concrete_ceiling_source_scalar_sum_bound_nat` /
`compact_probability_linear_concrete_source_scalar_sum_bound`; the former
candidates are stochastic interfaces, while the target scalar names are not
compiled declarations, so the route needs this local deterministic ceiling
bridge. -/
private theorem compact_inner_budget_source_ceiling_mono_lower
    (a : ℝ) (ha : 0 < a) :
    ∀ k : ℕ,
      a * (((k + 2 : ℕ) : ℝ) ^ 3) ≤
        (Nat.ceil (a * (((k + 2 : ℕ) : ℝ) ^ 3)) : ℝ) := by
  intro k
  have _harg_pos : 0 < a * (((k + 2 : ℕ) : ℝ) ^ 3) := by
    exact mul_pos ha (pow_pos (by positivity) 3)
  exact Nat.le_ceil _

/-- Row budget comparison for the compact Eq. (8.1.75) ceiling schedule.

This is the deterministic row step beneath Lan Corollary 8.3's compact
probability-linear source algebra: if `0 <= c <= a`, the sigma-only row scale
`c * (k+1) * (k+2)^2` is dominated by the concrete ceiling budget
`ceil (a * (k+2)^3)`. Candidate audit: searched target/SOptLib for compact
row-budget and ceiling-grid suppliers; existing compiled source suppliers
`compact_probability_linear_step7_bp_formula_algebra_bound_of_budget` and
`compact_probability_linear_step7_half_bp_source_bound` work after the
coarser Eq. (8.1.52) row, while Part006 ceiling-grid helpers are separate
route infrastructure. This helper is the smaller scalar row comparison needed
before any exact finite-grid aggregate can be revisited. -/
private theorem compact_inner_budget_source_row_budget_le_of_c_le_a
    (a c : ℝ) (ha : 0 < a) (hc : 0 ≤ c) (hca : c ≤ a) :
    ∀ k : ℕ,
      c * ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1) ^ 2 ≤
        (Nat.ceil (a * (((k + 2 : ℕ) : ℝ) ^ 3)) : ℝ) := by
  intro k
  have hceil := compact_inner_budget_source_ceiling_mono_lower a ha k
  have hk_nonneg :
      0 ≤ ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1) ^ 2 := by
    positivity
  have _hrow_nonneg :
      0 ≤ c * (((k + 1 : ℕ) : ℝ) *
          (((k + 1 : ℕ) : ℝ) + 1) ^ 2) :=
    mul_nonneg hc hk_nonneg
  have hca_scaled :
      c * (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1) ^ 2) ≤
        a * (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1) ^ 2) :=
    mul_le_mul_of_nonneg_right hca hk_nonneg
  have hk_succ :
      (((k + 1 : ℕ) : ℝ) + 1) = ((k + 2 : ℕ) : ℝ) := by
    have hk_nat : (k + 1) + 1 = k + 2 := by omega
    exact_mod_cast hk_nat
  calc
    c * ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1) ^ 2
        = c * (((k + 1 : ℕ) : ℝ) *
            (((k + 1 : ℕ) : ℝ) + 1) ^ 2) := by ring
    _ ≤ a * (((k + 1 : ℕ) : ℝ) *
            (((k + 1 : ℕ) : ℝ) + 1) ^ 2) := hca_scaled
    _ ≤ a * (((k + 2 : ℕ) : ℝ) ^ 3) := by
          have hka :
              ((k + 1 : ℕ) : ℝ) ≤ (((k + 1 : ℕ) : ℝ) + 1) := by
            linarith
          have hpow_nonneg :
              0 ≤ (((k + 1 : ℕ) : ℝ) + 1) ^ 2 := sq_nonneg _
          have hmul :=
            mul_le_mul_of_nonneg_right hka hpow_nonneg
          have hpoly :
              ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1) ^ 2 ≤
                ((k + 2 : ℕ) : ℝ) ^ 3 := by
            rw [← hk_succ]
            simpa [pow_succ, pow_two, mul_assoc] using hmul
          exact mul_le_mul_of_nonneg_left hpoly (le_of_lt ha)
    _ ≤ (Nat.ceil (a * (((k + 2 : ℕ) : ℝ) ^ 3)) : ℝ) := hceil


/-- Branch-local Eq. (8.1.52) row estimate for the compact linear `B_p(N)` term.

This is the source/coarser row API requested by the route audit.  It exposes
only the paper-level inner-sum conclusion, not the exact split into the
harmonic row or the older scalar/common-ceiling aggregate. -/
private theorem compact_probability_linear_eq8152_row_bound
    (T : PositiveTime → ℕ) {κ : PositiveTime} (hTκ : 0 < T κ) :
    (Finset.range (T κ)).sum (fun i =>
        (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (9 * S.lSmooth)) *
          (psWeightProduct spsP (T κ) *
            (1 - psWeightProduct spsP (T κ))⁻¹ *
              (1 - psWeightProduct spsP (T κ))⁻¹) *
          ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
            psWeightProduct spsP i)⁻¹) ≤
      (8 / (9 * S.lSmooth)) *
        (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (T κ : ℝ)) := by
  classical
  let Tκ : ℕ := T κ
  let C : ℝ := ((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (9 * S.lSmooth)
  let R : ℝ :=
    psWeightProduct spsP Tκ *
      (1 - psWeightProduct spsP Tκ)⁻¹ *
        (1 - psWeightProduct spsP Tκ)⁻¹
  let B : ℝ := C * (2 / (Tκ : ℝ) ^ 2)
  have hTκ_pos : 0 < (Tκ : ℝ) := by exact_mod_cast hTκ
  have hC_nonneg : 0 ≤ C := by
    have hk_nonneg : 0 ≤ (κ.1 : ℝ) := by exact_mod_cast (Nat.zero_le κ.1)
    dsimp [C]
    exact div_nonneg
      (mul_nonneg hk_nonneg (sq_nonneg _))
      (mul_nonneg (by norm_num) (le_of_lt S.L_pos))
  have hratio : R ≤ 2 / (Tκ : ℝ) ^ 2 := by
    simpa [R, Tκ] using
      (sps_product_gap_square_ratio_le_two_inv_sq (T := Tκ) hTκ)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg hC_nonneg
      (div_nonneg (by norm_num) (sq_nonneg (Tκ : ℝ)))
  have hpoint : ∀ i ∈ Finset.range Tκ,
      C * R *
          ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
            psWeightProduct spsP i)⁻¹ ≤
        B *
          ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
            psWeightProduct spsP i)⁻¹ := by
    intro i _hi
    have hsps_pos : 0 < spsP ⟨i + 1, Nat.succ_pos i⟩ := by
      unfold spsP
      positivity
    have hPi_pos : 0 < psWeightProduct spsP i := by
      rw [psWeightProduct_spsP_eq i]
      positivity
    have hQinv_nonneg :
        0 ≤ ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
            psWeightProduct spsP i)⁻¹ := by
      exact le_of_lt
        (inv_pos.mpr (mul_pos (pow_pos hsps_pos 2) hPi_pos))
    have hcoeff : C * R ≤ B := by
      dsimp [B]
      exact mul_le_mul_of_nonneg_left hratio hC_nonneg
    exact mul_le_mul_of_nonneg_right hcoeff hQinv_nonneg
  have hweights := sps_inner_weight_sum_le_four_budget Tκ
  have hmul :
      B *
          (Finset.range Tκ).sum (fun i =>
            ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
              psWeightProduct spsP i)⁻¹) ≤
        B * (4 * (Tκ : ℝ)) :=
    mul_le_mul_of_nonneg_left hweights hB_nonneg
  calc
    (Finset.range (T κ)).sum (fun i =>
        (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (9 * S.lSmooth)) *
          (psWeightProduct spsP (T κ) *
            (1 - psWeightProduct spsP (T κ))⁻¹ *
              (1 - psWeightProduct spsP (T κ))⁻¹) *
          ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
            psWeightProduct spsP i)⁻¹)
        =
      (Finset.range Tκ).sum (fun i =>
        C * R *
          ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
            psWeightProduct spsP i)⁻¹) := by
          simp [Tκ, C, R]
    _ ≤
      (Finset.range Tκ).sum (fun i =>
        B *
          ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
            psWeightProduct spsP i)⁻¹) := by
          exact Finset.sum_le_sum hpoint
    _ =
      B *
          (Finset.range Tκ).sum (fun i =>
            ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
              psWeightProduct spsP i)⁻¹) := by
          rw [Finset.mul_sum]
    _ ≤ B * (4 * (Tκ : ℝ)) := hmul
    _ =
      (8 / (9 * S.lSmooth)) *
        (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (T κ : ℝ)) := by
          dsimp [B, C, Tκ]
          field_simp [ne_of_gt S.L_pos, ne_of_gt hTκ_pos]
          ring

/-- Corrected step-7 row bridge for the source `4/(9L)` linear coefficient.

The compiled checked probability scale below has an unhalved linear summand.
The source-displayed high-probability step-7 term has half of that row: applying
the coarse Eq. (8.1.52) row bound to the full row and scaling by `1/2` gives
the paper coefficient `4/(9L)`. -/
private theorem compact_probability_linear_step7_half_eq8152_row_bound
    (T : PositiveTime → ℕ) {κ : PositiveTime} (hTκ : 0 < T κ) :
    (Finset.range (T κ)).sum (fun i =>
        (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (18 * S.lSmooth)) *
          (psWeightProduct spsP (T κ) *
            (1 - psWeightProduct spsP (T κ))⁻¹ *
              (1 - psWeightProduct spsP (T κ))⁻¹) *
          ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
            psWeightProduct spsP i)⁻¹) ≤
      (4 / (9 * S.lSmooth)) *
        (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (T κ : ℝ)) := by
  classical
  have hfull :=
    compact_probability_linear_eq8152_row_bound (S := S) T (κ := κ) hTκ
  have hscaled :
      (1 / 2) *
          (Finset.range (T κ)).sum (fun i =>
            (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (9 * S.lSmooth)) *
              (psWeightProduct spsP (T κ) *
                (1 - psWeightProduct spsP (T κ))⁻¹ *
                  (1 - psWeightProduct spsP (T κ))⁻¹) *
              ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
                psWeightProduct spsP i)⁻¹) ≤
        (1 / 2) *
          ((8 / (9 * S.lSmooth)) *
            (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (T κ : ℝ))) :=
    mul_le_mul_of_nonneg_left hfull (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hleft :
      (Finset.range (T κ)).sum (fun i =>
          (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (18 * S.lSmooth)) *
            (psWeightProduct spsP (T κ) *
              (1 - psWeightProduct spsP (T κ))⁻¹ *
                (1 - psWeightProduct spsP (T κ))⁻¹) *
            ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
              psWeightProduct spsP i)⁻¹) =
        (1 / 2) *
          (Finset.range (T κ)).sum (fun i =>
            (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (9 * S.lSmooth)) *
              (psWeightProduct spsP (T κ) *
                (1 - psWeightProduct spsP (T κ))⁻¹ *
                  (1 - psWeightProduct spsP (T κ))⁻¹) *
              ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
                psWeightProduct spsP i)⁻¹) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    field_simp [ne_of_gt S.L_pos]
    ring
  have hright :
      (1 / 2) *
          ((8 / (9 * S.lSmooth)) *
            (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (T κ : ℝ))) =
        (4 / (9 * S.lSmooth)) *
          (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (T κ : ℝ)) := by
    field_simp [ne_of_gt S.L_pos]
    ring
  rw [hleft, ← hright]
  exact hscaled

/-- Formula-level sharp compact `B_p(N)` algebra after Eq. (8.1.52).

The hypotheses are exactly the compact budget-ratio facts supplied by
`compact_budget_ratio_le`.  This is the remaining source formula boundary:
ordinary FILL should prove this displayed finite-sum simplification, not
re-enter the older exact-row, concrete-formula, or common-ceiling routes. -/
theorem compact_probability_linear_step7_bp_formula_algebra_bound_of_budget
    (N : PositiveTime) (Dtilde : ℝ) (hDtilde : 0 < Dtilde)
    (T : PositiveTime → ℕ)
    (hbudget : ∀ κ : PositiveTime,
      S.sigmaSq * (κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2 / (T κ : ℝ) ≤
        Dtilde * S.lSmooth ^ 2) :
    S.sigmaSq * compactGammaWeight N *
        (Finset.range N.1).sum (fun k =>
          let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
          (4 / (9 * S.lSmooth)) *
            (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (T κ : ℝ))) ≤
      S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) * ((8 * Dtilde) / 3) := by
  -- Formula-level Corollary 8.3 step-7 algebra for the displayed
  -- `4σ²/(9L) * ∑ k(k+1)^2/T_k` contribution.
  classical
  let formulaSum : ℝ :=
    (Finset.range N.1).sum (fun k =>
      let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
      (4 / (9 * S.lSmooth)) *
        (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (T κ : ℝ)))
  have hN_pos : 0 < (N.1 : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one N.2)
  have hN1_pos : 0 < (N.1 : ℝ) + 1 := by positivity
  have hN2_pos : 0 < (N.1 : ℝ) + 2 := by positivity
  have hGamma_nonneg : 0 ≤ compactGammaWeight N := by
    unfold compactGammaWeight
    positivity
  have hcoef_nonneg : 0 ≤ 4 / (9 * S.lSmooth) := by
    exact div_nonneg (by norm_num) (mul_nonneg (by norm_num) (le_of_lt S.L_pos))
  have hrow : ∀ k ∈ Finset.range N.1,
      S.sigmaSq *
          (let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
          (4 / (9 * S.lSmooth)) *
            (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (T κ : ℝ))) ≤
        4 * Dtilde * S.lSmooth / 9 := by
    intro k _hk
    let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
    have hκ := hbudget κ
    calc
      S.sigmaSq *
          ((4 / (9 * S.lSmooth)) *
            (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (T κ : ℝ)))
          = (4 / (9 * S.lSmooth)) *
              (S.sigmaSq * (κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2 / (T κ : ℝ)) := by
            ring
      _ ≤ (4 / (9 * S.lSmooth)) * (Dtilde * S.lSmooth ^ 2) :=
            mul_le_mul_of_nonneg_left hκ hcoef_nonneg
      _ = 4 * Dtilde * S.lSmooth / 9 := by
            field_simp [ne_of_gt S.L_pos]
  have hsum :
      S.sigmaSq * formulaSum ≤ (N.1 : ℝ) * (4 * Dtilde * S.lSmooth / 9) := by
    calc
      S.sigmaSq * formulaSum
          =
        (Finset.range N.1).sum (fun k =>
          S.sigmaSq *
            (let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
            (4 / (9 * S.lSmooth)) *
              (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (T κ : ℝ)))) := by
            dsimp [formulaSum]
            rw [Finset.mul_sum]
      _ ≤ (Finset.range N.1).sum (fun _ => 4 * Dtilde * S.lSmooth / 9) := by
            exact Finset.sum_le_sum hrow
      _ = (N.1 : ℝ) * (4 * Dtilde * S.lSmooth / 9) := by
            simp [Finset.sum_const, nsmul_eq_mul, mul_comm, mul_left_comm]
  have hscaled :
      compactGammaWeight N * (S.sigmaSq * formulaSum) ≤
        compactGammaWeight N * ((N.1 : ℝ) * (4 * Dtilde * S.lSmooth / 9)) :=
    mul_le_mul_of_nonneg_left hsum hGamma_nonneg
  calc
    S.sigmaSq * compactGammaWeight N *
        (Finset.range N.1).sum (fun k =>
          let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
          (4 / (9 * S.lSmooth)) *
            (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (T κ : ℝ)))
        = compactGammaWeight N * (S.sigmaSq * formulaSum) := by
          dsimp [formulaSum]
          ring
    _ ≤ compactGammaWeight N * ((N.1 : ℝ) * (4 * Dtilde * S.lSmooth / 9)) :=
          hscaled
    _ = S.lSmooth / (((N.1 : ℝ) + 1) * ((N.1 : ℝ) + 2)) *
          ((8 * Dtilde) / 3) := by
          unfold compactGammaWeight
          field_simp [ne_of_gt hN_pos, ne_of_gt hN1_pos, ne_of_gt hN2_pos]
          ring
    _ ≤ S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) *
          ((8 * Dtilde) / 3) := by
          field_simp [ne_of_gt hN_pos, ne_of_gt hN1_pos, ne_of_gt hN2_pos]
          nlinarith [hDtilde, S.L_pos, hN_pos]

/-- Compact `B_p(N)` step-7 formula bound for the paper's compact schedule. -/
theorem compact_probability_linear_step7_bp_formula_bound
    (N : PositiveTime) (Dtilde : ℝ) (hDtilde : 0 < Dtilde) :
    S.sigmaSq * compactGammaWeight N *
        (Finset.range N.1).sum (fun k =>
          let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
          (4 / (9 * S.lSmooth)) *
            (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) /
              (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ : ℝ))) ≤
      S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) * ((8 * Dtilde) / 3) := by
  classical
  let T : PositiveTime → ℕ :=
    innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)
  have hbudget : ∀ κ : PositiveTime,
      S.sigmaSq * (κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2 / (T κ : ℝ) ≤
        Dtilde * S.lSmooth ^ 2 := by
    intro κ
    let A : ℝ := S.mGrowth ^ 2 + S.sigmaSq
    have hsig_le_A : S.sigmaSq ≤ A := by
      dsimp [A]
      nlinarith [sq_nonneg S.mGrowth]
    have hcoef_nonneg : 0 ≤ (κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2 := by
      positivity
    have hnum :
        S.sigmaSq * ((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) ≤
          A * ((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) :=
      mul_le_mul_of_nonneg_right hsig_le_A hcoef_nonneg
    have hT_real_pos : 0 < (T κ : ℝ) := by
      exact_mod_cast (compactInnerBudgetSource S Dtilde hDtilde κ).2
    have hdiv :
        S.sigmaSq * ((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (T κ : ℝ) ≤
          A * ((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (T κ : ℝ) := by
      exact div_le_div_of_nonneg_right hnum (le_of_lt hT_real_pos)
    have hbudgetA := compact_budget_ratio_le (S := S) Dtilde hDtilde κ
    have hrearrange :
        A * ((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (T κ : ℝ) =
          (S.mGrowth ^ 2 + S.sigmaSq) * (κ.1 : ℝ) *
            ((κ.1 : ℝ) + 1) ^ 2 /
              (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ : ℝ) := by
      dsimp [A, T]
      ring
    calc
      S.sigmaSq * (κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2 / (T κ : ℝ)
          = S.sigmaSq * ((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (T κ : ℝ) := by
            ring
      _ ≤ A * ((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (T κ : ℝ) := hdiv
      _ ≤ Dtilde * S.lSmooth ^ 2 := by
            simpa [hrearrange] using hbudgetA
  simpa [T] using
    compact_probability_linear_step7_bp_formula_algebra_bound_of_budget
      (S := S) N Dtilde hDtilde T hbudget

/-- Corrected source/coarser compact step-7 supplier for the paper `4/(9L)` row.

This is the compiled source route selected by the Arbiter after accounting for
the coefficient mismatch in the current checked probability-scale object: the
source row is the half-linear checked summand, then the already-proved compact
budget/Gamma formula algebra closes the public `8 * Dtilde / 3` contribution. -/
theorem compact_probability_linear_step7_half_bp_source_bound
    (N : PositiveTime) (Dtilde : ℝ) (hDtilde : 0 < Dtilde) :
    S.sigmaSq * compactGammaWeight N *
        (Finset.range N.1).sum (fun k =>
          let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
          (Finset.range
              (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ)).sum
            (fun i =>
              (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (18 * S.lSmooth)) *
                (psWeightProduct spsP
                    (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ) *
                  (1 - psWeightProduct spsP
                    (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ))⁻¹ *
                    (1 - psWeightProduct spsP
                      (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ))⁻¹) *
                ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
                  psWeightProduct spsP i)⁻¹)) ≤
      S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) * ((8 * Dtilde) / 3) := by
  classical
  let T : PositiveTime → ℕ :=
    innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)
  let halfSum : ℝ :=
    (Finset.range N.1).sum (fun k =>
      let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
      (Finset.range (T κ)).sum (fun i =>
        (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (18 * S.lSmooth)) *
          (psWeightProduct spsP (T κ) *
            (1 - psWeightProduct spsP (T κ))⁻¹ *
              (1 - psWeightProduct spsP (T κ))⁻¹) *
          ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
            psWeightProduct spsP i)⁻¹))
  let formulaSum : ℝ :=
    (Finset.range N.1).sum (fun k =>
      let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
      (4 / (9 * S.lSmooth)) *
        (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (T κ : ℝ)))
  have hrows : halfSum ≤ formulaSum := by
    dsimp [halfSum, formulaSum]
    refine Finset.sum_le_sum ?_
    intro k _hk
    let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
    have hTκ : 0 < T κ :=
      (compactInnerBudgetSource S Dtilde hDtilde κ).2
    simpa [T, κ] using
      compact_probability_linear_step7_half_eq8152_row_bound
        (S := S) T (κ := κ) hTκ
  have hscale_nonneg : 0 ≤ S.sigmaSq * compactGammaWeight N := by
    exact mul_nonneg S.sigmaSq_nonneg (by unfold compactGammaWeight; positivity)
  have hformula :
      S.sigmaSq * compactGammaWeight N * formulaSum ≤
        S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) *
          ((8 * Dtilde) / 3) := by
    simpa [formulaSum, T] using
      compact_probability_linear_step7_bp_formula_bound
        (S := S) N Dtilde hDtilde
  calc
    S.sigmaSq * compactGammaWeight N *
        (Finset.range N.1).sum (fun k =>
          let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
          (Finset.range
              (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ)).sum
            (fun i =>
              (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (18 * S.lSmooth)) *
                (psWeightProduct spsP
                    (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ) *
                  (1 - psWeightProduct spsP
                    (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ))⁻¹ *
                    (1 - psWeightProduct spsP
                      (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ))⁻¹) *
                ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
                  psWeightProduct spsP i)⁻¹))
        =
      S.sigmaSq * compactGammaWeight N * halfSum := by
        simp [halfSum, T]
    _ ≤ S.sigmaSq * compactGammaWeight N * formulaSum :=
        mul_le_mul_of_nonneg_left hrows hscale_nonneg
    _ ≤ S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) *
        ((8 * Dtilde) / 3) := hformula

/-- Corrected compact Corollary 8.3 probability scale.

This is the source-facing compact step-7 object selected by the Arbiter.  It
keeps the Theorem 8.2 square-root branch unchanged and replaces the unhalved
checked linear branch by the source-displayed half-linear `4/(9L)` branch. -/
noncomputable def compactCorrectedProbabilityScale_formulaExtension
    (xStar : FeasiblePoint S) (hcompact : IsCompact S.X)
    (N : PositiveTime) (Dtilde : ℝ) (hDtilde : 0 < Dtilde) : ℝ :=
  Real.sqrt S.sigmaSq * compactGammaWeight N *
      Real.sqrt
        (2 * bregmanEnvelope_formulaExtension S xStar hcompact *
          (Finset.range N.1).sum (fun k =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
            (Finset.range
                (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ)).sum
              (fun i =>
                let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
                (compactGamma κ *
                  psWeightProduct spsP
                    (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ) /
                  (compactGammaWeight κ *
                    (1 - psWeightProduct spsP
                      (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ)) *
                    spsP ι * psWeightProduct spsP i)) ^ 2))) +
    S.sigmaSq * compactGammaWeight N *
      (Finset.range N.1).sum (fun k =>
        let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
        (Finset.range
            (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ)).sum
          (fun i =>
            (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (18 * S.lSmooth)) *
              (psWeightProduct spsP
                  (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ) *
                (1 - psWeightProduct spsP
                  (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ))⁻¹ *
                  (1 - psWeightProduct spsP
                    (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ))⁻¹) *
              ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
                psWeightProduct spsP i)⁻¹))

/-- Compact corrected scale split and comparison with the generic Theorem 8.2
scale.

Aligns with Lan Corollary 8.3 proof step 7: the corrected compact branch uses
the source `4/(9L)` row, i.e. half of the generic Eq. (8.1.71) variance proxy
after substituting Eq. (8.1.42).  Candidates considered:
`theorem82ProbabilityScale_formulaExtension` is the generic full source scale,
`compact_stochastic_schedule_coeff_eq` supplies the compact coefficient
normalization, and `compact_probability_linear_step7_half_bp_source_bound`
supplies only the downstream public bound; none state this local split. -/
private theorem compact_probability_scale_formulaExtension_eq_corrected_add_halfBranch
    (xStar : FeasiblePoint S) (hcompact : IsCompact S.X)
    (N : PositiveTime) (Dtilde : ℝ) (hDtilde : 0 < Dtilde) :
    theorem82ProbabilityScale_formulaExtension S xStar hcompact N
        (compactBeta S (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)))
        compactGamma compactGammaWeight
        (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)) =
      compactCorrectedProbabilityScale_formulaExtension S xStar hcompact N Dtilde hDtilde +
        S.sigmaSq * compactGammaWeight N *
          (Finset.range N.1).sum (fun k =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
            (Finset.range
                (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ)).sum
              (fun i =>
                (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (18 * S.lSmooth)) *
                  (psWeightProduct spsP
                      (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ) *
                    (1 - psWeightProduct spsP
                      (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ))⁻¹ *
                      (1 - psWeightProduct spsP
                        (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ))⁻¹) *
                  ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
                    psWeightProduct spsP i)⁻¹)) := by
  classical
  let T : PositiveTime → ℕ :=
    innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)
  let halfBranch : ℝ :=
    S.sigmaSq * compactGammaWeight N *
      (Finset.range N.1).sum (fun k =>
        let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
        (Finset.range (T κ)).sum (fun i =>
          (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (18 * S.lSmooth)) *
            (psWeightProduct spsP (T κ) *
              (1 - psWeightProduct spsP (T κ))⁻¹ *
                (1 - psWeightProduct spsP (T κ))⁻¹) *
            ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
              psWeightProduct spsP i)⁻¹))
  have hquad :
      S.sigmaSq * compactGammaWeight N *
          (Finset.range N.1).sum (fun k =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
            (Finset.range (T κ)).sum (fun i =>
              let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
              compactGamma κ * psWeightProduct spsP (T κ) /
                (compactBeta S T κ * compactGammaWeight κ *
                  (1 - psWeightProduct spsP (T κ)) *
                    spsP ι ^ 2 * psWeightProduct spsP i))) =
        2 * halfBranch := by
    dsimp [halfBranch]
    have hsum_eq :
        (Finset.range N.1).sum (fun k =>
          let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
          (Finset.range (T κ)).sum (fun i =>
            let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
            compactGamma κ * psWeightProduct spsP (T κ) /
              (compactBeta S T κ * compactGammaWeight κ *
                (1 - psWeightProduct spsP (T κ)) *
                  spsP ι ^ 2 * psWeightProduct spsP i))) =
          2 * (Finset.range N.1).sum (fun k =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
            (Finset.range (T κ)).sum (fun i =>
              (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (18 * S.lSmooth)) *
                (psWeightProduct spsP (T κ) *
                  (1 - psWeightProduct spsP (T κ))⁻¹ *
                    (1 - psWeightProduct spsP (T κ))⁻¹) *
                ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
                  psWeightProduct spsP i)⁻¹)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro k _hk
      let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
      have hTκ : 0 < T κ := by
        simpa [T, innerBudgetNat, compactInnerBudgetSource] using
          compactInnerBudget_pos S Dtilde hDtilde κ
      have hcoeff :=
        compact_stochastic_schedule_coeff_eq (S := S) T (κ := κ) hTκ
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _hi
      let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
      have hgap_pos : 0 < 1 - psWeightProduct spsP (T κ) :=
        one_sub_psWeightProduct_spsP_pos_of_pos hTκ
      have hgap_ne : 1 - psWeightProduct spsP (T κ) ≠ 0 := ne_of_gt hgap_pos
      have hsps_pos : 0 < spsP ι := by
        unfold spsP
        have hi : 0 < (ι.1 : ℝ) := by exact_mod_cast ι.2
        nlinarith
      have hsps_ne : spsP ι ≠ 0 := ne_of_gt hsps_pos
      have hprod_pos : 0 < psWeightProduct spsP i := by
        rw [psWeightProduct_spsP_eq i]
        positivity
      have hprod_ne : psWeightProduct spsP i ≠ 0 := ne_of_gt hprod_pos
      have hbeta_pos : 0 < compactBeta S T κ := by
        have hP_eq : explicitP (T κ) = psWeightProduct spsP (T κ) := by
          simpa [explicitP] using (psWeightProduct_spsP_eq (T κ)).symm
        unfold compactBeta
        rw [hP_eq]
        have hnum_pos : 0 < 9 * S.lSmooth *
            (1 - psWeightProduct spsP (T κ)) := by
          exact mul_pos (mul_pos (by norm_num) S.L_pos) hgap_pos
        have hden_pos : 0 < 2 * ((κ.1 : ℝ) + 1) := by
          positivity
        exact div_pos hnum_pos hden_pos
      have hbeta_ne : compactBeta S T κ ≠ 0 := ne_of_gt hbeta_pos
      have hGamma_pos : 0 < compactGammaWeight κ := by
        unfold compactGammaWeight
        positivity
      have hGamma_ne : compactGammaWeight κ ≠ 0 := ne_of_gt hGamma_pos
      have hL_ne : S.lSmooth ≠ 0 := ne_of_gt S.L_pos
      calc
        compactGamma κ * psWeightProduct spsP (T κ) /
            (compactBeta S T κ * compactGammaWeight κ *
              (1 - psWeightProduct spsP (T κ)) *
                spsP ι ^ 2 * psWeightProduct spsP i)
            =
          (compactGamma κ / (compactBeta S T κ * compactGammaWeight κ)) *
            psWeightProduct spsP (T κ) *
            (1 - psWeightProduct spsP (T κ))⁻¹ *
            ((spsP ι) ^ 2 * psWeightProduct spsP i)⁻¹ := by
              field_simp [hbeta_ne, hGamma_ne, hgap_ne, hsps_ne, hprod_ne]
        _ =
          (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) /
              (9 * S.lSmooth * (1 - psWeightProduct spsP (T κ)))) *
            psWeightProduct spsP (T κ) *
            (1 - psWeightProduct spsP (T κ))⁻¹ *
            ((spsP ι) ^ 2 * psWeightProduct spsP i)⁻¹ := by
              rw [hcoeff]
        _ =
          2 *
            ((((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (18 * S.lSmooth)) *
              (psWeightProduct spsP (T κ) *
                (1 - psWeightProduct spsP (T κ))⁻¹ *
                  (1 - psWeightProduct spsP (T κ))⁻¹) *
              ((spsP ι) ^ 2 * psWeightProduct spsP i)⁻¹) := by
              field_simp [hgap_ne, hL_ne]
              ring
    rw [hsum_eq]
    ring
  calc
    theorem82ProbabilityScale_formulaExtension S xStar hcompact N
        (compactBeta S (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)))
        compactGamma compactGammaWeight
        (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde))
        =
      Real.sqrt S.sigmaSq * compactGammaWeight N *
          Real.sqrt
            (2 * bregmanEnvelope_formulaExtension S xStar hcompact *
              (Finset.range N.1).sum (fun k =>
                let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
                (Finset.range (T κ)).sum (fun i =>
                  let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
                  (compactGamma κ * psWeightProduct spsP (T κ) /
                    (compactGammaWeight κ *
                      (1 - psWeightProduct spsP (T κ)) *
                      spsP ι * psWeightProduct spsP i)) ^ 2))) +
        2 * halfBranch := by
          simp [theorem82ProbabilityScale_formulaExtension,
            genericProbabilityScale_formulaExtension, sigma, T, hquad]
    _ =
      compactCorrectedProbabilityScale_formulaExtension S xStar hcompact N
          Dtilde hDtilde + halfBranch := by
        simp [compactCorrectedProbabilityScale_formulaExtension, halfBranch, T]
        ring

/-- The generic compact specialization of Theorem 8.2 carries one extra
nonnegative half-branch beyond the Arbiter-selected corrected source scale.

This is a compiled same-interface obstruction certificate for the current
source-boundary issue: the generic Theorem 8.2 high-probability event is
available only at a threshold at least as large as
`compactCorrectedProbabilityScale_formulaExtension`; monotonicity of strict
tail events therefore does not turn it into the corrected smaller-threshold
event. -/
theorem compact_corrected_probability_scale_le_theorem82_formulaExtension
    (xStar : FeasiblePoint S) (hcompact : IsCompact S.X)
    (N : PositiveTime) (Dtilde : ℝ) (hDtilde : 0 < Dtilde) :
    compactCorrectedProbabilityScale_formulaExtension S xStar hcompact N Dtilde hDtilde ≤
      theorem82ProbabilityScale_formulaExtension S xStar hcompact N
        (compactBeta S (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)))
        compactGamma compactGammaWeight
        (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)) := by
  classical
  let T : PositiveTime → ℕ :=
    innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)
  let halfBranch : ℝ :=
    S.sigmaSq * compactGammaWeight N *
      (Finset.range N.1).sum (fun k =>
        let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
        (Finset.range (T κ)).sum (fun i =>
          (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (18 * S.lSmooth)) *
            (psWeightProduct spsP (T κ) *
              (1 - psWeightProduct spsP (T κ))⁻¹ *
                (1 - psWeightProduct spsP (T κ))⁻¹) *
            ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
              psWeightProduct spsP i)⁻¹))
  have hhalf_nonneg : 0 ≤ halfBranch := by
    dsimp [halfBranch]
    refine mul_nonneg (mul_nonneg S.sigmaSq_nonneg ?_) ?_
    · unfold compactGammaWeight
      positivity
    · refine Finset.sum_nonneg ?_
      intro k _hk
      let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
      refine Finset.sum_nonneg ?_
      intro i _hi
      let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
      have hTκ : 0 < T κ := by
        simpa [T, innerBudgetNat, compactInnerBudgetSource] using
          compactInnerBudget_pos S Dtilde hDtilde κ
      have hgap_nonneg : 0 ≤ 1 - psWeightProduct spsP (T κ) :=
        le_of_lt (one_sub_psWeightProduct_spsP_pos_of_pos hTκ)
      have hprod_nonneg : 0 ≤ psWeightProduct spsP (T κ) := by
        exact le_of_lt (by rw [psWeightProduct_spsP_eq (T κ)]; positivity)
      have hprod_i_nonneg : 0 ≤ psWeightProduct spsP i := by
        exact le_of_lt (by rw [psWeightProduct_spsP_eq i]; positivity)
      have hsps_nonneg : 0 ≤ spsP ι := by
        unfold spsP
        positivity
      have hcoeff_nonneg :
          0 ≤ ((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (18 * S.lSmooth) := by
        exact div_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
          (mul_nonneg (by norm_num) (le_of_lt S.L_pos))
      have hmiddle_nonneg :
          0 ≤ psWeightProduct spsP (T κ) *
              (1 - psWeightProduct spsP (T κ))⁻¹ *
                (1 - psWeightProduct spsP (T κ))⁻¹ := by
        exact mul_nonneg
          (mul_nonneg hprod_nonneg (inv_nonneg.mpr hgap_nonneg))
          (inv_nonneg.mpr hgap_nonneg)
      have hlast_nonneg :
          0 ≤ ((spsP ι) ^ 2 * psWeightProduct spsP i)⁻¹ := by
        exact inv_nonneg.mpr (mul_nonneg (sq_nonneg _) hprod_i_nonneg)
      exact mul_nonneg (mul_nonneg hcoeff_nonneg hmiddle_nonneg) hlast_nonneg
  have hfull :=
    compact_probability_scale_formulaExtension_eq_corrected_add_halfBranch
      (S := S) (xStar := xStar) (hcompact := hcompact) (N := N)
      (Dtilde := Dtilde) (hDtilde := hDtilde)
  rw [hfull]
  exact le_add_of_nonneg_right hhalf_nonneg

/-- Scalar obstruction for the corrected half-scale high-probability event.

The full Eq. (8.1.69)/(8.1.71) source assembly controls the event at
`linearScale + fullScale`.  This concrete one-point scalar model satisfies the
full master inequality and avoids both full-scale bad events, while still lying
in the corrected target event with `linearScale + halfScale`.  Thus the missing
`hcorrected_event` below is not a tactic consequence of the full Theorem 8.2
source facts; it requires an independent source correction or a statement
revision. -/
private theorem compact_corrected_half_scale_event_not_forced_by_full_source_scalar :
    ∃ (gap linear fullQuadratic Bd fullMean linearScale halfScale fullScale
        correctedScale lambda : ℝ),
      0 < lambda ∧
      0 < halfScale ∧
      fullScale = 2 * halfScale ∧
      correctedScale = linearScale + halfScale ∧
      (∀ _ω : Unit, gap ≤ Bd + linear + (fullQuadratic - fullMean)) ∧
      gap > Bd + lambda * correctedScale ∧
      ¬ linear > lambda * linearScale ∧
      ¬ fullQuadratic > fullMean + lambda * fullScale := by
  refine ⟨6, 0, 8, 0, 2, 0, 1, 2, 1, 3, ?_⟩
  norm_num

/-- Same-interface obstruction for the corrected half-master component.

Lan Eq. (8.1.69) supplies the full centered quadratic contribution.  Replacing
that full contribution by the compact corrected half contribution is a strictly
stronger pathwise assertion, not an algebraic consequence of the source master.
The scalar instance below satisfies the full master with
`fullQuadratic = 2 * halfQuadratic` and `fullMean = 2 * halfMean`, while the
half-master target used by the corrected-scale event assembly fails. -/
private theorem compact_corrected_half_master_not_forced_by_source_master_scalar :
    ∃ (gap linear fullQuadratic halfQuadratic Bd fullMean halfMean : ℝ),
      fullQuadratic = 2 * halfQuadratic ∧
      fullMean = 2 * halfMean ∧
      gap ≤ Bd + linear + (fullQuadratic - fullMean) ∧
      ¬ gap ≤ Bd + linear + (halfQuadratic - halfMean) := by
  refine ⟨(3 / 2 : ℝ), 0, 2, 1, 0, 0, 0, ?_⟩
  norm_num

/-- Quantified same-interface obstruction for the corrected component supplier.

The first open leaf in
`compact_reverse_corrected_scale_event_components_from_mds` asks for the
pathwise corrected half-master.  This theorem records that even a fully
function-valued source master with `fullQuadratic = 2 * halfQuadratic` and
`fullMean = 2 * halfMean` does not imply that leaf.  It is therefore a typed
failed attempt against the exact component interface, not merely a scalar
comment about a different public theorem. -/
private theorem compact_corrected_half_master_implication_not_forced_by_source_components :
    ¬ (∀ (gap linear fullQuadratic halfQuadratic : Unit → ℝ)
        (Bd fullMean halfMean : ℝ),
        (∀ ω, fullQuadratic ω = 2 * halfQuadratic ω) →
        fullMean = 2 * halfMean →
        (∀ ω, gap ω ≤ Bd + linear ω + (fullQuadratic ω - fullMean)) →
        ∀ ω, gap ω ≤ Bd + linear ω + (halfQuadratic ω - halfMean)) := by
  intro h
  rcases compact_corrected_half_master_not_forced_by_source_master_scalar with
    ⟨gap, linear, fullQuadratic, halfQuadratic, Bd, fullMean, halfMean,
      hquad, hmean, hfull, hnot_half⟩
  exact hnot_half
    (h (fun _ : Unit => gap) (fun _ : Unit => linear)
      (fun _ : Unit => fullQuadratic) (fun _ : Unit => halfQuadratic)
      Bd fullMean halfMean
      (by intro ω; simpa using hquad) hmean
      (by intro ω; simpa using hfull) ())

/-- Exact pathwise source issue for the corrected component supplier.

The Arbiter-selected public compact scale is the source-specialized Corollary
8.3(b) scale.  The first component required by
`compact_reverse_corrected_scale_event_components_from_mds` is stronger than the
pathwise Eq. (8.1.69) master when the latter is instantiated with the generic
Theorem 8.2 quadratic contribution and then split into two equal compact
branches.  This theorem records the failed implication at the same component
granularity as the open leaf: even with the full pathwise master and exact
`full = 2 * corrected` identities, the corrected pathwise master need not hold.

The tail component is different: halving the quadratic random variable, mean,
and scale preserves the strict Eq. (8.1.71) bad event.  Thus the source issue is
not the Markov/light-tail tail estimate, but the missing source pre-relaxation
that would justify replacing the full centered quadratic contribution in the
pathwise master by the corrected compact branch. -/
private theorem compact_corrected_half_master_component_source_issue :
    ¬ (∀ (gap linear fullQuadratic correctedQuadratic : Unit → ℝ)
        (Bd fullMean correctedMean : ℝ),
        (∀ ω, fullQuadratic ω = 2 * correctedQuadratic ω) →
        fullMean = 2 * correctedMean →
        (∀ ω, gap ω ≤ Bd + linear ω + (fullQuadratic ω - fullMean)) →
        ∀ ω, gap ω ≤ Bd + linear ω + (correctedQuadratic ω - correctedMean)) :=
  compact_corrected_half_master_implication_not_forced_by_source_components

/-- Public same-interface source/statement issue for the corrected compact
high-probability event.

The available source Theorem 8.2(c) event is typed at the full quadratic
probability scale.  This scalar certificate shows that its full-scale event
assembly does not force the compact corrected-scale event used by Corollary
8.3(b).  Thus the active public route needs an independent corrected event
theorem at `compactCorrectedProbabilityScale_formulaExtension`, or the public
statement must be corrected. -/
theorem compact_corrected_half_scale_event_source_statement_issue :
    ∃ (gap linear fullQuadratic Bd fullMean linearScale halfScale fullScale
        correctedScale lambda : ℝ),
      0 < lambda ∧
      0 < halfScale ∧
      fullScale = 2 * halfScale ∧
      correctedScale = linearScale + halfScale ∧
      (∀ _ω : Unit, gap ≤ Bd + linear + (fullQuadratic - fullMean)) ∧
      gap > Bd + lambda * correctedScale ∧
      ¬ linear > lambda * linearScale ∧
      ¬ fullQuadratic > fullMean + lambda * fullScale :=
  compact_corrected_half_scale_event_not_forced_by_full_source_scalar

/-- Public same-interface source/statement issue for the corrected compact
half-master component.

Even with exact identities saying the generic quadratic contribution and mean
are twice the corrected compact contribution and mean, the source full master
does not imply the corrected half-master.  This is the component-level reason
the failed route cannot be repaired by another wrapper around Theorem 8.2(c). -/
theorem compact_corrected_half_master_source_statement_issue :
    ¬ (∀ (gap linear fullQuadratic correctedQuadratic : Unit → ℝ)
        (Bd fullMean correctedMean : ℝ),
        (∀ ω, fullQuadratic ω = 2 * correctedQuadratic ω) →
        fullMean = 2 * correctedMean →
        (∀ ω, gap ω ≤ Bd + linear ω + (fullQuadratic ω - fullMean)) →
        ∀ ω, gap ω ≤ Bd + linear ω + (correctedQuadratic ω - correctedMean)) :=
  compact_corrected_half_master_component_source_issue

/-- Event identity for the half-scaled Eq. (8.1.71) quadratic tail.

This isolates the part of the corrected component supplier that is pure algebra:
if the generic quadratic variable, mean, and scale are exactly twice the
corrected ones, then the strict generic bad event and the strict corrected bad
event are the same set. -/
private theorem compact_corrected_half_quadratic_bad_event_eq_full
    (fullQuadratic halfQuadratic : Ω → ℝ)
    (fullMean halfMean fullScale halfScale lambda : ℝ)
    (hquad : ∀ ω, fullQuadratic ω = 2 * halfQuadratic ω)
    (hmean : fullMean = 2 * halfMean)
    (hscale : fullScale = 2 * halfScale) :
    {ω | halfQuadratic ω > halfMean + lambda * halfScale} =
      {ω | fullQuadratic ω > fullMean + lambda * fullScale} := by
  ext ω
  constructor
  · intro hω
    change fullQuadratic ω > fullMean + lambda * fullScale
    change halfQuadratic ω > halfMean + lambda * halfScale at hω
    rw [hquad ω, hmean, hscale]
    nlinarith
  · intro hω
    change halfQuadratic ω > halfMean + lambda * halfScale
    change fullQuadratic ω > fullMean + lambda * fullScale at hω
    rw [hquad ω, hmean, hscale] at hω
    nlinarith

/-- Corrected strict-event assembly from the source Eq. (8.1.69)/(8.1.70)/(8.1.71)
components.

Aligns with Lan Theorem 8.2 high-probability proof after Eq. (8.1.71): once
the pathwise master inequality is written with the corrected half-quadratic
scale, the conclusion is only the strict scalar event split and the source
union bound.  The theorem above records that this half-master is not obtained
by simply halving the source Eq. (8.1.69) quadratic term. Candidates considered:
SOptLib selection/telescope candidates
`finiteWindowSelectedOutputExpectation_eq_weighted_sum`,
`outputWindow_sum_sub_succ`, and `expectedOutput_eq_weighted_sum_div` do not
state probability event algebra; the imported Part003 helpers
`theorem82_highProbability_master_strict_event_subset_scalar` and
`theorem82_highProbability_union_bound_source_formulaExtension` match the two
pure source steps and are used here. -/
private theorem compact_reverse_corrected_scale_event_assembly_from_components
    [MeasurableSpace Ω] (P : Measure Ω)
    (gap linear halfQuadratic : Ω → ℝ)
    (Bd halfMean linearScale halfScale correctedScale lambda : ℝ)
    (hmaster :
      ∀ ω, gap ω ≤ Bd + linear ω + (halfQuadratic ω - halfMean))
    (hscale : correctedScale = linearScale + halfScale)
    (hlinear :
      P {ω | linear ω > lambda * linearScale} ≤
        ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3)))
    (hhalf :
      P {ω | halfQuadratic ω > halfMean + lambda * halfScale} ≤
        ENNReal.ofReal (Real.exp (-lambda))) :
    P {ω | gap ω > Bd + lambda * correctedScale} ≤
      ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) := by
  classical
  let target : Set Ω := {ω | gap ω > Bd + lambda * (linearScale + halfScale)}
  let linearBad : Set Ω := {ω | linear ω > lambda * linearScale}
  let halfBad : Set Ω := {ω | halfQuadratic ω > halfMean + lambda * halfScale}
  have hsubset : target ⊆ linearBad ∪ halfBad := by
    exact
      theorem82_highProbability_master_strict_event_subset_scalar
        gap linear halfQuadratic Bd halfMean linearScale halfScale lambda hmaster
  have htarget :
      {ω | gap ω > Bd + lambda * correctedScale} = target := by
    ext ω
    simp [target, hscale]
  rw [htarget]
  exact
    theorem82_highProbability_union_bound_source_formulaExtension
      P target linearBad halfBad lambda hsubset
      (by simpa [linearBad] using hlinear)
      (by simpa [halfBad] using hhalf)

/-- Public bound for the corrected compact probability scale.

The linear branch is discharged by
`compact_probability_linear_step7_half_bp_source_bound`; the unhalved checked
aggregate is not used. -/
theorem compact_reverse_probability_scale_corrected_le_public
    (xStar : FeasiblePoint S) (hcompact : IsCompact S.X)
    (N : PositiveTime) (Dtilde : ℝ) (hDtilde : 0 < Dtilde) :
    compactCorrectedProbabilityScale_formulaExtension S xStar hcompact N
        Dtilde hDtilde ≤
      S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) *
        ((8 * Dtilde) / 3 +
          (12 * Real.sqrt (2 * Dtilde *
            bregmanEnvelope_formulaExtension S xStar hcompact)) / Real.sqrt 3) := by
  classical
  let sqSum : ℝ :=
    (Finset.range N.1).sum (fun k =>
      let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
      (Finset.range
          (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ)).sum
        (fun i =>
          let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
          (compactGamma κ *
            psWeightProduct spsP
              (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ) /
            (compactGammaWeight κ *
              (1 - psWeightProduct spsP
                (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ)) *
              spsP ι * psWeightProduct spsP i)) ^ 2))
  let halfLinSum : ℝ :=
    (Finset.range N.1).sum (fun k =>
      let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
      (Finset.range
          (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ)).sum
        (fun i =>
          (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (18 * S.lSmooth)) *
            (psWeightProduct spsP
                (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ) *
              (1 - psWeightProduct spsP
                (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ))⁻¹ *
                (1 - psWeightProduct spsP
                  (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ))⁻¹) *
            ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
              psWeightProduct spsP i)⁻¹))
  let V : ℝ := bregmanEnvelope_formulaExtension S xStar hcompact
  have hGammaN_nonneg : 0 ≤ compactGammaWeight N := by
    unfold compactGammaWeight
    positivity
  have hN_pos : 0 < (N.1 : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one N.2)
  have hN1_pos : 0 < (N.1 : ℝ) + 1 := by positivity
  have hN2_pos : 0 < (N.1 : ℝ) + 2 := by positivity
  have hV_nonneg : 0 ≤ V := by
    simpa [V] using bregmanEnvelope_formulaExtension_nonneg S xStar hcompact
  have hsqSum_nonneg : 0 ≤ sqSum := by
    dsimp [sqSum]
    exact Finset.sum_nonneg (fun k _hk =>
      Finset.sum_nonneg (fun i _hi => sq_nonneg _))
  have hsquare :
      S.sigmaSq * sqSum ≤
        (2 / 3) * Dtilde * S.lSmooth ^ 2 * (N.1 : ℝ) ^ 2 := by
    simpa [sqSum] using
      compact_probability_square_checked_sum_le (S := S) N Dtilde hDtilde
  have hsqrtArg_nonneg : 0 ≤ 2 * V * sqSum := by positivity
  have hDV_nonneg : 0 ≤ Dtilde * V := mul_nonneg (le_of_lt hDtilde) hV_nonneg
  have htwoV_nonneg : 0 ≤ 2 * V := by positivity
  have hsqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_core :
      Real.sqrt S.sigmaSq * Real.sqrt (2 * V * sqSum) ≤
        2 * S.lSmooth * (N.1 : ℝ) * Real.sqrt (Dtilde * V) / Real.sqrt 3 := by
    have hright_nonneg :
        0 ≤ 2 * S.lSmooth * (N.1 : ℝ) * Real.sqrt (Dtilde * V) / Real.sqrt 3 := by
      exact div_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num) (le_of_lt S.L_pos))
            (le_of_lt hN_pos))
          (Real.sqrt_nonneg _))
        (le_of_lt hsqrt3_pos)
    have hleft_nonneg :
        0 ≤ Real.sqrt S.sigmaSq * Real.sqrt (2 * V * sqSum) := by
      positivity
    have hscaled :
        2 * V * (S.sigmaSq * sqSum) ≤
          2 * V * ((2 / 3) * Dtilde * S.lSmooth ^ 2 * (N.1 : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hsquare htwoV_nonneg
    have hsq :
        (Real.sqrt S.sigmaSq * Real.sqrt (2 * V * sqSum)) ^ 2 ≤
          (2 * S.lSmooth * (N.1 : ℝ) * Real.sqrt (Dtilde * V) / Real.sqrt 3) ^ 2 := by
      calc
        (Real.sqrt S.sigmaSq * Real.sqrt (2 * V * sqSum)) ^ 2
            = 2 * V * (S.sigmaSq * sqSum) := by
              rw [mul_pow, Real.sq_sqrt S.sigmaSq_nonneg,
                Real.sq_sqrt hsqrtArg_nonneg]
              ring
        _ ≤ 2 * V * ((2 / 3) * Dtilde * S.lSmooth ^ 2 * (N.1 : ℝ) ^ 2) :=
              hscaled
        _ = (2 * S.lSmooth * (N.1 : ℝ) *
              Real.sqrt (Dtilde * V) / Real.sqrt 3) ^ 2 := by
              rw [div_pow, mul_pow, mul_pow, mul_pow,
                Real.sq_sqrt hDV_nonneg,
                Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
              field_simp [ne_of_gt hsqrt3_pos]
    have habs := (sq_le_sq.mp hsq)
    rwa [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg] at habs
  have hsqrt_core_loose :
      Real.sqrt S.sigmaSq * Real.sqrt (2 * V * sqSum) ≤
        2 * S.lSmooth * ((N.1 : ℝ) + 1) *
          Real.sqrt (2 * Dtilde * V) / Real.sqrt 3 := by
    have hDV2 : Dtilde * V ≤ 2 * Dtilde * V := by nlinarith [hDV_nonneg]
    have hsqrt_mono : Real.sqrt (Dtilde * V) ≤ Real.sqrt (2 * Dtilde * V) :=
      Real.sqrt_le_sqrt hDV2
    have hN_le : (N.1 : ℝ) ≤ (N.1 : ℝ) + 1 := by linarith
    have hprod :
        (N.1 : ℝ) * Real.sqrt (Dtilde * V) ≤
          ((N.1 : ℝ) + 1) * Real.sqrt (2 * Dtilde * V) := by
      exact mul_le_mul hN_le hsqrt_mono (Real.sqrt_nonneg _) (by positivity)
    have hscale_nonneg : 0 ≤ 2 * S.lSmooth / Real.sqrt 3 := by
      exact div_nonneg
        (mul_nonneg (by norm_num) (le_of_lt S.L_pos))
        (le_of_lt hsqrt3_pos)
    have hscaled := mul_le_mul_of_nonneg_left hprod hscale_nonneg
    have hrewrite :
        (2 * S.lSmooth / Real.sqrt 3) *
            ((N.1 : ℝ) * Real.sqrt (Dtilde * V)) =
          2 * S.lSmooth * (N.1 : ℝ) * Real.sqrt (Dtilde * V) / Real.sqrt 3 := by
      ring
    have hrewrite' :
        (2 * S.lSmooth / Real.sqrt 3) *
            (((N.1 : ℝ) + 1) * Real.sqrt (2 * Dtilde * V)) =
          2 * S.lSmooth * ((N.1 : ℝ) + 1) *
            Real.sqrt (2 * Dtilde * V) / Real.sqrt 3 := by
      ring
    exact le_trans hsqrt_core (by simpa [hrewrite, hrewrite'] using hscaled)
  have hsqrt :
      Real.sqrt S.sigmaSq * compactGammaWeight N *
          Real.sqrt (2 * V * sqSum) ≤
        S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) *
          ((12 * Real.sqrt (2 * Dtilde * V)) / Real.sqrt 3) := by
    calc
      Real.sqrt S.sigmaSq * compactGammaWeight N *
          Real.sqrt (2 * V * sqSum)
          = compactGammaWeight N *
              (Real.sqrt S.sigmaSq * Real.sqrt (2 * V * sqSum)) := by
            ring
      _ ≤ compactGammaWeight N *
            (2 * S.lSmooth * ((N.1 : ℝ) + 1) *
              Real.sqrt (2 * Dtilde * V) / Real.sqrt 3) :=
            mul_le_mul_of_nonneg_left hsqrt_core_loose hGammaN_nonneg
      _ = S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) *
          ((12 * Real.sqrt (2 * Dtilde * V)) / Real.sqrt 3) := by
            unfold compactGammaWeight
            field_simp [ne_of_gt hN_pos, ne_of_gt hN1_pos, ne_of_gt hN2_pos,
              ne_of_gt hsqrt3_pos]
            ring
  have hlin :
      S.sigmaSq * compactGammaWeight N * halfLinSum ≤
        S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) * ((8 * Dtilde) / 3) := by
    simpa [halfLinSum] using
      compact_probability_linear_step7_half_bp_source_bound (S := S) N Dtilde hDtilde
  calc
    compactCorrectedProbabilityScale_formulaExtension S xStar hcompact N
        Dtilde hDtilde
        =
      Real.sqrt S.sigmaSq * compactGammaWeight N *
          Real.sqrt (2 * V * sqSum) +
        S.sigmaSq * compactGammaWeight N * halfLinSum := by
        simp [compactCorrectedProbabilityScale_formulaExtension, sqSum, halfLinSum, V]
    _ ≤
      S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) *
          ((12 * Real.sqrt (2 * Dtilde * V)) / Real.sqrt 3) +
        S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) *
          ((8 * Dtilde) / 3) := add_le_add hsqrt hlin
    _ =
      S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) *
        ((8 * Dtilde) / 3 +
          (12 * Real.sqrt (2 * Dtilde * V)) / Real.sqrt 3) := by
          ring

/-- Public bound for the compact generic Theorem 8.2 probability scale.

This is the full Eq. (8.1.71) scale: it keeps the Arbiter-selected
`4/(9L)` half-linear branch and adds the second half-branch required by the
source master inequality. -/
theorem compact_reverse_probability_scale_full_le_public
    (xStar : FeasiblePoint S) (hcompact : IsCompact S.X)
    (N : PositiveTime) (Dtilde : ℝ) (hDtilde : 0 < Dtilde) :
    theorem82ProbabilityScale_formulaExtension S xStar hcompact N
        (compactBeta S (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)))
        compactGamma compactGammaWeight
        (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)) ≤
      S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) *
        ((16 * Dtilde) / 3 +
          (12 * Real.sqrt (2 * Dtilde *
            bregmanEnvelope_formulaExtension S xStar hcompact)) / Real.sqrt 3) := by
  classical
  let halfLinSum : ℝ :=
    (Finset.range N.1).sum (fun k =>
      let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
      (Finset.range
          (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ)).sum
        (fun i =>
          (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (18 * S.lSmooth)) *
            (psWeightProduct spsP
                (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ) *
              (1 - psWeightProduct spsP
                (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ))⁻¹ *
                (1 - psWeightProduct spsP
                  (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ))⁻¹) *
            ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
              psWeightProduct spsP i)⁻¹))
  let halfBranch : ℝ := S.sigmaSq * compactGammaWeight N * halfLinSum
  have hsplit :
      theorem82ProbabilityScale_formulaExtension S xStar hcompact N
          (compactBeta S (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)))
          compactGamma compactGammaWeight
          (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)) =
        compactCorrectedProbabilityScale_formulaExtension S xStar hcompact N Dtilde hDtilde +
          halfBranch := by
    simpa [halfBranch, halfLinSum] using
      compact_probability_scale_formulaExtension_eq_corrected_add_halfBranch
        (S := S) (xStar := xStar) (hcompact := hcompact) (N := N)
        (Dtilde := Dtilde) (hDtilde := hDtilde)
  have hcorrected :
      compactCorrectedProbabilityScale_formulaExtension S xStar hcompact N Dtilde hDtilde ≤
        S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) *
          ((8 * Dtilde) / 3 +
            (12 * Real.sqrt (2 * Dtilde *
              bregmanEnvelope_formulaExtension S xStar hcompact)) / Real.sqrt 3) :=
    compact_reverse_probability_scale_corrected_le_public
      (S := S) xStar hcompact N Dtilde hDtilde
  have hhalf :
      halfBranch ≤
        S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) * ((8 * Dtilde) / 3) := by
    simpa [halfBranch, halfLinSum] using
      compact_probability_linear_step7_half_bp_source_bound (S := S) N Dtilde hDtilde
  calc
    theorem82ProbabilityScale_formulaExtension S xStar hcompact N
        (compactBeta S (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)))
        compactGamma compactGammaWeight
        (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde))
        = compactCorrectedProbabilityScale_formulaExtension S xStar hcompact N Dtilde hDtilde +
            halfBranch := hsplit
    _ ≤
      S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) *
          ((8 * Dtilde) / 3 +
            (12 * Real.sqrt (2 * Dtilde *
              bregmanEnvelope_formulaExtension S xStar hcompact)) / Real.sqrt 3) +
        S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) * ((8 * Dtilde) / 3) :=
        add_le_add hcorrected hhalf
    _ =
      S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) *
        ((16 * Dtilde) / 3 +
          (12 * Real.sqrt (2 * Dtilde *
            bregmanEnvelope_formulaExtension S xStar hcompact)) / Real.sqrt 3) := by
          ring

/-- Retired source-boundary statement for the exact paper-scale compact
Corollary 8.3(b) probability route.

This is intentionally a `Prop`, not a theorem.  The attempted proof route needs
the strict event at `compactCorrectedProbabilityScale_formulaExtension`, whose
quadratic branch is only half of the full Theorem 8.2(c) probability scale.  The
compiled obstruction certificates
`compact_corrected_half_scale_event_source_statement_issue` and
`compact_corrected_half_master_source_statement_issue` show that the full source
event/master does not imply this smaller corrected event/master.  Until an
independent source theorem is supplied, the executable compact high-probability
result below uses the relaxed full-scale constant instead. -/
def compact_reverse_highProbability_correctedScale_runFormulaExtension_from_mds
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (N : PositiveTime) (Dtilde lambda : ℝ)
    (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hDtilde : 0 < Dtilde) (hlambda : 0 < lambda)
    (Tsrc : PositiveTime → InnerBudget)
    (beta : PositiveTime → ℝ) (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hTsrc : Tsrc = compactInnerBudgetSource S Dtilde hDtilde)
    (hbeta_def : beta = compactBeta S (innerBudgetNat Tsrc))
    (hdenom : theorem82DenominatorAdmissible beta compactGammaWeight
      (innerBudgetNat Tsrc))
    (hrun :
      IsGeneratedSGSProcess_formulaExtension S x0 beta compactGamma
        (innerBudgetNat Tsrc) law.sample states inner)
    (hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner))
    (hxStar : IsOptimalSolution S xStar)
    (hcompact : IsCompact S.X)
    (hmds : SGSLinearMDSLightTailInterface S law ⟨xStar, hxStar.1⟩ inner hcompact)
    (hlight : sgsOracleLightTailAssumption_8_1_57 S law) :
    Prop :=
    law.P {ω | objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
          objectiveOn S ⟨xStar, hxStar.1⟩ >
        (theorem82ReverseExpectedBound_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
            hcompact N beta compactGamma compactGammaWeight Tsrc hdenom +
          lambda *
            compactCorrectedProbabilityScale_formulaExtension S ⟨xStar, hxStar.1⟩
              hcompact N Dtilde hDtilde)} ≤
      ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda))

/-- Source issue marker for the selected-run source-boundary statement with the
exact corrected compact scale.

This statement remains as a source issue marker only.  The selected public
compact theorem below now proves the relaxed full-scale result directly from
Theorem 8.2(c); it does not consume this corrected half-scale boundary. -/
def compact_reverse_highProbability_correctedScale_selectedSourceBoundary
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (N : PositiveTime) (Dtilde lambda : ℝ)
    (hDtilde : 0 < Dtilde) (hlambda : 0 < lambda)
    (Tsrc : PositiveTime → InnerBudget)
    (beta : PositiveTime → ℝ) (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hTsrc : Tsrc = compactInnerBudgetSource S Dtilde hDtilde)
    (hbeta_def : beta = compactBeta S (innerBudgetNat Tsrc))
    (hdenom : theorem82DenominatorAdmissible beta compactGammaWeight
      (innerBudgetNat Tsrc))
    (hindep : sfoIndependent S law.P law.sample
      (sgsSelectedOracleQuery S x0 beta hbeta compactGamma compactGamma_mem_Icc
        (innerBudgetNat Tsrc) law.sample))
    (hxStar : IsOptimalSolution S xStar)
    (hcompact : IsCompact S.X)
    (hlight : sgsOracleLightTailAssumption_8_1_57 S law) :
    Prop :=
    sgsSelectedOutputGapStrictTailProbability S law x0 beta hbeta
        compactGamma compactGamma_mem_Icc (innerBudgetNat Tsrc) N xStar hxStar
        (theorem82ReverseExpectedBound_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
            hcompact N beta compactGamma compactGammaWeight Tsrc hdenom +
          lambda *
            compactCorrectedProbabilityScale_formulaExtension S ⟨xStar, hxStar.1⟩
              hcompact N Dtilde hDtilde)
        hindep ≤
      ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda))




/-- Fixed-horizon scalar simplification of the checked Theorem 8.2(a) bound.

Aligns with Lan Eq. (8.1.78).  Candidate audit: considered
`theorem82ExpectedBound_checked_eq_formulaExtension`,
`checkedQuotient_def`, `psWeightProduct_spsP_eq`,
`sps_step_weight_inv_eq`, `sps_normalized_weight_sum_eq_one`, and SOptLib
finite-window/telescope candidates; the existing lemmas expose quotient and SPS
normalizations but do not combine the fixed-horizon ceiling budget with the
displayed Corollary 8.3(a) scalar constants. -/
theorem fixed_horizon_expected_checked_bound_le_public
    (x0 xStar : FeasiblePoint S) (N : PositiveTime) (Dtilde : ℝ)
    (hDtilde : 0 < Dtilde)
    (hdenom : theorem82DenominatorAdmissible (fixedHorizonBeta S)
      fixedHorizonGammaWeight
      (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde))) :
    theorem82ExpectedBound_checkedFormulaExtension S x0 xStar N
        (fixedHorizonBeta S) fixedHorizonGamma fixedHorizonGammaWeight
        (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) hdenom ≤
      (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
        (3 * bregmanFormulaOnX S x0 xStar + 4 * Dtilde) := by
  rw [theorem82ExpectedBound_checked_eq_formulaExtension]
  unfold theorem82ExpectedBound_formulaExtension genericExpectedBound_formulaExtension
  have hfirst :
      fixedHorizonGammaWeight N * fixedHorizonBeta S oneTime *
          (1 - psWeightProduct spsP
            (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) oneTime))⁻¹ *
          bregmanFormulaOnX S x0 xStar ≤
        (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
          (3 * bregmanFormulaOnX S x0 xStar) :=
    fixed_horizon_initial_bregman_term_le (S := S) x0 xStar N Dtilde hDtilde
  have hstoch :
      fixedHorizonGammaWeight N *
          (Finset.range N.1).sum (fun k =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
            (Finset.range
                (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)).sum
              (fun i =>
                let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
                (S.mGrowth ^ 2 + S.sigmaSq) * fixedHorizonGamma κ *
                    psWeightProduct spsP
                      (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ) /
                  (fixedHorizonBeta S κ * fixedHorizonGammaWeight κ *
                    (1 - psWeightProduct spsP
                      (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)) *
                    spsP ι ^ 2 * psWeightProduct spsP i))) ≤
        (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) * (4 * Dtilde) := by
    have houter :=
      fixed_horizon_stochastic_outer_sum_le_four_Dtilde_L (S := S)
        N Dtilde hDtilde
    have hGammaN_nonneg : 0 ≤ fixedHorizonGammaWeight N := by
      unfold fixedHorizonGammaWeight
      positivity
    calc
      fixedHorizonGammaWeight N *
          (Finset.range N.1).sum (fun k =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
            (Finset.range
                (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)).sum
              (fun i =>
                let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
                (S.mGrowth ^ 2 + S.sigmaSq) * fixedHorizonGamma κ *
                    psWeightProduct spsP
                      (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ) /
                  (fixedHorizonBeta S κ * fixedHorizonGammaWeight κ *
                    (1 - psWeightProduct spsP
                      (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)) *
                    spsP ι ^ 2 * psWeightProduct spsP i)))
          ≤ fixedHorizonGammaWeight N * (4 * Dtilde * S.lSmooth) :=
            mul_le_mul_of_nonneg_left houter hGammaN_nonneg
      _ =
        (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) * (4 * Dtilde) := by
          unfold fixedHorizonGammaWeight
          have hN_pos : 0 < (N.1 : ℝ) := by
            exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one N.2)
          have hN1_pos : 0 < (N.1 : ℝ) + 1 := by positivity
          field_simp [ne_of_gt hN_pos, ne_of_gt hN1_pos]
  calc
    fixedHorizonGammaWeight N * fixedHorizonBeta S oneTime *
          (1 - psWeightProduct spsP
            (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) oneTime))⁻¹ *
          bregmanFormulaOnX S x0 xStar +
        fixedHorizonGammaWeight N *
          (Finset.range N.1).sum (fun k =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
            (Finset.range
                (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)).sum
              (fun i =>
                let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
                (S.mGrowth ^ 2 + S.sigmaSq) * fixedHorizonGamma κ *
                    psWeightProduct spsP
                      (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ) /
                  (fixedHorizonBeta S κ * fixedHorizonGammaWeight κ *
                    (1 - psWeightProduct spsP
                      (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)) *
                    spsP ι ^ 2 * psWeightProduct spsP i)))
        ≤ (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
            (3 * bregmanFormulaOnX S x0 xStar) +
          (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) * (4 * Dtilde) :=
          add_le_add hfirst hstoch
    _ = (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
        (3 * bregmanFormulaOnX S x0 xStar + 4 * Dtilde) := by
          ring

/-- Public source-boundary Corollary 8.3(a), expected fixed-horizon form.

Book JSON citation:
`book/FOML/StochasticGradientSliding.json:main_theorem.statement_math` states
the fixed-horizon expected bound for the SGS output `\bar{x}_N`, namely
`E[Ψ(\bar{x}_N)-Ψ(x*)]≤2L/(N(N+1))[3V(x_0,x*)+4\tilde D]`.

This uses the generated SGS run, the paper's positive inner budgets from
Eq. (8.1.72), and the paper expectation wrapper `expectedOutputGap`.  The
displayed Bregman term remains the explicit feasible-pair formula extension
until the Section 3.2 `X` versus `X^o` boundary is resolved.  Downstream Phase 2
instruction: prove as corrected feasible-Bregman Corollary 8.3(a), not as the
A-level original source-typed corollary. -/
theorem Corollary8_3_fixedHorizon_expected_sourceBoundary_feasibleBregman
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (N : PositiveTime) (Dtilde : ℝ)
    (hDtilde : 0 < Dtilde)
    (hindep : sfoIndependent S law.P law.sample
      (sgsSelectedOracleQuery S x0 (fixedHorizonBeta S) (fixedHorizonBeta_pos S)
        fixedHorizonGamma fixedHorizonGamma_mem_Icc
        (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde)) law.sample))
    (hxStar : IsOptimalSolution S xStar) :
    sgsSelectedExpectedOutputGap S law x0 (fixedHorizonBeta S)
        (fixedHorizonBeta_pos S) fixedHorizonGamma fixedHorizonGamma_mem_Icc
        (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde))
        N xStar hxStar hindep ≤
      (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
        (3 * bregmanFormulaOnX S x0 ⟨xStar, hxStar.1⟩ + 4 * Dtilde) := by
  have hconds := fixed_horizon_outer_conditions (S := S) N Dtilde hDtilde
  rcases hconds with ⟨hlower, hGamma, hmono⟩
  have hgeneric :=
    SGSGenericConvergence_Theorem8_2_expected_selectedRealizationExtension_feasibleBregman
      (S := S) (law := law) (x0 := x0) (xStar := xStar)
      (beta := fixedHorizonBeta S) (gamma := fixedHorizonGamma)
      (Gamma := fixedHorizonGammaWeight)
      (T := fixedHorizonInnerBudgetSource S N Dtilde hDtilde)
      (N := N) (hbeta := fixedHorizonBeta_pos S)
      (hgamma := fixedHorizonGamma_mem_Icc) (hxStar := hxStar)
      (hlower := hlower) (hGamma := hGamma) (hindep := hindep)
      (hmono := hmono)
  have hdenom :
      theorem82DenominatorAdmissible (fixedHorizonBeta S)
        fixedHorizonGammaWeight
        (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde)) :=
    theorem82DenominatorAdmissible_forward_source_obligation S
      (fixedHorizonBeta S) fixedHorizonGamma fixedHorizonGammaWeight
      (fixedHorizonInnerBudgetSource S N Dtilde hDtilde)
      (fixedHorizonBeta_pos S) hlower hGamma hmono
  have hscalar :=
    fixed_horizon_expected_checked_bound_le_public (S := S) x0
      ⟨xStar, hxStar.1⟩ N Dtilde hDtilde hdenom
  exact le_trans hgeneric hscalar

/-- Strict selected output-gap tail probabilities are antitone in the threshold.

This is the route-local event transport needed after Theorem 8.2(b) is applied
at its checked threshold.  Candidate audit: considered SOptLib strict-tail
finite-sum expansion helpers and target-file raw tail wrappers; they expand
selected probabilities but do not state this one-step threshold monotonicity, so
the proof directly unfolds the local strict event and uses `measure_mono`. -/
theorem sgs_selected_strict_tail_probability_antitone_threshold
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (beta gamma : PositiveTime → ℝ) (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma) (T : PositiveTime → ℕ)
    (N : PositiveTime) (hxStar : IsOptimalSolution S xStar)
    (threshold₁ threshold₂ : ℝ)
    (hindep : sfoIndependent S law.P law.sample
      (sgsSelectedOracleQuery S x0 beta hbeta gamma hgamma T law.sample))
    (hthreshold : threshold₁ ≤ threshold₂) :
    sgsSelectedOutputGapStrictTailProbability S law x0 beta hbeta gamma hgamma
        T N xStar hxStar threshold₂ hindep ≤
      sgsSelectedOutputGapStrictTailProbability S law x0 beta hbeta gamma hgamma
        T N xStar hxStar threshold₁ hindep := by
  unfold sgsSelectedOutputGapStrictTailProbability outputGapStrictTailProbability
    outputGapStrictTailProbabilityRaw outputGapStrictTailEvent
  exact measure_mono (by
    intro ω hω
    change
      outputGapRandomVariable S
          (sgsSelectedStates S x0 beta hbeta gamma hgamma T law.sample)
          N xStar hxStar ω > threshold₁
    change
      outputGapRandomVariable S
          (sgsSelectedStates S x0 beta hbeta gamma hgamma T law.sample)
          N xStar hxStar ω > threshold₂ at hω
    exact lt_of_le_of_lt hthreshold hω)

/-- Public source-boundary Corollary 8.3(a), high-probability fixed-horizon
form.

Book JSON citation:
`book/FOML/StochasticGradientSliding.json:main_theorem.statement_math` states
the fixed-horizon high-probability bound and the paper's light-tail assumption.

Downstream Phase 2 instruction: prove as corrected feasible-Bregman
Corollary 8.3(a) high-probability form; do not treat the feasible envelope as the
original source-typed `\bar V` until the domain bridge is supplied. -/
theorem Corollary8_3_fixedHorizon_highProbability_sourceBoundary_feasibleBregman
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (N : PositiveTime)
    (Dtilde lambda : ℝ)
    (hDtilde : 0 < Dtilde) (hlambda : 0 < lambda)
    (hindep : sfoIndependent S law.P law.sample
      (sgsSelectedOracleQuery S x0 (fixedHorizonBeta S) (fixedHorizonBeta_pos S)
        fixedHorizonGamma fixedHorizonGamma_mem_Icc
        (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde)) law.sample))
    (hxStar : IsOptimalSolution S xStar)
    (hcompact : IsCompact S.X)
    (hlight : sgsOracleLightTailAssumption_8_1_57 S law) :
    sgsSelectedOutputGapStrictTailProbability S law x0 (fixedHorizonBeta S)
        (fixedHorizonBeta_pos S) fixedHorizonGamma fixedHorizonGamma_mem_Icc
        (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde))
        N xStar hxStar
        ((2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
          (3 * bregmanFormulaOnX S x0 ⟨xStar, hxStar.1⟩ +
            4 * (1 + lambda) * Dtilde +
            (4 * lambda *
                Real.sqrt (Dtilde *
                  bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact)) /
              Real.sqrt 3))
        hindep ≤
      ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) := by
  classical
  let T : PositiveTime → InnerBudget :=
    fixedHorizonInnerBudgetSource S N Dtilde hDtilde
  have hconds := fixed_horizon_outer_conditions (S := S) N Dtilde hDtilde
  rcases hconds with ⟨hlower, hGamma, hmono⟩
  have hdenom :
      theorem82DenominatorAdmissible (fixedHorizonBeta S)
        fixedHorizonGammaWeight (innerBudgetNat T) :=
    theorem82DenominatorAdmissible_forward_source_obligation S
      (fixedHorizonBeta S) fixedHorizonGamma fixedHorizonGammaWeight T
      (fixedHorizonBeta_pos S) hlower hGamma hmono
  let checkedThreshold : ℝ :=
    theorem82ExpectedBound_checkedFormulaExtension S x0 ⟨xStar, hxStar.1⟩ N
        (fixedHorizonBeta S) fixedHorizonGamma fixedHorizonGammaWeight T hdenom +
      lambda *
        theorem82ProbabilityScale_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
          hcompact N (fixedHorizonBeta S) fixedHorizonGamma fixedHorizonGammaWeight
          T hdenom
  let publicThreshold : ℝ :=
    (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
      (3 * bregmanFormulaOnX S x0 ⟨xStar, hxStar.1⟩ +
        4 * (1 + lambda) * Dtilde +
        (4 * lambda *
            Real.sqrt (Dtilde *
              bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact)) /
          Real.sqrt 3)
  change
    sgsSelectedOutputGapStrictTailProbability S law x0 (fixedHorizonBeta S)
        (fixedHorizonBeta_pos S) fixedHorizonGamma fixedHorizonGamma_mem_Icc
        (innerBudgetNat T) N xStar hxStar publicThreshold hindep ≤
      ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda))
  have hgeneric :
      sgsSelectedOutputGapStrictTailProbability S law x0 (fixedHorizonBeta S)
          (fixedHorizonBeta_pos S) fixedHorizonGamma fixedHorizonGamma_mem_Icc
          (innerBudgetNat T) N xStar hxStar checkedThreshold hindep ≤
        ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) := by
    dsimp [checkedThreshold, T]
    exact
      SGSGenericConvergence_Theorem8_2_highProbability_selectedRealizationExtension_feasibleBregman
        (S := S) (law := law) (x0 := x0) (xStar := xStar)
        (beta := fixedHorizonBeta S) (gamma := fixedHorizonGamma)
        (Gamma := fixedHorizonGammaWeight)
        (T := fixedHorizonInnerBudgetSource S N Dtilde hDtilde)
        (N := N) (lambda := lambda)
        (hbeta := fixedHorizonBeta_pos S)
        (hgamma := fixedHorizonGamma_mem_Icc)
        (hlambda := hlambda) (hxStar := hxStar) (hlight := hlight)
        (hlower := hlower) (hGamma := hGamma) (hindep := hindep)
        (hmono := hmono) (hcompact := hcompact)
  have hexpected :
      theorem82ExpectedBound_checkedFormulaExtension S x0 ⟨xStar, hxStar.1⟩ N
          (fixedHorizonBeta S) fixedHorizonGamma fixedHorizonGammaWeight T hdenom ≤
        (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
          (3 * bregmanFormulaOnX S x0 ⟨xStar, hxStar.1⟩ + 4 * Dtilde) := by
    dsimp [T] at hdenom ⊢
    exact
      fixed_horizon_expected_checked_bound_le_public (S := S) x0
        ⟨xStar, hxStar.1⟩ N Dtilde hDtilde hdenom
  have hscale :
      theorem82ProbabilityScale_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
          hcompact N (fixedHorizonBeta S) fixedHorizonGamma fixedHorizonGammaWeight
          T hdenom ≤
        (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
          (4 * Dtilde +
            (4 * Real.sqrt (Dtilde *
              bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact)) /
              Real.sqrt 3) := by
    dsimp [T] at hdenom ⊢
    exact
      fixed_horizon_probability_scale_checked_le_public (S := S)
        ⟨xStar, hxStar.1⟩ hcompact N Dtilde hDtilde hdenom
  have hthreshold : checkedThreshold ≤ publicThreshold := by
    dsimp [checkedThreshold, publicThreshold]
    have hlambda_nonneg : 0 ≤ lambda := le_of_lt hlambda
    have hscale_mul :=
      mul_le_mul_of_nonneg_left hscale hlambda_nonneg
    calc
      theorem82ExpectedBound_checkedFormulaExtension S x0 ⟨xStar, hxStar.1⟩ N
            (fixedHorizonBeta S) fixedHorizonGamma fixedHorizonGammaWeight T hdenom +
          lambda *
            theorem82ProbabilityScale_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
              hcompact N (fixedHorizonBeta S) fixedHorizonGamma fixedHorizonGammaWeight
              T hdenom
          ≤
        (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
            (3 * bregmanFormulaOnX S x0 ⟨xStar, hxStar.1⟩ + 4 * Dtilde) +
          lambda *
            ((2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
              (4 * Dtilde +
                (4 * Real.sqrt (Dtilde *
                  bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact)) /
                  Real.sqrt 3)) := add_le_add hexpected hscale_mul
      _ =
        (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
          (3 * bregmanFormulaOnX S x0 ⟨xStar, hxStar.1⟩ +
            4 * (1 + lambda) * Dtilde +
            (4 * lambda *
                Real.sqrt (Dtilde *
                  bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact)) /
              Real.sqrt 3) := by
            ring
  have hmonoTail :
      sgsSelectedOutputGapStrictTailProbability S law x0 (fixedHorizonBeta S)
          (fixedHorizonBeta_pos S) fixedHorizonGamma fixedHorizonGamma_mem_Icc
          (innerBudgetNat T) N xStar hxStar publicThreshold hindep ≤
        sgsSelectedOutputGapStrictTailProbability S law x0 (fixedHorizonBeta S)
          (fixedHorizonBeta_pos S) fixedHorizonGamma fixedHorizonGamma_mem_Icc
          (innerBudgetNat T) N xStar hxStar checkedThreshold hindep :=
    sgs_selected_strict_tail_probability_antitone_threshold (S := S)
      (law := law) (x0 := x0) (xStar := xStar)
      (beta := fixedHorizonBeta S) (gamma := fixedHorizonGamma)
      (hbeta := fixedHorizonBeta_pos S) (hgamma := fixedHorizonGamma_mem_Icc)
      (T := innerBudgetNat T) (N := N) (hxStar := hxStar)
      (threshold₁ := checkedThreshold) (threshold₂ := publicThreshold)
      (hindep := hindep) hthreshold
  exact le_trans hmonoTail hgeneric

/-- Public source-boundary Corollary 8.3(b), expected compact-policy form.

Book JSON citation:
`book/FOML/StochasticGradientSliding.json:main_theorem.statement_math` states
the compact-policy expected bound under compactness,
`E[Ψ(\bar{x}_N)-Ψ(x*)]≤L/((N+1)(N+2))[27\bar V(x*)/2+16\tilde D/3]`.

Downstream Phase 2 instruction: prove as corrected feasible-Bregman
Corollary 8.3(b), not as the A-level original source-typed corollary. -/
theorem Corollary8_3_compact_expected_sourceBoundary_feasibleBregman
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (N : PositiveTime) (Dtilde : ℝ)
    (hDtilde : 0 < Dtilde)
    (hindep : sfoIndependent S law.P law.sample
      (sgsSelectedOracleQuery S x0
        (compactBeta S (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)))
        (by
          intro k
          simpa [innerBudgetNat] using compactBeta_innerBudget_pos S Dtilde hDtilde k)
        compactGamma compactGamma_mem_Icc
        (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)) law.sample))
    (hxStar : IsOptimalSolution S xStar)
    (hcompact : IsCompact S.X) :
    sgsSelectedExpectedOutputGap S law x0
        (compactBeta S (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)))
        (by
          intro k
          simpa [innerBudgetNat] using compactBeta_innerBudget_pos S Dtilde hDtilde k)
        compactGamma compactGamma_mem_Icc
        (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde))
        N xStar hxStar hindep ≤
      S.lSmooth / (((N.1 : ℝ) + 1) * ((N.1 : ℝ) + 2)) *
        ((27 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact) / 2 +
          (16 * Dtilde) / 3) := by
  classical
  let Tsrc : PositiveTime → InnerBudget := compactInnerBudgetSource S Dtilde hDtilde
  let beta : PositiveTime → ℝ := compactBeta S (innerBudgetNat Tsrc)
  have hbeta : ∀ k : PositiveTime, 0 < beta k := by
    intro k
    simpa [beta, Tsrc, innerBudgetNat, compactInnerBudgetSource] using
      compactBeta_innerBudget_pos S Dtilde hDtilde k
  rcases compact_policy_outer_conditions (S := S) Dtilde hDtilde with
    ⟨hlower, hGamma, hmono⟩
  have hdenom :
      theorem82DenominatorAdmissible beta compactGammaWeight (innerBudgetNat Tsrc) :=
    theorem82DenominatorAdmissible_reverse_source_obligation S beta compactGamma
      compactGammaWeight Tsrc hbeta
      (by simpa [beta, Tsrc] using hlower) hGamma
      (by simpa [beta, Tsrc] using hmono)
  have hgeneric :
      sgsSelectedExpectedOutputGap S law x0 beta hbeta compactGamma compactGamma_mem_Icc
          (innerBudgetNat Tsrc) N xStar hxStar
          (by simpa [beta, Tsrc] using hindep) ≤
        theorem82ReverseExpectedBound_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
          hcompact N beta compactGamma compactGammaWeight Tsrc hdenom := by
    have hraw :=
      SGSGenericConvergence_Theorem8_2_reverse_expected_selectedRealizationExtension_feasibleBregman
        (S := S) (law := law) (x0 := x0) (xStar := xStar)
        (beta := beta) (gamma := compactGamma) (Gamma := compactGammaWeight)
        (T := Tsrc) (N := N) hbeta compactGamma_mem_Icc hxStar hcompact
        (by simpa [beta, Tsrc] using hlower) hGamma
        (by simpa [beta, Tsrc] using hindep)
        (by simpa [beta, Tsrc] using hmono)
    simpa [theorem82ReverseExpectedBound_checkedFormulaExtension, beta, Tsrc] using hraw
  have hscalar :
      theorem82ReverseExpectedBound_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
          hcompact N beta compactGamma compactGammaWeight Tsrc hdenom ≤
        S.lSmooth / (((N.1 : ℝ) + 1) * ((N.1 : ℝ) + 2)) *
          ((27 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact) / 2 +
            (16 * Dtilde) / 3) := by
    simpa [beta, Tsrc] using
      compact_reverse_expected_checked_bound_le_public (S := S)
        ⟨xStar, hxStar.1⟩ hcompact N Dtilde hDtilde hdenom
  exact le_trans (by simpa [beta, Tsrc] using hgeneric) hscalar

/-- Public source-boundary relaxed Corollary 8.3(b), high-probability compact-policy
form.

Book JSON citation:
`book/FOML/StochasticGradientSliding.json:main_theorem.statement_math` states
the compact-policy high-probability bound and the paper's light-tail assumption.

The exact paper constant route would require the corrected half probability
scale `compactCorrectedProbabilityScale_formulaExtension`.  The source issue
certificates above show that this smaller event is not implied by the full
Theorem 8.2(c) event/master.  This theorem therefore records the proved
full-scale relaxation:
the paper's `8 * (2 + lambda) * Dtilde / 3` is replaced by
`16 * (1 + lambda) * Dtilde / 3`. -/
theorem Corollary8_3_compact_highProbability_sourceBoundary_feasibleBregman
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (N : PositiveTime)
    (Dtilde lambda : ℝ)
    (hDtilde : 0 < Dtilde) (hlambda : 0 < lambda)
    (hindep : sfoIndependent S law.P law.sample
      (sgsSelectedOracleQuery S x0
        (compactBeta S (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)))
        (by
          intro k
          simpa [innerBudgetNat] using compactBeta_innerBudget_pos S Dtilde hDtilde k)
        compactGamma compactGamma_mem_Icc
        (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)) law.sample))
    (hxStar : IsOptimalSolution S xStar)
    (hcompact : IsCompact S.X)
    (hlight : sgsOracleLightTailAssumption_8_1_57 S law) :
    sgsSelectedOutputGapStrictTailProbability S law x0
        (compactBeta S (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)))
        (by
          intro k
          simpa [innerBudgetNat] using compactBeta_innerBudget_pos S Dtilde hDtilde k)
        compactGamma compactGamma_mem_Icc
        (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde))
        N xStar hxStar
        (S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) *
          ((27 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact) / 2 +
            (16 * (1 + lambda) * Dtilde) / 3 +
              (12 * lambda *
                  Real.sqrt (2 * Dtilde *
                    bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact)) /
                Real.sqrt 3))
        hindep ≤
      ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) := by
  classical
  let Tsrc : PositiveTime → InnerBudget := compactInnerBudgetSource S Dtilde hDtilde
  let beta : PositiveTime → ℝ := compactBeta S (innerBudgetNat Tsrc)
  have hbeta : ∀ k : PositiveTime, 0 < beta k := by
    intro k
    simpa [beta, Tsrc, innerBudgetNat, compactInnerBudgetSource] using
      compactBeta_innerBudget_pos S Dtilde hDtilde k
  rcases compact_policy_outer_conditions (S := S) Dtilde hDtilde with
    ⟨hlower, hGamma, hmono⟩
  have hdenom :
      theorem82DenominatorAdmissible beta compactGammaWeight (innerBudgetNat Tsrc) :=
    theorem82DenominatorAdmissible_reverse_source_obligation S beta compactGamma
      compactGammaWeight Tsrc hbeta
      (by simpa [beta, Tsrc] using hlower) hGamma
      (by simpa [beta, Tsrc] using hmono)
  let checkedThreshold : ℝ :=
    theorem82ReverseExpectedBound_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
        hcompact N beta compactGamma compactGammaWeight Tsrc hdenom +
      lambda *
        theorem82ProbabilityScale_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
          hcompact N beta compactGamma compactGammaWeight Tsrc hdenom
  let publicThreshold : ℝ :=
    S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) *
      ((27 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact) / 2 +
        (16 * (1 + lambda) * Dtilde) / 3 +
          (12 * lambda *
              Real.sqrt (2 * Dtilde *
                bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact)) /
            Real.sqrt 3)
  change
    sgsSelectedOutputGapStrictTailProbability S law x0 beta hbeta
        compactGamma compactGamma_mem_Icc (innerBudgetNat Tsrc)
        N xStar hxStar publicThreshold
        (by simpa [beta, Tsrc] using hindep) ≤
      ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda))
  have hgeneric :
      sgsSelectedOutputGapStrictTailProbability S law x0 beta hbeta
          compactGamma compactGamma_mem_Icc (innerBudgetNat Tsrc)
          N xStar hxStar checkedThreshold
          (by simpa [beta, Tsrc] using hindep) ≤
        ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) := by
    dsimp [checkedThreshold]
    exact
      SGSGenericConvergence_Theorem8_2_reverse_highProbability_selectedRealizationExtension_feasibleBregman
        (S := S) (law := law) (x0 := x0) (xStar := xStar)
        (beta := beta) (gamma := compactGamma) (Gamma := compactGammaWeight)
        (T := Tsrc) (N := N) (lambda := lambda)
        (hbeta := hbeta) (hgamma := compactGamma_mem_Icc)
        (hlambda := hlambda) (hxStar := hxStar) (hcompact := hcompact)
        (hlight := hlight) (hlower := by simpa [beta, Tsrc] using hlower)
        (hGamma := hGamma) (hindep := by simpa [beta, Tsrc] using hindep)
        (hmono := by simpa [beta, Tsrc] using hmono)
  have hexpected_raw :
      theorem82ReverseExpectedBound_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
          hcompact N beta compactGamma compactGammaWeight Tsrc hdenom ≤
        S.lSmooth / (((N.1 : ℝ) + 1) * ((N.1 : ℝ) + 2)) *
          ((27 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact) / 2 +
            (16 * Dtilde) / 3) := by
    simpa [beta, Tsrc] using
      compact_reverse_expected_checked_bound_le_public (S := S)
        ⟨xStar, hxStar.1⟩ hcompact N Dtilde hDtilde hdenom
  have hexpected :
      theorem82ReverseExpectedBound_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
          hcompact N beta compactGamma compactGammaWeight Tsrc hdenom ≤
        S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) *
          ((27 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact) / 2 +
            (16 * Dtilde) / 3) := by
    let B : ℝ :=
      (27 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact) / 2 +
        (16 * Dtilde) / 3
    have hB_nonneg : 0 ≤ B := by
      have hV_nonneg :
          0 ≤ bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact :=
        bregmanEnvelope_formulaExtension_nonneg S ⟨xStar, hxStar.1⟩ hcompact
      dsimp [B]
      nlinarith [hV_nonneg, hDtilde]
    have hN_pos : 0 < (N.1 : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one N.2)
    have hN1_pos : 0 < (N.1 : ℝ) + 1 := by positivity
    have hN2_pos : 0 < (N.1 : ℝ) + 2 := by positivity
    have hden0_pos : 0 < (N.1 : ℝ) * ((N.1 : ℝ) + 2) :=
      mul_pos hN_pos hN2_pos
    have hden1_pos : 0 < (((N.1 : ℝ) + 1) * ((N.1 : ℝ) + 2)) :=
      mul_pos hN1_pos hN2_pos
    have hfactor :
        S.lSmooth / (((N.1 : ℝ) + 1) * ((N.1 : ℝ) + 2)) ≤
          S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) := by
      rw [div_le_div_iff₀ hden1_pos hden0_pos]
      nlinarith [S.L_pos, hN_pos, hN2_pos]
    exact le_trans hexpected_raw
      (by
        simpa [B] using mul_le_mul_of_nonneg_right hfactor hB_nonneg)
  have hscale :
      theorem82ProbabilityScale_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
          hcompact N beta compactGamma compactGammaWeight Tsrc hdenom ≤
        S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) *
          ((16 * Dtilde) / 3 +
            (12 * Real.sqrt (2 * Dtilde *
              bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact)) /
              Real.sqrt 3) := by
    rw [theorem82ProbabilityScale_checked_eq_formulaExtension
      S ⟨xStar, hxStar.1⟩ hcompact N beta compactGamma compactGammaWeight
      Tsrc hdenom]
    simpa [beta, Tsrc] using
      compact_reverse_probability_scale_full_le_public (S := S)
        ⟨xStar, hxStar.1⟩ hcompact N Dtilde hDtilde
  have hthreshold : checkedThreshold ≤ publicThreshold := by
    dsimp [checkedThreshold, publicThreshold]
    have hlambda_nonneg : 0 ≤ lambda := le_of_lt hlambda
    have hscale_mul :=
      mul_le_mul_of_nonneg_left hscale hlambda_nonneg
    calc
      theorem82ReverseExpectedBound_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
            hcompact N beta compactGamma compactGammaWeight Tsrc hdenom +
          lambda *
            theorem82ProbabilityScale_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
              hcompact N beta compactGamma compactGammaWeight Tsrc hdenom
          ≤
        S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) *
            ((27 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact) / 2 +
              (16 * Dtilde) / 3) +
          lambda *
            (S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) *
              ((16 * Dtilde) / 3 +
                (12 * Real.sqrt (2 * Dtilde *
                  bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact)) /
                  Real.sqrt 3)) := add_le_add hexpected hscale_mul
      _ =
        S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) *
          ((27 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact) / 2 +
            (16 * (1 + lambda) * Dtilde) / 3 +
              (12 * lambda *
                  Real.sqrt (2 * Dtilde *
                    bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact)) /
                Real.sqrt 3) := by
            ring
  have hmonoTail :
      sgsSelectedOutputGapStrictTailProbability S law x0 beta hbeta
          compactGamma compactGamma_mem_Icc (innerBudgetNat Tsrc)
          N xStar hxStar publicThreshold
          (by simpa [beta, Tsrc] using hindep) ≤
        sgsSelectedOutputGapStrictTailProbability S law x0 beta hbeta
          compactGamma compactGamma_mem_Icc (innerBudgetNat Tsrc)
          N xStar hxStar checkedThreshold
          (by simpa [beta, Tsrc] using hindep) :=
    sgs_selected_strict_tail_probability_antitone_threshold (S := S)
      (law := law) (x0 := x0) (xStar := xStar)
      (beta := beta) (gamma := compactGamma) (hbeta := hbeta)
      (hgamma := compactGamma_mem_Icc) (T := innerBudgetNat Tsrc)
      (N := N) (hxStar := hxStar)
      (threshold₁ := checkedThreshold) (threshold₂ := publicThreshold)
      (hindep := by simpa [beta, Tsrc] using hindep) hthreshold
  exact le_trans hmonoTail hgeneric

/-- Source-typed Corollary 8.3(a), expected fixed-horizon form.

This is the paper-facing sibling of the feasible-Bregman boundary theorem above:
the displayed term is `V(x_0,x*)` with `x_0 : X^o`, represented by
`bregmanOn`. -/
theorem Corollary8_3_fixedHorizon_expected_sourceTyped
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : ProxCorePoint S) (xStar : E)
    (N : PositiveTime) (Dtilde : ℝ)
    (hDtilde : 0 < Dtilde)
    (hindep : sfoIndependent S law.P law.sample
      (sgsSelectedOracleQuery S (proxCorePointToFeasible S x0)
        (fixedHorizonBeta S) (fixedHorizonBeta_pos S)
        fixedHorizonGamma fixedHorizonGamma_mem_Icc
        (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde)) law.sample))
    (hxStar : IsOptimalSolution S xStar) :
    sgsSelectedExpectedOutputGap S law (proxCorePointToFeasible S x0)
        (fixedHorizonBeta S)
        (fixedHorizonBeta_pos S) fixedHorizonGamma fixedHorizonGamma_mem_Icc
        (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde))
        N xStar hxStar hindep ≤
      (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
        (3 * bregmanOn S x0 ⟨xStar, hxStar.1⟩ + 4 * Dtilde) := by
  have hsource :=
    Corollary8_3_fixedHorizon_expected_sourceBoundary_feasibleBregman
      (S := S) (law := law) (x0 := proxCorePointToFeasible S x0)
      (xStar := xStar) (N := N) (Dtilde := Dtilde)
      hDtilde hindep hxStar
  have hBreg :
      bregmanFormulaOnX S (proxCorePointToFeasible S x0) ⟨xStar, hxStar.1⟩ =
        bregmanOn S x0 ⟨xStar, hxStar.1⟩ := by
    simpa [proxCorePointToFeasible] using
      bregmanFormulaOnX_eq_bregmanOn_of_mem_proxCore S
        (proxCorePointToFeasible S x0) ⟨xStar, hxStar.1⟩
        (by simpa [proxCorePointToFeasible] using x0.2)
  rw [← hBreg]
  exact hsource

/-- Conditional bridge for Corollary 8.3(a), high-probability fixed-horizon
form, after the compact Bregman-envelope domain boundary is resolved. -/
theorem Corollary8_3_fixedHorizon_highProbability_sourceTyped_conditionalBridge
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : ProxCorePoint S) (xStar : E)
    (N : PositiveTime)
    (Dtilde lambda : ℝ)
    (hDtilde : 0 < Dtilde) (hlambda : 0 < lambda)
    (hindep : sfoIndependent S law.P law.sample
      (sgsSelectedOracleQuery S (proxCorePointToFeasible S x0)
        (fixedHorizonBeta S) (fixedHorizonBeta_pos S)
        fixedHorizonGamma fixedHorizonGamma_mem_Icc
        (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde)) law.sample))
    (hxStar : IsOptimalSolution S xStar)
    (hcompact : IsCompact S.X)
    (hdomain : bregmanEnvelopeSourceDomainResolved S)
    (hlight : sgsOracleLightTailAssumption_8_1_57 S law) :
    sgsSelectedOutputGapStrictTailProbability S law (proxCorePointToFeasible S x0)
        (fixedHorizonBeta S)
        (fixedHorizonBeta_pos S) fixedHorizonGamma fixedHorizonGamma_mem_Icc
        (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde))
        N xStar hxStar
        ((2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
          (3 * bregmanOn S x0 ⟨xStar, hxStar.1⟩ +
            4 * (1 + lambda) * Dtilde +
            (4 * lambda *
                Real.sqrt (Dtilde *
                  bregmanEnvelope_sourceTyped S ⟨xStar, hxStar.1⟩ hcompact hdomain)) /
              Real.sqrt 3))
        hindep ≤
      ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) := by
  have hsource :=
    Corollary8_3_fixedHorizon_highProbability_sourceBoundary_feasibleBregman
      (S := S) (law := law) (x0 := proxCorePointToFeasible S x0)
      (xStar := xStar) (N := N) (Dtilde := Dtilde) (lambda := lambda)
      hDtilde hlambda hindep hxStar hcompact hlight
  have hBreg :
      bregmanFormulaOnX S (proxCorePointToFeasible S x0) ⟨xStar, hxStar.1⟩ =
        bregmanOn S x0 ⟨xStar, hxStar.1⟩ := by
    simpa [proxCorePointToFeasible] using
      bregmanFormulaOnX_eq_bregmanOn_of_mem_proxCore S
        (proxCorePointToFeasible S x0) ⟨xStar, hxStar.1⟩
        (by simpa [proxCorePointToFeasible] using x0.2)
  have hEnv :=
    bregmanEnvelope_sourceTyped_eq_formulaExtension_obligation S
      ⟨xStar, hxStar.1⟩ hcompact hdomain
  rw [← hBreg, hEnv]
  exact hsource

/-- Conditional bridge for Corollary 8.3(b), expected compact-policy form, after
the compact Bregman-envelope domain boundary is resolved. -/
theorem Corollary8_3_compact_expected_sourceTyped_conditionalBridge
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (N : PositiveTime) (Dtilde : ℝ)
    (hDtilde : 0 < Dtilde)
    (hindep : sfoIndependent S law.P law.sample
      (sgsSelectedOracleQuery S x0
        (compactBeta S (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)))
        (by
          intro k
          simpa [innerBudgetNat] using compactBeta_innerBudget_pos S Dtilde hDtilde k)
        compactGamma compactGamma_mem_Icc
        (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)) law.sample))
    (hxStar : IsOptimalSolution S xStar)
    (hcompact : IsCompact S.X)
    (hdomain : bregmanEnvelopeSourceDomainResolved S) :
    sgsSelectedExpectedOutputGap S law x0
        (compactBeta S (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)))
        (by
          intro k
          simpa [innerBudgetNat] using compactBeta_innerBudget_pos S Dtilde hDtilde k)
        compactGamma compactGamma_mem_Icc
        (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde))
        N xStar hxStar hindep ≤
      S.lSmooth / (((N.1 : ℝ) + 1) * ((N.1 : ℝ) + 2)) *
        ((27 * bregmanEnvelope_sourceTyped S ⟨xStar, hxStar.1⟩ hcompact hdomain) / 2 +
          (16 * Dtilde) / 3) := by
  have hsource :=
    Corollary8_3_compact_expected_sourceBoundary_feasibleBregman
      (S := S) (law := law) (x0 := x0) (xStar := xStar)
      (N := N) (Dtilde := Dtilde)
      hDtilde hindep hxStar hcompact
  have hEnv :=
    bregmanEnvelope_sourceTyped_eq_formulaExtension_obligation S
      ⟨xStar, hxStar.1⟩ hcompact hdomain
  rw [hEnv]
  exact hsource

/-- Conditional bridge for Corollary 8.3(b), high-probability compact-policy
form, after the compact Bregman-envelope domain boundary is resolved. -/
theorem Corollary8_3_compact_highProbability_sourceTyped_conditionalBridge
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (N : PositiveTime)
    (Dtilde lambda : ℝ)
    (hDtilde : 0 < Dtilde) (hlambda : 0 < lambda)
    (hindep : sfoIndependent S law.P law.sample
      (sgsSelectedOracleQuery S x0
        (compactBeta S (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)))
        (by
          intro k
          simpa [innerBudgetNat] using compactBeta_innerBudget_pos S Dtilde hDtilde k)
        compactGamma compactGamma_mem_Icc
        (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)) law.sample))
    (hxStar : IsOptimalSolution S xStar)
    (hcompact : IsCompact S.X)
    (hdomain : bregmanEnvelopeSourceDomainResolved S)
    (hlight : sgsOracleLightTailAssumption_8_1_57 S law) :
    sgsSelectedOutputGapStrictTailProbability S law x0
        (compactBeta S (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)))
        (by
          intro k
          simpa [innerBudgetNat] using compactBeta_innerBudget_pos S Dtilde hDtilde k)
        compactGamma compactGamma_mem_Icc
        (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde))
        N xStar hxStar
        (S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) *
          ((27 * bregmanEnvelope_sourceTyped S ⟨xStar, hxStar.1⟩ hcompact hdomain) / 2 +
            (16 * (1 + lambda) * Dtilde) / 3 +
              (12 * lambda *
                  Real.sqrt (2 * Dtilde *
                    bregmanEnvelope_sourceTyped S ⟨xStar, hxStar.1⟩ hcompact hdomain)) /
                Real.sqrt 3))
        hindep ≤
      ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) := by
  have hsource :=
    Corollary8_3_compact_highProbability_sourceBoundary_feasibleBregman
      (S := S) (law := law) (x0 := x0) (xStar := xStar)
      (N := N) (Dtilde := Dtilde) (lambda := lambda)
      hDtilde hlambda hindep hxStar hcompact hlight
  have hEnv :=
    bregmanEnvelope_sourceTyped_eq_formulaExtension_obligation S
      ⟨xStar, hxStar.1⟩ hcompact hdomain
  rw [hEnv]
  exact hsource

/-- Corrected public Theorem 8.2(a) expected-form signature at the feasible-Bregman
source boundary.

This is a signature alias, not a new theorem and not a new assumption.  It makes
the public contract active at the type level: the inhabited theorem below must be
implemented by the run-level generated-process declaration whose bound uses
`theorem82ExpectedBound_checkedFormulaExtension`, not by a selected-realization helper
or by an unsuffixed source-typed Bregman statement.  After the concrete
zero-dimensional counterexample ruled out the unqualified branch, the canonical
expected signature explicitly carries `gammaRangeCondition`. -/
def theorem82Expected_publicSignature_sourceBoundary_feasibleBregman
    (S : Setup E Sample)
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E] :
    Prop :=
  ∀ (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → InnerBudget)
    (N : PositiveTime)
    (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hgamma : gammaRangeCondition gamma)
    (hrun : IsGeneratedSGSProcess S x0 beta gamma (innerBudgetNat T) law.sample states inner)
    (hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner))
    (hxStar : IsOptimalSolution S xStar)
    (_hlower : outerLowerBoundCondition S beta gamma)
    (_hGamma : outerWeightCondition gamma Gamma)
    (_hmono : forwardMonotonicityCondition beta gamma Gamma (innerBudgetNat T)),
    expectedOutputGap S law x0 beta gamma (innerBudgetNat T) states inner N
        xStar hxStar hrun hindep ≤
        theorem82ExpectedBound_checkedFormulaExtension S x0 ⟨xStar, hxStar.1⟩ N
          beta gamma Gamma T
          (theorem82DenominatorAdmissible_forward_source_obligation S beta gamma Gamma T
            (IsGeneratedSGSProcess_beta_pos S x0 beta gamma (innerBudgetNat T)
              law.sample states inner hrun)
            _hlower _hGamma _hmono)

/-- Formal retirement certificate for the unqualified generated-run expected
Theorem 8.2(a) route.

This proposition is intentionally not a convergence theorem.  It records the
source-facing obstruction: Algorithm 8.1's public gamma domain is
`gammaNonnegativeCondition`, while the known Eq. (8.1.28) convexity route needs
`gammaRangeCondition`. -/
def theorem82Expected_sourceBoundary_gammaUpperGapCertificate : Prop :=
  ∃ gamma : PositiveTime → ℝ,
    gammaNonnegativeCondition gamma ∧ ¬ gammaRangeCondition gamma

theorem theorem82Expected_sourceBoundary_gammaUpperGapCertificate_holds :
    theorem82Expected_sourceBoundary_gammaUpperGapCertificate := by
  exact gammaNonnegativeCondition_not_imply_gammaRangeCondition

/-- Stronger retirement certificate for the unqualified generated-run expected
Theorem 8.2(a) route.

Unlike `theorem82Expected_sourceBoundary_gammaUpperGapCertificate`, this records
that the actual source schedule assumptions used by Theorem 8.2(a), including
Eq. (8.1.25), Eq. (8.1.32), and Eq. (8.1.33), do not force
`gammaRangeCondition`. -/
def theorem82Expected_sourceBoundary_sourceScheduleGammaGapCertificate
    (S : Setup E Sample) : Prop :=
  ∃ beta gamma Gamma : PositiveTime → ℝ, ∃ T : PositiveTime → InnerBudget,
    (∀ k : PositiveTime, 0 < beta k) ∧
      gammaNonnegativeCondition gamma ∧
        outerLowerBoundCondition S beta gamma ∧
          outerWeightCondition gamma Gamma ∧
            forwardMonotonicityCondition beta gamma Gamma (innerBudgetNat T) ∧
              ¬ gammaRangeCondition gamma

theorem theorem82Expected_sourceBoundary_sourceScheduleGammaGapCertificate_holds
    (S : Setup E Sample) :
    theorem82Expected_sourceBoundary_sourceScheduleGammaGapCertificate S := by
  exact theorem82GammaGap_sourceScheduleAssumptions_counterexample S

/-- Value-level correction artifact for the unqualified expected branch.

This is an existential, non-vacuous witness: the concrete zero-dimensional
setup/law/x0 above satisfy the unqualified Theorem 8.2(a) hypotheses for the
gamma-gap schedules, while the constant run has zero output gap and the checked
displayed bound is negative. -/
def theorem82Expected_sourceBoundary_zeroDimensionalCounterexampleCertificate : Prop :=
  ∃ (S₀ : Setup.{0, 0, 0} theorem82GammaGapZeroE Unit),
    ∃ (law : SGSProbabilityModel (Ω := Unit) S₀),
      ∃ _x0 : FeasiblePoint.{0, 0, 0} S₀,
      SGSGenericConvergence_Theorem8_2_expected_sourceBoundary_feasibleBregman_unsupported_unqualified_statement
        (Ω := Unit) S₀ → False

theorem theorem82Expected_sourceBoundary_zeroDimensionalCounterexampleCertificate_holds :
    theorem82Expected_sourceBoundary_zeroDimensionalCounterexampleCertificate := by
  exact ⟨theorem82GammaGapZeroSetup, theorem82GammaGapZeroLaw,
    theorem82GammaGapZeroX0,
    SGSGenericConvergence_Theorem8_2_expected_sourceBoundary_feasibleBregman_concreteZeroDimensional_counterexample⟩

/-- Corrected public Theorem 8.2(a) expected-form signature at the feasible
Bregman source boundary.

This is the executable replacement target for the generated-run expected branch:
it keeps the paper's generated-process boundary and checked quotient discipline,
but explicitly carries the gamma upper bound required by Eq. (8.1.28). -/
def theorem82Expected_publicSignature_sourceBoundary_feasibleBregman_under_gammaRange
    (S : Setup E Sample)
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E] :
    Prop :=
  ∀ (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → InnerBudget)
    (N : PositiveTime)
    (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hgamma : gammaRangeCondition gamma)
    (hrun : IsGeneratedSGSProcess S x0 beta gamma (innerBudgetNat T) law.sample states inner)
    (hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner))
    (hxStar : IsOptimalSolution S xStar)
    (_hlower : outerLowerBoundCondition S beta gamma)
    (_hGamma : outerWeightCondition gamma Gamma)
    (_hmono : forwardMonotonicityCondition beta gamma Gamma (innerBudgetNat T)),
    expectedOutputGap S law x0 beta gamma (innerBudgetNat T) states inner N
        xStar hxStar hrun hindep ≤
        theorem82ExpectedBound_checkedFormulaExtension S x0 ⟨xStar, hxStar.1⟩ N
          beta gamma Gamma T
          (theorem82DenominatorAdmissible_forward_source_obligation S beta gamma Gamma T
            (IsGeneratedSGSProcess_beta_pos S x0 beta gamma (innerBudgetNat T)
              law.sample states inner hrun)
            _hlower _hGamma _hmono)

/-- Public Theorem 8.2(b) high-probability signature at the corrected guarded
feasible-Bregman source boundary.

The active high-probability branch is selected-source-boundary shaped.  The
older arbitrary generated-run theorem is retained as a compatibility declaration
only; it is not the executable source route until a causal-selector invariant
transports the strict-past martingale hypotheses to arbitrary `states`/`inner`. -/
def theorem82HighProbability_publicSignature_sourceBoundary_feasibleBregman
    (S : Setup E Sample)
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E] :
    Prop :=
  ∀ (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → InnerBudget)
    (N : PositiveTime) (lambda : ℝ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hindep : sfoIndependent S law.P law.sample
      (sgsSelectedOracleQuery S x0 beta hbeta gamma hgamma
        (innerBudgetNat T) law.sample))
    (_hlambda : 0 < lambda) (hxStar : IsOptimalSolution S xStar)
    (_hlight : sgsOracleLightTailAssumption_8_1_57 S law)
    (_hlower : outerLowerBoundCondition S beta gamma)
    (_hGamma : outerWeightCondition gamma Gamma)
    (_hmono : forwardMonotonicityCondition beta gamma Gamma (innerBudgetNat T))
    (hcompact : IsCompact S.X),
      sgsSelectedOutputGapStrictTailProbability S law x0 beta hbeta gamma hgamma
              (innerBudgetNat T) N xStar hxStar
        (theorem82ExpectedBound_checkedFormulaExtension S x0 ⟨xStar, hxStar.1⟩ N
            beta gamma Gamma T
            (theorem82DenominatorAdmissible_forward_source_obligation S beta gamma Gamma T
              hbeta _hlower _hGamma _hmono) +
          lambda *
            theorem82ProbabilityScale_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
                hcompact N beta gamma Gamma T
                (theorem82DenominatorAdmissible_forward_source_obligation S beta gamma Gamma T
                  hbeta _hlower _hGamma _hmono))
        hindep ≤
      ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda))

/-- Public Theorem 8.2(c) reverse-monotone expected signature at the corrected
feasible-Bregman source boundary. -/
def theorem82ReverseExpected_publicSignature_sourceBoundary_feasibleBregman
    (S : Setup E Sample)
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E] :
    Prop :=
  ∀ (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → InnerBudget)
    (N : PositiveTime)
    (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hrun : IsGeneratedSGSProcess S x0 beta gamma (innerBudgetNat T) law.sample states inner)
    (hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner))
    (hxStar : IsOptimalSolution S xStar)
    (hcompact : IsCompact S.X)
    (_hlower : outerLowerBoundCondition S beta gamma)
    (_hGamma : outerWeightCondition gamma Gamma)
    (_hmono : reverseMonotonicityCondition beta gamma Gamma (innerBudgetNat T)),
    expectedOutputGap S law x0 beta gamma (innerBudgetNat T) states inner N
        xStar hxStar hrun hindep ≤
        theorem82ReverseExpectedBound_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
          hcompact N beta gamma Gamma T
          (theorem82DenominatorAdmissible_reverse_source_obligation S beta gamma Gamma T
            (IsGeneratedSGSProcess_beta_pos S x0 beta gamma (innerBudgetNat T)
              law.sample states inner hrun)
            _hlower _hGamma _hmono)

/-- Public Theorem 8.2(c) reverse-monotone high-probability selected signature at
the corrected feasible-Bregman source boundary. -/
def theorem82ReverseHighProbability_publicSignature_selectedSourceBoundary_feasibleBregman
    (S : Setup E Sample)
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E] :
    Prop :=
  ∀ (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → InnerBudget)
    (N : PositiveTime) (lambda : ℝ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hindep : sfoIndependent S law.P law.sample
      (sgsSelectedOracleQuery S x0 beta hbeta gamma hgamma
        (innerBudgetNat T) law.sample))
    (_hlambda : 0 < lambda) (hxStar : IsOptimalSolution S xStar)
    (hcompact : IsCompact S.X)
    (_hlight : sgsOracleLightTailAssumption_8_1_57 S law)
    (_hlower : outerLowerBoundCondition S beta gamma)
    (_hGamma : outerWeightCondition gamma Gamma)
    (_hmono : reverseMonotonicityCondition beta gamma Gamma (innerBudgetNat T)),
    sgsSelectedOutputGapStrictTailProbability S law x0 beta hbeta gamma hgamma
        (innerBudgetNat T) N
        xStar hxStar
        (theorem82ReverseExpectedBound_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
              hcompact N beta gamma Gamma T
              (theorem82DenominatorAdmissible_reverse_source_obligation S beta gamma Gamma T
                hbeta _hlower _hGamma _hmono) +
          lambda *
            theorem82ProbabilityScale_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
                hcompact N beta gamma Gamma T
                (theorem82DenominatorAdmissible_reverse_source_obligation S beta gamma Gamma T
                  hbeta _hlower _hGamma _hmono))
        hindep ≤
      ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda))

/-- Focused active contract statement for the public generic Theorem 8.2 surface.

This declaration is an audit target, not a mathematical strengthening: it names
the unsupported unqualified expected branch by its gamma-gap certificate, names
the unsupported unqualified high-probability branch by the concrete
zero-dimensional counterexample certificate, and names the corrected guarded
forward signatures that Phase 2a should fill.  Keeping this as a standalone
`Prop` prevents the focused Theorem 8.2 contract from being hidden inside the
broader Corollary 8.3/source-boundary contract. -/
def theorem82_publicSurface_activeSignatureContractStatement
    (S : Setup E Sample)
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E] :
    Prop :=
  theorem82Expected_sourceBoundary_gammaUpperGapCertificate ∧
    theorem82Expected_sourceBoundary_sourceScheduleGammaGapCertificate S ∧
      theorem82Expected_sourceBoundary_zeroDimensionalCounterexampleCertificate ∧
        theorem82HighProbability_sourceBoundary_zeroDimensionalCounterexampleCertificate ∧
          SGSGenericConvergence_Theorem8_2_expected_sourceBoundary_feasibleBregman_counterexample S ∧
            theorem82Expected_publicSignature_sourceBoundary_feasibleBregman
              (Ω := Ω) S ∧
              theorem82HighProbability_publicSignature_sourceBoundary_feasibleBregman (Ω := Ω) S ∧
                theorem82ReverseExpected_publicSignature_sourceBoundary_feasibleBregman (Ω := Ω) S ∧
                  theorem82ReverseHighProbability_publicSignature_selectedSourceBoundary_feasibleBregman
                    (Ω := Ω) S

/-- Active type-level contract for the public generic Theorem 8.2
source-boundary declarations.

This theorem is intentionally separate from selected-realization corollary
helpers: the expected branches remain corrected generated-run signatures where
the proof does not need the martingale strict-past invariant, while both active
high-probability branches are selected-source-boundary routes with the canonical
SGS/SPS process.  Arbitrary generated-run high-probability declarations remain
compatibility boundaries until a causal-selector invariant is available. -/
theorem theorem82_publicSurface_activeSignatureContract
    (S : Setup E Sample)
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E] :
  theorem82_publicSurface_activeSignatureContractStatement (Ω := Ω) S := by
  dsimp [theorem82_publicSurface_activeSignatureContractStatement]
  refine ⟨theorem82Expected_sourceBoundary_gammaUpperGapCertificate_holds,
    theorem82Expected_sourceBoundary_sourceScheduleGammaGapCertificate_holds S,
    theorem82Expected_sourceBoundary_zeroDimensionalCounterexampleCertificate_holds,
    theorem82HighProbability_sourceBoundary_zeroDimensionalCounterexampleCertificate_holds,
    SGSGenericConvergence_Theorem8_2_expected_sourceBoundary_feasibleBregman_counterexample_holds S,
    ?_, ?_, ?_, ?_⟩
  · intro law x0 xStar beta gamma Gamma T N states inner hgamma hrun hindep hxStar
      hlower hGamma hmono
    exact SGSGenericConvergence_Theorem8_2_expected_sourceBoundary_feasibleBregman
      S law x0 xStar beta gamma Gamma T N states inner hgamma hrun hindep hxStar
      hlower hGamma hmono
  · intro law x0 xStar beta gamma Gamma T N lambda hbeta hgamma hindep
      hlambda hxStar hlight hlower hGamma hmono hcompact
    exact
      SGSGenericConvergence_Theorem8_2_highProbability_selectedSourceBoundary_feasibleBregman
        S law x0 xStar beta gamma Gamma T N lambda hbeta hgamma hlambda hxStar
        hlight hlower hGamma hindep hmono hcompact
  · intro law x0 xStar beta gamma Gamma T N states inner hrun hindep hxStar
      hcompact hlower hGamma hmono
    exact SGSGenericConvergence_Theorem8_2_reverse_expected_sourceBoundary_feasibleBregman
      S law x0 xStar beta gamma Gamma T N states inner hrun hindep hxStar
      hcompact hlower hGamma hmono
  · intro law x0 xStar beta gamma Gamma T N lambda hbeta hgamma hindep
      hlambda hxStar hcompact hlight hlower hGamma hmono
    exact SGSGenericConvergence_Theorem8_2_reverse_highProbability_selectedSourceBoundary_feasibleBregman
      S law x0 xStar beta gamma Gamma T N lambda hbeta hgamma hindep
      hlambda hxStar hcompact hlight hlower hGamma hmono

/-- Exported statement of the active signature contract for the public
source-boundary surface.

This is not another convergence theorem.  It is a typechecked audit hook for
the boundary-corrected declarations above: Theorem 8.2 is exposed only through
run-level generated expected/reverse processes, the selected forward
high-probability process, positive `InnerBudget`s, checked quotient obligations
derived internally from the source hypotheses, and feasible-pair Bregman
formula/envelope objects.  The unqualified generated-run expected branch and
the arbitrary generated-run high-probability branch are not certified as
executable here; the active high-probability witness is the canonical selected
Algorithm 8.2 route with explicit `gammaRangeCondition`.

Book JSON citations:
`book/FOML/StochasticGradientSliding.json:key_lemmas[7].statement_math` gives
Theorem 8.2's expected/high-probability bounds and monotonicity cases, and
`book/FOML/StochasticGradientSliding.json:main_theorem.statement_math` gives the
four Corollary 8.3 public bounds.  The contract is a real proposition rather
than a theorem returning `True`: if any public declaration drifts back to
selected-realization hypotheses, raw natural budgets, raw Lean division, or an
unsuffixed A-level Bregman theorem name, the proof of
`publicSourceBoundary_activeSignatureContract` stops typechecking. -/
def publicSourceBoundary_activeSignatureContractStatement
    (S : Setup E Sample)
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E] :
    Prop :=
  theorem82Expected_sourceBoundary_zeroDimensionalCounterexampleCertificate ∧
  theorem82HighProbability_sourceBoundary_zeroDimensionalCounterexampleCertificate ∧
  ∃ theorem82_expected :
      ∀ (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
        (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → InnerBudget)
        (N : PositiveTime)
        (states : ℕ → Ω → SGSState S)
        (inner : PositiveTime → ℕ → Ω → SPSState S)
        (hgamma : gammaRangeCondition gamma)
        (hrun : IsGeneratedSGSProcess S x0 beta gamma (innerBudgetNat T) law.sample states inner)
        (hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner))
        (hxStar : IsOptimalSolution S xStar)
        (hlower : outerLowerBoundCondition S beta gamma)
        (hGamma : outerWeightCondition gamma Gamma)
        (hmono : forwardMonotonicityCondition beta gamma Gamma (innerBudgetNat T)),
        expectedOutputGap S law x0 beta gamma (innerBudgetNat T) states inner N
            xStar hxStar hrun hindep ≤
          theorem82ExpectedBound_checkedFormulaExtension S x0 ⟨xStar, hxStar.1⟩ N
              beta gamma Gamma T
              (theorem82DenominatorAdmissible_forward_source_obligation S beta gamma Gamma T
                (IsGeneratedSGSProcess_beta_pos S x0 beta gamma (innerBudgetNat T)
                  law.sample states inner hrun)
                hlower hGamma hmono),
  ∃ theorem82_highProbability :
      ∀ (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
        (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → InnerBudget)
        (N : PositiveTime) (lambda : ℝ)
        (hbeta : ∀ k : PositiveTime, 0 < beta k)
        (hgamma : gammaRangeCondition gamma)
        (hindep : sfoIndependent S law.P law.sample
          (sgsSelectedOracleQuery S x0 beta hbeta gamma hgamma
            (innerBudgetNat T) law.sample))
        (hlambda : 0 < lambda) (hxStar : IsOptimalSolution S xStar)
        (hlight : sgsOracleLightTailAssumption_8_1_57 S law)
        (hlower : outerLowerBoundCondition S beta gamma)
        (hGamma : outerWeightCondition gamma Gamma)
        (hmono : forwardMonotonicityCondition beta gamma Gamma (innerBudgetNat T))
        (hcompact : IsCompact S.X),
        sgsSelectedOutputGapStrictTailProbability S law x0 beta hbeta gamma hgamma
            (innerBudgetNat T) N xStar hxStar
            (theorem82ExpectedBound_checkedFormulaExtension S x0 ⟨xStar, hxStar.1⟩ N
                beta gamma Gamma T
                (theorem82DenominatorAdmissible_forward_source_obligation S beta gamma Gamma T
                  hbeta hlower hGamma hmono) +
              lambda *
                theorem82ProbabilityScale_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
                    hcompact N beta gamma Gamma T
                    (theorem82DenominatorAdmissible_forward_source_obligation S beta gamma Gamma T
                      hbeta hlower hGamma hmono))
            hindep ≤
          ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)),
  ∃ theorem82_reverse_expected :
      ∀ (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
        (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → InnerBudget)
        (N : PositiveTime)
        (states : ℕ → Ω → SGSState S)
        (inner : PositiveTime → ℕ → Ω → SPSState S)
        (hrun : IsGeneratedSGSProcess S x0 beta gamma (innerBudgetNat T) law.sample states inner)
        (hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner))
        (hxStar : IsOptimalSolution S xStar)
        (hcompact : IsCompact S.X)
        (hlower : outerLowerBoundCondition S beta gamma)
        (hGamma : outerWeightCondition gamma Gamma)
        (hmono : reverseMonotonicityCondition beta gamma Gamma (innerBudgetNat T)),
        expectedOutputGap S law x0 beta gamma (innerBudgetNat T) states inner N
            xStar hxStar hrun hindep ≤
          theorem82ReverseExpectedBound_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
              hcompact N beta gamma Gamma T
              (theorem82DenominatorAdmissible_reverse_source_obligation S beta gamma Gamma T
                (IsGeneratedSGSProcess_beta_pos S x0 beta gamma (innerBudgetNat T)
                  law.sample states inner hrun)
                hlower hGamma hmono),
  ∃ theorem82_reverse_highProbability :
      ∀ (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
        (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → InnerBudget)
        (N : PositiveTime) (lambda : ℝ)
        (hbeta : ∀ k : PositiveTime, 0 < beta k)
        (hgamma : gammaRangeCondition gamma)
        (hindep : sfoIndependent S law.P law.sample
          (sgsSelectedOracleQuery S x0 beta hbeta gamma hgamma
            (innerBudgetNat T) law.sample))
        (hlambda : 0 < lambda) (hxStar : IsOptimalSolution S xStar)
        (hcompact : IsCompact S.X)
        (hlight : sgsOracleLightTailAssumption_8_1_57 S law)
        (hlower : outerLowerBoundCondition S beta gamma)
        (hGamma : outerWeightCondition gamma Gamma)
        (hmono : reverseMonotonicityCondition beta gamma Gamma (innerBudgetNat T)),
        sgsSelectedOutputGapStrictTailProbability S law x0 beta hbeta gamma hgamma
            (innerBudgetNat T) N
            xStar hxStar
            (theorem82ReverseExpectedBound_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
                  hcompact N beta gamma Gamma T
                  (theorem82DenominatorAdmissible_reverse_source_obligation S beta gamma Gamma T
                    hbeta hlower hGamma hmono) +
              lambda *
                theorem82ProbabilityScale_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
                    hcompact N beta gamma Gamma T
                    (theorem82DenominatorAdmissible_reverse_source_obligation S beta gamma Gamma T
                      hbeta hlower hGamma hmono))
            hindep ≤
          ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)),
  ∃ corollary83_fixed_expected_selected_signature :
      ∀ (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S)
        (xStar : E) (N : PositiveTime) (Dtilde : ℝ)
        (hDtilde : 0 < Dtilde)
        (hindep : sfoIndependent S law.P law.sample
          (sgsSelectedOracleQuery S x0 (fixedHorizonBeta S) (fixedHorizonBeta_pos S)
            fixedHorizonGamma fixedHorizonGamma_mem_Icc
            (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde))
            law.sample))
        (hxStar : IsOptimalSolution S xStar),
        sgsSelectedExpectedOutputGap S law x0 (fixedHorizonBeta S)
            (fixedHorizonBeta_pos S) fixedHorizonGamma fixedHorizonGamma_mem_Icc
            (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde))
            N xStar hxStar hindep ≤
          (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
            (3 * bregmanFormulaOnX S x0 ⟨xStar, hxStar.1⟩ + 4 * Dtilde),
  ∃ corollary83_fixed_highProbability_selected_signature :
      ∀ (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S)
        (xStar : E) (N : PositiveTime) (Dtilde lambda : ℝ)
        (hDtilde : 0 < Dtilde) (hlambda : 0 < lambda)
        (hindep : sfoIndependent S law.P law.sample
          (sgsSelectedOracleQuery S x0 (fixedHorizonBeta S) (fixedHorizonBeta_pos S)
            fixedHorizonGamma fixedHorizonGamma_mem_Icc
            (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde))
            law.sample))
        (hxStar : IsOptimalSolution S xStar)
        (hcompact : IsCompact S.X)
        (hlight : sgsOracleLightTailAssumption_8_1_57 S law),
        sgsSelectedOutputGapStrictTailProbability S law x0 (fixedHorizonBeta S)
            (fixedHorizonBeta_pos S) fixedHorizonGamma fixedHorizonGamma_mem_Icc
            (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde))
            N xStar hxStar
            ((2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
              (3 * bregmanFormulaOnX S x0 ⟨xStar, hxStar.1⟩ +
                4 * (1 + lambda) * Dtilde +
                (4 * lambda *
                    Real.sqrt (Dtilde *
                      bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact)) /
                  Real.sqrt 3))
            hindep ≤
          ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)),
  ∃ corollary83_compact_expected_selected_signature :
      ∀ (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S)
        (xStar : E) (N : PositiveTime) (Dtilde : ℝ)
        (hDtilde : 0 < Dtilde)
        (hindep : sfoIndependent S law.P law.sample
          (sgsSelectedOracleQuery S x0
            (compactBeta S (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)))
            (by
              intro k
              simpa [innerBudgetNat] using compactBeta_innerBudget_pos S Dtilde hDtilde k)
            compactGamma compactGamma_mem_Icc
            (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)) law.sample))
        (hxStar : IsOptimalSolution S xStar)
        (hcompact : IsCompact S.X),
        sgsSelectedExpectedOutputGap S law x0
            (compactBeta S (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)))
            (by
              intro k
              simpa [innerBudgetNat] using compactBeta_innerBudget_pos S Dtilde hDtilde k)
            compactGamma compactGamma_mem_Icc
            (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde))
            N xStar hxStar hindep ≤
          S.lSmooth / (((N.1 : ℝ) + 1) * ((N.1 : ℝ) + 2)) *
            ((27 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact) / 2 +
              (16 * Dtilde) / 3),
  ∃ corollary83_compact_highProbability_selected_signature :
      ∀ (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S)
        (xStar : E) (N : PositiveTime) (Dtilde lambda : ℝ)
        (hDtilde : 0 < Dtilde) (hlambda : 0 < lambda)
        (hindep : sfoIndependent S law.P law.sample
          (sgsSelectedOracleQuery S x0
            (compactBeta S (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)))
            (by
              intro k
              simpa [innerBudgetNat] using compactBeta_innerBudget_pos S Dtilde hDtilde k)
            compactGamma compactGamma_mem_Icc
            (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)) law.sample))
        (hxStar : IsOptimalSolution S xStar)
        (hcompact : IsCompact S.X)
        (hlight : sgsOracleLightTailAssumption_8_1_57 S law),
        sgsSelectedOutputGapStrictTailProbability S law x0
            (compactBeta S (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)))
            (by
              intro k
              simpa [innerBudgetNat] using compactBeta_innerBudget_pos S Dtilde hDtilde k)
            compactGamma compactGamma_mem_Icc
            (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde))
            N xStar hxStar
            (S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) *
              ((27 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact) / 2 +
                (16 * (1 + lambda) * Dtilde) / 3 +
                  (12 * lambda *
                      Real.sqrt (2 * Dtilde *
                        bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact)) /
                    Real.sqrt 3))
            hindep ≤
          ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)),
  ∃ sourceTyped_expected_target :
      ∀ (x0Core : ProxCorePoint S) (xStar : FeasiblePoint S)
        (N : PositiveTime) (beta gamma Gamma : PositiveTime → ℝ)
        (T : PositiveTime → ℕ),
        theorem82ExpectedBound_sourceTyped S x0Core xStar N beta gamma Gamma T =
          genericExpectedBound_sourceTyped S x0Core xStar N beta gamma Gamma T,
  ∃ sourceTyped_expected_bridge :
      ∀ (x0 : FeasiblePoint S) (hx0 : x0.1 ∈ proxCore S.X S.proxPotential)
        (xStar : FeasiblePoint S) (N : PositiveTime)
        (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ),
        theorem82ExpectedBound_sourceTyped S ⟨x0.1, hx0⟩ xStar N beta gamma Gamma T =
          theorem82ExpectedBound_formulaExtension S x0 xStar N beta gamma Gamma T,
  True

/-- Active signature contract for the public source-boundary surface. -/
theorem publicSourceBoundary_activeSignatureContract
    (S : Setup E Sample)
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E] :
    publicSourceBoundary_activeSignatureContractStatement (Ω := Ω) S := by
  have theorem82_expected :
      ∀ (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
        (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → InnerBudget)
        (N : PositiveTime)
        (states : ℕ → Ω → SGSState S)
        (inner : PositiveTime → ℕ → Ω → SPSState S)
        (hgamma : gammaRangeCondition gamma)
        (hrun : IsGeneratedSGSProcess S x0 beta gamma (innerBudgetNat T) law.sample states inner)
        (hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner))
        (hxStar : IsOptimalSolution S xStar)
        (hlower : outerLowerBoundCondition S beta gamma)
        (hGamma : outerWeightCondition gamma Gamma)
        (hmono : forwardMonotonicityCondition beta gamma Gamma (innerBudgetNat T)),
        expectedOutputGap S law x0 beta gamma (innerBudgetNat T) states inner N
            xStar hxStar hrun hindep ≤
            theorem82ExpectedBound_checkedFormulaExtension S x0 ⟨xStar, hxStar.1⟩ N
              beta gamma Gamma T
              (theorem82DenominatorAdmissible_forward_source_obligation S beta gamma Gamma T
                (IsGeneratedSGSProcess_beta_pos S x0 beta gamma (innerBudgetNat T)
                  law.sample states inner hrun)
                hlower hGamma hmono) := by
    intro law x0 xStar beta gamma Gamma T N states inner hgamma hrun hindep hxStar
      hlower hGamma hmono
    exact SGSGenericConvergence_Theorem8_2_expected_sourceBoundary_feasibleBregman
      S law x0 xStar beta gamma Gamma T N states inner hgamma hrun hindep hxStar
      hlower hGamma hmono
  have theorem82_highProbability :
      ∀ (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
        (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → InnerBudget)
        (N : PositiveTime) (lambda : ℝ)
        (hbeta : ∀ k : PositiveTime, 0 < beta k)
        (hgamma : gammaRangeCondition gamma)
        (hindep : sfoIndependent S law.P law.sample
          (sgsSelectedOracleQuery S x0 beta hbeta gamma hgamma
            (innerBudgetNat T) law.sample))
        (hlambda : 0 < lambda) (hxStar : IsOptimalSolution S xStar)
        (hlight : sgsOracleLightTailAssumption_8_1_57 S law)
        (hlower : outerLowerBoundCondition S beta gamma)
        (hGamma : outerWeightCondition gamma Gamma)
        (hmono : forwardMonotonicityCondition beta gamma Gamma (innerBudgetNat T))
        (hcompact : IsCompact S.X),
        sgsSelectedOutputGapStrictTailProbability S law x0 beta hbeta gamma hgamma
            (innerBudgetNat T) N xStar hxStar
            (theorem82ExpectedBound_checkedFormulaExtension S x0 ⟨xStar, hxStar.1⟩ N
                beta gamma Gamma T
                (theorem82DenominatorAdmissible_forward_source_obligation S beta gamma Gamma T
                  hbeta hlower hGamma hmono) +
              lambda *
                theorem82ProbabilityScale_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
                    hcompact N beta gamma Gamma T
                    (theorem82DenominatorAdmissible_forward_source_obligation S beta gamma Gamma T
                      hbeta hlower hGamma hmono))
            hindep ≤
          ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) := by
    intro law x0 xStar beta gamma Gamma T N lambda hbeta hgamma hindep
      hlambda hxStar hlight hlower hGamma hmono hcompact
    exact
      SGSGenericConvergence_Theorem8_2_highProbability_selectedSourceBoundary_feasibleBregman
        S law x0 xStar beta gamma Gamma T N lambda hbeta hgamma hlambda hxStar
        hlight hlower hGamma hindep hmono hcompact
  have theorem82_reverse_expected :
      ∀ (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
        (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → InnerBudget)
        (N : PositiveTime)
        (states : ℕ → Ω → SGSState S)
        (inner : PositiveTime → ℕ → Ω → SPSState S)
        (hrun : IsGeneratedSGSProcess S x0 beta gamma (innerBudgetNat T) law.sample states inner)
        (hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner))
        (hxStar : IsOptimalSolution S xStar)
        (hcompact : IsCompact S.X)
        (hlower : outerLowerBoundCondition S beta gamma)
        (hGamma : outerWeightCondition gamma Gamma)
        (hmono : reverseMonotonicityCondition beta gamma Gamma (innerBudgetNat T)),
        expectedOutputGap S law x0 beta gamma (innerBudgetNat T) states inner N
            xStar hxStar hrun hindep ≤
            theorem82ReverseExpectedBound_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
              hcompact N beta gamma Gamma T
              (theorem82DenominatorAdmissible_reverse_source_obligation S beta gamma Gamma T
                (IsGeneratedSGSProcess_beta_pos S x0 beta gamma (innerBudgetNat T)
                  law.sample states inner hrun)
                hlower hGamma hmono) := by
    intro law x0 xStar beta gamma Gamma T N states inner hrun hindep hxStar
      hcompact hlower hGamma hmono
    exact SGSGenericConvergence_Theorem8_2_reverse_expected_sourceBoundary_feasibleBregman
      S law x0 xStar beta gamma Gamma T N states inner hrun hindep hxStar
      hcompact hlower hGamma hmono
  have theorem82_reverse_highProbability :
      ∀ (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
        (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → InnerBudget)
        (N : PositiveTime) (lambda : ℝ)
        (hbeta : ∀ k : PositiveTime, 0 < beta k)
        (hgamma : gammaRangeCondition gamma)
        (hindep : sfoIndependent S law.P law.sample
          (sgsSelectedOracleQuery S x0 beta hbeta gamma hgamma
            (innerBudgetNat T) law.sample))
        (hlambda : 0 < lambda) (hxStar : IsOptimalSolution S xStar)
        (hcompact : IsCompact S.X)
        (hlight : sgsOracleLightTailAssumption_8_1_57 S law)
        (hlower : outerLowerBoundCondition S beta gamma)
        (hGamma : outerWeightCondition gamma Gamma)
        (hmono : reverseMonotonicityCondition beta gamma Gamma (innerBudgetNat T)),
        sgsSelectedOutputGapStrictTailProbability S law x0 beta hbeta gamma hgamma
            (innerBudgetNat T) N
            xStar hxStar
            (theorem82ReverseExpectedBound_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
                  hcompact N beta gamma Gamma T
                  (theorem82DenominatorAdmissible_reverse_source_obligation S beta gamma Gamma T
                    hbeta hlower hGamma hmono) +
              lambda *
                theorem82ProbabilityScale_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
                    hcompact N beta gamma Gamma T
                    (theorem82DenominatorAdmissible_reverse_source_obligation S beta gamma Gamma T
                      hbeta hlower hGamma hmono))
            hindep ≤
          ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) := by
    intro law x0 xStar beta gamma Gamma T N lambda hbeta hgamma hindep
      hlambda hxStar hcompact hlight hlower hGamma hmono
    simpa using SGSGenericConvergence_Theorem8_2_reverse_highProbability_selectedSourceBoundary_feasibleBregman
      S law x0 xStar beta gamma Gamma T N lambda hbeta hgamma hindep
      hlambda hxStar hcompact hlight hlower hGamma hmono
  have corollary83_fixed_expected :=
    Corollary8_3_fixedHorizon_expected_sourceBoundary_feasibleBregman (Ω := Ω) (S := S)
  have corollary83_fixed_highProbability :=
    Corollary8_3_fixedHorizon_highProbability_sourceBoundary_feasibleBregman (Ω := Ω) (S := S)
  have corollary83_compact_expected :=
    Corollary8_3_compact_expected_sourceBoundary_feasibleBregman (Ω := Ω) (S := S)
  have corollary83_compact_highProbability :=
    Corollary8_3_compact_highProbability_sourceBoundary_feasibleBregman (Ω := Ω) (S := S)
  have corollary83_fixed_expected_selected_signature :
      ∀ (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S)
        (xStar : E) (N : PositiveTime) (Dtilde : ℝ)
        (hDtilde : 0 < Dtilde)
        (hindep : sfoIndependent S law.P law.sample
          (sgsSelectedOracleQuery S x0 (fixedHorizonBeta S) (fixedHorizonBeta_pos S)
            fixedHorizonGamma fixedHorizonGamma_mem_Icc
            (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde))
            law.sample))
        (hxStar : IsOptimalSolution S xStar),
        sgsSelectedExpectedOutputGap S law x0 (fixedHorizonBeta S)
            (fixedHorizonBeta_pos S) fixedHorizonGamma fixedHorizonGamma_mem_Icc
            (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde))
            N xStar hxStar hindep ≤
          (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
            (3 * bregmanFormulaOnX S x0 ⟨xStar, hxStar.1⟩ + 4 * Dtilde) := by
    intro law x0 xStar N Dtilde hDtilde hindep hxStar
    simpa [sgsSelectedExpectedOutputGap] using
      Corollary8_3_fixedHorizon_expected_sourceBoundary_feasibleBregman
        S law x0 xStar N Dtilde hDtilde hindep hxStar
  have corollary83_fixed_highProbability_selected_signature :
      ∀ (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S)
        (xStar : E) (N : PositiveTime) (Dtilde lambda : ℝ)
        (hDtilde : 0 < Dtilde) (hlambda : 0 < lambda)
        (hindep : sfoIndependent S law.P law.sample
          (sgsSelectedOracleQuery S x0 (fixedHorizonBeta S) (fixedHorizonBeta_pos S)
            fixedHorizonGamma fixedHorizonGamma_mem_Icc
            (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde))
            law.sample))
        (hxStar : IsOptimalSolution S xStar)
        (hcompact : IsCompact S.X)
        (hlight : sgsOracleLightTailAssumption_8_1_57 S law),
        sgsSelectedOutputGapStrictTailProbability S law x0 (fixedHorizonBeta S)
            (fixedHorizonBeta_pos S) fixedHorizonGamma fixedHorizonGamma_mem_Icc
            (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde))
            N xStar hxStar
            ((2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
              (3 * bregmanFormulaOnX S x0 ⟨xStar, hxStar.1⟩ +
                4 * (1 + lambda) * Dtilde +
                (4 * lambda *
                    Real.sqrt (Dtilde *
                      bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact)) /
                  Real.sqrt 3))
            hindep ≤
          ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) := by
    intro law x0 xStar N Dtilde lambda hDtilde hlambda hindep hxStar hcompact hlight
    simpa [sgsSelectedOutputGapStrictTailProbability] using
      Corollary8_3_fixedHorizon_highProbability_sourceBoundary_feasibleBregman
        S law x0 xStar N Dtilde lambda hDtilde hlambda hindep hxStar hcompact hlight
  have corollary83_compact_expected_selected_signature :
      ∀ (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S)
        (xStar : E) (N : PositiveTime) (Dtilde : ℝ)
        (hDtilde : 0 < Dtilde)
        (hindep : sfoIndependent S law.P law.sample
          (sgsSelectedOracleQuery S x0
            (compactBeta S (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)))
            (by
              intro k
              simpa [innerBudgetNat] using compactBeta_innerBudget_pos S Dtilde hDtilde k)
            compactGamma compactGamma_mem_Icc
            (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)) law.sample))
        (hxStar : IsOptimalSolution S xStar)
        (hcompact : IsCompact S.X),
        sgsSelectedExpectedOutputGap S law x0
            (compactBeta S (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)))
            (by
              intro k
              simpa [innerBudgetNat] using compactBeta_innerBudget_pos S Dtilde hDtilde k)
            compactGamma compactGamma_mem_Icc
            (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde))
            N xStar hxStar hindep ≤
          S.lSmooth / (((N.1 : ℝ) + 1) * ((N.1 : ℝ) + 2)) *
            ((27 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact) / 2 +
              (16 * Dtilde) / 3) := by
    intro law x0 xStar N Dtilde hDtilde hindep hxStar hcompact
    simpa [sgsSelectedExpectedOutputGap] using
      Corollary8_3_compact_expected_sourceBoundary_feasibleBregman
        S law x0 xStar N Dtilde hDtilde hindep hxStar hcompact
  have corollary83_compact_highProbability_selected_signature :
      ∀ (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S)
        (xStar : E) (N : PositiveTime) (Dtilde lambda : ℝ)
        (hDtilde : 0 < Dtilde) (hlambda : 0 < lambda)
        (hindep : sfoIndependent S law.P law.sample
          (sgsSelectedOracleQuery S x0
            (compactBeta S (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)))
            (by
              intro k
              simpa [innerBudgetNat] using compactBeta_innerBudget_pos S Dtilde hDtilde k)
            compactGamma compactGamma_mem_Icc
            (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)) law.sample))
        (hxStar : IsOptimalSolution S xStar)
        (hcompact : IsCompact S.X)
        (hlight : sgsOracleLightTailAssumption_8_1_57 S law),
        sgsSelectedOutputGapStrictTailProbability S law x0
            (compactBeta S (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)))
            (by
              intro k
              simpa [innerBudgetNat] using compactBeta_innerBudget_pos S Dtilde hDtilde k)
            compactGamma compactGamma_mem_Icc
            (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde))
            N xStar hxStar
            (S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) *
              ((27 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact) / 2 +
                (16 * (1 + lambda) * Dtilde) / 3 +
                  (12 * lambda *
                      Real.sqrt (2 * Dtilde *
                        bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact)) /
                    Real.sqrt 3))
            hindep ≤
          ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) := by
    intro law x0 xStar N Dtilde lambda hDtilde hlambda hindep hxStar hcompact hlight
    simpa [sgsSelectedOutputGapStrictTailProbability] using
      Corollary8_3_compact_highProbability_sourceBoundary_feasibleBregman
        S law x0 xStar N Dtilde lambda hDtilde hlambda hindep hxStar hcompact hlight
  have sourceTyped_expected_target :
      ∀ (x0Core : ProxCorePoint S) (xStar : FeasiblePoint S)
        (N : PositiveTime) (beta gamma Gamma : PositiveTime → ℝ)
        (T : PositiveTime → ℕ),
        theorem82ExpectedBound_sourceTyped S x0Core xStar N beta gamma Gamma T =
          genericExpectedBound_sourceTyped S x0Core xStar N beta gamma Gamma T := by
    intro x0Core xStar N beta gamma Gamma T
    rfl
  have sourceTyped_expected_bridge :
      ∀ (x0 : FeasiblePoint S) (hx0 : x0.1 ∈ proxCore S.X S.proxPotential)
        (xStar : FeasiblePoint S) (N : PositiveTime)
        (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ),
        theorem82ExpectedBound_sourceTyped S ⟨x0.1, hx0⟩ xStar N beta gamma Gamma T =
          theorem82ExpectedBound_formulaExtension S x0 xStar N beta gamma Gamma T := by
    intro x0 hx0 xStar N beta gamma Gamma T
    exact theorem82ExpectedBound_sourceTyped_eq_formulaExtension S x0 hx0 xStar N beta gamma Gamma T
  exact
    ⟨theorem82Expected_sourceBoundary_zeroDimensionalCounterexampleCertificate_holds,
      theorem82HighProbability_sourceBoundary_zeroDimensionalCounterexampleCertificate_holds,
      theorem82_expected, theorem82_highProbability, theorem82_reverse_expected,
      theorem82_reverse_highProbability, corollary83_fixed_expected_selected_signature,
      corollary83_fixed_highProbability_selected_signature,
      corollary83_compact_expected_selected_signature,
      corollary83_compact_highProbability_selected_signature,
      sourceTyped_expected_target, sourceTyped_expected_bridge, trivial⟩

/-- Run-level formula-extension helper for Corollary 8.3(a), expected form, for the output of one
generated fixed-horizon SGS run. -/
theorem Corollary8_3_fixedHorizon_expected_runFormulaExtension [MeasurableSpace Ω]
    [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (N : PositiveTime) (Dtilde : ℝ)
    (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hrun :
      IsGeneratedSGSProcess_formulaExtension S x0 (fixedHorizonBeta S) fixedHorizonGamma
        (fixedHorizonInnerBudget S N.1 Dtilde) law.sample states inner)
    (hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner))
    (hDtilde : 0 < Dtilde) (hxStar : IsOptimalSolution S xStar) :
    (∫ ω, objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
          objectiveOn S ⟨xStar, hxStar.1⟩ ∂law.P) ≤
      (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
        (3 * bregmanFormulaOnX S x0 ⟨xStar, hxStar.1⟩ + 4 * Dtilde) := by
  have hgenerated_mean :
      generatedSFOUnbiased S law.P law.sample (sgsGeneratedOracleQuery S inner) :=
    law.generated_unbiased (sgsGeneratedOracleQuery S inner) hindep
  have hgenerated_var :
      generatedSFOVariance S law.P law.sample (sgsGeneratedOracleQuery S inner) :=
    law.generated_variance (sgsGeneratedOracleQuery S inner) hindep
  classical
  let Tsrc : PositiveTime → InnerBudget :=
    fixedHorizonInnerBudgetSource S N Dtilde hDtilde
  rcases fixed_horizon_outer_conditions (S := S) N Dtilde hDtilde with
    ⟨hlower, hGamma, hmono⟩
  have hdenom :
      theorem82DenominatorAdmissible (fixedHorizonBeta S)
        fixedHorizonGammaWeight (innerBudgetNat Tsrc) :=
    theorem82DenominatorAdmissible_forward_source_obligation S
      (fixedHorizonBeta S) fixedHorizonGamma fixedHorizonGammaWeight Tsrc
      (fixedHorizonBeta_pos S) hlower hGamma hmono
  have hgeneric_formula :
      (∫ ω, objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
          objectiveOn S ⟨xStar, hxStar.1⟩ ∂law.P) ≤
        theorem82ExpectedBound_formulaExtension S x0 ⟨xStar, hxStar.1⟩ N
          (fixedHorizonBeta S) fixedHorizonGamma fixedHorizonGammaWeight
          (innerBudgetNat Tsrc) := by
    exact
      SGSGenericConvergence_Theorem8_2_expected_runFormulaExtension_under_gammaRange
        (S := S) (law := law) (x0 := x0) (xStar := xStar)
        (beta := fixedHorizonBeta S) (gamma := fixedHorizonGamma)
        (Gamma := fixedHorizonGammaWeight) (T := innerBudgetNat Tsrc)
        (N := N) (states := states) (inner := inner)
        (by
          simpa [Tsrc, fixedHorizonInnerBudget, innerBudgetNat,
            fixedHorizonInnerBudgetSource] using hrun)
        hindep hxStar (fixedHorizonBeta_pos S) fixedHorizonGamma_mem_Icc
        hlower hGamma (by simpa [Tsrc] using hmono)
  have hscalar_checked :
      theorem82ExpectedBound_checkedFormulaExtension S x0 ⟨xStar, hxStar.1⟩ N
          (fixedHorizonBeta S) fixedHorizonGamma fixedHorizonGammaWeight
          Tsrc hdenom ≤
        (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
          (3 * bregmanFormulaOnX S x0 ⟨xStar, hxStar.1⟩ + 4 * Dtilde) := by
    dsimp [Tsrc] at hdenom ⊢
    exact
      fixed_horizon_expected_checked_bound_le_public (S := S) x0
        ⟨xStar, hxStar.1⟩ N Dtilde hDtilde hdenom
  have hscalar_formula :
      theorem82ExpectedBound_formulaExtension S x0 ⟨xStar, hxStar.1⟩ N
          (fixedHorizonBeta S) fixedHorizonGamma fixedHorizonGammaWeight
          (innerBudgetNat Tsrc) ≤
        (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
          (3 * bregmanFormulaOnX S x0 ⟨xStar, hxStar.1⟩ + 4 * Dtilde) := by
    simpa [
      theorem82ExpectedBound_checked_eq_formulaExtension S x0 ⟨xStar, hxStar.1⟩
        N (fixedHorizonBeta S) fixedHorizonGamma fixedHorizonGammaWeight Tsrc hdenom]
      using hscalar_checked
  exact le_trans hgeneric_formula hscalar_formula

/-- MDS-conditional run-level formula-extension helper for Corollary 8.3(a),
high-probability form. -/
theorem Corollary8_3_fixedHorizon_highProbability_runFormulaExtension_from_mds [MeasurableSpace Ω]
    [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (N : PositiveTime)
    (Dtilde lambda : ℝ)
    (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hrun :
      IsGeneratedSGSProcess_formulaExtension S x0 (fixedHorizonBeta S) fixedHorizonGamma
        (fixedHorizonInnerBudget S N.1 Dtilde) law.sample states inner)
    (hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner))
    (hDtilde : 0 < Dtilde) (hlambda : 0 < lambda)
    (hxStar : IsOptimalSolution S xStar)
    (hcompact : IsCompact S.X)
    (hmds : SGSLinearMDSLightTailInterface S law ⟨xStar, hxStar.1⟩ inner hcompact)
    (hlight : sgsOracleLightTailAssumption_8_1_57 S law) :
    law.P {ω | objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
          objectiveOn S ⟨xStar, hxStar.1⟩ >
            (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
              (3 * bregmanFormulaOnX S x0 ⟨xStar, hxStar.1⟩ +
                4 * (1 + lambda) * Dtilde +
                (4 * lambda *
                    Real.sqrt (Dtilde *
                      bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact)) /
                  Real.sqrt 3)} ≤
      ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) := by
  have hgenerated_mean :
      generatedSFOUnbiased S law.P law.sample (sgsGeneratedOracleQuery S inner) :=
    law.generated_unbiased (sgsGeneratedOracleQuery S inner) hindep
  have hgenerated_var :
      generatedSFOVariance S law.P law.sample (sgsGeneratedOracleQuery S inner) :=
    law.generated_variance (sgsGeneratedOracleQuery S inner) hindep
  have hgenerated_light :
      generatedSFOLightTail S law.P law.sample (sgsGeneratedOracleQuery S inner) :=
    sgsOracleLightTailAssumption_8_1_57.generated S law hlight
      (sgsGeneratedOracleQuery S inner) hindep
  classical
  let Tsrc : PositiveTime → InnerBudget :=
    fixedHorizonInnerBudgetSource S N Dtilde hDtilde
  have hconds := fixed_horizon_outer_conditions (S := S) N Dtilde hDtilde
  rcases hconds with ⟨hlower, hGamma, hmono⟩
  have hdenom :
      theorem82DenominatorAdmissible (fixedHorizonBeta S)
        fixedHorizonGammaWeight (innerBudgetNat Tsrc) :=
    theorem82DenominatorAdmissible_forward_source_obligation S
      (fixedHorizonBeta S) fixedHorizonGamma fixedHorizonGammaWeight Tsrc
      (fixedHorizonBeta_pos S) hlower hGamma hmono
  let checkedThreshold : ℝ :=
    theorem82ExpectedBound_checkedFormulaExtension S x0 ⟨xStar, hxStar.1⟩ N
        (fixedHorizonBeta S) fixedHorizonGamma fixedHorizonGammaWeight Tsrc hdenom +
      lambda *
        theorem82ProbabilityScale_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
          hcompact N (fixedHorizonBeta S) fixedHorizonGamma fixedHorizonGammaWeight
          Tsrc hdenom
  let publicThreshold : ℝ :=
    (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
      (3 * bregmanFormulaOnX S x0 ⟨xStar, hxStar.1⟩ +
        4 * (1 + lambda) * Dtilde +
        (4 * lambda *
            Real.sqrt (Dtilde *
              bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact)) /
          Real.sqrt 3)
  change
    law.P {ω | objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
          objectiveOn S ⟨xStar, hxStar.1⟩ > publicThreshold} ≤
      ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda))
  have hquery_strictPast_meas :
      ∀ κ i,
        Measurable[sgsStrictPastSampleSpace (Ω := Ω) law.sample κ i]
          (fun ω => sgsGeneratedOracleQuery S inner κ i ω) := by
    intro κ i
    exact (hmds κ i).1
  have hlinear_condExp_zero :
      ∀ κ i,
        let ζ : Ω → ℝ := fun ω =>
          ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
              (law.sample κ i ω),
            xStar - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ
        law.P[ζ | sgsStrictPastSampleSpace (Ω := Ω) law.sample κ i] =ᵐ[law.P] 0 := by
    intro κ i
    simpa using (hmds κ i).2.2.1
  have hlinear_exp_sq_integrable :
      ∀ κ i,
        let ζ : Ω → ℝ := fun ω =>
          ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
              (law.sample κ i ω),
            xStar - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ
        let lightScale : ℝ :=
          2 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact * S.sigmaSq
        Integrable (fun ω => Real.exp (ζ ω ^ 2 / lightScale)) law.P := by
    intro κ i
    simpa using (hmds κ i).2.2.2.1
  have hlinear_condExp_light :
      ∀ κ i,
        let ζ : Ω → ℝ := fun ω =>
          ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
              (law.sample κ i ω),
            xStar - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ
        let lightScale : ℝ :=
          2 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact * S.sigmaSq
        law.P[(fun ω => Real.exp (ζ ω ^ 2 / lightScale)) |
              sgsStrictPastSampleSpace (Ω := Ω) law.sample κ i] ≤ᵐ[law.P]
            fun _ => Real.exp 1 := by
    intro κ i
    simpa using (hmds κ i).2.2.2.2
  have hgeneric_formula :
      law.P {ω | objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
            objectiveOn S ⟨xStar, hxStar.1⟩ >
              theorem82ExpectedBound_formulaExtension S x0 ⟨xStar, hxStar.1⟩ N
                  (fixedHorizonBeta S) fixedHorizonGamma fixedHorizonGammaWeight
                  (innerBudgetNat Tsrc) +
                lambda *
                  theorem82ProbabilityScale_formulaExtension S ⟨xStar, hxStar.1⟩
                    hcompact N (fixedHorizonBeta S) fixedHorizonGamma
                    fixedHorizonGammaWeight (innerBudgetNat Tsrc)} ≤
        ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) := by
    exact
      SGSGenericConvergence_Theorem8_2_highProbability_runFormulaExtension_from_mds_under_gammaRange
        (S := S) (law := law) (x0 := x0) (xStar := xStar)
        (beta := fixedHorizonBeta S) (gamma := fixedHorizonGamma)
        (Gamma := fixedHorizonGammaWeight) (T := innerBudgetNat Tsrc)
        (N := N) (lambda := lambda) (states := states) (inner := inner)
        (by
          simpa [Tsrc, fixedHorizonInnerBudget, innerBudgetNat,
            fixedHorizonInnerBudgetSource] using hrun)
        hindep hlambda hxStar (fixedHorizonBeta_pos S) fixedHorizonGamma_mem_Icc
        hlight hlower hGamma (by simpa [Tsrc] using hmono) hcompact
        hquery_strictPast_meas hlinear_condExp_zero hlinear_exp_sq_integrable
        hlinear_condExp_light
  have hgeneric :
      law.P {ω | objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
            objectiveOn S ⟨xStar, hxStar.1⟩ > checkedThreshold} ≤
        ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) := by
    simpa [checkedThreshold,
      theorem82ExpectedBound_checked_eq_formulaExtension S x0 ⟨xStar, hxStar.1⟩
        N (fixedHorizonBeta S) fixedHorizonGamma fixedHorizonGammaWeight Tsrc hdenom,
      theorem82ProbabilityScale_checked_eq_formulaExtension S ⟨xStar, hxStar.1⟩
        hcompact N (fixedHorizonBeta S) fixedHorizonGamma fixedHorizonGammaWeight Tsrc hdenom]
      using hgeneric_formula
  have hexpected :
      theorem82ExpectedBound_checkedFormulaExtension S x0 ⟨xStar, hxStar.1⟩ N
          (fixedHorizonBeta S) fixedHorizonGamma fixedHorizonGammaWeight Tsrc hdenom ≤
        (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
          (3 * bregmanFormulaOnX S x0 ⟨xStar, hxStar.1⟩ + 4 * Dtilde) := by
    dsimp [Tsrc] at hdenom ⊢
    exact
      fixed_horizon_expected_checked_bound_le_public (S := S) x0
        ⟨xStar, hxStar.1⟩ N Dtilde hDtilde hdenom
  have hscale :
      theorem82ProbabilityScale_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
          hcompact N (fixedHorizonBeta S) fixedHorizonGamma fixedHorizonGammaWeight
          Tsrc hdenom ≤
        (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
          (4 * Dtilde +
            (4 * Real.sqrt (Dtilde *
              bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact)) /
              Real.sqrt 3) := by
    dsimp [Tsrc] at hdenom ⊢
    exact
      fixed_horizon_probability_scale_checked_le_public (S := S)
        ⟨xStar, hxStar.1⟩ hcompact N Dtilde hDtilde hdenom
  have hthreshold : checkedThreshold ≤ publicThreshold := by
    dsimp [checkedThreshold, publicThreshold]
    have hlambda_nonneg : 0 ≤ lambda := le_of_lt hlambda
    have hscale_mul :=
      mul_le_mul_of_nonneg_left hscale hlambda_nonneg
    calc
      theorem82ExpectedBound_checkedFormulaExtension S x0 ⟨xStar, hxStar.1⟩ N
            (fixedHorizonBeta S) fixedHorizonGamma fixedHorizonGammaWeight Tsrc hdenom +
          lambda *
            theorem82ProbabilityScale_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
              hcompact N (fixedHorizonBeta S) fixedHorizonGamma fixedHorizonGammaWeight
              Tsrc hdenom
          ≤
        (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
            (3 * bregmanFormulaOnX S x0 ⟨xStar, hxStar.1⟩ + 4 * Dtilde) +
          lambda *
            ((2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
              (4 * Dtilde +
                (4 * Real.sqrt (Dtilde *
                  bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact)) /
                  Real.sqrt 3)) := add_le_add hexpected hscale_mul
      _ =
        (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
          (3 * bregmanFormulaOnX S x0 ⟨xStar, hxStar.1⟩ +
            4 * (1 + lambda) * Dtilde +
            (4 * lambda *
                Real.sqrt (Dtilde *
                  bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact)) /
              Real.sqrt 3) := by
            ring
  have hmonoTail :
      law.P {ω | objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
            objectiveOn S ⟨xStar, hxStar.1⟩ > publicThreshold} ≤
        law.P {ω | objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
            objectiveOn S ⟨xStar, hxStar.1⟩ > checkedThreshold} :=
    measure_mono (by
      intro ω hω
      exact lt_of_le_of_lt hthreshold hω)
  exact le_trans hmonoTail hgeneric

/-- Run-level formula-extension helper for Corollary 8.3(b), expected form, for the compact policy. -/
theorem Corollary8_3_compact_expected_runFormulaExtension [MeasurableSpace Ω]
    [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (N : PositiveTime) (Dtilde : ℝ)
    (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hrun :
      IsGeneratedSGSProcess_formulaExtension S x0 (compactBeta S (compactInnerBudget S Dtilde)) compactGamma
        (compactInnerBudget S Dtilde) law.sample states inner)
    (hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner))
    (hDtilde : 0 < Dtilde) (hxStar : IsOptimalSolution S xStar)
    (hcompact : IsCompact S.X) :
    (∫ ω, objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
          objectiveOn S ⟨xStar, hxStar.1⟩ ∂law.P) ≤
      S.lSmooth / (((N.1 : ℝ) + 1) * ((N.1 : ℝ) + 2)) *
        ((27 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact) / 2 +
          (16 * Dtilde) / 3) := by
  have hgenerated_mean :
      generatedSFOUnbiased S law.P law.sample (sgsGeneratedOracleQuery S inner) :=
    law.generated_unbiased (sgsGeneratedOracleQuery S inner) hindep
  have hgenerated_var :
      generatedSFOVariance S law.P law.sample (sgsGeneratedOracleQuery S inner) :=
    law.generated_variance (sgsGeneratedOracleQuery S inner) hindep
  classical
  let Tsrc : PositiveTime → InnerBudget := compactInnerBudgetSource S Dtilde hDtilde
  let beta : PositiveTime → ℝ := compactBeta S (innerBudgetNat Tsrc)
  have hbeta : ∀ k : PositiveTime, 0 < beta k := by
    intro k
    simpa [beta, Tsrc, innerBudgetNat, compactInnerBudgetSource] using
      compactBeta_innerBudget_pos S Dtilde hDtilde k
  rcases compact_policy_outer_conditions (S := S) Dtilde hDtilde with
    ⟨hlower, hGamma, hmono⟩
  have hdenom :
      theorem82DenominatorAdmissible beta compactGammaWeight (innerBudgetNat Tsrc) :=
    theorem82DenominatorAdmissible_reverse_source_obligation S beta compactGamma
      compactGammaWeight Tsrc hbeta
      (by simpa [beta, Tsrc] using hlower) hGamma
      (by simpa [beta, Tsrc] using hmono)
  have hgeneric_raw :
      (∫ ω, objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
          objectiveOn S ⟨xStar, hxStar.1⟩ ∂law.P) ≤
        compactGamma N * beta N *
            bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact *
            (1 - psWeightProduct spsP (innerBudgetNat Tsrc N))⁻¹ +
          compactGammaWeight N *
            (Finset.range N.1).sum (fun k =>
              let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
              (Finset.range (innerBudgetNat Tsrc κ)).sum (fun i =>
                let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
                (S.mGrowth ^ 2 + S.sigmaSq) * compactGamma κ *
                    psWeightProduct spsP (innerBudgetNat Tsrc κ) /
                  (beta κ * compactGammaWeight κ *
                    (1 - psWeightProduct spsP (innerBudgetNat Tsrc κ)) *
                      spsP ι ^ 2 * psWeightProduct spsP i))) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      SGSGenericConvergence_Theorem8_2_reverse_expected_runFormulaExtension
        (S := S) (law := law) (x0 := x0) (xStar := xStar)
        (beta := beta) (gamma := compactGamma) (Gamma := compactGammaWeight)
        (T := innerBudgetNat Tsrc) (N := N) (states := states) (inner := inner)
        (by
          simpa [beta, Tsrc, compactInnerBudget, innerBudgetNat,
            compactInnerBudgetSource] using hrun)
        hindep hxStar hbeta hcompact
        (by simpa [beta, Tsrc] using hlower) hGamma
        (by simpa [beta, Tsrc] using hmono)
  have hgeneric_checked :
      (∫ ω, objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
          objectiveOn S ⟨xStar, hxStar.1⟩ ∂law.P) ≤
        theorem82ReverseExpectedBound_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
          hcompact N beta compactGamma compactGammaWeight Tsrc hdenom := by
    simpa [
      theorem82ReverseExpectedBound_checked_eq_formulaExtension S ⟨xStar, hxStar.1⟩
        hcompact N beta compactGamma compactGammaWeight Tsrc hdenom,
      mul_comm, mul_left_comm, mul_assoc] using hgeneric_raw
  have hscalar :
      theorem82ReverseExpectedBound_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
          hcompact N beta compactGamma compactGammaWeight Tsrc hdenom ≤
        S.lSmooth / (((N.1 : ℝ) + 1) * ((N.1 : ℝ) + 2)) *
          ((27 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact) / 2 +
            (16 * Dtilde) / 3) := by
    simpa [beta, Tsrc] using
      compact_reverse_expected_checked_bound_le_public (S := S)
        ⟨xStar, hxStar.1⟩ hcompact N Dtilde hDtilde hdenom
  exact le_trans hgeneric_checked hscalar

/-- MDS-conditional run-level formula-extension helper for the relaxed Corollary
8.3(b) high-probability form, for the compact policy. -/
theorem Corollary8_3_compact_highProbability_runFormulaExtension_from_mds [MeasurableSpace Ω]
    [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (N : PositiveTime)
    (Dtilde lambda : ℝ)
    (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hrun :
      IsGeneratedSGSProcess_formulaExtension S x0 (compactBeta S (compactInnerBudget S Dtilde)) compactGamma
        (compactInnerBudget S Dtilde) law.sample states inner)
    (hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner))
    (hDtilde : 0 < Dtilde) (hlambda : 0 < lambda)
    (hxStar : IsOptimalSolution S xStar)
    (hcompact : IsCompact S.X)
    (hmds : SGSLinearMDSLightTailInterface S law ⟨xStar, hxStar.1⟩ inner hcompact)
    (hlight : sgsOracleLightTailAssumption_8_1_57 S law) :
    law.P {ω | objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
          objectiveOn S ⟨xStar, hxStar.1⟩ >
            S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) *
              ((27 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact) / 2 +
                (16 * (1 + lambda) * Dtilde) / 3 +
                  (12 * lambda *
                      Real.sqrt (2 * Dtilde *
                        bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact)) /
                    Real.sqrt 3)} ≤
      ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) := by
  have hgenerated_mean :
      generatedSFOUnbiased S law.P law.sample (sgsGeneratedOracleQuery S inner) :=
    law.generated_unbiased (sgsGeneratedOracleQuery S inner) hindep
  have hgenerated_var :
      generatedSFOVariance S law.P law.sample (sgsGeneratedOracleQuery S inner) :=
    law.generated_variance (sgsGeneratedOracleQuery S inner) hindep
  have hgenerated_light :
      generatedSFOLightTail S law.P law.sample (sgsGeneratedOracleQuery S inner) :=
    sgsOracleLightTailAssumption_8_1_57.generated S law hlight
      (sgsGeneratedOracleQuery S inner) hindep
  classical
  let Tsrc : PositiveTime → InnerBudget := compactInnerBudgetSource S Dtilde hDtilde
  let beta : PositiveTime → ℝ := compactBeta S (innerBudgetNat Tsrc)
  have hbeta : ∀ k : PositiveTime, 0 < beta k := by
    intro k
    simpa [beta, Tsrc, innerBudgetNat, compactInnerBudgetSource] using
      compactBeta_innerBudget_pos S Dtilde hDtilde k
  rcases compact_policy_outer_conditions (S := S) Dtilde hDtilde with
    ⟨hlower, hGamma, hmono⟩
  have hdenom :
      theorem82DenominatorAdmissible beta compactGammaWeight (innerBudgetNat Tsrc) :=
    theorem82DenominatorAdmissible_reverse_source_obligation S beta compactGamma
      compactGammaWeight Tsrc hbeta
      (by simpa [beta, Tsrc] using hlower) hGamma
      (by simpa [beta, Tsrc] using hmono)
  let checkedThreshold : ℝ :=
    theorem82ReverseExpectedBound_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
        hcompact N beta compactGamma compactGammaWeight Tsrc hdenom +
      lambda *
        theorem82ProbabilityScale_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
          hcompact N beta compactGamma compactGammaWeight Tsrc hdenom
  let publicThreshold : ℝ :=
    S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) *
      ((27 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact) / 2 +
        (16 * (1 + lambda) * Dtilde) / 3 +
          (12 * lambda *
              Real.sqrt (2 * Dtilde *
                bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact)) /
            Real.sqrt 3)
  change
    law.P {ω | objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
          objectiveOn S ⟨xStar, hxStar.1⟩ > publicThreshold} ≤
      ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda))
  have hquery_strictPast_meas :
      ∀ κ i,
        Measurable[sgsStrictPastSampleSpace (Ω := Ω) law.sample κ i]
          (fun ω => sgsGeneratedOracleQuery S inner κ i ω) := by
    intro κ i
    exact (hmds κ i).1
  have hlinear_condExp_zero :
      ∀ κ i,
        let ζ : Ω → ℝ := fun ω =>
          ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
              (law.sample κ i ω),
            xStar - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ
        law.P[ζ | sgsStrictPastSampleSpace (Ω := Ω) law.sample κ i] =ᵐ[law.P] 0 := by
    intro κ i
    simpa using (hmds κ i).2.2.1
  have hlinear_exp_sq_integrable :
      ∀ κ i,
        let ζ : Ω → ℝ := fun ω =>
          ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
              (law.sample κ i ω),
            xStar - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ
        let lightScale : ℝ :=
          2 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact * S.sigmaSq
        Integrable (fun ω => Real.exp (ζ ω ^ 2 / lightScale)) law.P := by
    intro κ i
    simpa using (hmds κ i).2.2.2.1
  have hlinear_condExp_light :
      ∀ κ i,
        let ζ : Ω → ℝ := fun ω =>
          ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
              (law.sample κ i ω),
            xStar - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ
        let lightScale : ℝ :=
          2 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact * S.sigmaSq
        law.P[(fun ω => Real.exp (ζ ω ^ 2 / lightScale)) |
              sgsStrictPastSampleSpace (Ω := Ω) law.sample κ i] ≤ᵐ[law.P]
            fun _ => Real.exp 1 := by
    intro κ i
    simpa using (hmds κ i).2.2.2.2
  have hgeneric_formula :
      law.P {ω | objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
            objectiveOn S ⟨xStar, hxStar.1⟩ >
              (compactGamma N * beta N *
                  bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact *
                    (1 - psWeightProduct spsP (innerBudgetNat Tsrc N))⁻¹ +
                compactGammaWeight N *
                  (Finset.range N.1).sum (fun k =>
                    let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
                    (Finset.range (innerBudgetNat Tsrc κ)).sum (fun i =>
                      let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                      (S.mGrowth ^ 2 + S.sigmaSq) * compactGamma κ *
                          psWeightProduct spsP (innerBudgetNat Tsrc κ) /
                        (beta κ * compactGammaWeight κ *
                          (1 - psWeightProduct spsP (innerBudgetNat Tsrc κ)) *
                          spsP ι ^ 2 * psWeightProduct spsP i))) +
                lambda *
                  theorem82ProbabilityScale_formulaExtension S ⟨xStar, hxStar.1⟩
                    hcompact N beta compactGamma compactGammaWeight
                    (innerBudgetNat Tsrc))} ≤
        ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      SGSGenericConvergence_Theorem8_2_reverse_highProbability_formulaExtension_from_mds_bridge_under_gammaRange
        (S := S) (law := law) (x0 := x0) (xStar := xStar)
        (beta := beta) (gamma := compactGamma) (Gamma := compactGammaWeight)
        (T := innerBudgetNat Tsrc) (N := N) (lambda := lambda)
        (states := states) (inner := inner)
        compactGamma_mem_Icc
        (by
          simpa [beta, Tsrc, compactInnerBudget, innerBudgetNat,
            compactInnerBudgetSource] using hrun)
        hindep hlambda hxStar hcompact hlight
        (by simpa [beta, Tsrc] using hlower) hGamma
        (by simpa [beta, Tsrc] using hmono)
        hquery_strictPast_meas hlinear_condExp_zero hlinear_exp_sq_integrable
        hlinear_condExp_light
  have hgeneric :
      law.P {ω | objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
            objectiveOn S ⟨xStar, hxStar.1⟩ > checkedThreshold} ≤
        ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) := by
    simpa [checkedThreshold,
      theorem82ReverseExpectedBound_checked_eq_formulaExtension
        S ⟨xStar, hxStar.1⟩ hcompact N beta compactGamma compactGammaWeight
        Tsrc hdenom,
      theorem82ProbabilityScale_checked_eq_formulaExtension
        S ⟨xStar, hxStar.1⟩ hcompact N beta compactGamma compactGammaWeight
        Tsrc hdenom] using hgeneric_formula
  have hexpected_raw :
      theorem82ReverseExpectedBound_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
          hcompact N beta compactGamma compactGammaWeight Tsrc hdenom ≤
        S.lSmooth / (((N.1 : ℝ) + 1) * ((N.1 : ℝ) + 2)) *
          ((27 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact) / 2 +
            (16 * Dtilde) / 3) := by
    simpa [beta, Tsrc] using
      compact_reverse_expected_checked_bound_le_public (S := S)
        ⟨xStar, hxStar.1⟩ hcompact N Dtilde hDtilde hdenom
  have hexpected :
      theorem82ReverseExpectedBound_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
          hcompact N beta compactGamma compactGammaWeight Tsrc hdenom ≤
        S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) *
          ((27 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact) / 2 +
            (16 * Dtilde) / 3) := by
    let B : ℝ :=
      (27 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact) / 2 +
        (16 * Dtilde) / 3
    have hB_nonneg : 0 ≤ B := by
      have hV_nonneg :
          0 ≤ bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact :=
        bregmanEnvelope_formulaExtension_nonneg S ⟨xStar, hxStar.1⟩ hcompact
      dsimp [B]
      nlinarith [hV_nonneg, hDtilde]
    have hN_pos : 0 < (N.1 : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one N.2)
    have hN1_pos : 0 < (N.1 : ℝ) + 1 := by positivity
    have hN2_pos : 0 < (N.1 : ℝ) + 2 := by positivity
    have hden0_pos : 0 < (N.1 : ℝ) * ((N.1 : ℝ) + 2) :=
      mul_pos hN_pos hN2_pos
    have hden1_pos : 0 < (((N.1 : ℝ) + 1) * ((N.1 : ℝ) + 2)) :=
      mul_pos hN1_pos hN2_pos
    have hfactor :
        S.lSmooth / (((N.1 : ℝ) + 1) * ((N.1 : ℝ) + 2)) ≤
          S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) := by
      rw [div_le_div_iff₀ hden1_pos hden0_pos]
      nlinarith [S.L_pos, hN_pos, hN2_pos]
    exact le_trans hexpected_raw
      (by
        simpa [B] using mul_le_mul_of_nonneg_right hfactor hB_nonneg)
  have hscale :
      theorem82ProbabilityScale_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
          hcompact N beta compactGamma compactGammaWeight Tsrc hdenom ≤
        S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) *
          ((16 * Dtilde) / 3 +
            (12 * Real.sqrt (2 * Dtilde *
              bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact)) /
              Real.sqrt 3) := by
    rw [theorem82ProbabilityScale_checked_eq_formulaExtension
      S ⟨xStar, hxStar.1⟩ hcompact N beta compactGamma compactGammaWeight
      Tsrc hdenom]
    simpa [beta, Tsrc] using
      compact_reverse_probability_scale_full_le_public (S := S)
        ⟨xStar, hxStar.1⟩ hcompact N Dtilde hDtilde
  have hthreshold : checkedThreshold ≤ publicThreshold := by
    dsimp [checkedThreshold, publicThreshold]
    have hlambda_nonneg : 0 ≤ lambda := le_of_lt hlambda
    have hscale_mul :=
      mul_le_mul_of_nonneg_left hscale hlambda_nonneg
    calc
      theorem82ReverseExpectedBound_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
            hcompact N beta compactGamma compactGammaWeight Tsrc hdenom +
          lambda *
            theorem82ProbabilityScale_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
              hcompact N beta compactGamma compactGammaWeight Tsrc hdenom
          ≤
        S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) *
            ((27 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact) / 2 +
              (16 * Dtilde) / 3) +
          lambda *
            (S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) *
              ((16 * Dtilde) / 3 +
                (12 * Real.sqrt (2 * Dtilde *
                  bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact)) /
                  Real.sqrt 3)) := add_le_add hexpected hscale_mul
      _ =
        S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) *
          ((27 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact) / 2 +
            (16 * (1 + lambda) * Dtilde) / 3 +
              (12 * lambda *
                  Real.sqrt (2 * Dtilde *
                    bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact)) /
                Real.sqrt 3) := by
            ring
  have hmonoTail :
      law.P {ω | objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
            objectiveOn S ⟨xStar, hxStar.1⟩ > publicThreshold} ≤
        law.P {ω | objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
            objectiveOn S ⟨xStar, hxStar.1⟩ > checkedThreshold} :=
    measure_mono (by
      intro ω hω
      exact lt_of_le_of_lt hthreshold hω)
  exact le_trans hmonoTail hgeneric

/-- Formula-extension helper corresponding to Corollary 8.3(a), expected form. -/
theorem Corollary8_3_fixedHorizon_expected_formulaExtension [MeasurableSpace Ω]
    [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (N : PositiveTime) (Dtilde : ℝ)
    (hDtilde : 0 < Dtilde) (hxStar : IsOptimalSolution S xStar)
    (hindep : sfoIndependent S law.P law.sample
      (sgsOracleQuery S x0 (fixedHorizonBeta S) (fixedHorizonBeta_pos S)
        fixedHorizonGamma fixedHorizonGamma_mem_Icc
        (fixedHorizonInnerBudget S N.1 Dtilde) law.sample)) :
    (∫ ω,
        objectiveOn S
          (sgsOutput_formulaExtensionSelector S x0 (fixedHorizonBeta S) (fixedHorizonBeta_pos S)
            fixedHorizonGamma fixedHorizonGamma_mem_Icc
            (fixedHorizonInnerBudget S N.1 Dtilde) law.sample N.1 ω) -
          objectiveOn S ⟨xStar, hxStar.1⟩ ∂law.P) ≤
      (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
        (3 * bregmanFormulaOnX S x0 ⟨xStar, hxStar.1⟩ + 4 * Dtilde) := by
  have hgenerated_mean :
      generatedSFOUnbiased S law.P law.sample
        (sgsOracleQuery S x0 (fixedHorizonBeta S) (fixedHorizonBeta_pos S)
          fixedHorizonGamma fixedHorizonGamma_mem_Icc
          (fixedHorizonInnerBudget S N.1 Dtilde) law.sample) :=
    law.generated_unbiased
      (sgsOracleQuery S x0 (fixedHorizonBeta S) (fixedHorizonBeta_pos S)
        fixedHorizonGamma fixedHorizonGamma_mem_Icc
        (fixedHorizonInnerBudget S N.1 Dtilde) law.sample) hindep
  have hgenerated_var :
      generatedSFOVariance S law.P law.sample
        (sgsOracleQuery S x0 (fixedHorizonBeta S) (fixedHorizonBeta_pos S)
          fixedHorizonGamma fixedHorizonGamma_mem_Icc
          (fixedHorizonInnerBudget S N.1 Dtilde) law.sample) :=
    law.generated_variance
      (sgsOracleQuery S x0 (fixedHorizonBeta S) (fixedHorizonBeta_pos S)
        fixedHorizonGamma fixedHorizonGamma_mem_Icc
        (fixedHorizonInnerBudget S N.1 Dtilde) law.sample) hindep
  simpa [sgsSelectedExpectedOutputGap, fixedHorizonInnerBudget, innerBudgetNat,
    fixedHorizonInnerBudgetSource] using
    Corollary8_3_fixedHorizon_expected_sourceBoundary_feasibleBregman
      (S := S) (law := law) (x0 := x0) (xStar := xStar) (N := N)
      (Dtilde := Dtilde) hDtilde
      (by
        simpa [fixedHorizonInnerBudget, innerBudgetNat, fixedHorizonInnerBudgetSource] using
          hindep)
      hxStar

/-- Formula-extension helper corresponding to Corollary 8.3(a), high-probability
form. -/
theorem Corollary8_3_fixedHorizon_highProbability_formulaExtension [MeasurableSpace Ω]
    [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (N : PositiveTime)
    (Dtilde lambda : ℝ)
    (hDtilde : 0 < Dtilde) (hlambda : 0 < lambda)
    (hxStar : IsOptimalSolution S xStar)
    (hcompact : IsCompact S.X)
    (hlight : sgsOracleLightTailAssumption_8_1_57 S law)
    (hindep : sfoIndependent S law.P law.sample
      (sgsOracleQuery S x0 (fixedHorizonBeta S) (fixedHorizonBeta_pos S)
        fixedHorizonGamma fixedHorizonGamma_mem_Icc
        (fixedHorizonInnerBudget S N.1 Dtilde) law.sample)) :
    law.P {ω | objectiveOn S
            (sgsOutput_formulaExtensionSelector S x0 (fixedHorizonBeta S) (fixedHorizonBeta_pos S)
              fixedHorizonGamma fixedHorizonGamma_mem_Icc
              (fixedHorizonInnerBudget S N.1 Dtilde) law.sample N.1 ω) -
          objectiveOn S ⟨xStar, hxStar.1⟩ >
            (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
              (3 * bregmanFormulaOnX S x0 ⟨xStar, hxStar.1⟩ +
                4 * (1 + lambda) * Dtilde +
                (4 * lambda *
                    Real.sqrt (Dtilde *
                      bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact)) /
                  Real.sqrt 3)} ≤
      ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) := by
  have hgenerated_mean :
      generatedSFOUnbiased S law.P law.sample
        (sgsOracleQuery S x0 (fixedHorizonBeta S) (fixedHorizonBeta_pos S)
          fixedHorizonGamma fixedHorizonGamma_mem_Icc
          (fixedHorizonInnerBudget S N.1 Dtilde) law.sample) :=
    law.generated_unbiased
      (sgsOracleQuery S x0 (fixedHorizonBeta S) (fixedHorizonBeta_pos S)
        fixedHorizonGamma fixedHorizonGamma_mem_Icc
        (fixedHorizonInnerBudget S N.1 Dtilde) law.sample) hindep
  have hgenerated_var :
      generatedSFOVariance S law.P law.sample
        (sgsOracleQuery S x0 (fixedHorizonBeta S) (fixedHorizonBeta_pos S)
          fixedHorizonGamma fixedHorizonGamma_mem_Icc
          (fixedHorizonInnerBudget S N.1 Dtilde) law.sample) :=
    law.generated_variance
      (sgsOracleQuery S x0 (fixedHorizonBeta S) (fixedHorizonBeta_pos S)
        fixedHorizonGamma fixedHorizonGamma_mem_Icc
        (fixedHorizonInnerBudget S N.1 Dtilde) law.sample) hindep
  have hgenerated_light :
      generatedSFOLightTail S law.P law.sample
        (sgsOracleQuery S x0 (fixedHorizonBeta S) (fixedHorizonBeta_pos S)
          fixedHorizonGamma fixedHorizonGamma_mem_Icc
          (fixedHorizonInnerBudget S N.1 Dtilde) law.sample) :=
    sgsOracleLightTailAssumption_8_1_57.generated S law hlight
      (sgsOracleQuery S x0 (fixedHorizonBeta S) (fixedHorizonBeta_pos S)
        fixedHorizonGamma fixedHorizonGamma_mem_Icc
        (fixedHorizonInnerBudget S N.1 Dtilde) law.sample) hindep
  simpa [sgsSelectedOutputGapStrictTailProbability, fixedHorizonInnerBudget, innerBudgetNat,
    fixedHorizonInnerBudgetSource] using
    Corollary8_3_fixedHorizon_highProbability_sourceBoundary_feasibleBregman
      (S := S) (law := law) (x0 := x0) (xStar := xStar) (N := N)
      (Dtilde := Dtilde) (lambda := lambda) hDtilde hlambda
      (by
        simpa [fixedHorizonInnerBudget, innerBudgetNat, fixedHorizonInnerBudgetSource] using
          hindep)
      hxStar hcompact hlight

/-- Formula-extension helper corresponding to Corollary 8.3(b), expected form. -/
theorem Corollary8_3_compact_expected_formulaExtension [MeasurableSpace Ω]
    [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (N : PositiveTime) (Dtilde : ℝ)
    (hDtilde : 0 < Dtilde) (hxStar : IsOptimalSolution S xStar)
    (hcompact : IsCompact S.X)
    (hindep : sfoIndependent S law.P law.sample
      (sgsOracleQuery S x0 (compactBeta S (compactInnerBudget S Dtilde))
        (compactBeta_innerBudget_pos S Dtilde hDtilde)
        compactGamma compactGamma_mem_Icc (compactInnerBudget S Dtilde) law.sample)) :
    (∫ ω,
        objectiveOn S
          (sgsOutput_formulaExtensionSelector S x0 (compactBeta S (compactInnerBudget S Dtilde))
            (compactBeta_innerBudget_pos S Dtilde hDtilde)
            compactGamma compactGamma_mem_Icc (compactInnerBudget S Dtilde) law.sample N.1 ω) -
          objectiveOn S ⟨xStar, hxStar.1⟩ ∂law.P) ≤
      S.lSmooth / (((N.1 : ℝ) + 1) * ((N.1 : ℝ) + 2)) *
        ((27 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact) / 2 +
          (16 * Dtilde) / 3) := by
  have hgenerated_mean :
      generatedSFOUnbiased S law.P law.sample
        (sgsOracleQuery S x0 (compactBeta S (compactInnerBudget S Dtilde))
          (compactBeta_innerBudget_pos S Dtilde hDtilde)
          compactGamma compactGamma_mem_Icc (compactInnerBudget S Dtilde) law.sample) :=
    law.generated_unbiased
      (sgsOracleQuery S x0 (compactBeta S (compactInnerBudget S Dtilde))
        (compactBeta_innerBudget_pos S Dtilde hDtilde)
        compactGamma compactGamma_mem_Icc (compactInnerBudget S Dtilde) law.sample) hindep
  have hgenerated_var :
      generatedSFOVariance S law.P law.sample
        (sgsOracleQuery S x0 (compactBeta S (compactInnerBudget S Dtilde))
          (compactBeta_innerBudget_pos S Dtilde hDtilde)
          compactGamma compactGamma_mem_Icc (compactInnerBudget S Dtilde) law.sample) :=
    law.generated_variance
      (sgsOracleQuery S x0 (compactBeta S (compactInnerBudget S Dtilde))
        (compactBeta_innerBudget_pos S Dtilde hDtilde)
        compactGamma compactGamma_mem_Icc (compactInnerBudget S Dtilde) law.sample) hindep
  simpa [sgsSelectedExpectedOutputGap, compactInnerBudget, innerBudgetNat,
    compactInnerBudgetSource] using
    Corollary8_3_compact_expected_sourceBoundary_feasibleBregman
      (S := S) (law := law) (x0 := x0) (xStar := xStar) (N := N)
      (Dtilde := Dtilde) hDtilde
      (by
        simpa [compactInnerBudget, innerBudgetNat, compactInnerBudgetSource] using hindep)
      hxStar hcompact

/-- Formula-extension helper corresponding to Corollary 8.3(b), high-probability
form. -/
theorem Corollary8_3_compact_highProbability_formulaExtension [MeasurableSpace Ω]
    [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (N : PositiveTime)
    (Dtilde lambda : ℝ)
    (hDtilde : 0 < Dtilde) (hlambda : 0 < lambda)
    (hxStar : IsOptimalSolution S xStar)
    (hcompact : IsCompact S.X)
    (hlight : sgsOracleLightTailAssumption_8_1_57 S law)
    (hindep : sfoIndependent S law.P law.sample
      (sgsOracleQuery S x0 (compactBeta S (compactInnerBudget S Dtilde))
        (compactBeta_innerBudget_pos S Dtilde hDtilde)
        compactGamma compactGamma_mem_Icc (compactInnerBudget S Dtilde) law.sample)) :
    law.P {ω | objectiveOn S
            (sgsOutput_formulaExtensionSelector S x0 (compactBeta S (compactInnerBudget S Dtilde))
              (compactBeta_innerBudget_pos S Dtilde hDtilde)
              compactGamma compactGamma_mem_Icc (compactInnerBudget S Dtilde) law.sample N.1 ω) -
          objectiveOn S ⟨xStar, hxStar.1⟩ >
            S.lSmooth / ((N.1 : ℝ) * ((N.1 : ℝ) + 2)) *
              ((27 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact) / 2 +
                (16 * (1 + lambda) * Dtilde) / 3 +
                  (12 * lambda *
                      Real.sqrt (2 * Dtilde *
                        bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact)) /
                    Real.sqrt 3)} ≤
      ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) := by
  have hgenerated_mean :
      generatedSFOUnbiased S law.P law.sample
        (sgsOracleQuery S x0 (compactBeta S (compactInnerBudget S Dtilde))
          (compactBeta_innerBudget_pos S Dtilde hDtilde)
          compactGamma compactGamma_mem_Icc (compactInnerBudget S Dtilde) law.sample) :=
    law.generated_unbiased
      (sgsOracleQuery S x0 (compactBeta S (compactInnerBudget S Dtilde))
        (compactBeta_innerBudget_pos S Dtilde hDtilde)
        compactGamma compactGamma_mem_Icc (compactInnerBudget S Dtilde) law.sample) hindep
  have hgenerated_var :
      generatedSFOVariance S law.P law.sample
        (sgsOracleQuery S x0 (compactBeta S (compactInnerBudget S Dtilde))
          (compactBeta_innerBudget_pos S Dtilde hDtilde)
          compactGamma compactGamma_mem_Icc (compactInnerBudget S Dtilde) law.sample) :=
    law.generated_variance
      (sgsOracleQuery S x0 (compactBeta S (compactInnerBudget S Dtilde))
        (compactBeta_innerBudget_pos S Dtilde hDtilde)
        compactGamma compactGamma_mem_Icc (compactInnerBudget S Dtilde) law.sample) hindep
  have hgenerated_light :
      generatedSFOLightTail S law.P law.sample
        (sgsOracleQuery S x0 (compactBeta S (compactInnerBudget S Dtilde))
          (compactBeta_innerBudget_pos S Dtilde hDtilde)
          compactGamma compactGamma_mem_Icc (compactInnerBudget S Dtilde) law.sample) :=
    sgsOracleLightTailAssumption_8_1_57.generated S law hlight
      (sgsOracleQuery S x0 (compactBeta S (compactInnerBudget S Dtilde))
        (compactBeta_innerBudget_pos S Dtilde hDtilde)
        compactGamma compactGamma_mem_Icc (compactInnerBudget S Dtilde) law.sample) hindep
  simpa [sgsSelectedOutputGapStrictTailProbability, compactInnerBudget, innerBudgetNat,
    compactInnerBudgetSource] using
    Corollary8_3_compact_highProbability_sourceBoundary_feasibleBregman
      (S := S) (law := law) (x0 := x0) (xStar := xStar) (N := N)
      (Dtilde := Dtilde) (lambda := lambda) hDtilde hlambda
      (by
        simpa [compactInnerBudget, innerBudgetNat, compactInnerBudgetSource] using hindep)
      hxStar hcompact hlight

end StochasticGradientSliding
