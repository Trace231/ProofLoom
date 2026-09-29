import Mathlib.Tactic
import SOptLib.Glue.Algebra

open MeasureTheory
open scoped BigOperators

-- Generalization plan (G1):
-- concept/name: strict measure tail for the squared norm of an inverse-cardinality
-- finite-sum average from the strict tail of the unnormalized sum.
-- generality used: arbitrary finite index set, arbitrary measurable sample space,
-- arbitrary measure, and any real seminormed vector space; no probability, martingale,
-- smoothness, convexity, interval indexing, or finite-dimensional structure is used.
-- portable call pattern: finite-sample stochastic proofs first bound the
-- unnormalized squared norm of a residual/noise sum by a constant per-index
-- variance budget, then normalize by the sample count without changing the final
-- probability budget.
-- counterargument checked: this is not covered by finite-average norm inequalities
-- because it transports strict tail events and their probability bounds.
-- minimal hypotheses: retained only nonempty finite cardinality for the scalar
-- threshold conversion.

/-- A strict tail bound for an unnormalized finite vector sum transfers to its
inverse-cardinality average.

If the squared norm of `s.sum zeta` has a strict tail bounded at `lambda` times
a constant per-index variance budget, then the squared norm of
`s.card⁻¹ • s.sum zeta` has the corresponding normalized strict tail bound.

Layer: Glue | Gap: Level 1 (strict tail transport through finite-average normalization)
Proof: use measure monotonicity and pointwise scalar algebra: the normalized
strict event implies the unnormalized strict event because `s.card > 0`, and
the constant variance sum over `s` is `s.card * sigma ^ 2`.
Source: Mathlib measure monotonicity, finite sums, seminormed-space scalar norms,
and real ordered-field arithmetic -/
theorem measure_norm_sq_inv_nat_smul_sum_gt_le_of_sum_tail_const_variance
    {ι Ω E : Type*} [MeasurableSpace Ω]
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (s : Finset ι) (zeta : ι → Ω → E)
    (sigma lambda : ℝ) (hs : 0 < s.card)
    (hsumTail :
      μ {ω |
          ‖s.sum (fun k => zeta k ω)‖ ^ 2 >
            lambda * s.sum (fun _ => sigma ^ 2)}
        ≤ ENNReal.ofReal (1 / lambda)) :
    μ {ω |
        ‖((s.card : ℝ)⁻¹) • s.sum (fun k => zeta k ω)‖ ^ 2 >
          lambda * sigma ^ 2 / s.card} ≤
      ENNReal.ofReal (1 / lambda) := by
  classical
  refine le_trans (measure_mono ?_) hsumTail
  intro ω hω
  let y : E := s.sum (fun k => zeta k ω)
  have hspos : 0 < (s.card : ℝ) := by exact_mod_cast hs
  have hsne : (s.card : ℝ) ≠ 0 := ne_of_gt hspos
  have hsum_sigma :
      s.sum (fun _ => sigma ^ 2) = (s.card : ℝ) * sigma ^ 2 := by
    simp [Finset.sum_const, nsmul_eq_mul]
  have hnormavg :
      ‖((s.card : ℝ)⁻¹) • y‖ ^ 2 =
        ‖y‖ ^ 2 / (s.card : ℝ) ^ 2 := by
    rw [norm_smul]
    have hinv_nonneg : 0 ≤ ((s.card : ℝ)⁻¹) :=
      inv_nonneg.mpr (le_of_lt hspos)
    rw [Real.norm_of_nonneg hinv_nonneg]
    field_simp [hsne]
  have hω' :
      ‖y‖ ^ 2 / (s.card : ℝ) ^ 2 >
        lambda * sigma ^ 2 / s.card := by
    simpa [y, hnormavg] using hω
  have htarget : ‖y‖ ^ 2 > lambda * ((s.card : ℝ) * sigma ^ 2) := by
    have hs2pos : 0 < (s.card : ℝ) ^ 2 := sq_pos_of_ne_zero hsne
    have hmul := mul_lt_mul_of_pos_right hω' hs2pos
    field_simp [hsne] at hmul
    nlinarith
  simpa [y, hsum_sigma, mul_assoc, mul_left_comm, mul_comm] using htarget
