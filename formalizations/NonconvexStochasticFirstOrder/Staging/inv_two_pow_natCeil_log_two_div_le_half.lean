import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: inverse dyadic tail bound from a base-two logarithmic natural
--   ceiling; orig was `runCount_confidence_tail_bound`.
-- generality used: one positive real confidence scale `Lambda`; no measure,
--   independence, integrability, convexity, oracle, normed-space, or
--   finite-dimensional assumptions are used.
-- portable call pattern: confidence-amplification and repeated-run probability
--   proofs choose `S = Nat.ceil (Real.log (2 / Lambda) / Real.log 2)` and need
--   to convert the geometric failure term `2^{-S}` into `Lambda / 2`; only the
--   confidence parameter changes.
-- counterargument checked: this is short scalar arithmetic, but it is not a
--   pure rename or paper-local traceability because the exact ceiling-to-tail
--   conversion recurs in amplification proofs and is not covered by the
--   existing logarithmic ceiling upper-bound lemmas.
-- coverage search: queried "inverse two power nat ceil logarithm two divided
--   less equal half", "ceil log division power inverse bound", and "logb less
--   equal rpow ceil"; top SOptLib hits included
--   `ceil_log_two_div_le_three_log_one_div_over_log_two`,
--   `pow_nat_le_inv_of_neg_log_div_log_le`, and geometric-log ceiling lower
--   bounds, all partial but not this inverse dyadic tail conclusion. Mathlib
--   LeanSearch found integer-log and generic ceiling estimates, not this real
--   logarithm natural-ceiling specialization.
-- minimal hypotheses: `0 < Lambda` is the only hypothesis used; the source
--   confidence upper bound `Lambda < 1` is not needed for this tail inequality.

/-- A base-two logarithmic natural ceiling makes the inverse dyadic tail at most
half of the target scale.

For any positive real `Lambda`, choosing
`S = Nat.ceil (Real.log (2 / Lambda) / Real.log 2)` gives
`((2 : Real) ^ S)⁻¹ <= Lambda / 2`.

Layer: Glue | Gap: Level 0 (base-two logarithmic ceiling inverse-tail bound)
Proof: compare the base-two logarithm of `2 / Lambda` with the natural ceiling,
  exponentiate through `Real.logb_le_iff_le_rpow`, then invert the resulting
  positive power inequality.
Source: Mathlib real logarithm-base, real-power, natural ceiling, and ordered-field inverse APIs
Used in: repeated independent stochastic-gradient run amplification, converting the chosen run count into the `2^{-S} <= Lambda / 2` geometric failure term
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/main_theorem/proof/16
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic gradient descent -/
theorem inv_two_pow_natCeil_log_two_div_le_half
    (Lambda : ℝ) (hLambda_pos : 0 < Lambda) :
    ((2 : ℝ) ^ Nat.ceil (Real.log (2 / Lambda) / Real.log 2))⁻¹ <=
      Lambda / 2 := by
  have hx_pos : 0 < 2 / Lambda :=
    div_pos (by norm_num : (0 : ℝ) < 2) hLambda_pos
  have hceil :
      Real.log (2 / Lambda) / Real.log 2 <=
        (Nat.ceil (Real.log (2 / Lambda) / Real.log 2) : ℝ) := by
    exact Nat.le_ceil (Real.log (2 / Lambda) / Real.log 2)
  have hlogb :
      Real.logb 2 (2 / Lambda) <=
        (Nat.ceil (Real.log (2 / Lambda) / Real.log 2) : ℝ) := by
    simpa [Real.log_div_log] using hceil
  have hpow_rpow :
      2 / Lambda <=
        (2 : ℝ) ^ (Nat.ceil (Real.log (2 / Lambda) / Real.log 2) : ℝ) :=
    (Real.logb_le_iff_le_rpow
      (by norm_num : (1 : ℝ) < 2) hx_pos).mp hlogb
  have hpow :
      2 / Lambda <=
        (2 : ℝ) ^ Nat.ceil (Real.log (2 / Lambda) / Real.log 2) := by
    simpa [Real.rpow_natCast] using hpow_rpow
  have hpow_pos :
      0 < (2 : ℝ) ^ Nat.ceil (Real.log (2 / Lambda) / Real.log 2) :=
    pow_pos (by norm_num : (0 : ℝ) < 2) _
  have hinv :
      ((2 : ℝ) ^ Nat.ceil (Real.log (2 / Lambda) / Real.log 2))⁻¹ <=
        (2 / Lambda)⁻¹ :=
    (inv_le_inv₀ hpow_pos hx_pos).2 hpow
  have hx_inv : (2 / Lambda)⁻¹ = Lambda / 2 := by
    field_simp [hLambda_pos.ne']
  simpa [hx_inv] using hinv

end SOptLib
