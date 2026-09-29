import Mathlib.Tactic
import SOptLib.Glue.Probability

open MeasureTheory

-- Generalization plan (G0):
-- concept/name: non-strict Markov tail at a positive scalar multiple of an
--   integral budget; orig was `markov_tail_le_inv_of_integral_le_mul_budget`.
-- generality used: arbitrary measurable sample space, arbitrary measure,
--   real-valued observable, real budget `C`, and positive scalar `lambda`; no
--   probability, independence, convexity, oracle, normed-space, or
--   finite-dimensional assumptions are used.
-- portable call pattern: stochastic-optimization tail proofs first establish
--   nonnegativity, integrability, and an expectation budget for a stationarity
--   or residual statistic, then apply Markov at threshold `lambda * C`; the
--   measure, observable, budget, and confidence multiplier change while the
--   conclusion remains `ofReal (1 / lambda)`.
-- counterargument checked: SOptLib already has
--   `measure_ge_le_of_integral_le_of_nonneg`, but that lower-level theorem
--   requires each caller to supply the positive threshold and scalar ratio
--   side condition. This wrapper packages the recurring `lambda * C` threshold
--   specialization without paper-specific data.
-- coverage search: queried "measure set greater equal threshold integral
--   nonnegative Markov inequality" and "measure ge lambda times C integral le
--   nonnegative one over lambda"; top SOptLib hit was
--   `measure_ge_le_of_integral_le_of_nonneg`, which covers the Markov core but
--   not the scalar-multiple budget specialization. LeanSearch returned
--   Mathlib's `MeasureTheory.meas_ge_le_lintegral_div`, an ENNReal Markov
--   primitive rather than this real-integral specialization.
-- minimal hypotheses: pointwise nonnegativity, Bochner integrability, integral
--   budget, `0 < C`, and `0 < lambda` are exactly the hypotheses used to make
--   the threshold positive and simplify `C / (lambda * C)` to `1 / lambda`.

/-- A nonnegative integrable real random variable has Markov tail at a positive
multiple of any positive integral budget.

If `∫ f <= C`, `0 < C`, and `0 < lambda`, then the non-strict tail at
`lambda * C` is bounded by `ofReal (1 / lambda)`.

Layer: Glue | Gap: Level 1 (scalar-multiple nonnegative Markov tail from real integral budget)
Proof: specialize `measure_ge_le_of_integral_le_of_nonneg` at threshold
  `lambda * C`, prove threshold positivity, and simplify the real ratio
  `C / (lambda * C)` to `1 / lambda`.
Source: Mathlib measure-theory Markov inequality through SOptLib's
  real-integral nonnegative tail wrapper and ordered-field arithmetic
Used in: two-phase randomized stochastic gradient descent, converting a
  one-run expected squared-gradient stationarity budget into the per-run
  failure probability used before independent-run aggregation
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/key_lemmas/One_run_Markov_tail_bound
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic gradient descent -/
theorem measure_ge_mul_le_inv_of_integral_le_of_nonneg
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (f : Ω -> Real) (C lambda : Real)
    (hf_int : Integrable f μ) (hf_nonneg : forall ω, 0 <= f ω)
    (h_int_le : ∫ ω, f ω ∂μ <= C)
    (hC_pos : 0 < C) (hlambda : 0 < lambda) :
    μ {ω | f ω >= lambda * C} <= ENNReal.ofReal (1 / lambda) := by
  have ht_pos : 0 < lambda * C := mul_pos hlambda hC_pos
  have hratio : C / (lambda * C) <= 1 / lambda := by
    have hlambda_ne : lambda ≠ 0 := ne_of_gt hlambda
    have hC_ne : C ≠ 0 := ne_of_gt hC_pos
    have hEq : C / (lambda * C) = 1 / lambda := by
      field_simp [hlambda_ne, hC_ne]
    exact le_of_eq hEq
  exact
    measure_ge_le_of_integral_le_of_nonneg
      (μ := μ) f (lambda * C) C (1 / lambda)
      hf_int hf_nonneg h_int_le ht_pos hratio
