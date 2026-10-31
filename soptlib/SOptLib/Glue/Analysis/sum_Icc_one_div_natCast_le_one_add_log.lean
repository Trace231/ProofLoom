import Mathlib.NumberTheory.Harmonic.Bounds

open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: sum_Icc_one_div_natCast_le_one_add_log exposes the real-valued one-based harmonic prefix bound by `1 + log T`; orig was amsgrad_harmonic_Icc_le_one_add_log.
-- generality used: a natural horizon and real scalar reciprocals over `Finset.Icc 1 T`; no measure, filtration, carrier, convexity, smoothness, oracle, or finite-dimensional assumptions are used.
-- portable call pattern: finite-horizon adaptive-gradient, mirror-descent, and online-learning rate proofs can replace `sum_{j=1}^T 1 / j` by `1 + log T`; the horizon and surrounding Cauchy-Schwarz or denominator estimate change while the harmonic conclusion stays fixed.
-- counterargument checked: Mathlib already proves `harmonic_le_one_add_log` for rational harmonic numbers, so this staging theorem is only the reusable real `Finset.Icc` bridge used by optimization proofs rather than a duplicate integral-comparison proof.
-- coverage search: searched `one-based harmonic sum over Icc reciprocal nat cast at most one plus logarithm` and `harmonic_le_one_add_log real Icc harmonic_eq_sum_Icc`; top hit was Mathlib `harmonic_le_one_add_log` plus `harmonic_eq_sum_Icc`, while SOptLib logarithmic prefix-sum lemmas cover cumulative denominators, not the plain harmonic real interval form.
-- minimal hypotheses: the source positive-horizon hypothesis is not needed; Mathlib's bound covers `T = 0`, so the staged statement keeps only `(T : Nat)`.

/-- The real one-based harmonic prefix is bounded by one plus the logarithm of
the terminal index.

Layer: Glue | Gap: Level 0 (real closed-interval harmonic-log bridge)
Proof: apply Mathlib's rational harmonic-number bound `harmonic_le_one_add_log`
  and rewrite `harmonic` as the closed interval `Finset.Icc 1 T`, casting the
  rational reciprocal sum to real scalars.
Source: Mathlib `NumberTheory.Harmonic.Bounds`, especially
  `harmonic_le_one_add_log` and `harmonic_eq_sum_Icc`
Used in: adaptive-gradient regret proofs that bound a coordinate history term
  after Cauchy-Schwarz by replacing the one-based harmonic weight sum with a
  logarithmic horizon factor
Book citation: book/ICLR2018/AMSGrad.json#/main_theorem/proof/3
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond, AMSGrad Algorithm 2 -/
theorem sum_Icc_one_div_natCast_le_one_add_log (T : ℕ) :
    (∑ j ∈ Finset.Icc 1 T, (1 : ℝ) / (j : ℝ)) ≤
      1 + Real.log (T : ℝ) := by
  have h := harmonic_le_one_add_log T
  rw [harmonic_eq_sum_Icc] at h
  simpa only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div] using h
