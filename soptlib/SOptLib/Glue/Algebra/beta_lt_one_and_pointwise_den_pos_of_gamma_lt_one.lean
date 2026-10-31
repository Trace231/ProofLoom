import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: strict contraction factor and pointwise denominator positivity; orig was generated_amsgrad_beta1_lt_one_and_den_pos.
-- generality used: ordered commutative-ring scalar coefficients, a natural-indexed coefficient schedule, one nonnegative factor and a normalized second square component, and pointwise coefficient domination; no measure, filtration, norm, convexity, oracle, or finite-dimensional assumptions are used.
-- portable call pattern: adaptive-momentum proofs instantiate the base coefficient, time-varying momentum schedule, horizon, square-root witnesses, and quotient relation to obtain the strict base bound and positivity of every denominator before a finite-horizon telescope.
-- counterargument checked: not paper-local traceability or a caller-side expression because the theorem composes a nontrivial quotient/contraction argument with a whole finite-window denominator conclusion; Mathlib and SOptLib provide the component inequalities but no matching compound bridge.
-- coverage search: searched `beta less one pointwise one minus beta_t positive from quotient gamma less one`, `scalar quotient sqrt quotient gamma beta denominator positivity`, and `quotient less than one implies numerator less denominator positive denominator`; existing hits were paper-local AMSGrad helpers, generic contraction facts, and unrelated quotient APIs, so coverage is partial rather than full.
-- minimal hypotheses: the horizon lower bound, schedule nonnegativity, and base nonnegativity are removed; only nonnegativity of the quotient factor, square-component normalization, the quotient equation, gamma strictness, and pointwise upper domination remain.

/-- A coefficient represented by a normalized quotient is strictly below one,
and every pointwise dominated coefficient has a positive one-minus denominator.

Layer: Glue | Gap: Level 1 (scalar contraction to finite-window denominator positivity)
Proof: Split on the zero quotient factor, then use the normalized squared components to bound the nonnegative factor by one and transport `gamma < 1` through the quotient relation; finish pointwise by linear arithmetic.
Source: Mathlib ordered-field arithmetic and finite natural intervals
Used in: adaptive-momentum and exponentially weighted-history proofs that need `1 - beta_t t > 0` before dividing the metric-drop and correction terms
Book citation: book/ICLR2018/AMSGrad.json#/assumptions/5
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond - AMSGrad Algorithm 2 -/
theorem beta_lt_one_and_pointwise_den_pos_of_gamma_lt_one
    {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (beta : R) (beta_t : ℕ → R) (factor gamma complement : R)
    (T : ℕ)
    (hfactor_nonneg : 0 ≤ factor)
    (hcomponents : factor ^ 2 + complement ^ 2 = 1)
    (hquot : factor * gamma = beta)
    (hgamma_lt : gamma < 1)
    (hbeta_t_le : ∀ t ∈ Finset.Icc 1 T, beta_t t ≤ beta) :
    beta < 1 ∧
      ∀ t ∈ Finset.Icc 1 T, 0 < 1 - beta_t t := by
  have hfactor_sq_le_one : factor ^ 2 ≤ 1 := by
    linarith [sq_nonneg complement]
  have hfactor_le_one : factor ≤ 1 := by
    exact le_of_sq_le_sq (by simpa using hfactor_sq_le_one) (by norm_num)
  by_cases hbeta_nonneg : 0 ≤ beta
  · by_cases hfactor_zero : factor = 0
    · have hbeta_zero : beta = 0 := by
        simpa [hfactor_zero] using hquot.symm
      have hbeta_lt : beta < 1 := by
        simpa [hbeta_zero] using (zero_lt_one : (0 : R) < 1)
      refine ⟨hbeta_lt, ?_⟩
      intro t ht
      have hbeta_t_le' := hbeta_t_le t ht
      exact sub_pos.mpr (lt_of_le_of_lt hbeta_t_le' hbeta_lt)
    · have hfactor_pos : 0 < factor :=
        lt_of_le_of_ne hfactor_nonneg (Ne.symm hfactor_zero)
      have hgamma_nonneg : 0 ≤ gamma := by
        have hprod_nonneg : 0 ≤ gamma * factor := by
          rw [mul_comm, hquot]
          exact hbeta_nonneg
        exact nonneg_of_mul_nonneg_left hprod_nonneg hfactor_pos
      have hbeta_lt : beta < 1 := by
        have hmul_le : factor * gamma ≤ 1 * gamma :=
          mul_le_mul_of_nonneg_right hfactor_le_one hgamma_nonneg
        calc
          beta = factor * gamma := hquot.symm
          _ ≤ gamma := by simpa using hmul_le
          _ < 1 := hgamma_lt
      refine ⟨hbeta_lt, ?_⟩
      intro t ht
      have hbeta_t_le' := hbeta_t_le t ht
      exact sub_pos.mpr (lt_of_le_of_lt hbeta_t_le' hbeta_lt)
  · have hbeta_lt : beta < 1 := by linarith
    refine ⟨hbeta_lt, ?_⟩
    intro t ht
    have hbeta_t_le' := hbeta_t_le t ht
    exact sub_pos.mpr (lt_of_le_of_lt hbeta_t_le' hbeta_lt)
