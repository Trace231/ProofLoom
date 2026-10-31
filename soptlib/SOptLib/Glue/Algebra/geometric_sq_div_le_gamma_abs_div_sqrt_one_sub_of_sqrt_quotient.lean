import SOptLib.Model.ParameterChoices.realSqrtSpec
import Mathlib.Tactic

-- Generalization plan (G0):
-- concept/name: geometric denominator transport from square-root quotient witnesses;
--   orig was amsgrad_eq17_denominator_transport
-- generality used: real scalar arithmetic with pointwise square-root witness
--   relations; no measure, filtration, convexity, smoothness, or oracle assumptions
-- portable call pattern: adaptive-momentum proofs use a lower bound on a squared
--   denominator to transport a beta1-weighted square into a gamma-weighted
--   absolute-value quotient; beta parameters, witnesses, index, and denominator
--   change while the conclusion stays the same
-- counterargument checked: the candidate is not a caller-side expression or a
--   one-line wrapper; it packages square identities, absolute-value transport,
--   positive division, and coefficient monotonicity. Existing square-root witness
--   infrastructure covers only the witness relation, not this inequality.
-- coverage search: searched geometric square quotient bounds, positive denominator
--   square-root transport, and scalar quotient inequalities; Mathlib/SOptLib had
--   only partial square-root witness and unrelated denominator results
-- minimal hypotheses: replaced the algorithm-specific IsScalarSqrt and
--   IsScalarQuotient wrappers by realSqrtSpec and the equality field actually used;
--   retained positivity and nonnegativity assumptions used by the ordered-field proof

/-- A squared denominator lower bound transports a geometric square quotient to an
absolute-value quotient through square-root witnesses and a coefficient quotient.

Layer: Glue | Gap: Level 1 (geometric squared-denominator transport)
Proof: Rewrite the squared lower bound as an absolute-value bound for the
square-root-scaled numerator, divide by the positive denominator, and multiply
by the nonnegative geometric coefficient.
Source: Mathlib real square-root witness, absolute-value order, and ordered-field
division APIs used in the scalar estimate behind Appendix D Eq. (17)
Used in: adaptive-momentum history estimates that convert each beta1-weighted
coordinate square over an adaptive second-moment denominator into a gamma-weighted
coordinate absolute value over sqrt(1 - beta2)
Book citation: book/ICLR2018/AMSGrad.json#/key_lemmas/2/proof/1
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond, AMSGrad Algorithm 2 -/
theorem geometric_sq_div_le_gamma_abs_div_sqrt_one_sub_of_sqrt_quotient
    {beta1 beta2 sqrtBeta2 gamma sqrtOneMinus V g : ℝ} (k : ℕ)
    (hsqrtBeta2 : realSqrtSpec beta2 sqrtBeta2)
    (hgamma : sqrtBeta2 * gamma = beta1)
    (hsqrtOneMinus : realSqrtSpec (1 - beta2) sqrtOneMinus)
    (hgamma_nonneg : 0 ≤ gamma)
    (hV_pos : 0 < V)
    (hsqrtOneMinus_pos : 0 < sqrtOneMinus)
    (hv : (1 - beta2) * beta2 ^ k * g ^ 2 ≤ V ^ 2) :
    beta1 ^ k * g ^ 2 / V ≤ gamma ^ k * |g| / sqrtOneMinus := by
  have hsqrtBeta2_nonneg : 0 ≤ sqrtBeta2 := hsqrtBeta2.1
  have hbase_nonneg :
      0 ≤ sqrtOneMinus * sqrtBeta2 ^ k * |g| := by
    exact mul_nonneg
      (mul_nonneg (le_of_lt hsqrtOneMinus_pos)
        (pow_nonneg hsqrtBeta2_nonneg k))
      (abs_nonneg g)
  have hV_nonneg : 0 ≤ V := le_of_lt hV_pos
  have hpow_sq :
      (sqrtBeta2 ^ k) ^ 2 = (sqrtBeta2 ^ 2) ^ k := by
    induction k with
    | zero =>
        simp
    | succ k ih =>
        simp [pow_succ, mul_pow]
        ring
  have hsq_identity :
      (sqrtOneMinus * sqrtBeta2 ^ k * |g|) ^ 2 =
        (1 - beta2) * beta2 ^ k * g ^ 2 := by
    rw [mul_pow, mul_pow, sq_abs, hpow_sq, hsqrtOneMinus.2,
      hsqrtBeta2.2]
  have hbase_sq_le : (sqrtOneMinus * sqrtBeta2 ^ k * |g|) ^ 2 ≤ V ^ 2 := by
    simpa [hsq_identity] using hv
  have habs_le : |(sqrtOneMinus * sqrtBeta2 ^ k * |g|)| ≤ |V| := by
    exact sq_le_sq.mp hbase_sq_le
  have hbase_le : sqrtOneMinus * sqrtBeta2 ^ k * |g| ≤ V := by
    simpa [abs_of_nonneg hbase_nonneg, abs_of_nonneg hV_nonneg] using habs_le
  have hratio_le : sqrtBeta2 ^ k * |g| / V ≤ 1 / sqrtOneMinus := by
    field_simp [ne_of_gt hV_pos, ne_of_gt hsqrtOneMinus_pos]
    nlinarith [hbase_le]
  have hcoef_nonneg : 0 ≤ gamma ^ k * |g| := by
    exact mul_nonneg (pow_nonneg hgamma_nonneg k) (abs_nonneg g)
  calc
    beta1 ^ k * g ^ 2 / V
        = gamma ^ k * |g| * (sqrtBeta2 ^ k * |g| / V) := by
          rw [← hgamma, mul_pow, ← sq_abs g]
          field_simp [ne_of_gt hV_pos]
    _ ≤ gamma ^ k * |g| * (1 / sqrtOneMinus) := by
          exact mul_le_mul_of_nonneg_left hratio_le hcoef_nonneg
    _ = gamma ^ k * |g| / sqrtOneMinus := by
          field_simp [ne_of_gt hsqrtOneMinus_pos]
