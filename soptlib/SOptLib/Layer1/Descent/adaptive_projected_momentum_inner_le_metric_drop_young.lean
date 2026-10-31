import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: adaptive projected-momentum inner-product bound with metric drop and Young terms; orig was generated_projection_young_bound_on_horizon
-- generality used: finite real coordinate vectors indexed by `Fin d`; no measure, filtration, convexity, smoothness, oracle, or algorithm-specific setup assumptions; positivity of the adaptive weights, step size, and momentum denominator is stated pointwise
-- portable call pattern: Adam/AMSGrad-style projected-gradient proofs provide a weighted projection square expansion and the affine first-moment recurrence, then reuse the metric-drop plus current/previous momentum Young bound while changing the coordinate sequences and schedules
-- counterargument checked: this is not paper-local traceability or a caller-side wrapper because it composes the projection expansion, momentum substitution, and diagonal Young absorption into a reusable one-step inequality; existing SOptLib Young and projection declarations cover only partial ingredients
-- coverage search: searched `weighted projection square expansion momentum recurrence inner product Young metric drop`, `negative inner product Young bound weighted coordinate square positive weights`, and `adaptive projected momentum inner product metric drop Young`; SOptLib hits were generic Hilbert Young bounds and separate projection/telescope results, with no complete matching contract
-- minimal hypotheses: quotient and square-root witness relations are reduced to the only fact used by the proof, strict positivity of every coordinate weight; alpha positivity, beta nonnegativity, and `1 - beta` positivity are exactly the scalar conditions used by division and scaling

/-- A weighted projected-momentum step bounds the current gradient pairing by a
metric drop, current-direction energy, previous-momentum energy, and a beta
metric correction.

The projection hypothesis is the weighted square expansion for the next point,
and the momentum hypothesis is the affine first-moment recurrence tested against
the current displacement.  The previous-momentum cross term is absorbed
coordinatewise by Young's inequality.

Layer: Layer1 | Gap: Level 1 (adaptive projected-momentum metric-drop inequality)
Proof: rearrange the weighted projection expansion through the first-moment
recurrence, divide by the positive momentum denominator, and apply coordinatewise
Young absorption to the lagged momentum inner product.
Source: AMSGrad Appendix D Eq. (15), finite real inner-product coordinate
algebra, and ordered-field Young inequality
Used in: Adam/AMSGrad projected-gradient regret proofs immediately after the
weighted projection contraction and first-moment substitution, before finite-horizon
telescoping of metric and momentum terms
Book citation: book/ICLR2018/AMSGrad.json#/key_lemmas/1/statement_math
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond, AMSGrad Algorithm 2 -/
theorem adaptive_projected_momentum_inner_le_metric_drop_young {d : ℕ}
    (x xNext xStar mPrev m g direction sqrtV :
      EuclideanSpace ℝ (Fin d))
    (alpha beta : ℝ)
    (halpha : 0 < alpha)
    (hbeta : 0 ≤ beta)
    (hden : 0 < 1 - beta)
    (hsqrtV_pos : ∀ i : Fin d, 0 < sqrtV i)
    (hprojection :
      (∑ i, sqrtV i * ((xNext - xStar) i) ^ 2) ≤
        (∑ i, sqrtV i * ((x - xStar) i) ^ 2) -
          2 * alpha * inner ℝ m (x - xStar) +
          alpha ^ 2 * (∑ i, sqrtV i * (direction i) ^ 2))
    (hmomentum :
      inner ℝ m (x - xStar) =
        beta * inner ℝ mPrev (x - xStar) +
          (1 - beta) * inner ℝ g (x - xStar)) :
    inner ℝ g (x - xStar) ≤
      ((∑ i, sqrtV i * ((x - xStar) i) ^ 2) -
        (∑ i, sqrtV i * ((xNext - xStar) i) ^ 2)) /
          (2 * alpha * (1 - beta)) +
        (alpha * (∑ i, sqrtV i * (direction i) ^ 2)) /
          (2 * (1 - beta)) +
        (beta * alpha *
          (∑ i, (mPrev i) ^ 2 / sqrtV i)) /
          (2 * (1 - beta)) +
        (beta * (∑ i, sqrtV i * ((x - xStar) i) ^ 2)) /
          (2 * alpha * (1 - beta)) := by
  let y : EuclideanSpace ℝ (Fin d) := x - xStar
  let A : ℝ := ∑ i, sqrtV i * (y i) ^ 2
  let N : ℝ := ∑ i, sqrtV i * ((xNext - xStar) i) ^ 2
  let C : ℝ := ∑ i, sqrtV i * (direction i) ^ 2
  let M : ℝ := inner ℝ m y
  let P : ℝ := inner ℝ mPrev y
  let G : ℝ := inner ℝ g y
  have hprojection' : N ≤ A - 2 * alpha * M + alpha ^ 2 * C := by
    simpa [A, N, C, M, y] using hprojection
  have hmomentum' : M = beta * P + (1 - beta) * G := by
    simpa [M, P, G, y] using hmomentum
  have htwoalpha_pos : 0 < 2 * alpha := by
    nlinarith
  have hM_mul : M * (2 * alpha) ≤ A - N + alpha ^ 2 * C := by
    nlinarith [hprojection']
  have hM_bound : M ≤ (A - N + alpha ^ 2 * C) / (2 * alpha) := by
    exact (le_div_iff₀ htwoalpha_pos).2 hM_mul
  have hG_scaled :
      (1 - beta) * G ≤
        (A - N + alpha ^ 2 * C) / (2 * alpha) - beta * P := by
    nlinarith [hmomentum', hM_bound]
  have hG_bound :
      G ≤ ((A - N + alpha ^ 2 * C) / (2 * alpha) - beta * P) /
          (1 - beta) := by
    exact (le_div_iff₀ hden).2 (by
      simpa [mul_comm] using hG_scaled)
  have hscale_nonneg : 0 ≤ beta / (1 - beta) := by
    exact div_nonneg hbeta (le_of_lt hden)
  have hsum :
      - inner ℝ mPrev y ≤
        ∑ i, (alpha / 2 * ((mPrev i) ^ 2 / sqrtV i) +
          (sqrtV i * (y i) ^ 2) / (2 * alpha)) := by
    have hinner : inner ℝ mPrev y = ∑ i, mPrev i * y i := by
      rw [PiLp.inner_apply]
      simp [inner, mul_comm]
    rw [hinner]
    calc
      - (∑ i, mPrev i * y i) =
          ∑ i, -(mPrev i * y i) := by
            simp [Finset.sum_neg_distrib]
      _ ≤ ∑ i, (alpha / 2 * ((mPrev i) ^ 2 / sqrtV i) +
            (sqrtV i * (y i) ^ 2) / (2 * alpha)) := by
        exact Finset.sum_le_sum (by
          intro i _hi
          have htwoalpha_pos : 0 < 2 * alpha := by
            nlinarith
          have hden_coord : 0 < 2 * alpha * sqrtV i :=
            mul_pos htwoalpha_pos (hsqrtV_pos i)
          have hnonneg :
              0 ≤ (alpha * mPrev i + sqrtV i * y i) ^ 2 /
                (2 * alpha * sqrtV i) := by
            exact div_nonneg (sq_nonneg _)
              (le_of_lt hden_coord)
          have heq :
              alpha / 2 * ((mPrev i) ^ 2 / sqrtV i) +
                  (sqrtV i * (y i) ^ 2) / (2 * alpha) +
                    mPrev i * y i =
                (alpha * mPrev i + sqrtV i * y i) ^ 2 /
                  (2 * alpha * sqrtV i) := by
            field_simp [ne_of_gt halpha, ne_of_gt (hsqrtV_pos i)]
            ring
          have hnonneg' :
              0 ≤ alpha / 2 * ((mPrev i) ^ 2 / sqrtV i) +
                (sqrtV i * (y i) ^ 2) / (2 * alpha) +
                  mPrev i * y i := by
            simpa [heq] using hnonneg
          linarith)
  have hscaled := mul_le_mul_of_nonneg_left hsum hscale_nonneg
  have halpha_ne : alpha ≠ 0 := ne_of_gt halpha
  have hden_ne : 1 - beta ≠ 0 := ne_of_gt hden
  have hsum_expand :
      (∑ i, (alpha / 2 * ((mPrev i) ^ 2 / sqrtV i) +
        (sqrtV i * (y i) ^ 2) / (2 * alpha))) =
        alpha / 2 * (∑ i, (mPrev i) ^ 2 / sqrtV i) +
          (1 / (2 * alpha)) * (∑ i, sqrtV i * (y i) ^ 2) := by
    simp [Finset.sum_add_distrib, Finset.mul_sum, div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm]
  have hYoung :
      - (beta / (1 - beta)) * P ≤
        (beta * alpha * (∑ i, (mPrev i) ^ 2 / sqrtV i)) /
            (2 * (1 - beta)) +
          (beta * (∑ i, sqrtV i * (y i) ^ 2)) /
            (2 * alpha * (1 - beta)) := by
    calc
      - (beta / (1 - beta)) * P =
      (beta / (1 - beta)) * (-P) := by ring
      _ ≤ (beta / (1 - beta)) *
          (∑ i, (alpha / 2 * ((mPrev i) ^ 2 / sqrtV i) +
            (sqrtV i * (y i) ^ 2) / (2 * alpha))) := hscaled
      _ = (beta * alpha * (∑ i, (mPrev i) ^ 2 / sqrtV i)) /
            (2 * (1 - beta)) +
          (beta * (∑ i, sqrtV i * (y i) ^ 2)) /
            (2 * alpha * (1 - beta)) := by
        rw [hsum_expand]
        field_simp [halpha_ne, hden_ne]
  calc
    inner ℝ g (x - xStar) = G := by simp [G, y]
    _ ≤ ((A - N + alpha ^ 2 * C) / (2 * alpha) - beta * P) /
          (1 - beta) := hG_bound
    _ = (A - N) / (2 * alpha * (1 - beta)) +
          (alpha * C) / (2 * (1 - beta)) -
          (beta / (1 - beta)) * P := by
      field_simp [halpha_ne, hden_ne]
    _ ≤ (A - N) / (2 * alpha * (1 - beta)) +
          (alpha * C) / (2 * (1 - beta)) +
          (beta * alpha * (∑ i, (mPrev i) ^ 2 / sqrtV i)) /
            (2 * (1 - beta)) +
          (beta * (∑ i, sqrtV i * (y i) ^ 2)) /
            (2 * alpha * (1 - beta)) := by
      linarith
    _ = ((∑ i, sqrtV i * ((x - xStar) i) ^ 2) -
        (∑ i, sqrtV i * ((xNext - xStar) i) ^ 2)) /
          (2 * alpha * (1 - beta)) +
        (alpha * (∑ i, sqrtV i * (direction i) ^ 2)) /
          (2 * (1 - beta)) +
        (beta * alpha * (∑ i, (mPrev i) ^ 2 / sqrtV i)) /
          (2 * (1 - beta)) +
          (beta * (∑ i, sqrtV i * ((x - xStar) i) ^ 2)) /
          (2 * alpha * (1 - beta)) := by
      simp [A, N, C, P, y]
