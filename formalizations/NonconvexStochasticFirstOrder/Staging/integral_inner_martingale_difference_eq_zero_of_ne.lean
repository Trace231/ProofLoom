import Mathlib.Probability.Process.Filtration
import SOptLib.Glue.Martingale

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

-- Generalization plan (G0):
-- concept/name: off-diagonal Hilbert martingale-difference orthogonality in
--   integral; orig was `martingale_cross_integral_zero_of_indices`, renamed
--   away from the local second-moment proof and finite-window bookkeeping.
-- generality used: arbitrary measurable source space, arbitrary finite
--   measure, natural-time Mathlib filtration, and an arbitrary complete real
--   Hilbert target with measurable Borel second-countable structure; no
--   objective, oracle, smoothness, convexity, probability normalization, or
--   finite-dimensional Euclidean structure is used.
-- portable call pattern: martingale second-moment, validation residual, and
--   variance-reduced stochastic approximation proofs use this to cancel
--   off-diagonal covariance terms for adapted earlier increments and
--   conditionally centered later increments; the measure, filtration,
--   increment process, and finite summation window vary.
-- counterargument checked: this is not just paper traceability because it
--   combines filtration monotonicity, conditional mean-zero cancellation,
--   L2 inner-product integrability, and index orientation into one reusable
--   martingale orthogonality step; existing SOptLib oracle residual lemmas
--   assume a supplied one-step cancellation or oracle-specific structure.
-- coverage search: searched `integral inner martingale difference zero
--   conditional expectation adapted`, `distinct martingale difference
--   increments inner product integral zero`, Mathlib LeanSearch for
--   `martingale differences distinct indices inner product expectation zero`,
--   and catalog off-diagonal martingale/cross-integral entries; closest hits
--   were `integral_inner_sub_const_eq_zero_of_condExp_eq_zero`,
--   `centeredOracleResidual_inner_integral_eq_zero_of_distinct_fresh`, and
--   Mathlib martingale constructors, all partial rather than this direct
--   off-diagonal filtered increment theorem.
-- minimal hypotheses: the finite-measure class supplies the sigma-finiteness
--   needed by conditional-expectation integration; square-integrability is
--   pointwise per used index, and no second-moment bound or finite window is
--   retained.

/-- Distinct adapted martingale-difference increments have zero cross integral.

For a filtered Hilbert-valued sequence, if each increment is adapted to its own
time, conditionally centered on the previous time, integrable, and
square-integrable, then the expected inner product of any two distinct positive
time increments vanishes.

Layer: Glue | Gap: Level 1 (off-diagonal martingale-difference orthogonality)
Proof: orient the two indices, promote the earlier adapted increment through
filtration monotonicity to the later past sigma-algebra, derive scalar
inner-product integrability from the two L2 hypotheses, and apply the existing
conditional-expectation inner-product cancellation lemma.
Source: Mathlib filtration order and conditional expectation APIs, plus
  SOptLib Hilbert L2 inner-product integrability and martingale cancellation
Used in: martingale second-moment proofs that diagonalize finite covariance
  sums for stochastic gradient residuals before applying Markov tail bounds
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/key_lemmas/1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic gradient descent -/
theorem integral_inner_martingale_difference_eq_zero_of_ne
    {Ω E : Type*} {mΩ : MeasurableSpace Ω}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Filtration Nat mΩ)
    (zeta : Nat → Ω → E)
    (hmeas : ∀ k : Nat, 1 ≤ k → @Measurable Ω E (F k) _ (zeta k))
    (hint : ∀ k : Nat, 1 ≤ k → Integrable (zeta k) μ)
    (hcond : ∀ k : Nat, 1 ≤ k →
      μ[zeta k | F (k - 1)] =ᵐ[μ] (fun _ => (0 : E)))
    (hsq_int : ∀ k : Nat, 1 ≤ k →
      Integrable (fun ω => ‖zeta k ω‖ ^ 2) μ)
    {i j : Nat} (hi : 1 ≤ i) (hj : 1 ≤ j) (hij_ne : i ≠ j) :
    ∫ ω, ⟪zeta i ω, zeta j ω⟫_ℝ ∂μ = 0 := by
  classical
  have h_ae_meas : ∀ k : Nat, 1 ≤ k → AEStronglyMeasurable (zeta k) μ := by
    intro k hk
    exact ((hmeas k hk).of_measurableSpace_le (F.le k)).aestronglyMeasurable
  have hordered :
      ∀ {a b : Nat}, 1 ≤ a → 1 ≤ b → a < b →
        ∫ ω, ⟪zeta a ω, zeta b ω⟫_ℝ ∂μ = 0 := by
    intro a b ha hb hab
    have hab_pred : a ≤ b - 1 := Nat.le_pred_of_lt hab
    have hx : Measurable[F (b - 1)] (zeta a) :=
      (hmeas a ha).mono (F.mono hab_pred) (by rfl)
    have hinner_int :
        Integrable (fun ω => ⟪zeta b ω, zeta a ω - (0 : E)⟫_ℝ) μ := by
      simpa [sub_zero] using
        integrable_inner_of_integrable_sq_norm
          (P := μ) (u := zeta b) (v := zeta a)
          (h_ae_meas b hb) (h_ae_meas a ha) (hsq_int b hb) (hsq_int a ha)
    have hzero_later :
        ∫ ω, ⟪zeta b ω, zeta a ω - (0 : E)⟫_ℝ ∂μ = 0 := by
      exact integral_inner_sub_const_eq_zero_of_condExp_eq_zero
        (P := μ) (m := F (b - 1)) (δ := zeta b) (x := zeta a)
        (c := (0 : E)) (F.le (b - 1)) hx (hcond b hb)
        (hint b hb) hinner_int
    simpa [sub_zero, real_inner_comm] using hzero_later
  rcases lt_or_gt_of_ne hij_ne with hij | hji
  · exact hordered hi hj hij
  · simpa [real_inner_comm] using hordered hj hi hji
