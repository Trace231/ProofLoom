import Mathlib.Tactic
import SOptLib.Glue.Martingale
import Staging.MartingaleDifferenceL2Hypotheses
import Staging.integrable_norm_sq_finset_sum_of_integrable_norm_sq
import Staging.integral_inner_martingale_difference_eq_zero_of_ne

open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace

-- Generalization plan (G0):
-- concept/name: martingale_second_moment_and_strict_tail_bound exposes the
--   finite-window L2 and strict Markov tail bound for Hilbert-valued
--   martingale-difference sums; orig was `Martingale_second_moment_bound`,
--   renamed away from the source theorem boundary and paper capitalization.
-- generality used: arbitrary measurable finite-measure space, Mathlib natural
--   filtration, arbitrary complete real Hilbert target with measurable Borel
--   second-countable structure, an increment process, and per-time real L2
--   budgets; no objective, oracle, iterate, smoothness, convexity, or
--   finite-dimensional Euclidean structure is used.
-- portable call pattern: validation residual, stochastic-gradient, and
--   mini-batch proofs invoke the same finite-window martingale bound before
--   converting residual sums into high-probability estimates; the probability
--   space, filtration, increments, horizon, and sigma budgets vary while the
--   L2-plus-tail conclusion stays unchanged.
-- counterargument checked: this is not a paper-local wrapper because it
--   combines orthogonality of martingale differences, finite Hilbert covariance
--   diagonalization, per-index moment budgets, aggregate L2 integrability, and
--   strict Markov conversion in one reusable proof step; existing entries cover
--   only separate components.
-- coverage search: queried `martingale finite sum second moment tail bound per
--   index variance`, `measure greater than Markov inequality integral bound
--   strict tail`, and `MartingaleDifferenceHypotheses`; top hits were
--   `integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero`,
--   `measure_gt_le_of_integral_le_of_nonneg`,
--   `integral_inner_martingale_difference_eq_zero_of_ne`, and
--   `MartingaleDifferenceL2Hypotheses`, all partial rather than this combined
--   martingale L2 plus strict-tail contract.
-- minimal hypotheses: the source tuple is replaced by
--   `MartingaleDifferenceL2Hypotheses`; finite measure suffices for the
--   component martingale and strict Markov APIs. No positive horizon hypothesis
--   is needed because the empty finite window is handled by the same proof.

/-- A finite sum of Hilbert-valued martingale differences has second moment
bounded by the sum of its per-time L2 budgets, and satisfies the corresponding
strict Markov tail bound.

Layer: Glue | Gap: Level 1 (martingale finite-window second-moment and strict-tail bound)
Proof: cancel off-diagonal covariance terms with martingale-difference
  orthogonality, diagonalize the finite Hilbert covariance sum, apply the
  per-index second-moment budgets, then feed the aggregate squared-norm
  integrability and bound to the strict Markov inequality.
Source: Mathlib filtration, conditional expectation, Hilbert finite-sum
  covariance algebra, and SOptLib strict nonnegative Markov tail API
Used in: validation residual and stochastic-gradient finite-window martingale
  bounds before converting aggregate residual energy into probability tails
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/key_lemmas/1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic gradient descent -/
theorem martingale_second_moment_and_strict_tail_bound
    {Ω E : Type*} [mΩ : MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Filtration Nat mΩ) (zeta : Nat -> Ω -> E) (sigmaSeq : Nat -> ℝ)
    (hMD : SOptLib.MartingaleDifferenceL2Hypotheses μ F zeta sigmaSeq)
    (N : Nat) :
    (∫ ω, ‖Finset.sum (Finset.Icc 1 N) (fun i => zeta i ω)‖ ^ 2 ∂μ) <=
        Finset.sum (Finset.Icc 1 N) (fun i => sigmaSeq i ^ 2) /\
      forall lambda : ℝ, 0 < lambda ->
        μ {ω | ‖Finset.sum (Finset.Icc 1 N) (fun i => zeta i ω)‖ ^ 2 >
            lambda * Finset.sum (Finset.Icc 1 N)
              (fun i => sigmaSeq i ^ 2)} <=
          ENNReal.ofReal (1 / lambda) := by
  classical
  let I := Finset.Icc 1 N
  have h_ae_meas : forall i, i ∈ I ->
      AEStronglyMeasurable (zeta i) μ := by
    intro i hi
    have hi1 : 1 <= i := (Finset.mem_Icc.mp hi).1
    have hmeas_i : @Measurable Ω E (F i) _ (zeta i) :=
      SOptLib.MartingaleDifferenceL2Hypotheses.measurable hMD i hi1
    exact (hmeas_i.of_measurableSpace_le (F.le i)).aestronglyMeasurable
  have hL2I : forall i, i ∈ I ->
      Integrable (fun ω => ‖zeta i ω‖ ^ 2) μ := by
    intro i hi
    exact SOptLib.MartingaleDifferenceL2Hypotheses.integrable_norm_sq
      hMD i ((Finset.mem_Icc.mp hi).1)
  have hcross :
      forall i, i ∈ I -> forall j, j ∈ I -> i ≠ j ->
        ∫ ω, ⟪zeta i ω, zeta j ω⟫_ℝ ∂μ = 0 := by
    intro i hi j hj hij
    exact integral_inner_martingale_difference_eq_zero_of_ne
      (μ := μ) F zeta
      (SOptLib.MartingaleDifferenceL2Hypotheses.measurable hMD)
      (SOptLib.MartingaleDifferenceL2Hypotheses.integrable hMD)
      (SOptLib.MartingaleDifferenceL2Hypotheses.condExp_eq_zero hMD)
      (SOptLib.MartingaleDifferenceL2Hypotheses.integrable_norm_sq hMD)
      ((Finset.mem_Icc.mp hi).1) ((Finset.mem_Icc.mp hj).1) hij
  have hdiag :
      ∫ ω, ‖Finset.sum I (fun i => zeta i ω)‖ ^ 2 ∂μ =
        Finset.sum I (fun i => ∫ ω, ‖zeta i ω‖ ^ 2 ∂μ) :=
    integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero
      μ I zeta h_ae_meas hL2I hcross
  have hL2Bound :
      (∫ ω, ‖Finset.sum I (fun i => zeta i ω)‖ ^ 2 ∂μ) <=
        Finset.sum I (fun i => sigmaSeq i ^ 2) := by
    rw [hdiag]
    exact Finset.sum_le_sum (by
      intro i hi
      exact SOptLib.MartingaleDifferenceL2Hypotheses.second_moment_le
        hMD i ((Finset.mem_Icc.mp hi).1))
  constructor
  · simpa [I] using hL2Bound
  · intro lambda hlambda
    set C : ℝ := Finset.sum I (fun i => sigmaSeq i ^ 2) with hC_def
    have hC_nonneg : 0 <= C := by
      rw [hC_def]
      exact Finset.sum_nonneg (by
        intro i hi
        exact sq_nonneg (sigmaSeq i))
    have hsum_int :
        Integrable
          (fun ω => ‖Finset.sum I (fun i => zeta i ω)‖ ^ 2) μ :=
      SOptLib.integrable_norm_sq_finset_sum_of_integrable_norm_sq
        μ I zeta h_ae_meas hL2I
    have hL2BoundC :
        (∫ ω, ‖Finset.sum I (fun i => zeta i ω)‖ ^ 2 ∂μ) <= C := by
      simpa [hC_def] using hL2Bound
    have htail := measure_gt_le_of_integral_le_of_nonneg
      (μ := μ)
      (f := fun ω => ‖Finset.sum I (fun i => zeta i ω)‖ ^ 2)
      (t := lambda * C) (C := C) (b := 1 / lambda)
      hsum_int
      (by intro ω; exact sq_nonneg (‖Finset.sum I (fun i => zeta i ω)‖))
      hL2BoundC
      (mul_nonneg (le_of_lt hlambda) hC_nonneg)
      (by
        intro htpos
        have hCpos : 0 < C := by
          nlinarith [htpos, hlambda, hC_nonneg]
        have hEq : C / (lambda * C) = 1 / lambda := by
          field_simp [hlambda.ne', hCpos.ne']
        rw [hEq])
      (by
        intro htzero
        nlinarith [hC_nonneg, hlambda, htzero])
    simpa [I, hC_def] using htail
