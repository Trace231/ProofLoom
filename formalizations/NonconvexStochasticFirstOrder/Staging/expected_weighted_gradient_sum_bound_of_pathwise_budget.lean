import SOptLib.Glue.Probability

open MeasureTheory
open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: expected finite-window weighted-gradient budget from a pathwise budget
-- generality used: arbitrary measurable sample space, probability measure, finite index set, real-valued summands, and scalar coefficients; no objective, oracle, smoothness, independence, filtration, Hilbert-space, or finite-dimensional assumptions are used
-- portable call pattern: stochastic-gradient, variance-reduced, and distributed-noise convergence proofs call this after a pathwise weighted budget has been derived; the index window, weighted target, cross term, residual-square term, coefficients, and deterministic variance budget vary while the expected aggregation conclusion stays fixed
-- counterargument checked: not paper-local traceability or a caller-side wrapper because it packages the recurring integration, zero-cross-term cancellation, and nonnegative residual-budget aggregation; existing finite-sum expectation lifts and zero-mean quadratic-noise lemmas cover only partial steps or different pointwise contracts
-- coverage search: queried `finite sum integral pointwise inequality integrable summands zero integral cross term variance bound`, `integral finset sum le of pointwise finset sum bound`, and `expected weighted gradient sum bound`; closest hits were `integral_finset_sum_le_of_pointwise_finset_sum_le` in SOptLib.Glue.Probability and `finite_window_zero_mean_plus_quadratic_noise_integral_bound` in SOptLib.Layer1.Telescope, both partial
-- minimal hypotheses: probability normalization is needed only to integrate the deterministic initial budget; integrability is pointwise on the active finite window, cross cancellation is pointwise on that window, and residual coefficients are assumed nonnegative only where monotonicity uses them

/-- A pathwise weighted budget gives an expected weighted finite-window bound.

If a finite sum of integrable target terms is pointwise bounded by an initial
budget plus cross terms and residual-square terms, if every cross term has zero
integral, and if each residual-square integral is bounded by a common budget,
then the expected target sum is bounded by the initial budget plus the
coefficient-weighted residual budget.

Layer: Layer1 | Gap: Level 1 (expected weighted finite-window budget aggregation)
Proof: lift the pointwise finite-sum inequality through Bochner integral
monotonicity, split each correction integral by linearity, cancel the
zero-integral cross term, and apply the nonnegative residual coefficient to
the per-index integral bound.
Source: Mathlib Bochner integral monotonicity, finite-sum linearity, and
ordered real arithmetic APIs
Used in: stochastic-gradient stationarity proofs after a pathwise weighted
descent budget has been telescoped and residual cross terms have been shown
to vanish in expectation
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning - two-phase randomized stochastic gradient descent -/
theorem expected_weighted_gradient_sum_bound_of_pathwise_budget
    {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Finset ι)
    (A cross deltaSq : ι → Ω → ℝ)
    (crossCoeff stepSq : ι → ℝ)
    (initial sigma2 : ℝ)
    (hA_int : ∀ i ∈ s, Integrable (A i) μ)
    (hcross_int : ∀ i ∈ s, Integrable (cross i) μ)
    (hdeltaSq_int : ∀ i ∈ s, Integrable (deltaSq i) μ)
    (hpoint :
      ∀ᵐ ω ∂μ,
        Finset.sum s (fun i => A i ω) ≤
          initial +
            Finset.sum s (fun i =>
              crossCoeff i * cross i ω + stepSq i * deltaSq i ω))
    (hcross_zero : ∀ i ∈ s, ∫ ω, cross i ω ∂μ = 0)
    (hdeltaSq_bound : ∀ i ∈ s, ∫ ω, deltaSq i ω ∂μ ≤ sigma2)
    (hstepSq_nonneg : ∀ i ∈ s, 0 ≤ stepSq i) :
    Finset.sum s (fun i => ∫ ω, A i ω ∂μ) ≤
      initial + sigma2 * Finset.sum s stepSq := by
  classical
  let C : ι → Ω → ℝ := fun i ω =>
    crossCoeff i * cross i ω + stepSq i * deltaSq i ω
  have hC_int : ∀ i ∈ s, Integrable (C i) μ := by
    intro i hi
    exact (hcross_int i hi).const_mul (crossCoeff i) |>.add
      ((hdeltaSq_int i hi).const_mul (stepSq i))
  have hlift :=
    integral_finset_sum_le_of_pointwise_finset_sum_le
      (mu := μ) (s := s) (A := A) (C := C) (c := (1 : ℝ))
      (gap := initial) hA_int hC_int (by
        filter_upwards [hpoint] with ω hω
        simpa [C, one_smul] using hω)
  have hC_eval :
      Finset.sum s (fun i => ∫ ω, C i ω ∂μ) ≤
        sigma2 * Finset.sum s stepSq := by
    calc
      Finset.sum s (fun i => ∫ ω, C i ω ∂μ)
          ≤ Finset.sum s (fun i => stepSq i * sigma2) := by
            refine Finset.sum_le_sum ?_
            intro i hi
            have hC_i :
                ∫ ω, C i ω ∂μ =
                  stepSq i * ∫ ω, deltaSq i ω ∂μ := by
              rw [integral_add]
              · rw [integral_const_mul, integral_const_mul, hcross_zero i hi]
                ring
              · exact (hcross_int i hi).const_mul (crossCoeff i)
              · exact (hdeltaSq_int i hi).const_mul (stepSq i)
            rw [hC_i]
            exact mul_le_mul_of_nonneg_left
              (hdeltaSq_bound i hi) (hstepSq_nonneg i hi)
      _ = sigma2 * Finset.sum s stepSq := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
  calc
    Finset.sum s (fun i => ∫ ω, A i ω ∂μ)
        = (1 : ℝ) • Finset.sum s (fun i => ∫ ω, A i ω ∂μ) := by
          simp
    _ ≤ initial +
        (1 : ℝ) • Finset.sum s (fun i => ∫ ω, C i ω ∂μ) := by
          simpa using hlift
    _ ≤ initial + sigma2 * Finset.sum s stepSq := by
          simpa using add_le_add_left hC_eval initial
