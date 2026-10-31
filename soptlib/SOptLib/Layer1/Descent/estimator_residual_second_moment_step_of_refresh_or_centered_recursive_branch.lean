import SOptLib.Layer1.Descent

open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: estimator residual second-moment step for a refresh-or-centered recursive branch
-- generality used: an arbitrary measure on a measurable space and Hilbert-valued residual, refresh, recursive-increment, and displacement processes; the proof uses only Bochner integrability, a branch decomposition, a zero refresh residual, and a false-branch square budget. No probability normalization, finite-dimensionality, objective, or filtration is needed.
-- portable call pattern: variance-reduced stochastic estimators use this after proving the refresh branch is exact and the centered recursive branch has a weighted square budget; the residual processes, branch map, displacement, refresh probability, smoothness constant, and batch denominator vary across algorithms.
-- counterargument checked: existing additive second-moment lemmas cover a recursive sum with a supplied cross cancellation, while this theorem packages the two-branch estimator composition and its weighted integral algebra. It is therefore a reusable proof step rather than a paper-local label or a caller-side expression.
-- coverage search: searched `estimator residual second moment recursion branch`, `recursive estimator residual second moment`, and `refresh centered recursive branch`; existing SOptLib coverage was partial (`recursiveEstimatorResidual_secondMoment_step_le_of_centered_minibatch` requires a single recursive branch and finite-row hypotheses), so this theorem adds the refresh branch and measure-level false-branch budget.
-- minimal hypotheses: no integrability or probability instance is added beyond the supplied integral inequality; smoothness and batch-cardinality assumptions are represented by its scalar budget and denominator.

/-- A refresh-or-centered-recursive estimator step obeys its weighted residual
second-moment recursion.

The refresh branch is required to have zero residual, while the recursive branch
adds a centered increment to the previous residual.  A false-branch square
budget then yields the usual `(1 - q)` old-error term and `((1-q) L^2 / b)`
displacement term.

Layer: Layer1 | Gap: Level 1 (refresh-or-recursive estimator second-moment composition)
Proof: rewrite the next residual through the branch decomposition, apply the supplied false-branch square bound, and normalize its scalar expression pointwise.
Source: Mathlib Bochner integral algebra and Hilbert-space norm-square estimates for stochastic recursive estimators
Used in: variance-reduced stochastic-gradient steps that combine an exact refresh estimator with a centered recursive mini-batch update
Book citation: book/research/PAGE.json#/key_lemmas/2
Origin algorithm: Li, Bao, Zhang, and Richtárik, PAGE: A Simple and Optimal Probabilistic Gradient Estimator for Nonconvex Optimization -/
theorem estimator_residual_second_moment_step_of_refresh_or_centered_recursive_branch
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E]
    (μ : Measure Ω)
    (residualPrev residualNext refreshError recursiveIncrement displacement : Ω → E)
    (branch : Ω → Bool) (q L b : ℝ)
    (hbranch_decomp : ∀ ω,
      residualNext ω = if branch ω then refreshError ω
        else residualPrev ω + recursiveIncrement ω)
    (hrefresh_zero : ∀ ω, branch ω → refreshError ω = 0)
    (hfalse_square_bound :
      (∫ ω, (if branch ω = false then
          ‖residualPrev ω + recursiveIncrement ω‖ ^ 2 else 0) ∂μ) ≤
        ∫ ω, (1 - q) *
          (‖residualPrev ω‖ ^ 2 + (L ^ 2 / b) * ‖displacement ω‖ ^ 2) ∂μ) :
    ∫ ω, ‖residualNext ω‖ ^ 2 ∂μ ≤
      ∫ ω, (1 - q) * ‖residualPrev ω‖ ^ 2 +
        (((1 - q) * L ^ 2) / b) * ‖displacement ω‖ ^ 2 ∂μ := by
  have hnext_eq :
      (fun ω => ‖residualNext ω‖ ^ 2) =
        (fun ω => if branch ω = false then
          ‖residualPrev ω + recursiveIncrement ω‖ ^ 2 else 0) := by
    funext ω
    rw [hbranch_decomp ω]
    by_cases hbranch : branch ω
    · have hrefresh := hrefresh_zero ω hbranch
      simp [hbranch, hrefresh]
    · simp [hbranch]
  calc
    (∫ ω, ‖residualNext ω‖ ^ 2 ∂μ) =
        ∫ ω, (if branch ω = false then
          ‖residualPrev ω + recursiveIncrement ω‖ ^ 2 else 0) ∂μ := by
      rw [hnext_eq]
    _ ≤ ∫ ω, (1 - q) *
          (‖residualPrev ω‖ ^ 2 + (L ^ 2 / b) *
            ‖displacement ω‖ ^ 2) ∂μ := hfalse_square_bound
    _ = ∫ ω, (1 - q) * ‖residualPrev ω‖ ^ 2 +
          (((1 - q) * L ^ 2) / b) * ‖displacement ω‖ ^ 2 ∂μ := by
      have hsplit :
          (fun ω => (1 - q) *
            (‖residualPrev ω‖ ^ 2 + (L ^ 2 / b) *
              ‖displacement ω‖ ^ 2)) =
            (fun ω => (1 - q) * ‖residualPrev ω‖ ^ 2 +
              (((1 - q) * L ^ 2) / b) * ‖displacement ω‖ ^ 2) := by
        funext ω
        ring
      rw [hsplit]

end SOptLib
