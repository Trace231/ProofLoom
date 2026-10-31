import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

open MeasureTheory

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: integrated objective-error Lyapunov one-step inequality; orig was the PAGE-local `page_integrated_lyapunov_step`
-- generality used: an arbitrary measurable space and measure, four real-valued time-indexed observables (objective error, estimator error, gradient square, and displacement square), and positive scalar stepsize, refresh weight, and batch denominator; no finite-dimensional, probability, objective, oracle, or filtration assumptions are used
-- portable call pattern: PAGE, SPIDER, SARAH, and stochastic-gradient convergence proofs provide a pathwise smooth-descent inequality and an integrated estimator-error recursion, changing the objective, processes, measure, and scalar coefficients while reusing the same collected Lyapunov conclusion
-- counterargument checked: the existing descent and estimator-recursion entries provide the two premises separately, while no searched declaration combines their integrated forms with the exact displacement coefficient; this is a substantive composition boundary rather than a paper-local wrapper
-- coverage search: queried `integrated Lyapunov objective estimator error variance recursion`, `descent variance recursion collected coefficient`, and SOptLib Layer1 Descent/Telescope; hits such as `summed_one_step_gap_bound_of_telescope` and `estimator_residual_second_moment_step_of_refresh_or_centered_recursive_branch` were partial and have different finite-window or branch-level conclusions
-- minimal hypotheses: integrability of F at t and t+1 and of R, G, and D at t, one pathwise descent inequality, one integrated variance recursion, and positivity of the stepsize, refresh weight, and batch denominator; no probability normalization or sign assumption on the smoothness scalar is used

/-- A pathwise smooth-descent inequality and an integrated estimator-error
recursion combine into the collected one-step Lyapunov bound.

The four observable processes represent objective error, estimator error,
gradient-square, and displacement-square terms.  This keeps the integration
boundary explicit while allowing different stochastic-gradient algorithms to
instantiate the same algebra with their own processes and measures.

Layer: Layer1 | Gap: Level 1 (integrated objective-error Lyapunov composition)
Proof: integrate the pathwise descent inequality, rewrite the integrated
variance recursion through linearity of the Bochner integral, scale it by the
nonnegative Lyapunov weight, and normalize the displacement coefficient by
ordered-field arithmetic.
Source: Mathlib Bochner integration linearity, integral monotonicity, and real
ordered-field arithmetic for stochastic-gradient Lyapunov recurrences
Used in: PAGE, SPIDER, SARAH, and stochastic-gradient analyses after the
smooth-descent and estimator-variance steps and before telescoping over time
Book citation: book/research/PAGE.json#/main_theorem/proof/3
Origin algorithm: Li, Bao, Zhang, and Richtárik, PAGE: A Simple and Optimal Probabilistic Gradient Estimator for Nonconvex Optimization -/
theorem integrated_objective_error_lyapunov_step_of_integrands
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω)
    (F R G D : ℕ → Ω → ℝ)
    {η p L b : ℝ} (t : ℕ)
    (hη_pos : 0 < η) (hp_pos : 0 < p) (hb_pos : 0 < b)
    (hF_t_int : Integrable (F t) P)
    (hF_t1_int : Integrable (F (t + 1)) P)
    (hR_t_int : Integrable (R t) P)
    (hG_t_int : Integrable (G t) P)
    (hD_t_int : Integrable (D t) P)
    (hdescent_point : ∀ ω : Ω,
      F (t + 1) ω ≤ F t ω - (η / 2) * G t ω -
          ((2 * η)⁻¹ - L / 2) * D t ω + (η / 2) * R t ω)
    (hvariance :
      (∫ ω, R (t + 1) ω ∂P) ≤
        ∫ ω, (1 - p) * R t ω +
          (((1 - p) * L ^ 2) / b) * D t ω ∂P) :
    (∫ ω, F (t + 1) ω ∂P) + η / (2 * p) *
        (∫ ω, R (t + 1) ω ∂P) ≤
      (∫ ω, F t ω ∂P) + η / (2 * p) *
          (∫ ω, R t ω ∂P) - (η / 2) *
            (∫ ω, G t ω ∂P) -
        ((2 * η)⁻¹ - L / 2 -
            ((1 - p) * η * L ^ 2) / (2 * p * b)) *
          (∫ ω, D t ω ∂P) := by
  have hdescent_rhs_int :
      Integrable (fun ω =>
        F t ω - (η / 2) * G t ω -
          ((2 * η)⁻¹ - L / 2) * D t ω + (η / 2) * R t ω) P := by
    exact
      ((hF_t_int.sub (hG_t_int.const_mul (η / 2))).sub
        (hD_t_int.const_mul ((2 * η)⁻¹ - L / 2))).add
          (hR_t_int.const_mul (η / 2))
  have hdescent_int :
      (∫ ω, F (t + 1) ω ∂P) ≤
        ∫ ω, F t ω - (η / 2) * G t ω -
          ((2 * η)⁻¹ - L / 2) * D t ω + (η / 2) * R t ω ∂P := by
    exact integral_mono hF_t1_int hdescent_rhs_int hdescent_point
  have hdescent_rhs_eq :
      (∫ ω, F t ω - (η / 2) * G t ω -
          ((2 * η)⁻¹ - L / 2) * D t ω + (η / 2) * R t ω ∂P) =
        (∫ ω, F t ω ∂P) - (η / 2) * (∫ ω, G t ω ∂P) -
          ((2 * η)⁻¹ - L / 2) * (∫ ω, D t ω ∂P) +
            (η / 2) * (∫ ω, R t ω ∂P) := by
    calc
      (∫ ω, F t ω - (η / 2) * G t ω -
          ((2 * η)⁻¹ - L / 2) * D t ω + (η / 2) * R t ω ∂P) =
          (∫ ω, F t ω - (η / 2) * G t ω -
              ((2 * η)⁻¹ - L / 2) * D t ω ∂P) +
            ∫ ω, (η / 2) * R t ω ∂P := by
        simpa only [Pi.add_apply] using
          (integral_add
            ((hF_t_int.sub (hG_t_int.const_mul (η / 2))).sub
              (hD_t_int.const_mul ((2 * η)⁻¹ - L / 2)))
            (hR_t_int.const_mul (η / 2)))
      _ =
          (((∫ ω, F t ω - (η / 2) * G t ω ∂P) -
              ∫ ω, ((2 * η)⁻¹ - L / 2) * D t ω ∂P) +
            ∫ ω, (η / 2) * R t ω ∂P) := by
        congr 1
        simpa only [Pi.sub_apply] using
          (integral_sub
            (hF_t_int.sub (hG_t_int.const_mul (η / 2)))
            (hD_t_int.const_mul ((2 * η)⁻¹ - L / 2)))
      _ =
          (((∫ ω, F t ω ∂P) -
              ∫ ω, (η / 2) * G t ω ∂P) -
            ∫ ω, ((2 * η)⁻¹ - L / 2) * D t ω ∂P) +
            ∫ ω, (η / 2) * R t ω ∂P := by
        congr 2
        simpa only [Pi.sub_apply] using
          (integral_sub hF_t_int (hG_t_int.const_mul (η / 2)))
      _ =
          (∫ ω, F t ω ∂P) - (η / 2) * (∫ ω, G t ω ∂P) -
            ((2 * η)⁻¹ - L / 2) * (∫ ω, D t ω ∂P) +
              (η / 2) * (∫ ω, R t ω ∂P) := by
        rw [integral_const_mul, integral_const_mul, integral_const_mul]
  have hdescent :
      (∫ ω, F (t + 1) ω ∂P) ≤
        (∫ ω, F t ω ∂P) - (η / 2) * (∫ ω, G t ω ∂P) -
          ((2 * η)⁻¹ - L / 2) * (∫ ω, D t ω ∂P) +
            (η / 2) * (∫ ω, R t ω ∂P) := by
    rw [hdescent_rhs_eq] at hdescent_int
    exact hdescent_int
  have hvariance_rhs_eq :
      (∫ ω, (1 - p) * R t ω +
          (((1 - p) * L ^ 2) / b) * D t ω ∂P) =
        (1 - p) * (∫ ω, R t ω ∂P) +
          (((1 - p) * L ^ 2) / b) * (∫ ω, D t ω ∂P) := by
    calc
      (∫ ω, (1 - p) * R t ω +
          (((1 - p) * L ^ 2) / b) * D t ω ∂P) =
          ∫ ω, (1 - p) * R t ω ∂P +
            ∫ ω, (((1 - p) * L ^ 2) / b) * D t ω ∂P := by
        simpa only [Pi.add_apply] using
          (integral_add (hR_t_int.const_mul (1 - p))
            (hD_t_int.const_mul (((1 - p) * L ^ 2) / b)))
      _ = (1 - p) * (∫ ω, R t ω ∂P) +
            (((1 - p) * L ^ 2) / b) * (∫ ω, D t ω ∂P) := by
        rw [integral_const_mul, integral_const_mul]
  have hvar :
      (∫ ω, R (t + 1) ω ∂P) ≤
        (1 - p) * (∫ ω, R t ω ∂P) +
          (((1 - p) * L ^ 2) / b) * (∫ ω, D t ω ∂P) := by
    rw [hvariance_rhs_eq] at hvariance
    exact hvariance
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  have hb_ne : b ≠ 0 := ne_of_gt hb_pos
  have hweight_nonneg : 0 ≤ η / (2 * p) := by
    exact div_nonneg hη_pos.le (mul_nonneg (by norm_num) hp_pos.le)
  have hvar_scaled :
      η / (2 * p) * (∫ ω, R (t + 1) ω ∂P) ≤
        η / (2 * p) *
          ((1 - p) * (∫ ω, R t ω ∂P) +
            (((1 - p) * L ^ 2) / b) * (∫ ω, D t ω ∂P)) :=
    mul_le_mul_of_nonneg_left hvar hweight_nonneg
  calc
    (∫ ω, F (t + 1) ω ∂P) + η / (2 * p) *
          (∫ ω, R (t + 1) ω ∂P) ≤
        ((∫ ω, F t ω ∂P) - (η / 2) * (∫ ω, G t ω ∂P) -
            ((2 * η)⁻¹ - L / 2) * (∫ ω, D t ω ∂P) +
              (η / 2) * (∫ ω, R t ω ∂P)) +
          η / (2 * p) * (∫ ω, R (t + 1) ω ∂P) := by
      exact add_le_add hdescent (le_refl _)
    _ ≤
        ((∫ ω, F t ω ∂P) - (η / 2) * (∫ ω, G t ω ∂P) -
            ((2 * η)⁻¹ - L / 2) * (∫ ω, D t ω ∂P) +
              (η / 2) * (∫ ω, R t ω ∂P)) +
          η / (2 * p) *
            ((1 - p) * (∫ ω, R t ω ∂P) +
              (((1 - p) * L ^ 2) / b) * (∫ ω, D t ω ∂P)) := by
      exact add_le_add (le_refl _) hvar_scaled
    _ =
        (∫ ω, F t ω ∂P) + η / (2 * p) *
            (∫ ω, R t ω ∂P) - (η / 2) *
              (∫ ω, G t ω ∂P) -
          ((2 * η)⁻¹ - L / 2 -
              ((1 - p) * η * L ^ 2) / (2 * p * b)) *
            (∫ ω, D t ω ∂P) := by
      field_simp [hp_ne, hb_ne]
      ring

/-- Combine scalar integrated descent and estimator-error recursions into the
collected objective-error Lyapunov step.

This scalar form is the call-site boundary for algorithms that have already
established the relevant Bochner integrals and reduced their pathwise
inequalities to real sequences.

Layer: Layer1 | Gap: Level 1 (scalar integrated Lyapunov algebra)
Proof: scale the variance recursion by the nonnegative Lyapunov weight and
collect the objective, estimator, gradient, and displacement coefficients by
ordered-field normalization.
Source: Mathlib ordered-field arithmetic for the collected PAGE Lyapunov
recurrence
Used in: PAGE and variance-reduced stochastic-gradient proofs after
integrating the smooth-descent and estimator-error inequalities
Book citation: book/research/PAGE.json#/main_theorem/proof/4
Origin algorithm: Li, Bao, Zhang, and Richtárik, PAGE: A Simple and Optimal Probabilistic Gradient Estimator for Nonconvex Optimization -/
theorem integrated_objective_error_lyapunov_step
    (F R G D : ℕ → ℝ) {η p L b : ℝ} (t : ℕ)
    (hη_pos : 0 < η) (hp_pos : 0 < p) (hb_pos : 0 < b)
    (hdescent :
      F (t + 1) ≤ F t - (η / 2) * G t -
        ((2 * η)⁻¹ - L / 2) * D t + (η / 2) * R t)
    (hvariance :
      R (t + 1) ≤ (1 - p) * R t +
        (((1 - p) * L ^ 2) / b) * D t) :
    F (t + 1) + η / (2 * p) * R (t + 1) ≤
      F t + η / (2 * p) * R t - (η / 2) * G t -
        ((2 * η)⁻¹ - L / 2 -
          ((1 - p) * η * L ^ 2) / (2 * p * b)) * D t := by
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  have hb_ne : b ≠ 0 := ne_of_gt hb_pos
  have hweight_nonneg : 0 ≤ η / (2 * p) := by
    exact div_nonneg hη_pos.le (mul_nonneg (by norm_num) hp_pos.le)
  have hvar_scaled :
      η / (2 * p) * R (t + 1) ≤
        η / (2 * p) *
          ((1 - p) * R t + (((1 - p) * L ^ 2) / b) * D t) :=
    mul_le_mul_of_nonneg_left hvariance hweight_nonneg
  calc
    F (t + 1) + η / (2 * p) * R (t + 1) ≤
        (F t - (η / 2) * G t -
            ((2 * η)⁻¹ - L / 2) * D t + (η / 2) * R t) +
          η / (2 * p) * R (t + 1) := by
      exact add_le_add hdescent (le_refl _)
    _ ≤
        (F t - (η / 2) * G t -
            ((2 * η)⁻¹ - L / 2) * D t + (η / 2) * R t) +
          η / (2 * p) *
            ((1 - p) * R t + (((1 - p) * L ^ 2) / b) * D t) := by
      exact add_le_add (le_refl _) hvar_scaled
    _ = F t + η / (2 * p) * R t - (η / 2) * G t -
        ((2 * η)⁻¹ - L / 2 -
          ((1 - p) * η * L ^ 2) / (2 * p * b)) * D t := by
      field_simp [hp_ne, hb_ne]
      ring

end SOptLib
