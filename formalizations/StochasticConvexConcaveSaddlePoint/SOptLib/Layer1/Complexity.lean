import Mathlib.Tactic
import SOptLib.Glue.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import SOptLib.Glue.Algebra
import SOptLib.Model.Complexity

/-- A budget with an affine inverse-plus-variance inverse-square ceiling has the same rate.

This packages the arithmetic used after a closed-form stochastic-optimization
budget selector has been upper-bounded by deterministic, variance, stability,
and constant ceiling-slack terms.

Layer: Layer1 | Gap: Level 1 (inverse-square budget rate algebra)
Proof: choose a constant dominating the deterministic, variance, stability, and
  ceiling-slack coefficients; use `0 < ε ≤ 1` to absorb constants into `ε⁻¹`
  and variance-stability terms into `σ² ε⁻²`.
Source: Mathlib ordered-field arithmetic and nonlinear arithmetic APIs for
  stochastic-optimization complexity rates
Used in: nonconvex stochastic mirror descent per-run SFO budget complexity
  accounting for the two-phase randomized parameter choice
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
theorem exists_const_budget_le_inv_add_sigma_sq_inv_sq
    (budget : ℝ → ℕ) (σ A B C : ℝ)
    (hA_nonneg : 0 ≤ A) (hB_nonneg : 0 ≤ B) (hC_nonneg : 0 ≤ C)
    (hbudget_le :
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        (budget ε : ℝ) ≤
          A * ε⁻¹ + B * σ ^ 2 * ε⁻¹ ^ 2 + C * σ ^ 2 + 2) :
    ∃ CN : ℝ, 0 < CN ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        (budget ε : ℝ) ≤ CN * (ε⁻¹ + σ ^ 2 * ε⁻¹ ^ 2) := by
  refine ⟨3 + A + B + C, ?_, ?_⟩
  · nlinarith
  · intro ε hε hε_le_one
    have hupper := hbudget_le ε hε hε_le_one
    have hε_inv_ge_one : 1 ≤ ε⁻¹ := by
      field_simp [ne_of_gt hε]
      exact hε_le_one
    have hε_inv_sq_ge_one : 1 ≤ ε⁻¹ ^ 2 := by
      nlinarith
    have hσ_sq_nonneg : 0 ≤ σ ^ 2 := sq_nonneg σ
    have hCN_BC : B + C ≤ 3 + A + B + C := by nlinarith
    have hpart₁ : A * ε⁻¹ + 2 ≤ (3 + A + B + C) * ε⁻¹ := by
      nlinarith
    have hpart₂ :
        B * σ ^ 2 * ε⁻¹ ^ 2 + C * σ ^ 2 ≤
          (3 + A + B + C) * (σ ^ 2 * ε⁻¹ ^ 2) := by
      have hCterm :
          C * σ ^ 2 ≤ C * σ ^ 2 * ε⁻¹ ^ 2 := by
        have hcoef_nonneg : 0 ≤ C * σ ^ 2 :=
          mul_nonneg hC_nonneg hσ_sq_nonneg
        nlinarith
      have hsum :
          B * σ ^ 2 * ε⁻¹ ^ 2 + C * σ ^ 2 ≤
            (B + C) * (σ ^ 2 * ε⁻¹ ^ 2) := by
        calc
          B * σ ^ 2 * ε⁻¹ ^ 2 + C * σ ^ 2
              ≤ B * σ ^ 2 * ε⁻¹ ^ 2 + C * σ ^ 2 * ε⁻¹ ^ 2 := by
                exact add_le_add (le_refl _) hCterm
          _ = (B + C) * (σ ^ 2 * ε⁻¹ ^ 2) := by ring
      have hscale_nonneg : 0 ≤ σ ^ 2 * ε⁻¹ ^ 2 :=
        mul_nonneg hσ_sq_nonneg (sq_nonneg ε⁻¹)
      exact le_trans hsum (mul_le_mul_of_nonneg_right hCN_BC hscale_nonneg)
    have hrate :
        A * ε⁻¹ + B * σ ^ 2 * ε⁻¹ ^ 2 + C * σ ^ 2 + 2 ≤
          (3 + A + B + C) * (ε⁻¹ + σ ^ 2 * ε⁻¹ ^ 2) := by
      nlinarith
    exact le_trans hupper hrate

/-- A logarithmic run count times a validation count has the two-phase log-squared rate.

If the real run-count envelope `S` is bounded by three base-two logarithms and
the validation-count envelope `T` is bounded by the paper variance-balancing
quantity plus a constant slack, then `S * T` is bounded by a universal constant
times the sum of the linear-log and variance log-squared rates.

Layer: Layer1 | Gap: Level 1 (two-phase validation-count rate algebra)
Proof: expand `S * T` using the validation-count upper bound, control the
  quadratic run-count term by the squared logarithmic envelope, and absorb the
  linear slack using `ε ≤ 1` and the logarithmic lower bound.
Source: Mathlib ordered-field arithmetic, real logarithm, and nonlinear
  arithmetic APIs for stochastic-optimization complexity rates
Used in: nonconvex stochastic mirror descent SFO complexity accounting for the
  repeated-run validation phase
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
theorem exists_const_run_mul_validation_le_log_rate
    (S T : ℝ → ℝ → ℝ) (σ : ℝ)
    (hS_nonneg :
      ∀ ε Λ : ℝ, 0 < ε → 0 < Λ → 0 ≤ S ε Λ)
    (hS_le :
      ∀ ε Λ : ℝ, 0 < ε → 0 < Λ → Λ ≤ 1 / 2 →
        S ε Λ ≤ 3 * (Real.log (1 / Λ) / Real.log 2))
    (hT_le :
      ∀ ε Λ : ℝ, 0 < ε → 0 < Λ →
        T ε Λ ≤ 24 * S ε Λ * σ ^ 2 / (Λ * ε) + 2) :
    ∃ CT : ℝ, 0 < CT ∧
      ∀ ε Λ : ℝ, 0 < ε → ε ≤ 1 → 0 < Λ → Λ ≤ 1 / 2 →
        S ε Λ * T ε Λ ≤
          CT *
            (ε⁻¹ * (Real.log (1 / Λ) / Real.log 2) +
              σ ^ 2 / (Λ * ε) *
                (Real.log (1 / Λ) / Real.log 2) ^ 2) := by
  refine ⟨300, by norm_num, ?_⟩
  intro ε Λ hε hε_le_one hΛ_pos hΛ_half
  let l : ℝ := Real.log (1 / Λ) / Real.log 2
  let S₀ : ℝ := S ε Λ
  let T₀ : ℝ := T ε Λ
  let q : ℝ := σ ^ 2 / (Λ * ε)
  let y : ℝ := 24 * S₀ * σ ^ 2 / (Λ * ε)
  have hl_ge_one : 1 ≤ l := by
    simpa [l] using
      one_le_log_one_div_over_log_two_of_pos_le_half Λ hΛ_pos hΛ_half
  have hl_nonneg : 0 ≤ l := by linarith
  have hS_bound : S₀ ≤ 3 * l := by
    simpa [S₀, l] using hS_le ε Λ hε hΛ_pos hΛ_half
  have hS₀_nonneg : 0 ≤ S₀ := by
    simpa [S₀] using hS_nonneg ε Λ hε hΛ_pos
  have hT_bound : T₀ ≤ y + 2 := by
    simpa [T₀, y, S₀] using hT_le ε Λ hε hΛ_pos
  have hprod_step : S₀ * T₀ ≤ S₀ * (y + 2) :=
    mul_le_mul_of_nonneg_left hT_bound hS₀_nonneg
  have hprod_bound :
      S₀ * T₀ ≤ 24 * S₀ ^ 2 * σ ^ 2 / (Λ * ε) + 2 * S₀ := by
    calc
      S₀ * T₀ ≤ S₀ * (y + 2) := hprod_step
      _ = 24 * S₀ ^ 2 * σ ^ 2 / (Λ * ε) + 2 * S₀ := by
        dsimp [y]
        field_simp [ne_of_gt hΛ_pos, ne_of_gt hε]
  have hε_inv_ge_one : 1 ≤ ε⁻¹ := by
    field_simp [ne_of_gt hε]
    exact hε_le_one
  have hS_sq : S₀ ^ 2 ≤ 9 * l ^ 2 := by
    nlinarith
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    positivity
  have hvar_scaled : q * S₀ ^ 2 ≤ q * (9 * l ^ 2) :=
    mul_le_mul_of_nonneg_left hS_sq hq_nonneg
  have hvar_bound :
      24 * S₀ ^ 2 * σ ^ 2 / (Λ * ε) ≤
        216 * (σ ^ 2 / (Λ * ε) * l ^ 2) := by
    have hscaled24 : 24 * (q * S₀ ^ 2) ≤ 24 * (q * (9 * l ^ 2)) :=
      mul_le_mul_of_nonneg_left hvar_scaled (by norm_num)
    calc
      24 * S₀ ^ 2 * σ ^ 2 / (Λ * ε)
          = 24 * (q * S₀ ^ 2) := by
            dsimp [q]
            ring
      _ ≤ 24 * (q * (9 * l ^ 2)) := hscaled24
      _ = 216 * (σ ^ 2 / (Λ * ε) * l ^ 2) := by
            dsimp [q]
            ring
  have hlinear_bound : 2 * S₀ ≤ 6 * (ε⁻¹ * l) := by
    have hl_le_inv_l : l ≤ ε⁻¹ * l :=
      by simpa using mul_le_mul_of_nonneg_right hε_inv_ge_one hl_nonneg
    nlinarith
  have ht₁_nonneg : 0 ≤ ε⁻¹ * l := by
    positivity
  have ht₃_nonneg : 0 ≤ σ ^ 2 / (Λ * ε) * l ^ 2 := by
    positivity
  have hcombined :
      S₀ * T₀ ≤
        6 * (ε⁻¹ * l) +
          216 * (σ ^ 2 / (Λ * ε) * l ^ 2) := by
    nlinarith
  have hrate :
      6 * (ε⁻¹ * l) +
          216 * (σ ^ 2 / (Λ * ε) * l ^ 2) ≤
        300 *
          (ε⁻¹ * l + σ ^ 2 / (Λ * ε) * l ^ 2) := by
    nlinarith
  simpa [S₀, T₀, l] using le_trans hcombined hrate

/-- A two-phase SFO call envelope has the displayed logarithmic asymptotic rate.

The theorem abstracts the deterministic complexity accounting for a method with
a run count, an optimization budget, and a validation budget.  It combines an
inverse-plus-inverse-square optimization envelope with a log-squared validation
envelope and a pointwise total-call comparison.

Layer: Layer1 | Gap: Level 1 (two-phase SFO-call rate algebra)
Proof: split the total call count into optimization and validation products,
  apply the supplied rate envelopes, and absorb the two partial bounds into the
  closed-form logarithmic rate by ordered-field arithmetic.
Source: Mathlib ordered-field arithmetic, natural-number casts, and real
  logarithm APIs for stochastic-optimization complexity rates
Used in: nonconvex stochastic mirror descent SFO-call complexity bound for the
  two-phase randomized confidence amplification argument
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
theorem twoPhaseSFOCallBound_bigO_rate
    (calls : ℝ → ℝ → ℕ)
    (rate : ℝ → ℝ → ℝ)
    (runs : ℝ → ℕ)
    (budget : ℝ → ℕ)
    (validation : ℝ → ℝ → ℕ)
    (σ : ℝ)
    (hrate :
      ∀ ε Λ : ℝ, rate ε Λ =
        ε⁻¹ * (Real.log (1 / Λ) / Real.log 2) +
          σ ^ 2 * ε⁻¹ ^ 2 * (Real.log (1 / Λ) / Real.log 2) +
            σ ^ 2 / (Λ * ε) * (Real.log (1 / Λ) / Real.log 2) ^ 2)
    (hruns_le :
      ∀ Λ : ℝ, 0 < Λ → Λ ≤ 1 / 2 →
        (runs Λ : ℝ) ≤ 3 * (Real.log (1 / Λ) / Real.log 2))
    (hbudget_core :
      ∃ CN : ℝ, 0 < CN ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
          (budget ε : ℝ) ≤ CN * (ε⁻¹ + σ ^ 2 * ε⁻¹ ^ 2))
    (hvalidation_core :
      ∃ CT : ℝ, 0 < CT ∧
        ∀ ε Λ : ℝ, 0 < ε → ε ≤ 1 → 0 < Λ → Λ ≤ 1 / 2 →
          (runs Λ : ℝ) * (validation ε Λ : ℝ) ≤
            CT *
              (ε⁻¹ * (Real.log (1 / Λ) / Real.log 2) +
                σ ^ 2 / (Λ * ε) *
                  (Real.log (1 / Λ) / Real.log 2) ^ 2))
    (hcalls_le :
      ∀ ε Λ : ℝ, 0 < ε → ε ≤ 1 → 0 < Λ → Λ ≤ 1 / 2 →
        calls ε Λ ≤ runs Λ * (budget ε + validation ε Λ)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ε Λ : ℝ, 0 < ε → ε ≤ 1 → 0 < Λ → Λ ≤ 1 / 2 →
        ((calls ε Λ : ℝ) ≤ C * rate ε Λ) := by
  rcases hbudget_core with ⟨CN, hCN_pos, hN_core⟩
  rcases hvalidation_core with ⟨CT, hCT_pos, hT_core⟩
  refine ⟨3 * CN + CT, by positivity, ?_⟩
  intro ε Λ hε hε_le_one hΛ_pos hΛ_half
  let l : ℝ := Real.log (1 / Λ) / Real.log 2
  let t₁ : ℝ := ε⁻¹ * l
  let t₂ : ℝ := σ ^ 2 * ε⁻¹ ^ 2 * l
  let t₃ : ℝ := σ ^ 2 / (Λ * ε) * l ^ 2
  have hl_ge_one : 1 ≤ l := by
    simpa [l] using
      one_le_log_one_div_over_log_two_of_pos_le_half Λ hΛ_pos hΛ_half
  have hl_nonneg : 0 ≤ l := by linarith
  have hε_inv_pos : 0 < ε⁻¹ := inv_pos.mpr hε
  have hε_inv_nonneg : 0 ≤ ε⁻¹ := le_of_lt hε_inv_pos
  have hσ_sq_nonneg : 0 ≤ σ ^ 2 := sq_nonneg σ
  have hN_nonneg : 0 ≤ (budget ε : ℝ) := by positivity
  have hbudget_core_point := hN_core ε hε hε_le_one
  have hS_le : (runs Λ : ℝ) ≤ 3 * l := by
    simpa [l] using hruns_le Λ hΛ_pos hΛ_half
  have hSN_mul :
      (runs Λ : ℝ) * (budget ε : ℝ) ≤
        (3 * l) * (CN * (ε⁻¹ + σ ^ 2 * ε⁻¹ ^ 2)) := by
    exact mul_le_mul hS_le hbudget_core_point
      hN_nonneg
      (mul_nonneg (by positivity) hl_nonneg)
  have hSN :
      (runs Λ : ℝ) * (budget ε : ℝ) ≤
        3 * CN * (t₁ + t₂) := by
    calc
      (runs Λ : ℝ) * (budget ε : ℝ)
          ≤ (3 * l) * (CN * (ε⁻¹ + σ ^ 2 * ε⁻¹ ^ 2)) := hSN_mul
      _ = 3 * CN * (t₁ + t₂) := by
        simp [t₁, t₂]
        ring
  have hST :
      (runs Λ : ℝ) * (validation ε Λ : ℝ) ≤ CT * (t₁ + t₃) := by
    simpa [t₁, t₃, l] using hT_core ε Λ hε hε_le_one hΛ_pos hΛ_half
  have ht₁_nonneg : 0 ≤ t₁ := by
    exact mul_nonneg hε_inv_nonneg hl_nonneg
  have ht₂_nonneg : 0 ≤ t₂ := by
    exact mul_nonneg (mul_nonneg hσ_sq_nonneg (sq_nonneg ε⁻¹)) hl_nonneg
  have hden_nonneg : 0 ≤ Λ * ε := le_of_lt (mul_pos hΛ_pos hε)
  have ht₃_nonneg : 0 ≤ t₃ := by
    exact mul_nonneg (div_nonneg hσ_sq_nonneg hden_nonneg) (sq_nonneg l)
  have htotal :
      (calls ε Λ : ℝ) ≤ 3 * CN * (t₁ + t₂) + CT * (t₁ + t₃) := by
    calc
      (calls ε Λ : ℝ)
          ≤ (runs Λ * (budget ε + validation ε Λ) : ℕ) := by
            exact_mod_cast hcalls_le ε Λ hε hε_le_one hΛ_pos hΛ_half
      _ = (runs Λ : ℝ) * (budget ε : ℝ) +
              (runs Λ : ℝ) * (validation ε Λ : ℝ) := by
            simp [Nat.cast_mul, Nat.cast_add, left_distrib]
      _ ≤ 3 * CN * (t₁ + t₂) + CT * (t₁ + t₃) :=
            add_le_add hSN hST
  rw [hrate ε Λ]
  dsimp [t₁, t₂, t₃, l] at *
  nlinarith [ht₁_nonneg, ht₂_nonneg, ht₃_nonneg, htotal, hCN_pos, hCT_pos]

/-- A two-phase natural-valued call counter is bounded by the logarithmic rate
when its optimization and validation components satisfy the standard envelopes.

The result isolates the final deterministic arithmetic step in a two-phase
confidence-amplification proof.  The concrete algorithm only supplies a
pointwise comparison with `runs * (budget + validation)` and separate component
rate bounds.

Layer: Layer1 | Gap: Level 1 (two-phase component-to-rate complexity algebra)
Proof: split the total call count into optimization and validation products,
  bound each product by its component envelope, and absorb the resulting three
  nonnegative terms into the displayed logarithmic rate by ordered-field
  arithmetic.
Source: Mathlib ordered-field arithmetic, natural-number casts, and real logarithm
  APIs for stochastic-optimization complexity rates
Used in: nonconvex stochastic mirror descent two-phase SFO-call bound near zero
  accuracy and confidence
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
theorem twoPhase_calls_le_const_mul_log_rate_of_components
    (calls : ℝ → ℝ → ℕ)
    (rate : ℝ → ℝ → ℝ)
    (runs : ℝ → ℕ)
    (budget : ℝ → ℕ)
    (validation : ℝ → ℝ → ℕ)
    (σ : ℝ)
    (hrate :
      ∀ ε Λ : ℝ, rate ε Λ =
        ε⁻¹ * (Real.log (1 / Λ) / Real.log 2) +
          σ ^ 2 * ε⁻¹ ^ 2 * (Real.log (1 / Λ) / Real.log 2) +
            σ ^ 2 / (Λ * ε) * (Real.log (1 / Λ) / Real.log 2) ^ 2)
    (hruns_le :
      ∀ Λ : ℝ, 0 < Λ → Λ ≤ 1 / 2 →
        (runs Λ : ℝ) ≤ 3 * (Real.log (1 / Λ) / Real.log 2))
    (hbudget_core :
      ∃ CN : ℝ, 0 < CN ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
          (budget ε : ℝ) ≤ CN * (ε⁻¹ + σ ^ 2 * ε⁻¹ ^ 2))
    (hvalidation_core :
      ∃ CT : ℝ, 0 < CT ∧
        ∀ ε Λ : ℝ, 0 < ε → ε ≤ 1 → 0 < Λ → Λ ≤ 1 / 2 →
          (runs Λ : ℝ) * (validation ε Λ : ℝ) ≤
            CT *
              (ε⁻¹ * (Real.log (1 / Λ) / Real.log 2) +
                σ ^ 2 / (Λ * ε) *
                  (Real.log (1 / Λ) / Real.log 2) ^ 2))
    (hcalls_le :
      ∀ ε Λ : ℝ, 0 < ε → ε ≤ 1 → 0 < Λ → Λ ≤ 1 / 2 →
        calls ε Λ ≤ runs Λ * (budget ε + validation ε Λ)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ε Λ : ℝ, 0 < ε → ε ≤ 1 → 0 < Λ → Λ ≤ 1 / 2 →
        ((calls ε Λ : ℝ) ≤ C * rate ε Λ) :=
  twoPhaseSFOCallBound_bigO_rate calls rate runs budget validation σ hrate hruns_le
    hbudget_core hvalidation_core hcalls_le



-- Generalization plan (G0):
-- G0.1 naming: exists_counterexample_l1_floor_corollary_scalar_compression
--   (orig was: exists_counterexample_l1_floor_corollary_scalar_compression);
--   the name describes a scalar counterexample to compressing an L1-floor
--   expected-gap corollary bound, without theorem numbers or paper-local setup.
-- G0.2 typeclass level used:
--   E: none; the proof is purely over real scalar complexity parameters.
--   measure: none; no stochastic process or measure-theoretic structure is used.
--   convexity: none; no feasible-set or convexity hypothesis is used.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional gradient, checking whether retained
--      mini-batch L1 floor terms can be compressed into a displayed coefficient.
--   2. stochastic Frank-Wolfe and conditional-gradient sliding variants, where
--      variance-balanced stepsizes and L1 residual floors are normalized into
--      final expected-gap displays.
-- G0.4 search trace:
--   queries: ["scalar counterexample floor compression",
--     "exists positive real not less equal"]
--   top hits: ["abs_scalar_block_oracle_noise_le_sample_majorant_add_mean_bound",
--     "exists_uniform_l1_bound_scalar_block_oracle_noise",
--     "integrable_scalar_oracle_noise_of_indep_uniform_l1_bound",
--     "exists_pos_const_mul_ge_of_nonneg_of_pos",
--     "exists_const_run_mul_validation_le_log_rate"]
--   coverage: none; hits cover scalar oracle bounds or positive scalar
--     domination, not an existential counterexample for a variance-balanced
--     stepsize formula versus a compressed L1-floor complexity bound.
-- G0.4 not-a-thin-wrapper rationale: the theorem packages a concrete
--   seven-parameter real witness showing a proposed compression is not a
--   consequence of the variance-balanced stepsize formula.
-- G0.5 structural-content rationale: this is a theorem with an explicit
--   counterexample and a square-root identity proof, not a def or structure.
-- G0.5c thin-wrapper self-detect: clean — body has explicit witness
--   construction, square-root normalization, and arithmetic contradiction.
-- G0.5d minimal-hypothesis check: all already minimal; the statement is
--   existential and carries no global hypotheses.

/-- A variance-balanced scalar stepsize can fail the compressed L1-floor bound.

There are positive scalar complexity parameters satisfying the displayed
variance-balanced stepsize formula with `α ≤ 1` and zero noise for which the
theorem-level RHS retaining the L1 floor is not bounded by the compressed
coefficient-`5` RHS.

Layer: Layer1 | Gap: Level 1 (scalar counterexample to L1-floor compression)
Proof: choose explicit real parameters, verify the square-root stepsize identity
  by squaring both sides, and discharge the remaining positivity and inequality
  checks by ordered-field arithmetic.
Source: Mathlib real square-root and ordered-field arithmetic APIs
Used in: stochastic nonconvex conditional-gradient expected-Wolfe-gap bound
  audit for variance-balanced stepsize normalization with retained L1 floors
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem exists_counterexample_l1_floor_corollary_scalar_compression :
    ∃ fGap L D α σ m N : ℝ,
      0 < fGap ∧ 0 < L ∧ 0 < D ∧ 0 ≤ σ ∧ 0 < m ∧ 0 < N ∧
      α ≤ 1 ∧
      α = Real.sqrt ((1 / N + σ ^ 2 / (L * m)) / (L * D ^ 2)) ∧
      ¬
        fGap / (N * α) + (7 / 2) * L * D ^ 2 * α +
            σ ^ 2 / (2 * L * m * α) + D * σ / Real.sqrt m ≤
          fGap / Real.sqrt N + 7 * L * D ^ 2 / (2 * Real.sqrt N) +
            5 * σ * D / Real.sqrt m := by
  refine ⟨20, 4, 1, 1 / 4, 0, 1, 4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  ·
    have hsqrt : Real.sqrt ((1 : ℝ) / 16) = 1 / 4 := by
      have hsq : (Real.sqrt ((1 : ℝ) / 16)) ^ 2 = (1 / 4 : ℝ) ^ 2 := by
        rw [Real.sq_sqrt]
        · norm_num
        · norm_num
      have hcases := sq_eq_sq_iff_eq_or_eq_neg.mp hsq
      rcases hcases with h | h
      · exact h
      · have hnonneg : 0 ≤ Real.sqrt ((1 : ℝ) / 16) := Real.sqrt_nonneg _
        nlinarith
    norm_num [hsqrt]
  · norm_num



-- Generalization plan (G0):
-- G0.1 naming: exists_counterexample_variance_balanced_stepsize_scalar_compression
--   (orig was: exists_counterexample_corollary712_printed_compression); renamed
--   to remove the theorem-number marker and describe the scalar complexity
--   obstruction: variance-balanced stepsize normalization does not force a
--   compressed residual-floor coefficient bound.
-- G0.2 typeclass level used:
--   E: none; the statement is purely real scalar complexity algebra.
--   measure: none; no probability space or stochastic process is used.
--   convexity: none; no feasible-set or convexity structure is used.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional gradient, checking compressed
--      expected-Wolfe-gap displays after variance-balanced stepsize choice.
--   2. stochastic Frank-Wolfe and conditional-gradient sliding variants, where
--      retained residual floors are normalized into final scalar complexity
--      bounds.
-- G0.4 search trace:
--   queries: ["scalar counterexample compression",
--     "positive real parameters sqrt not less equal",
--     "l1 floor corollary scalar compression"]
--   top hits: ["abs_scalar_block_oracle_noise_le_sample_majorant_add_mean_bound",
--     "exists_uniform_l1_bound_scalar_block_oracle_noise",
--     "integrable_scalar_oracle_noise_of_indep_uniform_l1_bound",
--     "le_positive_ceil_max_one",
--     "positiveStepsizeMirrorProxBlock",
--     "exists_counterexample_l1_floor_corollary_scalar_compression"]
--   coverage: partial — the previous staged
--     exists_counterexample_l1_floor_corollary_scalar_compression handles the
--     coefficient-5 instance, while this theorem strengthens it by quantifying
--     over an arbitrary scalar coefficient in the residual-floor term.
-- G0.4 not-a-thin-wrapper rationale: the theorem packages a concrete
--   seven-parameter real witness that defeats every coefficient-only
--   compression of the residual-floor term under the variance-balanced
--   stepsize formula.
-- G0.5 structural-content rationale: this is a theorem with an explicit
--   counterexample, a square-root normalization proof, and arithmetic
--   contradiction, not a def or structure.
-- G0.5c thin-wrapper self-detect: clean — body has explicit witness
--   construction, square-root normalization, and coefficient-parametric
--   arithmetic closure.
-- G0.5d minimal-hypothesis check: all already minimal; the statement is
--   coefficient-parametric and existential with no global hypotheses.

/-- A variance-balanced scalar stepsize can fail every coefficient compression.

For any proposed scalar coefficient on the residual-floor term, there are
positive scalar complexity parameters satisfying the variance-balanced stepsize
formula with `α ≤ 1` and zero noise for which the theorem-level RHS retaining
the residual floor is not bounded by the compressed coefficient RHS.

Layer: Layer1 | Gap: Level 1 (scalar counterexample to residual-floor compression)
Proof: choose explicit real parameters with zero variance, verify the square-root
  stepsize identity by squaring both sides, and discharge the remaining
  positivity and coefficient-parametric inequality checks by ordered-field
  arithmetic.
Source: Mathlib real square-root and ordered-field arithmetic APIs
Used in: stochastic nonconvex conditional-gradient expected-Wolfe-gap bound
  audit for variance-balanced stepsize normalization with retained residual floors
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem exists_counterexample_variance_balanced_stepsize_scalar_compression
    (c : ℝ) :
    ∃ fGap L D α σ m N : ℝ,
      0 < fGap ∧ 0 < L ∧ 0 < D ∧ 0 ≤ σ ∧ 0 < m ∧ 0 < N ∧
      α ≤ 1 ∧
      α = Real.sqrt ((1 / N + σ ^ 2 / (L * m)) / (L * D ^ 2)) ∧
      ¬
        fGap / (N * α) + (7 / 2) * L * D ^ 2 * α +
            σ ^ 2 / (2 * L * m * α) + D * σ / Real.sqrt m ≤
          fGap / Real.sqrt N + 7 * L * D ^ 2 / (2 * Real.sqrt N) +
            c * σ * D / Real.sqrt m := by
  refine ⟨20, 4, 1, 1 / 4, 0, 1, 4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  ·
    have hsqrt : Real.sqrt ((1 : ℝ) / 16) = 1 / 4 := by
      have hsq : (Real.sqrt ((1 : ℝ) / 16)) ^ 2 = (1 / 4 : ℝ) ^ 2 := by
        rw [Real.sq_sqrt]
        · norm_num
        · norm_num
      have hcases := sq_eq_sq_iff_eq_or_eq_neg.mp hsq
      rcases hcases with h | h
      · exact h
      · have hnonneg : 0 ≤ Real.sqrt ((1 : ℝ) / 16) := Real.sqrt_nonneg _
        nlinarith
    norm_num [hsqrt]
  · norm_num



-- Generalization plan (G0):
-- G0.1 naming: exists_counterexample_variance_balanced_stepsize_no_floor_scalar_compression
--   (orig was: exists_counterexample_theorem717_scalar_compression); renamed
--   to remove the theorem-number marker and describe the scalar complexity
--   obstruction: variance-balanced stepsize normalization does not force a
--   compressed no-floor expected-gap RHS.
-- G0.2 typeclass level used:
--   E: none; the proof is purely over real scalar complexity parameters.
--   measure: none; no stochastic process or measure-theoretic structure is used.
--   convexity: none; no feasible-set or convexity hypothesis is used.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional gradient, checking whether the
--      inverse-stepsize initial-gap term can be compressed into a printed
--      expected-Wolfe-gap display after a variance-balanced stepsize choice.
--   2. stochastic Frank-Wolfe and conditional-gradient sliding variants, where
--      constant variance-balanced stepsizes are normalized into final scalar
--      complexity bounds.
-- G0.4 search trace:
--   queries: ["scalar compression counterexample",
--     "positive real parameters alpha formula inequality"]
--   top hits: ["exists_counterexample_l1_floor_corollary_scalar_compression",
--     "exists_counterexample_variance_balanced_stepsize_scalar_compression",
--     "stochastic_l1_floor_absorption_scalar_counterexample",
--     "corollary_7_12_general_with_wellDefined_theorem717_scalar_obstruction",
--     "rawAlphaFormula"]
--   coverage: partial — existing staged counterexamples include an L1 or
--     residual floor on the theorem-side RHS; this declaration removes that
--     floor and makes the compressed coefficient arbitrary.
-- G0.4 not-a-thin-wrapper rationale: the theorem packages a concrete
--   seven-parameter real witness showing a proposed no-floor compression is
--   not a consequence of the variance-balanced stepsize formula.
-- G0.5 structural-content rationale: this is a theorem with an explicit
--   counterexample, a square-root normalization proof, and coefficient-
--   parametric arithmetic closure, not a def or structure.
-- G0.5c thin-wrapper self-detect: clean — body has explicit witness
--   construction, square-root normalization, and arithmetic contradiction.
-- G0.5d minimal-hypothesis check: all already minimal; the statement is
--   coefficient-parametric and existential with no global hypotheses.

/-- A variance-balanced scalar stepsize can fail no-floor compression.

For any proposed scalar coefficient on the variance term, there are positive
scalar complexity parameters satisfying the variance-balanced stepsize formula
with `α ≤ 1` and zero noise for which the theorem-level RHS without an L1 floor
is not bounded by the compressed square-root-horizon RHS.

Layer: Layer1 | Gap: Level 1 (scalar counterexample to no-floor compression)
Proof: choose explicit real parameters with zero variance, verify the
  square-root stepsize identity by squaring both sides, and discharge the
  remaining positivity and coefficient-parametric inequality checks by
  ordered-field arithmetic.
Source: Mathlib real square-root and ordered-field arithmetic APIs
Used in: stochastic nonconvex conditional-gradient expected-Wolfe-gap bound
  audit for variance-balanced stepsize normalization without retained L1 floors
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem exists_counterexample_variance_balanced_stepsize_no_floor_scalar_compression
    (c : ℝ) :
    ∃ fGap L D α σ m N : ℝ,
      0 < fGap ∧ 0 < L ∧ 0 < D ∧ 0 ≤ σ ∧ 0 < m ∧ 0 < N ∧
      α ≤ 1 ∧
      α = Real.sqrt ((1 / N + σ ^ 2 / (L * m)) / (L * D ^ 2)) ∧
      ¬
        fGap / (N * α) + (7 / 2) * L * D ^ 2 * α +
            σ ^ 2 / (2 * L * m * α) ≤
          fGap / Real.sqrt N + 7 * L * D ^ 2 / (2 * Real.sqrt N) +
            c * σ * D / Real.sqrt m := by
  refine ⟨20, 4, 1, 1 / 4, 0, 1, 4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  ·
    have hsqrt : Real.sqrt ((1 : ℝ) / 16) = 1 / 4 := by
      have hsq : (Real.sqrt ((1 : ℝ) / 16)) ^ 2 = (1 / 4 : ℝ) ^ 2 := by
        rw [Real.sq_sqrt]
        · norm_num
        · norm_num
      have hcases := sq_eq_sq_iff_eq_or_eq_neg.mp hsq
      rcases hcases with h | h
      · exact h
      · have hnonneg : 0 ≤ Real.sqrt ((1 : ℝ) / 16) := Real.sqrt_nonneg _
        nlinarith
    norm_num [hsqrt]
  · norm_num

-- Batch 7 promoted from Staging/case4_rate_bound_of_floor_tail_prefactor.lean
-- Generalization plan (G0):
-- concept/name: anchored floor-tail real-power rate finalization with
--   prefactor normalization.
-- generality used: Layer1 real scalar rate algebra only; no carrier type,
--   measure, convexity, smoothness, oracle, filtration, or finite-dimensional
--   assumptions are used.
-- portable call pattern: two-phase and restarted stochastic-optimization rate
--   proofs supply an epoch length `T >= m/2`, an anchored tail index
--   `c <= tail <= s`, a base at least one, and the same prefactor
--   normalization to convert an anchored contraction into the closed-form
--   tail rate while varying only the constants and tail anchor.
-- counterargument checked: not paper-local traceability because the statement
--   combines the recurring exponent-budget comparison with the denominator
--   normalization; not a pure wrapper over `Real.rpow_le_rpow_of_exponent_le`
--   because the prefactor comparison and nonnegativity side conditions are
--   packaged with the exponent step.
-- coverage search: searched project/catalog tokens `rpow_tail`, `prefactor`,
--   `floor_tail`, `case4`, and `rate_bound`; existing staged
--   `rpow_tail_prefactor_le_of_ratio_le` only discards a nonpositive tail
--   factor under a ratio hypothesis, while `real_rpow_le_inv_of_log_div_log_selector`
--   handles logarithmic selector inversion. LeanSearch returned Mathlib
--   `Real.rpow_le_rpow_of_exponent_le` and monotonicity primitives, but no
--   combined anchored-rate prefactor theorem.
-- minimal hypotheses: source natural casts and setup fields were replaced by
--   real parameters; `0 <= m`, `0 < mu`, `0 < L`, `0 < T`, `0 <= D0`,
--   `T >= m/2`, `c <= tail`, and `tail <= s` are exactly the scalar facts used.

/-- An anchored floor-tail real-power prefactor is bounded by the closed-form
tail rate.

If a tail epoch length satisfies `T >= m / 2` and the anchor lies before the
tail threshold, then the anchored exponent `T * (s - c)` dominates the printed
tail exponent `m * (s - tail) / 2`. The same `T >= m / 2` hypothesis normalizes
the finite-epoch prefactor to the closed-form tail denominator.

Layer: Layer1 | Gap: Level 1 (floor-tail real-power rate finalization)
Proof: compare exponents using monotonicity of `Real.rpow` for bases at least
  one, compare the prefactors by clearing positive denominators, then multiply
  the two inequalities with nonnegativity side conditions.
Source: Mathlib real-power monotonicity and ordered-field arithmetic APIs for
  stochastic-optimization complexity rates
Used in: variance-reduced accelerated finite-sum linear-tail rate conversion
  after the floor tail anchor has been selected
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem rpow_anchored_tail_prefactor_le_closed_tail_rate
    {m L mu D0 T s c tail base : ℝ}
    (hbase_ge_one : 1 ≤ base) (hm_nonneg : 0 ≤ m) (hmu_pos : 0 < mu)
    (hL_pos : 0 < L) (hD0_nonneg : 0 ≤ D0) (hT_pos : 0 < T)
    (hT_ge_half_m : m / 2 ≤ T) (hc_le_tail : c ≤ tail) (htail_le_s : tail ≤ s) :
    Real.rpow base (-(T * (s - c))) *
        (D0 * (2 * m * mu / (3 * L * T))) ≤
      Real.rpow base (-(m * (s - tail) / 2)) *
        (D0 / (3 * L / (4 * mu))) := by
  have hbase_pos : 0 < base := lt_of_lt_of_le zero_lt_one hbase_ge_one
  have htail_gap_nonneg : 0 ≤ s - tail := by linarith
  have htail_gap_le_anchor_gap : s - tail ≤ s - c := by linarith
  have hexponent_budget : m * (s - tail) / 2 ≤ T * (s - c) := by
    calc
      m * (s - tail) / 2 = (m / 2) * (s - tail) := by ring
      _ ≤ T * (s - tail) := by
        exact mul_le_mul_of_nonneg_right hT_ge_half_m htail_gap_nonneg
      _ ≤ T * (s - c) := by
        exact mul_le_mul_of_nonneg_left htail_gap_le_anchor_gap (le_of_lt hT_pos)
  have hexponent_le : -(T * (s - c)) ≤ -(m * (s - tail) / 2) := by
    linarith
  have hpower_le :
      Real.rpow base (-(T * (s - c))) ≤
        Real.rpow base (-(m * (s - tail) / 2)) :=
    Real.rpow_le_rpow_of_exponent_le hbase_ge_one hexponent_le
  have hcoef_le :
      2 * m * mu / (3 * L * T) ≤ 4 * mu / (3 * L) := by
    field_simp [ne_of_gt hT_pos, ne_of_gt hL_pos]
    nlinarith [hT_ge_half_m, hmu_pos]
  have hprefactor_le :
      D0 * (2 * m * mu / (3 * L * T)) ≤
        D0 / (3 * L / (4 * mu)) := by
    calc
      D0 * (2 * m * mu / (3 * L * T)) ≤
          D0 * (4 * mu / (3 * L)) := by
        exact mul_le_mul_of_nonneg_left hcoef_le hD0_nonneg
      _ = D0 / (3 * L / (4 * mu)) := by
        field_simp [ne_of_gt hmu_pos, ne_of_gt hL_pos]
  have hleft_prefactor_nonneg :
      0 ≤ D0 * (2 * m * mu / (3 * L * T)) := by
    have hcoef_nonneg :
        0 ≤ 2 * m * mu / (3 * L * T) := by
      positivity
    exact mul_nonneg hD0_nonneg hcoef_nonneg
  have hright_power_nonneg :
      0 ≤ Real.rpow base (-(m * (s - tail) / 2)) :=
    le_of_lt (Real.rpow_pos_of_pos hbase_pos _)
  exact mul_le_mul hpower_le hprefactor_le hleft_prefactor_nonneg hright_power_nonneg

-- Batch 7 promoted from Staging/log_selector_calls_le_const_mul_finite_sum_log_rate.lean
-- Generalization plan (G0):
-- concept/name: logarithmic epoch selector call domination for finite-sum
--   complexity; orig was `finite_sum_log_selector_calls_le_log_rate`, renamed
--   away from the corrected-core proof branch and Eq. (5.4.34) labels.
-- generality used: pure real and natural-number scalar complexity accounting;
--   no carrier type, measure, filtration, convexity, smoothness, oracle, or
--   finite-dimensional hypothesis is used.
-- portable call pattern: SVRG/SAGA/Katyusha-style finite-sum complexity proofs
--   can change the call counter, refresh count `m`, accuracy `epsilon`, gap
--   scale `D0`, and per-epoch multiplier `A` while preserving the conclusion
--   that a base-two logarithmic selector gives a constant multiple of
--   `m * log (D0 / epsilon)`.
-- counterargument checked: this is not paper-local traceability because it
--   combines the reusable ceiling overshoot and logarithmic lower-bound steps
--   with an abstract call-counter envelope; it is not a pure wrapper around one
--   existing Mathlib/SOptLib theorem.
-- coverage search: searched CATALOG.md/SOptLib for `log selector calls`,
--   `finite sum log rate`, and `calls_le`; LeanSearch query
--   "ceil logarithm selector max one bounded by logarithmic rate call count
--   finite sum" returned Mathlib ceiling-log primitives such as
--   `Real.ceil_logb_natCast`, while SOptLib hits
--   `natCast_max_one_ceil_le_add_two`,
--   `one_le_log_one_div_over_log_two_of_pos_le_half`, and
--   `twoPhaseSFOCallBound_bigO_rate` are partial but do not cover this
--   one-phase finite-sum call-domination shape.
-- minimal hypotheses: pointwise call upper and nonnegativity assumptions replace
--   all algorithm setup fields; the only selector-specific assumption is the
--   concrete `max 1 (Nat.ceil (log(D0/epsilon)/log 2))` used in the conclusion.

/-- A base-two logarithmic selector turns a linear epoch-call envelope into a
finite-sum logarithmic rate bound.

If calls through epoch `q` are at most `A * m * q`, then choosing
`q = max 1 ceil(log(D0/epsilon)/log 2)` and `epsilon <= D0/2` makes the call
count bounded by any constant `C` dominating `3A / log 2` times
`m * log(D0/epsilon)`.

Layer: Layer1 | Gap: Level 1 (finite-sum logarithmic selector call domination)
Proof: use the `max 1 ceil` two-unit overshoot bound and the reciprocal
  base-two logarithm lower bound to absorb the additive selector slack into the
  logarithmic rate; finish with ordered-field arithmetic.
Source: Mathlib real logarithm and natural ceiling APIs, plus SOptLib scalar
  ceiling-overshoot complexity lemmas
Used in: variance-reduced accelerated finite-sum gradient call accounting for
  the first logarithmic branch of an expected-accuracy selector
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem log_selector_calls_le_const_mul_finite_sum_log_rate
    (calls : Nat → ℝ) (m D0 epsilon A C : ℝ)
    (hm_nonneg : 0 ≤ m) (hepsilon_pos : 0 < epsilon)
    (hepsilon_le_half : epsilon ≤ D0 / 2)
    (hA_nonneg : 0 ≤ A) (hC_dom : 3 * A / Real.log 2 ≤ C)
    (hcalls_nonneg : ∀ q : Nat, 0 ≤ calls q)
    (hcalls_le : ∀ q : Nat, calls q ≤ A * m * (q : ℝ)) :
    ‖calls (max 1 (Nat.ceil (Real.log (D0 / epsilon) / Real.log 2)))‖ ≤
      C * ‖m * Real.log (D0 / epsilon)‖ := by
  let y : ℝ := Real.log (D0 / epsilon) / Real.log 2
  let q : Nat := max 1 (Nat.ceil y)
  have hlog2_pos : 0 < Real.log 2 :=
    Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hD0_pos : 0 < D0 := by nlinarith
  have hLambda_pos : 0 < epsilon / D0 := div_pos hepsilon_pos hD0_pos
  have hLambda_half : epsilon / D0 ≤ 1 / 2 := by
    rw [div_le_iff₀ hD0_pos]
    nlinarith
  have hrecip : 1 / (epsilon / D0) = D0 / epsilon := by
    field_simp [ne_of_gt hepsilon_pos, ne_of_gt hD0_pos]
  have hy_one : 1 ≤ y := by
    simpa [y, hrecip] using
      one_le_log_one_div_over_log_two_of_pos_le_half
        (epsilon / D0) hLambda_pos hLambda_half
  have hy_nonneg : 0 ≤ y := by linarith
  have hq_le : (q : ℝ) ≤ y + 2 := by
    simpa [q] using natCast_max_one_ceil_le_add_two y hy_nonneg
  have hselector_calls :
      calls q ≤ A * m * (y + 2) := by
    have hAm_nonneg : 0 ≤ A * m := mul_nonneg hA_nonneg hm_nonneg
    exact (hcalls_le q).trans (mul_le_mul_of_nonneg_left hq_le hAm_nonneg)
  have hcalls_norm_le : ‖calls q‖ ≤ A * m * (y + 2) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hcalls_nonneg q)]
    exact hselector_calls
  have hy_add_le : y + 2 ≤ 3 * y := by nlinarith
  have hAm_nonneg : 0 ≤ A * m := mul_nonneg hA_nonneg hm_nonneg
  have hovershoot_rate :
      A * m * (y + 2) ≤ A * m * (3 * y) :=
    mul_le_mul_of_nonneg_left hy_add_le hAm_nonneg
  have hrewrite :
      A * m * (3 * y) =
        (3 * A / Real.log 2) * (m * Real.log (D0 / epsilon)) := by
    dsimp [y]
    field_simp [ne_of_gt hlog2_pos]
  have htwo_le_ratio : (2 : ℝ) ≤ D0 / epsilon := by
    rw [le_div_iff₀ hepsilon_pos]
    nlinarith
  have hratio_gt_one : (1 : ℝ) < D0 / epsilon :=
    lt_of_lt_of_le one_lt_two htwo_le_ratio
  have hlog_ratio_pos : 0 < Real.log (D0 / epsilon) :=
    Real.log_pos hratio_gt_one
  have hrate_nonneg : 0 ≤ m * Real.log (D0 / epsilon) :=
    mul_nonneg hm_nonneg (le_of_lt hlog_ratio_pos)
  have hconstant_absorb :
      (3 * A / Real.log 2) * (m * Real.log (D0 / epsilon)) ≤
        C * (m * Real.log (D0 / epsilon)) :=
    mul_le_mul_of_nonneg_right hC_dom hrate_nonneg
  calc
    ‖calls (max 1 (Nat.ceil (Real.log (D0 / epsilon) / Real.log 2)))‖
        = ‖calls q‖ := by simp [q, y]
    _ ≤ A * m * (y + 2) := hcalls_norm_le
    _ ≤ A * m * (3 * y) := hovershoot_rate
    _ = (3 * A / Real.log 2) * (m * Real.log (D0 / epsilon)) := hrewrite
    _ ≤ C * (m * Real.log (D0 / epsilon)) := hconstant_absorb
    _ = C * ‖m * Real.log (D0 / epsilon)‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg hrate_nonneg]

-- Batch 7 promoted from Staging/sqrt_selector_calls_le_const_mul_finite_sum_sqrt_log_rate.lean
-- Generalization plan (G0):
-- concept/name: square-root epoch selector call domination for finite-sum
--   complexity; orig was `finite_sum_sqrt_selector_calls_le_sqrt_log_rate`,
--   renamed away from corrected-core branch labels and local proof variables.
-- generality used: pure real and natural-number scalar complexity accounting;
--   no carrier type, measure, filtration, convexity, smoothness, oracle, or
--   finite-dimensional hypothesis is used.
-- portable call pattern: SVRG/SAGA/Katyusha-style finite-sum complexity proofs
--   can change the call counter, component scale `m`, accuracy `epsilon`,
--   initial budget `D0`, cutoff epoch, per-epoch multiplier, and overhead
--   constant while preserving domination by the named
--   `sqrt (m * D0 / epsilon) + m * log m` finite-sum rate.
-- counterargument checked: this is not paper-local traceability because it
--   packages the reusable second-branch accounting step combining ceiling
--   overshoot, cutoff-overhead absorption, and square-root normalization; it is
--   not covered by the staged logarithmic selector lemma or the lower-level
--   square-root normalization helper alone.
-- coverage search: searched CATALOG.md/SOptLib/Staging for `sqrt selector`,
--   `finite sum sqrt log rate`, `selector calls`, and the precise
--   `sqrt (m * D0 / epsilon) + m * log m` shape. Relevant partial hits were
--   `log_selector_calls_le_const_mul_finite_sum_log_rate`,
--   `mul_sqrt_const_div_mul_le_sqrt_mul_div`,
--   `natCast_max_one_ceil_le_add_two`, and
--   `SOptLib.smoothFiniteSumGradientEvaluationSqrtLogRate`; LeanSearch for a
--   square-root ceiling selector call bound returned only Mathlib ceiling and
--   square-root primitives, not this finite-sum rate package.
-- minimal hypotheses: pointwise call upper/nonnegativity assumptions replace
--   all algorithm setup fields; `1 <= m` is the natural finite-sum domain
--   condition needed to make `m * log m` nonnegative and absorb cutoff
--   overhead into the rate.

/-- A square-root selector plus cutoff overhead is dominated by the finite-sum
square-root logarithmic rate.

If calls through `cutoff + q` are bounded by a linear epoch envelope, `q`
overshoots the square-root selector by at most two, and the fixed cutoff
overhead is controlled by `Cbase * m`, then the call count is bounded by any
constant `C` dominating `Cbase + 4 * A` times the named finite-sum
`sqrt (m * D0 / epsilon) + m * log m` rate.

Layer: Layer1 | Gap: Level 1 (finite-sum square-root selector call domination)
Proof: split the epoch envelope into cutoff overhead and square-root selector
  terms, normalize `m * sqrt (16 * D0 / (m * epsilon))` to
  `sqrt (m * D0 / epsilon)`, and absorb both terms into the nonnegative
  square-root logarithmic rate.
Source: Mathlib real square-root, logarithm, natural cast, and ordered-field
  arithmetic APIs, plus SOptLib finite-sum complexity rate definitions
Used in: variance-reduced accelerated finite-sum gradient call accounting for
  the high-accuracy square-root selector branch
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem sqrt_selector_calls_le_const_mul_finite_sum_sqrt_log_rate
    (calls : Nat → ℝ) (m D0 epsilon A K Cbase C : ℝ) (cutoff q : Nat)
    (hm_ge_one : 1 ≤ m) (hD0_pos : 0 < D0) (hepsilon_pos : 0 < epsilon)
    (hselector_branch : m < D0 / epsilon)
    (hA_nonneg : 0 ≤ A) (hCbase_nonneg : 0 ≤ Cbase)
    (hcutoff_overhead : A * m * ((cutoff : ℝ) + 2) ≤ K)
    (hK_le_Cbase_m : K ≤ Cbase * m)
    (hC_dom : Cbase + 4 * A ≤ C)
    (hcalls_nonneg : ∀ r : Nat, 0 ≤ calls r)
    (hcalls_le : ∀ r : Nat, calls r ≤ A * m * (r : ℝ))
    (hq_le :
      (q : ℝ) ≤ Real.sqrt (16 * D0 / (m * epsilon)) + 2) :
    ‖calls (cutoff + q)‖ ≤
      C * ‖SOptLib.smoothFiniteSumGradientEvaluationSqrtLogRate m epsilon D0‖ := by
  let rate : ℝ := SOptLib.smoothFiniteSumGradientEvaluationSqrtLogRate m epsilon D0
  have hm_pos : 0 < m := lt_of_lt_of_le zero_lt_one hm_ge_one
  have hlogm_nonneg : 0 ≤ Real.log m := Real.log_nonneg hm_ge_one
  have hsqrt_ge_m : m ≤ Real.sqrt (m * D0 / epsilon) := by
    rw [Real.le_sqrt (le_of_lt hm_pos) (by positivity)]
    have hmul_ratio : m * m ≤ m * (D0 / epsilon) :=
      mul_le_mul_of_nonneg_left (le_of_lt hselector_branch) (le_of_lt hm_pos)
    calc
      m ^ 2 = m * m := by ring
      _ ≤ m * (D0 / epsilon) := hmul_ratio
      _ = m * D0 / epsilon := by ring
  have hrate_ge_m : m ≤ rate := by
    dsimp [rate, SOptLib.smoothFiniteSumGradientEvaluationSqrtLogRate]
    calc
      m ≤ Real.sqrt (m * D0 / epsilon) := hsqrt_ge_m
      _ ≤ Real.sqrt (m * D0 / epsilon) + m * Real.log m := by
        nlinarith [mul_nonneg (le_of_lt hm_pos) hlogm_nonneg]
  have hrate_nonneg : 0 ≤ rate := le_trans (le_of_lt hm_pos) hrate_ge_m
  have hrate_norm_ge_m :
      m ≤ ‖SOptLib.smoothFiniteSumGradientEvaluationSqrtLogRate m epsilon D0‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg hrate_nonneg]
    exact hrate_ge_m
  have hsqrt_rate_le_rate_norm :
      Real.sqrt (m * D0 / epsilon) ≤
        ‖SOptLib.smoothFiniteSumGradientEvaluationSqrtLogRate m epsilon D0‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg hrate_nonneg]
    dsimp [rate, SOptLib.smoothFiniteSumGradientEvaluationSqrtLogRate]
    nlinarith [mul_nonneg (le_of_lt hm_pos) hlogm_nonneg]
  have hsum_le :
      ((cutoff + q : Nat) : ℝ) ≤
        (cutoff : ℝ) + Real.sqrt (16 * D0 / (m * epsilon)) + 2 := by
    have hsum_cast : ((cutoff + q : Nat) : ℝ) = (cutoff : ℝ) + (q : ℝ) := by
      norm_num [Nat.cast_add]
    rw [hsum_cast]
    linarith
  have hcalls_norm_le :
      ‖calls (cutoff + q)‖ ≤ A * m * ((cutoff + q : Nat) : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hcalls_nonneg (cutoff + q))]
    exact hcalls_le (cutoff + q)
  have hsqrt_call :
      A * m * Real.sqrt (16 * D0 / (m * epsilon)) ≤
        4 * A * Real.sqrt (m * D0 / epsilon) := by
    have hbase :
        m * Real.sqrt (16 * D0 / (m * epsilon)) ≤
          4 * Real.sqrt (m * D0 / epsilon) := by
      simpa [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq_eq_abs] using
        (SOptLib.mul_sqrt_const_div_mul_le_sqrt_mul_div
          (m := m) (D := D0) (eps := epsilon) (K := 16)
          hm_pos (le_of_lt hD0_pos) hepsilon_pos (by norm_num))
    have hmul := mul_le_mul_of_nonneg_left hbase hA_nonneg
    nlinarith
  have hcalls_split :
      ‖calls (cutoff + q)‖ ≤ K + 4 * A * Real.sqrt (m * D0 / epsilon) := by
    have hAm_nonneg : 0 ≤ A * m := mul_nonneg hA_nonneg (le_of_lt hm_pos)
    calc
      ‖calls (cutoff + q)‖ ≤ A * m * ((cutoff + q : Nat) : ℝ) := hcalls_norm_le
      _ ≤ A * m * ((cutoff : ℝ) + Real.sqrt (16 * D0 / (m * epsilon)) + 2) :=
        mul_le_mul_of_nonneg_left hsum_le hAm_nonneg
      _ = A * m * ((cutoff : ℝ) + 2) +
            A * m * Real.sqrt (16 * D0 / (m * epsilon)) := by
        ring
      _ ≤ K + 4 * A * Real.sqrt (m * D0 / epsilon) :=
        add_le_add hcutoff_overhead hsqrt_call
  have hK_le_rate :
      K ≤ Cbase * ‖SOptLib.smoothFiniteSumGradientEvaluationSqrtLogRate m epsilon D0‖ := by
    calc
      K ≤ Cbase * m := hK_le_Cbase_m
      _ ≤ Cbase *
          ‖SOptLib.smoothFiniteSumGradientEvaluationSqrtLogRate m epsilon D0‖ :=
        mul_le_mul_of_nonneg_left hrate_norm_ge_m hCbase_nonneg
  have hsqrt_part_le_rate :
      4 * A * Real.sqrt (m * D0 / epsilon) ≤
        (4 * A) *
          ‖SOptLib.smoothFiniteSumGradientEvaluationSqrtLogRate m epsilon D0‖ := by
    exact mul_le_mul_of_nonneg_left hsqrt_rate_le_rate_norm
      (mul_nonneg (by norm_num) hA_nonneg)
  calc
    ‖calls (cutoff + q)‖ ≤ K + 4 * A * Real.sqrt (m * D0 / epsilon) :=
      hcalls_split
    _ ≤ Cbase * ‖SOptLib.smoothFiniteSumGradientEvaluationSqrtLogRate m epsilon D0‖ +
        (4 * A) * ‖SOptLib.smoothFiniteSumGradientEvaluationSqrtLogRate m epsilon D0‖ :=
      add_le_add hK_le_rate hsqrt_part_le_rate
    _ = (Cbase + 4 * A) *
        ‖SOptLib.smoothFiniteSumGradientEvaluationSqrtLogRate m epsilon D0‖ := by
      ring
    _ ≤ C * ‖SOptLib.smoothFiniteSumGradientEvaluationSqrtLogRate m epsilon D0‖ :=
      mul_le_mul_of_nonneg_right hC_dom (norm_nonneg _)

