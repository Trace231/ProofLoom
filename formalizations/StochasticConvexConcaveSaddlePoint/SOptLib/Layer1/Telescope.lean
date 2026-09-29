import Mathlib.Analysis.Convex.Jensen
import Mathlib.Algebra.Order.Floor.Div
import SOptLib.Glue.Algebra
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic
import SOptLib.Glue.Probability
import SOptLib.Model.ConditionalGradient
import SOptLib.Model.Iterates
import SOptLib.Model.Saddle
import SOptLib.Layer1.Proximal
import SOptLib.Model.Objective
-- SOptLib/Layer1/Telescope.lean
import Mathlib.MeasureTheory.Integral.Bochner.Basic


open MeasureTheory

/-- Integrate a pathwise finite-window bound and cancel the mean-zero correction.

If a gap is bounded pointwise by a positive scale times `A + B - C`, the integral
of `B` is bounded by `R`, and the correction `C` has zero integral, then the
expected gap is bounded by the same scale applied to `∫ A + R`.

Layer: Layer1 | Gap: Level 1 (expectation bridge for pathwise window bounds)
Proof: integrate the pathwise inequality, split the Bochner integral over
  addition/subtraction, cancel the zero correction, and scale the variance bound.
Source: Mathlib Bochner integral monotonicity and linearity
Used in: stochastic mirror descent expectation bridge
Book citation: book/PAPER/ALG.json#/stochastic_mirror_descent
Origin algorithm: Lan stochastic mirror descent finite-window summation -/
theorem expectation_bound_of_window_pathwise_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (gap A B C : Ω → ℝ) (baseline W R : ℝ)
    (hgap_int : Integrable gap μ)
    (hA_int : Integrable A μ)
    (hB_int : Integrable B μ)
    (hC_int : Integrable C μ)
    (hW_pos : 0 < W)
    (hpath : ∀ ω, gap ω - baseline ≤ W⁻¹ * (A ω + B ω - C ω))
    (hB_bound : ∫ ω, B ω ∂μ ≤ R)
    (hC_zero : ∫ ω, C ω ∂μ = 0) :
    (∫ ω, gap ω ∂μ) - baseline ≤ W⁻¹ * ((∫ ω, A ω ∂μ) + R) := by
  let centeredGap : Ω → ℝ := fun ω => gap ω - baseline
  have hcentered_int : Integrable centeredGap μ :=
    hgap_int.sub (integrable_const (c := baseline))
  have hWinv_nonneg : 0 ≤ W⁻¹ := inv_nonneg.mpr (le_of_lt hW_pos)
  have hright_int : Integrable (fun ω => W⁻¹ * (A ω + B ω - C ω)) μ :=
    ((hA_int.add hB_int).sub hC_int).const_mul W⁻¹
  have hint :
      ∫ ω, centeredGap ω ∂μ ≤ ∫ ω, W⁻¹ * (A ω + B ω - C ω) ∂μ := by
    exact integral_mono hcentered_int hright_int hpath
  have hright_eq :
      ∫ ω, W⁻¹ * (A ω + B ω - C ω) ∂μ =
        W⁻¹ * ((∫ ω, A ω ∂μ) + (∫ ω, B ω ∂μ) - (∫ ω, C ω ∂μ)) := by
    have hAB_int : Integrable (fun ω => A ω + B ω) μ := by
      simpa [Pi.add_apply] using hA_int.add hB_int
    have hadd :
        ∫ ω, A ω + B ω ∂μ = (∫ ω, A ω ∂μ) + (∫ ω, B ω ∂μ) := by
      simpa [Pi.add_apply] using integral_add hA_int hB_int
    have hsub :
        ∫ ω, A ω + B ω - C ω ∂μ =
          (∫ ω, A ω + B ω ∂μ) - ∫ ω, C ω ∂μ := by
      simpa using integral_sub hAB_int hC_int
    rw [integral_const_mul]
    rw [hsub, hadd]
  have hinside :
      (∫ ω, A ω ∂μ) + (∫ ω, B ω ∂μ) - (∫ ω, C ω ∂μ) ≤
        (∫ ω, A ω ∂μ) + R := by
    rw [hC_zero, sub_zero]
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left hB_bound (∫ ω, A ω ∂μ)
  have hmain :
      ∫ ω, centeredGap ω ∂μ ≤ W⁻¹ * ((∫ ω, A ω ∂μ) + R) :=
    le_trans hint
    (by
      rw [hright_eq]
      exact mul_le_mul_of_nonneg_left hinside hWinv_nonneg)
  have hcentered_eq :
      ∫ ω, centeredGap ω ∂μ = (∫ ω, gap ω ∂μ) - baseline := by
    have hsub := integral_sub hgap_int (integrable_const (c := baseline))
    simpa [centeredGap, integral_const, probReal_univ] using hsub
  simpa [hcentered_eq] using hmain


open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace

/-- Sum one-step gap bounds, telescope the descent term, and drop a nonnegative tail.

If each one-step gap is bounded by a telescoping descent increment plus a variance
term minus a correction term, and the descent increments sum to `initial - terminal`
with `terminal ≥ 0`, then the summed gap is bounded by
`initial + sum variance - sum correction`.

Layer: Layer1 | Gap: Level 1 (finite-window one-step telescope)
Proof: sum the pointwise inequalities, split the finite sums, rewrite by the
  telescope identity, and use nonnegativity of the terminal tail.
Source: Mathlib finite sums over ordered additive groups
Used in: stochastic mirror descent finite-window one-step gap bound
Book citation: book/PAPER/ALG.json#/stochastic_mirror_descent
Origin algorithm: Lan stochastic mirror descent finite-window summation -/
theorem summed_one_step_gap_bound_of_telescope
    {ι : Type*} (s : Finset ι)
    (gap descent variance correction : ι → ℝ) (initial terminal : ℝ)
    (hstep : ∀ i ∈ s, gap i ≤ descent i + variance i - correction i)
    (htelescope : Finset.sum s descent = initial - terminal)
    (hterminal_nonneg : 0 ≤ terminal) :
    Finset.sum s gap ≤ initial + Finset.sum s variance - Finset.sum s correction := by
  classical
  have hsum :
      Finset.sum s gap ≤
        Finset.sum s (fun i => descent i + variance i - correction i) := by
    exact Finset.sum_le_sum hstep
  have hdecomp :
      Finset.sum s (fun i => descent i + variance i - correction i) =
        Finset.sum s descent + Finset.sum s variance - Finset.sum s correction := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  calc
    Finset.sum s gap
        ≤ Finset.sum s (fun i => descent i + variance i - correction i) := hsum
    _ = Finset.sum s descent + Finset.sum s variance - Finset.sum s correction := hdecomp
    _ = (initial - terminal) + Finset.sum s variance - Finset.sum s correction := by
          rw [htelescope]
    _ ≤ initial + Finset.sum s variance - Finset.sum s correction := by
          linarith


open scoped BigOperators

/-- Telescope successive differences over a positive natural-number output window.

The window finset is abstracted by a reindexing identity to the closed natural
interval `[start, stop]`, so the result applies to subtype-indexed algorithm
times without mentioning any algorithm-specific state.

Layer: Layer1 | Gap: Level 1 (positive-time output-window telescope)
Proof: reindex the subtype window to `Finset.Icc`, reduce to the standard
  closed-interval telescope, and simplify the positive-time boundary casts.
Source: Mathlib finite sums over natural intervals
Used in: stochastic mirror descent output-window Bregman telescope
Book citation: book/PAPER/ALG.json#/stochastic_mirror_descent
Origin algorithm: Lan stochastic mirror descent finite-window summation -/
theorem outputWindow_sum_sub_succ
    {α : Type*} [AddCommGroup α]
    (times : Finset {t : ℕ // 1 ≤ t})
    (a : {t : ℕ // 1 ≤ t} → α)
    {start stop : ℕ} (hstart : 1 ≤ start) (hle : start ≤ stop)
    (htimes_sum_eq_Icc :
      ∀ φ : {t : ℕ // 1 ≤ t} → α,
        Finset.sum times φ =
          Finset.sum (Finset.Icc start stop) (fun n =>
            if hn : n ∈ Finset.Icc start stop then
              φ ⟨n, le_trans hstart (Finset.mem_Icc.mp hn).1⟩
            else 0)) :
    Finset.sum times (fun t =>
        a t - a ⟨t.1 + 1, Nat.succ_le_succ (Nat.zero_le t.1)⟩) =
      a ⟨start, hstart⟩ -
        a ⟨stop + 1, Nat.succ_le_succ (Nat.zero_le stop)⟩ := by
  classical
  let A : ℕ → α := fun n =>
    if hn : 1 ≤ n then a ⟨n, hn⟩ else 0
  calc
    Finset.sum times (fun t =>
        a t - a ⟨t.1 + 1, Nat.succ_le_succ (Nat.zero_le t.1)⟩)
        = Finset.sum (Finset.Icc start stop) (fun n =>
            if hn : n ∈ Finset.Icc start stop then
              a ⟨n, le_trans hstart (Finset.mem_Icc.mp hn).1⟩ -
                a ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n)⟩
            else 0) := by
          rw [htimes_sum_eq_Icc]
    _ = Finset.sum (Finset.Icc start stop) (fun n => A n - A (n + 1)) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          rw [dif_pos hn]
          have hn_start : start ≤ n := (Finset.mem_Icc.mp hn).1
          have hn_pos : 1 ≤ n := le_trans hstart hn_start
          have hn_succ_pos : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
          simp [A, hn_pos, hn_succ_pos]
    _ = A start - A (stop + 1) := by
          exact sum_Icc_sub_succ A start stop hle
    _ = a ⟨start, hstart⟩ -
        a ⟨stop + 1, Nat.succ_le_succ (Nat.zero_le stop)⟩ := by
          have hstop_pos : 1 ≤ stop + 1 := Nat.succ_le_succ (Nat.zero_le stop)
          simp [A, hstart, hstop_pos]


open scoped BigOperators

/-- Jensen's inequality for a finite weighted average with an explicit positive
normalizing weight.

Layer: Layer1 | Gap: Level 1 (finite weighted Jensen bridge)
Proof: normalize the weights by `W`, apply `ConvexOn.map_sum_le`, then factor
  the common scalar from the finite sum.
Source: Mathlib finite Jensen inequality, `ConvexOn.map_sum_le`
Used in: stochastic mirror descent weighted-output objective bound
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/output/math
Origin algorithm: Lan stochastic mirror descent finite-window output -/
theorem convexOn_weighted_average_le_weighted_sum
    {ι E : Type*} [AddCommGroup E] [Module ℝ E]
    {X : Set E} {f : E → ℝ}
    (hf : ConvexOn ℝ X f)
    (s : Finset ι) (γ : ι → ℝ) (p : ι → E) (xbar : E) (W : ℝ)
    (hγ_nonneg : ∀ i ∈ s, 0 ≤ γ i)
    (hp_mem : ∀ i ∈ s, p i ∈ X)
    (hW_pos : 0 < W)
    (hW_eq : W = Finset.sum s γ)
    (hxbar : xbar = W⁻¹ • Finset.sum s (fun i => γ i • p i)) :
    f xbar ≤ W⁻¹ * Finset.sum s (fun i => γ i * f (p i)) := by
  classical
  have hW_ne : W ≠ 0 := ne_of_gt hW_pos
  have hweights_sum : Finset.sum s (fun i => W⁻¹ * γ i) = 1 := by
    calc
      Finset.sum s (fun i => W⁻¹ * γ i) =
          W⁻¹ * Finset.sum s γ := by
        rw [Finset.mul_sum]
      _ = W⁻¹ * W := by
        rw [← hW_eq]
      _ = 1 := inv_mul_cancel₀ hW_ne
  have hweights_nonneg : ∀ i ∈ s, 0 ≤ W⁻¹ * γ i := by
    intro i hi
    exact mul_nonneg (inv_nonneg.mpr (le_of_lt hW_pos)) (hγ_nonneg i hi)
  have haverage :
      xbar = Finset.sum s (fun i => (W⁻¹ * γ i) • p i) := by
    calc
      xbar = W⁻¹ • Finset.sum s (fun i => γ i • p i) := hxbar
      _ = Finset.sum s (fun i => (W⁻¹ * γ i) • p i) := by
        simp [Finset.smul_sum, smul_smul]
  have hJ :=
    hf.map_sum_le (t := s) (w := fun i => W⁻¹ * γ i) (p := p)
      hweights_nonneg hweights_sum hp_mem
  rw [← haverage] at hJ
  have hright :
      Finset.sum s (fun i => (W⁻¹ * γ i) • f (p i)) =
        W⁻¹ * Finset.sum s (fun i => γ i * f (p i)) := by
    calc
      Finset.sum s (fun i => (W⁻¹ * γ i) • f (p i)) =
          Finset.sum s (fun i => W⁻¹ * (γ i * f (p i))) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        simp [smul_eq_mul, mul_assoc]
      _ = W⁻¹ * Finset.sum s (fun i => γ i * f (p i)) := by
        rw [Finset.mul_sum]
  rw [hright] at hJ
  exact hJ

/-- Push a scalar baseline inside a normalized finite weighted average bound.

If `value` is bounded by the normalized weighted average of `F`, and the total
weight is the positive scalar `W`, then subtracting a scalar baseline from
`value` is bounded by the same normalized weighted average of the pointwise
gaps `F i - baseline`.

Layer: Layer1 | Gap: Level 0 (finite weighted-average baseline shift)
Proof: rewrite the baseline as `W⁻¹ * (W * baseline)` using `W ≠ 0`, identify
  `W * baseline` with the finite sum of weighted constants, and finish by
  distributing finite sums and ring normalization.
Source: Mathlib Finset sum algebra and linear ordered field APIs
Used in: stochastic mirror descent finite-window bound normalization with a baseline
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem weighted_average_sub_baseline_le_weighted_gap
    {ι : Type*} (s : Finset ι) (γ F : ι → ℝ) (value baseline W : ℝ)
    (hW_pos : 0 < W)
    (hW_eq : Finset.sum s γ = W)
    (hvalue_le : value ≤ W⁻¹ * Finset.sum s (fun i => γ i * F i)) :
    value - baseline ≤
      W⁻¹ * Finset.sum s (fun i => γ i * (F i - baseline)) := by
  classical
  have hW_ne : W ≠ 0 := ne_of_gt hW_pos
  have hsum_const :
      Finset.sum s (fun i => γ i * baseline) = W * baseline := by
    rw [← Finset.sum_mul]
    exact congrArg (fun z => z * baseline) hW_eq
  have hcancel : W⁻¹ * W = 1 := inv_mul_cancel₀ hW_ne
  calc
    value - baseline
        ≤ W⁻¹ * Finset.sum s (fun i => γ i * F i) - baseline := by
          exact sub_le_sub_right hvalue_le baseline
    _ = W⁻¹ * Finset.sum s (fun i => γ i * F i) -
          W⁻¹ * (W * baseline) := by
          rw [← mul_assoc, hcancel, one_mul]
    _ = W⁻¹ *
          (Finset.sum s (fun i => γ i * F i) - W * baseline) := by
          ring
    _ = W⁻¹ *
          (Finset.sum s (fun i => γ i * F i) -
            Finset.sum s (fun i => γ i * baseline)) := by
          rw [hsum_const]
    _ = W⁻¹ * Finset.sum s (fun i => γ i * F i - γ i * baseline) := by
          rw [Finset.sum_sub_distrib]
    _ = W⁻¹ * Finset.sum s (fun i => γ i * (F i - baseline)) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro i _hi
          ring

/-- Compose a pathwise Jensen gap bound with a finite-window summed one-step bound.

If a pathwise gap is bounded by `W⁻¹` times the finite-window sum of one-step
gaps, and that sum is bounded by the initial term plus error minus correction,
then the gap is bounded by the scaled aggregate right-hand side.

Layer: Layer1 | Gap: Level 0 (finite-window Jensen aggregation)
Proof: multiply the summed one-step inequality by the nonnegative scalar `W⁻¹`
  using positivity of `W`, then compose it with the Jensen bound by transitivity
  of `≤`.
Source: Mathlib ordered-ring inequalities and Finset sum APIs
Used in: stochastic mirror descent finite-window pathwise gap bound from Jensen
  aggregation and one-step telescoping
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem window_pathwise_bound_of_jensen_and_summed_one_step
    {Ω ι : Type*} (s : Finset ι)
    (gap : Ω → ℝ) (oneStepGap : ι → Ω → ℝ)
    (initial error correction : Ω → ℝ) (W : ℝ)
    (hW_pos : 0 < W)
    (hjensen :
      ∀ ω : Ω, gap ω ≤ W⁻¹ * Finset.sum s (fun i => oneStepGap i ω))
    (hsummed :
      ∀ ω : Ω,
        Finset.sum s (fun i => oneStepGap i ω) ≤
          initial ω + error ω - correction ω) :
    ∀ ω : Ω, gap ω ≤ W⁻¹ * (initial ω + error ω - correction ω) := by
  intro ω
  have hWinv_nonneg : 0 ≤ W⁻¹ := inv_nonneg.mpr (le_of_lt hW_pos)
  have hscaled :
      W⁻¹ * Finset.sum s (fun i => oneStepGap i ω) ≤
        W⁻¹ * (initial ω + error ω - correction ω) := by
    exact mul_le_mul_of_nonneg_left (hsummed ω) hWinv_nonneg
  exact le_trans (hjensen ω) hscaled

/-- A finite randomized output expectation is its raw weighted sum divided by the denominator.

For any finite output window, raw weights `w`, output scores `A`, and denominator
`W`, summing the normalized contributions `(w i / W) * A i` is the same as
dividing the raw weighted sum by `W`.

Layer: Layer1 | Gap: Level 0 (finite randomized-output weighted-sum normalization)
Proof: factor the common denominator out of the finite sum using
  `Finset.sum_div`, then prove each summand agrees by ordered-ring arithmetic.
Source: Mathlib finite sums and real field division APIs
Used in: nonconvex stochastic mirror descent randomized-output stationarity
  normalization from stopping masses to weighted projected-gradient integrals
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem expectedOutput_eq_weighted_sum_div
    {ι : Type*} (times : Finset ι) (w A : ι → ℝ) (W : ℝ) :
    Finset.sum times (fun i => (w i / W) * A i) =
      (Finset.sum times (fun i => w i * A i)) / W := by
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro i hi
  ring

/-- Integrate a finite telescoping sum and use a pointwise lower bound on the tail.

If a finite family of integrable drops sums pointwise to `initial - terminal`
and `terminal` is bounded below by `lower`, then the sum of the expected drops
is bounded by `initial - lower`.

Layer: Layer1 | Gap: Level 1 (expected finite-sum telescope with terminal lower bound)
Proof: commute the Bochner integral with the finite sum, use the pointwise
  telescope identity and terminal lower bound under `integral_mono`, and evaluate
  the constant integral under a probability measure.
Source: Mathlib Bochner integral finite-sum linearity and integral monotonicity
Used in: nonconvex stochastic mirror descent expected objective-drop telescope
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem integral_sum_telescope_bound_of_pointwise_lower_bound
    {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (times : Finset ι) (drop : ι → Ω → ℝ) (terminal : Ω → ℝ)
    (initial lower : ℝ)
    (hdrop_int : ∀ i ∈ times, Integrable (drop i) P)
    (hpoint : ∀ ω, Finset.sum times (fun i => drop i ω) = initial - terminal ω)
    (hlower : ∀ ω, lower ≤ terminal ω) :
    Finset.sum times (fun i => ∫ ω, drop i ω ∂P) ≤ initial - lower := by
  classical
  have hsum_int :
      Integrable (fun ω => Finset.sum times (fun i => drop i ω)) P := by
    exact integrable_finset_sum times hdrop_int
  have hsum_eq :
      Finset.sum times (fun i => ∫ ω, drop i ω ∂P) =
        ∫ ω, Finset.sum times (fun i => drop i ω) ∂P := by
    rw [integral_finset_sum times hdrop_int]
  have hbound :
      ∫ ω, Finset.sum times (fun i => drop i ω) ∂P ≤
        ∫ _ω, initial - lower ∂P := by
    refine integral_mono hsum_int (integrable_const (c := initial - lower)) ?_
    intro ω
    calc
      Finset.sum times (fun i => drop i ω) = initial - terminal ω := hpoint ω
      _ ≤ initial - lower := sub_le_sub_left (hlower ω) initial
  calc
    Finset.sum times (fun i => ∫ ω, drop i ω ∂P)
        = ∫ ω, Finset.sum times (fun i => drop i ω) ∂P := hsum_eq
    _ ≤ ∫ _ω, initial - lower ∂P := hbound
    _ = initial - lower := by
          simp [integral_const, probReal_univ]

/-- A finite window of zero-mean scalar noise plus nonnegative quadratic noise
weights is bounded by the corresponding weighted quadratic budgets.

For each window index, the linear noise term has zero integral and the
quadratic noise term has integral at most `B k`. After exchanging the finite
sum with the integral, the linear terms cancel and the nonnegative coefficients
`(1 / 2) * η k ^ 2` preserve the per-index bounds.

Layer: Layer1 | Gap: Level 1 (finite-window zero-mean plus quadratic-noise expectation bound)
Proof: commute the Bochner integral with the finite sum, split each affine
  summand by integral linearity, cancel the zero-mean component, and apply
  monotonicity under the nonnegative quadratic coefficient.
Source: Mathlib Bochner integral finite-sum linearity and ordered real arithmetic
Used in: stochastic block mirror descent finite-window martingale-noise cancellation with selected quadratic oracle budget
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic block mirror descent -/
theorem finite_window_zero_mean_plus_quadratic_noise_integral_bound
    {Ω τ : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (times : Finset τ) (η : τ → ℝ)
    (δ δbar : τ → Ω → ℝ) (B : τ → ℝ)
    (hδ_int : ∀ k ∈ times, Integrable (δ k) P)
    (hδbar_int : ∀ k ∈ times, Integrable (δbar k) P)
    (hδ_zero : ∀ k ∈ times, ∫ ω, δ k ω ∂P = 0)
    (hδbar_bound : ∀ k ∈ times, ∫ ω, δbar k ω ∂P ≤ B k) :
    ∫ ω, Finset.sum times (fun k =>
        η k * δ k ω + (1 / 2 : ℝ) * η k ^ 2 * δbar k ω) ∂P ≤
      (1 / 2 : ℝ) * Finset.sum times (fun k => η k ^ 2 * B k) := by
  classical
  let noise : τ → Ω → ℝ := fun k ω =>
    η k * δ k ω + (1 / 2 : ℝ) * η k ^ 2 * δbar k ω
  have hnoise_int : ∀ k ∈ times, Integrable (noise k) P := by
    intro k hk
    exact ((hδ_int k hk).const_mul (η k)).add
      ((hδbar_int k hk).const_mul ((1 / 2 : ℝ) * η k ^ 2))
  calc
    ∫ ω, Finset.sum times (fun k =>
        η k * δ k ω + (1 / 2 : ℝ) * η k ^ 2 * δbar k ω) ∂P
        = Finset.sum times (fun k => ∫ ω, noise k ω ∂P) := by
          rw [integral_finset_sum]
          exact hnoise_int
    _ ≤ Finset.sum times (fun k => (1 / 2 : ℝ) * η k ^ 2 * B k) := by
          refine Finset.sum_le_sum ?_
          intro k hk
          have hcoef_nonneg : 0 ≤ (1 / 2 : ℝ) * η k ^ 2 :=
            mul_nonneg (by norm_num) (sq_nonneg (η k))
          calc
            ∫ ω, noise k ω ∂P =
                η k * (∫ ω, δ k ω ∂P) +
                  ((1 / 2 : ℝ) * η k ^ 2) * (∫ ω, δbar k ω ∂P) := by
                    rw [integral_add ((hδ_int k hk).const_mul (η k))
                      ((hδbar_int k hk).const_mul ((1 / 2 : ℝ) * η k ^ 2))]
                    rw [integral_const_mul, integral_const_mul]
            _ = ((1 / 2 : ℝ) * η k ^ 2) * (∫ ω, δbar k ω ∂P) := by
                    rw [hδ_zero k hk]
                    ring
            _ ≤ (1 / 2 : ℝ) * η k ^ 2 * B k := by
                    simpa [mul_assoc] using
                      mul_le_mul_of_nonneg_left (hδbar_bound k hk) hcoef_nonneg
    _ = (1 / 2 : ℝ) * Finset.sum times (fun k => η k ^ 2 * B k) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _hk
          ring

/-- A positive-time output-window telescope is bounded by its first value when
the terminal value is nonnegative.

For a finite output window reindexed to `[start, stop]`, the sum of successive
drops `a t - a (t + 1)` telescopes to `a start - a (stop + 1)`. A nonnegative
terminal value therefore bounds the whole window by the initial value.

Layer: Layer1 | Gap: Level 1 (positive-time output-window telescope inequality)
Proof: apply the positive-time output-window telescope equality, then use the
  ordered-additive-group fact that subtracting a nonnegative element does not
  increase a value.
Source: Mathlib finite sums over natural intervals and ordered additive groups
Used in: stochastic block mirror descent output-window aggregate-potential telescope
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec/convergence_results
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem outputWindow_sum_sub_succ_le_first_of_last_nonneg
    {α : Type*} [AddCommGroup α] [LE α] [AddLeftMono α]
    (times : Finset {t : ℕ // 1 ≤ t})
    (a : {t : ℕ // 1 ≤ t} → α)
    {start stop : ℕ} (hstart : 1 ≤ start) (hle : start ≤ stop)
    (htimes_sum_eq_Icc :
      ∀ φ : {t : ℕ // 1 ≤ t} → α,
        Finset.sum times φ =
          Finset.sum (Finset.Icc start stop) (fun n =>
            if hn : n ∈ Finset.Icc start stop then
              φ ⟨n, le_trans hstart (Finset.mem_Icc.mp hn).1⟩
            else 0))
    (hterm : 0 ≤ a ⟨stop + 1, Nat.succ_le_succ (Nat.zero_le stop)⟩) :
    Finset.sum times (fun t =>
        a t - a ⟨t.1 + 1, Nat.succ_le_succ (Nat.zero_le t.1)⟩) ≤
      a ⟨start, hstart⟩ := by
  rw [outputWindow_sum_sub_succ times a hstart hle htimes_sum_eq_Icc]
  exact sub_le_self (a ⟨start, hstart⟩) hterm

/-- Bound a convex weighted-output gap by an initial potential plus finite-window noise.

If the output is the weighted average of feasible iterates, each weighted
objective gap is bounded by a potential drop plus a noise term, and the
potential drops telescope to at most the initial potential, then the normalized
output gap is bounded by the initial potential plus the summed noise.

Layer: Layer1 | Gap: Level 1 (weighted-output potential telescope)
Proof: apply finite weighted Jensen, push the baseline into the normalized
  weighted sum, sum the pointwise descent bounds, and dominate the descent
  sum by the telescope hypothesis before scaling by `W⁻¹`.
Source: Mathlib convex finite Jensen inequality and finite-sum ordered-ring APIs
Used in: stochastic block mirror descent weighted-average output gap after
  aggregating one-step mirror descent recursions
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem weighted_output_gap_le_initial_potential_add_noise
    {T E : Type*} [AddCommGroup E] [Module ℝ E]
    {X : Set E} {objective : E → ℝ}
    (hobjective_convex : ConvexOn ℝ X objective)
    (times : Finset T) (weight : T → ℝ) (W : ℝ)
    (xbar xRef : E) (xAt : T → E)
    (index : T → ℕ) (V : ℕ → ℝ) (noise : T → ℝ)
    (hweight_nonneg : ∀ t ∈ times, 0 ≤ weight t)
    (hxAt_mem : ∀ t ∈ times, xAt t ∈ X)
    (hW_pos : 0 < W)
    (hW_eq : W = Finset.sum times weight)
    (hxbar : xbar = W⁻¹ • Finset.sum times (fun t => weight t • xAt t))
    (hpoint :
      ∀ t ∈ times,
        weight t * (objective (xAt t) - objective xRef) ≤
          V (index t) - V (index t + 1) + noise t)
    (htelescope :
      Finset.sum times (fun t => V (index t) - V (index t + 1)) ≤ V 0) :
    objective xbar - objective xRef ≤
      W⁻¹ * (V 0 + Finset.sum times noise) := by
  classical
  have hJ :
      objective xbar ≤ W⁻¹ * Finset.sum times (fun t => weight t * objective (xAt t)) := by
    exact convexOn_weighted_average_le_weighted_sum
      hobjective_convex times weight xAt xbar W
      hweight_nonneg hxAt_mem hW_pos hW_eq hxbar
  have hgapJ :
      objective xbar - objective xRef ≤
        W⁻¹ * Finset.sum times (fun t => weight t * (objective (xAt t) - objective xRef)) := by
    exact weighted_average_sub_baseline_le_weighted_gap times weight
      (fun t => objective (xAt t)) (objective xbar) (objective xRef) W
      hW_pos hW_eq.symm hJ
  have hsum_point :
      Finset.sum times (fun t => weight t * (objective (xAt t) - objective xRef)) ≤
        Finset.sum times (fun t => V (index t) - V (index t + 1) + noise t) := by
    exact Finset.sum_le_sum hpoint
  have hsum_bound :
      Finset.sum times (fun t => weight t * (objective (xAt t) - objective xRef)) ≤
        V 0 + Finset.sum times noise := by
    calc
      Finset.sum times (fun t => weight t * (objective (xAt t) - objective xRef))
          ≤ Finset.sum times (fun t => V (index t) - V (index t + 1) + noise t) :=
            hsum_point
      _ = Finset.sum times (fun t => V (index t) - V (index t + 1)) +
            Finset.sum times noise := by
          rw [Finset.sum_add_distrib]
      _ ≤ V 0 + Finset.sum times noise := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right htelescope (Finset.sum times noise)
  have hscaled :
      W⁻¹ * Finset.sum times (fun t => weight t * (objective (xAt t) - objective xRef)) ≤
        W⁻¹ * (V 0 + Finset.sum times noise) := by
    exact mul_le_mul_of_nonneg_left hsum_bound (inv_nonneg.mpr (le_of_lt hW_pos))
  exact le_trans hgapJ hscaled

-- From Staging/active_partition_sum_mul_const_eq_global_sum.lean

open scoped BigOperators

-- Generalization plan (G0):
-- G0.1 naming: active_partition_sum_mul_const_eq_global_sum (orig was:
--   active_alpha_square_sum_eq_global_theorem716). The name removes the
--   theorem-number and alpha-specific paper vocabulary, and names the
--   finite active-partition constant-multiple transport concept.
-- G0.2 typeclass level used:
--   E: none; the proof is scalar finite-sum algebra.
--   measure: none; no probability or integration appears in the statement.
--   convexity: none; no geometric hypothesis is used.
-- G0.3 reusability — could instantiate:
--   1. finite-sum nonconvex conditional gradient, collecting active epoch
--      curvature terms into one global stepsize-square budget.
--   2. stochastic conditional gradient with recursive minibatches, transporting
--      active epoch variance-floor curvature terms to the global output window.
-- G0.4 search trace:
--   queries: ["active partition sum", "Finset sum reindex multiply constant"]
--   top hits: ["active_sum_scaled_alpha_sq_eq_global",
--     "integrable_const_mul_add_finset_sum_sub_finset_sum",
--     "integrable_finset_sum_const_mul",
--     "sum_positiveTimeOutputWindowTimes_eq_Icc"]
--   coverage: strengthens active_sum_scaled_alpha_sq_eq_global — this theorem
--     allows arbitrary global index type, arbitrary window finset, arbitrary
--     weights, and a single semiring constant instead of Nat/Icc/alpha-square
--     data with the scale split as L * D^2.
-- G0.4 not-a-thin-wrapper rationale: the theorem packages the reusable invariant
--   that a finite active/global partition identity is preserved by uniform
--   left multiplication, including the nested active-coordinate sum shape.
-- G0.5 structural-content rationale: the declaration turns the recurring
--   active-window-to-global-budget transport into a named distributivity lemma without
--   paper-local epochs, stepsizes, or smoothness constants.
-- G0.5b name-body alignment: the theorem name promises a constant-multiple
--   equality for active-partition sums, and the body proves exactly that.
-- G0.5c thin-wrapper self-detect: clean — body has nested finite-sum factoring
--   plus partition substitution, not a direct alias of one Mathlib lemma.
-- G0.5d minimal-hypothesis check: all already minimal; the only hypothesis is
--   the active/global partition equality consumed by the proof.

/-- Uniform left multiplication preserves an active-partition finite-sum identity.

If a nested active-coordinate sum of weights reindexes to a global window sum,
then multiplying each active summand by the same coefficient gives the same
coefficient times the global window sum.

Layer: Layer1 | Gap: Level 0 (active-partition scalar budget reindexing)
Proof: factor the common coefficient through the inner and outer finite sums
  using finite-sum distributivity, then rewrite by the partition identity.
Source: Mathlib finite big-operator distributivity over semirings
Used in: nonconvex stochastic conditional-gradient collection of active epoch
  curvature terms into the global output-window alpha-square budget
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem active_partition_sum_mul_const_eq_global_sum
    {A B K R : Type*} [NonUnitalNonAssocSemiring R]
    (epochs : Finset A) (active : A → Finset B)
    (idx : A → B → K) (window : Finset K) (w : K → R) (c : R)
    (hpartition :
      Finset.sum epochs
          (fun a => Finset.sum (active a) (fun b => w (idx a b))) =
        Finset.sum window w) :
    Finset.sum epochs
        (fun a => Finset.sum (active a) (fun b => c * w (idx a b))) =
      c * Finset.sum window w := by
  calc
    Finset.sum epochs
        (fun a => Finset.sum (active a) (fun b => c * w (idx a b)))
        = Finset.sum epochs
            (fun a => c * Finset.sum (active a) (fun b => w (idx a b))) := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          rw [Finset.mul_sum]
    _ = c *
        Finset.sum epochs
          (fun a => Finset.sum (active a) (fun b => w (idx a b))) := by
          rw [Finset.mul_sum]
    _ = c * Finset.sum window w := by
          rw [hpartition]


-- From Staging/active_sum_objective_drop_add_scalar_budget.lean

open scoped BigOperators

-- Generalization plan (G0):
-- G0.1 naming: active_sum_objective_drop_add_scalar_budget
--   (kept planner name; the concept is an active-window finite-sum assembly of
--   objective-drop and scalar-budget contributions).
-- G0.2 typeclass level used:
--   E: none; objective drops and stochastic error terms have already been
--     reduced to scalar aggregate bounds before this Layer1 assembly step;
--     scalars use `[AddCommGroup R] [Preorder R] [IsOrderedAddMonoid R]`,
--     enough for finite sums, subtraction, and monotone addition.
--   measure: none; expectations enter only through the scalar-valued `Obj`
--     and `Scal` functions and their aggregate bounds.
--   convexity: none; convexity, smoothness, and feasibility are discharged in
--     the one-step and objective-telescope hypotheses supplied to this lemma.
-- G0.3 reusability — could instantiate:
--   1. finite-sum nonconvex conditional gradient, combining active objective
--      drops with the Theorem 7.16 delta-square, curvature, and residual
--      scalar budget after the one-step inequalities are summed.
--   2. stochastic nonconvex conditional gradient or variance-reduced
--      Frank-Wolfe, assembling active expected objective-drop telescopes with
--      separately proved estimator-variance and stepsize scalar budgets.
-- G0.4 search trace:
--   queries: ["active sum objective drop scalar budget",
--     "sum over finset split add telescope lower bound scalar"]
--   top hits: ["finite_active_objective_drop_telescope",
--     "stochastic_active_objective_drop_telescope",
--     "finite_epochDifference_form_scalar_budget_theorem716",
--     "three_term_scalar_budget_le_alpha_square_add_penalty",
--     "integral_sum_telescope_bound_of_pointwise_lower_bound",
--     "summed_one_step_gap_bound_of_telescope",
--     "weighted_gap_sum_bound_of_active_one_step_with_l1_floor"]
--   coverage: partial — hits provide objective telescopes, scalar budgets, or
--     richer weighted-gap aggregators, but none subsumes the two-level
--     active-window split of objective-drop plus scalar terms with independent
--     aggregate bounds `init - lower` and `scalarBound`.
-- G0.4 not-a-thin-wrapper rationale: the theorem adds the reusable invariant
--   that matching active finite sums of objective-drop and scalar terms split
--   exactly and combine two independently proved aggregate budgets.
-- G0.5 structural-content rationale: the statement exposes the common
--   two-level active finite-sum frame and the two budget hypotheses while
--   eliminating paper-local epoch, integral, and estimator notation.
-- G0.5b name-body alignment: the name promises an active objective-drop sum
--   plus scalar-budget bound, and the theorem proves exactly that bound.
-- G0.5c thin-wrapper self-detect: clean — body splits nested sums, rewrites
--   the active objective/scalar decomposition, and combines two independent
--   budget inequalities rather than aliasing one Mathlib or SOptLib lemma.
-- G0.5d minimal-hypothesis check: all already minimal; every hypothesis is an
--   aggregate scalar bound used directly in the final finite-sum assembly.

/-- Active objective-drop and scalar-budget sums combine over the same nested
finite-sum frame.

If the active objective-drop sum is bounded by `init - lower` and the matching
active scalar contribution is bounded by `scalarBound`, then the active sum of
their pointwise sum is bounded by `init - lower + scalarBound`.

Layer: Layer1 | Gap: Level 0 (active objective-drop plus scalar-budget assembly)
Proof: split the nested finite sum over addition, then apply the two aggregate
  budget hypotheses with monotonicity of addition.
Source: Mathlib finite big-operator distributivity and ordered additive-group
  arithmetic
Used in: nonconvex stochastic conditional-gradient active-window assembly after
  objective-drop telescoping and estimator scalar-budget aggregation
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem active_sum_objective_drop_add_scalar_budget
    {Aidx Bidx R : Type*} [AddCommGroup R] [Preorder R] [IsOrderedAddMonoid R]
    (epochs : Finset Aidx) (active : Aidx → Finset Bidx)
    (Obj Scal : Aidx → Bidx → R) (init lower scalarBound : R)
    (hobj :
      Finset.sum epochs (fun s => Finset.sum (active s) (fun j => Obj s j)) ≤
        init - lower)
    (hscalar :
      Finset.sum epochs (fun s => Finset.sum (active s) (fun j => Scal s j)) ≤
        scalarBound) :
    Finset.sum epochs
        (fun s => Finset.sum (active s) (fun j => Obj s j + Scal s j)) ≤
      init - lower + scalarBound := by
  classical
  calc
    Finset.sum epochs
        (fun s => Finset.sum (active s) (fun j => Obj s j + Scal s j))
        =
      Finset.sum epochs (fun s => Finset.sum (active s) (fun j => Obj s j)) +
        Finset.sum epochs (fun s => Finset.sum (active s) (fun j => Scal s j)) := by
          simp only [Finset.sum_add_distrib]
    _ ≤ (init - lower) + scalarBound := add_le_add hobj hscalar


-- From Staging/secondMoment_add_recurrence_le_of_cross_zero.lean

-- Generalization plan (G0):
-- G0.1 naming: second_moment_add_recurrence_le_of_cross_zero
--   (orig was: secondMoment_add_recurrence_le_of_cross_zero)
-- G0.2 typeclass level used:
--   E: [NormedAddCommGroup E] [InnerProductSpace ℝ E]; inner product is used
--      for the Hilbert-space polarization identity, finite dimensionality is not used.
--   measure: arbitrary Measure μ on a measurable space; no probability property is used.
--   convexity: none.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional gradient, epochwise estimator-error recurrence
--   2. finite-sum variance-reduced conditional gradient, recursive estimator-error recurrence
-- G0.4 search trace:
--   queries: ["second moment recurrence", "integral norm add inner"]
--   top hits: ["epochwise_delta_one_step_second_moment_le",
--     "finite_delta_one_step_second_moment_le",
--     "integral_norm_sq_sub_le_integral_norm_sq_of_inner_sub_zero",
--     "integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero",
--     "integrable_inner_of_integrable_sq_norm"]
--   coverage: partial — existing hits provide L2 inner-product integrability,
--     centering contraction, or finite covariance diagonalization, but not the
--     two-term additive second-moment recurrence with an external increment bound.
-- G0.4 not-a-thin-wrapper rationale: the theorem packages recurrence equality,
--   Hilbert-square expansion, cross-term cancellation, L2 integrability, and a
--   separately supplied increment bound into one reusable stochastic recurrence.
-- G0.5 structural-content rationale: no new structure or def is introduced; the
--   theorem exposes the load-bearing invariant used by recursive estimator proofs.
-- G0.5c thin-wrapper self-detect: clean — body has multi-step integral expansion
--   and domination proof, not a direct alias of one existing theorem.
-- G0.5d minimal-hypothesis check: all already minimal; recurrence is a.e.,
--   measurability and square-integrability are only required for the two summands.

open MeasureTheory

/-- A two-term Hilbert-valued error recurrence gives an additive second-moment bound.

If `deltaNext = deltaPrev + inc` almost everywhere, the cross moment
`∫ ⟪deltaPrev, inc⟫` vanishes, and the increment second moment is bounded by
`B`, then the next second moment is integrable and bounded by the previous
second moment plus `B`.

Layer: Layer1 | Gap: Level 1 (Hilbert second-moment additive recurrence)
Proof: prove square-integrability of the updated random vector by a two-term
  norm-square domination, expand `‖deltaPrev + inc‖ ^ 2` by polarization under
  the integral, cancel the cross term, and apply the increment bound.
Source: Mathlib Bochner integral linearity and real Hilbert-space norm-square APIs
Used in: stochastic conditional-gradient recursive estimator-error variance recurrence
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem second_moment_add_recurrence_le_of_cross_zero
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure Ω) (deltaPrev deltaNext inc : Ω → E) (B : ℝ)
    (hprev_meas : AEStronglyMeasurable deltaPrev μ)
    (hinc_meas : AEStronglyMeasurable inc μ)
    (hprev_sq : Integrable (fun ω => ‖deltaPrev ω‖ ^ 2) μ)
    (hinc_sq : Integrable (fun ω => ‖inc ω‖ ^ 2) μ)
    (hrec : Filter.EventuallyEq (ae μ) deltaNext (fun ω => deltaPrev ω + inc ω))
    (hcross :
      MeasureTheory.integral μ (fun ω => inner ℝ (deltaPrev ω) (inc ω)) = 0)
    (hinc_bound : MeasureTheory.integral μ (fun ω => ‖inc ω‖ ^ 2) ≤ B) :
    Integrable (fun ω => ‖deltaNext ω‖ ^ 2) μ ∧
      MeasureTheory.integral μ (fun ω => ‖deltaNext ω‖ ^ 2) ≤
        MeasureTheory.integral μ (fun ω => ‖deltaPrev ω‖ ^ 2) + B := by
  have hsum_sq :
      Integrable (fun ω => ‖deltaPrev ω + inc ω‖ ^ 2) μ := by
    have hsum_meas :
        AEStronglyMeasurable (fun ω => ‖deltaPrev ω + inc ω‖ ^ 2) μ := by
      simpa [pow_two] using
        ((hprev_meas.add hinc_meas).norm.mul
          (hprev_meas.add hinc_meas).norm)
    refine Integrable.mono'
      ((hprev_sq.const_mul 2).add (hinc_sq.const_mul 2))
      hsum_meas ?_
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa using
      SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq
        (deltaPrev ω) (inc ω)
  have hnext_sq :
      Integrable (fun ω => ‖deltaNext ω‖ ^ 2) μ := by
    refine hsum_sq.congr ?_
    filter_upwards [hrec] with ω hω
    rw [hω]
  have hinner_int :
      Integrable (fun ω => inner ℝ (deltaPrev ω) (inc ω)) μ :=
    integrable_inner_of_integrable_sq_norm
      (P := μ) (u := deltaPrev) (v := inc)
      hprev_meas hinc_meas hprev_sq hinc_sq
  have hintegral_expand :
      ∫ ω, ‖deltaNext ω‖ ^ 2 ∂μ =
        ∫ ω, ‖deltaPrev ω‖ ^ 2 ∂μ +
          2 * ∫ ω, inner ℝ (deltaPrev ω) (inc ω) ∂μ +
          ∫ ω, ‖inc ω‖ ^ 2 ∂μ := by
    have h_expand :
        (fun ω => ‖deltaNext ω‖ ^ 2) =ᵐ[μ]
          (fun ω => ‖deltaPrev ω‖ ^ 2 +
            2 * inner ℝ (deltaPrev ω) (inc ω) + ‖inc ω‖ ^ 2) := by
      filter_upwards [hrec] with ω hω
      rw [hω]
      simpa using norm_add_sq_real (deltaPrev ω) (inc ω)
    calc
      ∫ ω, ‖deltaNext ω‖ ^ 2 ∂μ =
          ∫ ω, ‖deltaPrev ω‖ ^ 2 +
            2 * inner ℝ (deltaPrev ω) (inc ω) + ‖inc ω‖ ^ 2 ∂μ := by
            exact integral_congr_ae h_expand
      _ = ∫ ω, (‖deltaPrev ω‖ ^ 2 +
            2 * inner ℝ (deltaPrev ω) (inc ω)) + ‖inc ω‖ ^ 2 ∂μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro ω
            ring
      _ =
          ∫ ω, ‖deltaPrev ω‖ ^ 2 +
            2 * inner ℝ (deltaPrev ω) (inc ω) ∂μ +
            ∫ ω, ‖inc ω‖ ^ 2 ∂μ := by
            exact integral_add (hprev_sq.add (hinner_int.const_mul 2)) hinc_sq
      _ =
          (∫ ω, ‖deltaPrev ω‖ ^ 2 ∂μ +
            ∫ ω, 2 * inner ℝ (deltaPrev ω) (inc ω) ∂μ) +
            ∫ ω, ‖inc ω‖ ^ 2 ∂μ := by
            rw [integral_add hprev_sq (hinner_int.const_mul 2)]
      _ =
          ∫ ω, ‖deltaPrev ω‖ ^ 2 ∂μ +
            2 * ∫ ω, inner ℝ (deltaPrev ω) (inc ω) ∂μ +
            ∫ ω, ‖inc ω‖ ^ 2 ∂μ := by
            rw [integral_const_mul 2]
  constructor
  · exact hnext_sq
  · calc
      ∫ ω, ‖deltaNext ω‖ ^ 2 ∂μ =
          ∫ ω, ‖deltaPrev ω‖ ^ 2 ∂μ + ∫ ω, ‖inc ω‖ ^ 2 ∂μ := by
            rw [hintegral_expand, hcross]
            ring
      _ ≤ ∫ ω, ‖deltaPrev ω‖ ^ 2 ∂μ + B := by
            linarith


-- From Staging/epochwise_secondMoment_bound_of_one_step_recurrence.lean

open MeasureTheory
open scoped BigOperators

-- Generalization plan (G0):
-- G0.1 naming: epoch_second_moment_le_difference_sum_add_const_of_one_step_recurrence
--   (orig was: epochwise_secondMoment_bound_of_one_step_recurrence)
-- G0.2 typeclass level used:
--   E: [NormedAddCommGroup E]; the proof only forms squared norms of residuals
--      and iterate differences. Inner products, scalar multiplication, completeness,
--      and finite dimensionality are not used.
--   measure: arbitrary Measure μ on a measurable space; no probability,
--      independence, or finite-measure normalization is used by the induction.
--   convexity: none; geometric and oracle assumptions enter only through the
--      one-step second-moment recurrence and base refresh bound.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional gradient, recursive estimator variance
--      accumulation with an epoch-refresh mini-batch variance floor
--   2. variance-reduced mirror descent or SARAH/SPIDER-style gradient estimators,
--      carrying a refresh variance floor through within-epoch recurrences
-- G0.4 search trace:
--   queries: ["epochwise second moment recurrence refresh",
--     "integral norm square recursive bound additive constant"]
--   top hits: ["epochwise_delta_one_step_second_moment_le",
--     "second_moment_add_recurrence_le_of_cross_zero",
--     "epoch_recursive_estimator_second_moment_le_difference_sum",
--     "finite_delta_one_step_second_moment_le",
--     "integral_norm_sq_sub_le_integral_norm_sq_of_inner_sub_zero",
--     "integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero",
--     "Subadditive", "Nat.leRec"]
--   coverage: partial — existing hits provide the one-step Hilbert recurrence,
--     mini-batch variance floors, and the no-refresh epoch induction, but none
--     carries an arbitrary additive base constant through the epoch recurrence.
-- G0.4 not-a-thin-wrapper rationale: the theorem strengthens the existing
--   no-refresh epoch induction by exposing the invariant that an additive
--   refresh/base variance term is preserved through the same finite-interval
--   accumulation.
-- G0.5 structural-content rationale: no structure or def is introduced; the
--   theorem packages the load-bearing epoch induction over the named
--   `SOptLib.epochSquaredDifferenceSum` object with an additive base floor.
-- G0.5b name-body alignment: the name promises a second-moment upper bound
--   from a one-step recurrence with a difference-sum plus constant, and the
--   body proves exactly that property.
-- G0.5c thin-wrapper self-detect: clean — body performs Nat induction,
--   prefix-validity transport, finite-sum integral splitting, recurrence
--   application, and additive-constant algebra rather than a direct lemma alias.
-- G0.5d minimal-hypothesis check: all already minimal; validity is pointwise
--   and prefix-closed, integrability is requested only for residuals and
--   difference terms at the indices used by the finite interval split, and the
--   recurrence hypotheses are pointwise in the epoch coordinate.

/-- An epoch second moment recurrence preserves an additive base variance floor.

If the first residual in each valid epoch is bounded by the accumulated squared
iterate-difference sum plus a constant `refresh`, and every later valid
coordinate satisfies a one-step recurrence, then induction gives the same
constant added to the accumulated epoch squared-difference bound.

Layer: Layer1 | Gap: Level 1 (epoch second-moment recurrence with additive floor)
Proof: induct on the epoch-local coordinate. The successor case transports
validity to predecessors, splits the finite-interval integral defining
`epochSquaredDifferenceSum`, applies the one-step recurrence and induction
hypothesis, then closes by ordered-ring arithmetic.
Source: Mathlib natural-number induction, finite interval sums, and Bochner
  integral linearity
Used in: stochastic nonconvex conditional-gradient recursive estimator variance
  accumulation after an epoch-refresh mini-batch variance floor
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem epoch_second_moment_le_difference_sum_add_const_of_one_step_recurrence
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (delta x : ℕ → Ω → E) (index : ℕ → ℕ → ℕ)
    (Valid : ℕ → ℕ → Prop) (T : ℕ) (c refresh : ℝ)
    (hvalid_prefix :
      ∀ {s i j : ℕ}, i ≤ j → Valid s j → Valid s i)
    (hbase :
      ∀ s : ℕ, Valid s 1 →
        ∫ ω, ‖delta (index s 1) ω‖ ^ 2 ∂μ ≤
          c * ∫ ω, SOptLib.epochSquaredDifferenceSum x index s 1 ω ∂μ + refresh)
    (hdelta_sq_int :
      ∀ s j : ℕ, 1 ≤ j → j ≤ T → Valid s j →
        Integrable (fun ω => ‖delta (index s j) ω‖ ^ 2) μ)
    (hdiff_sq_int :
      ∀ s i : ℕ, 2 ≤ i → i ≤ T → Valid s i →
        Integrable
          (fun ω => ‖x (index s i) ω - x (index s (i - 1)) ω‖ ^ 2) μ)
    (hstep :
      ∀ s j : ℕ, 2 ≤ j → j ≤ T → Valid s j →
        Integrable (fun ω => ‖delta (index s (j - 1)) ω‖ ^ 2) μ →
        ∫ ω, ‖delta (index s j) ω‖ ^ 2 ∂μ ≤
          ∫ ω, ‖delta (index s (j - 1)) ω‖ ^ 2 ∂μ +
            c * ∫ ω, ‖x (index s j) ω - x (index s (j - 1)) ω‖ ^ 2 ∂μ)
    (s t : ℕ) (ht : 1 ≤ t) (ht_le : t ≤ T) (hvalid : Valid s t) :
    ∫ ω, ‖delta (index s t) ω‖ ^ 2 ∂μ ≤
      c * ∫ ω, SOptLib.epochSquaredDifferenceSum x index s t ω ∂μ + refresh := by
  induction t with
  | zero =>
      omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        exact hbase s hvalid
      · have hn_pos : 1 ≤ n := by omega
        have hj2 : 2 ≤ n + 1 := by omega
        have hn_le_t : n ≤ n + 1 := by omega
        have hn_le_T : n ≤ T := by omega
        have hprev_valid : Valid s n :=
          hvalid_prefix hn_le_t hvalid
        have hprev_bound :
            ∫ ω, ‖delta (index s n) ω‖ ^ 2 ∂μ ≤
              c * ∫ ω, SOptLib.epochSquaredDifferenceSum x index s n ω ∂μ + refresh :=
          ih hn_pos hn_le_T hprev_valid
        have hprev_sq :
            Integrable (fun ω => ‖delta (index s n) ω‖ ^ 2) μ :=
          hdelta_sq_int s n hn_pos hn_le_T hprev_valid
        have hsum_n_int :
            Integrable (SOptLib.epochSquaredDifferenceSum x index s n) μ := by
          unfold SOptLib.epochSquaredDifferenceSum
          exact MeasureTheory.integrable_finset_sum
            (s := Finset.Icc 2 n)
            (fun i hi =>
              hdiff_sq_int s i
                (by
                  exact (Finset.mem_Icc.mp hi).1)
                (by
                  have hi_le : i ≤ n := (Finset.mem_Icc.mp hi).2
                  omega)
                (hvalid_prefix
                  (by
                    have hi_le : i ≤ n := (Finset.mem_Icc.mp hi).2
                    omega)
                  hvalid))
        have hdiff_int :
            Integrable
              (fun ω =>
                ‖x (index s (n + 1)) ω - x (index s n) ω‖ ^ 2) μ := by
          simpa using hdiff_sq_int s (n + 1) hj2 ht_le hvalid
        have hsum_succ :
            ∫ ω, SOptLib.epochSquaredDifferenceSum x index s (n + 1) ω ∂μ =
              ∫ ω, SOptLib.epochSquaredDifferenceSum x index s n ω ∂μ +
                ∫ ω,
                  ‖x (index s (n + 1)) ω - x (index s n) ω‖ ^ 2 ∂μ := by
          let f : ℕ → Ω → ℝ := fun i ω =>
            ‖x (index s i) ω - x (index s (i - 1)) ω‖ ^ 2
          calc
            ∫ ω, SOptLib.epochSquaredDifferenceSum x index s (n + 1) ω ∂μ =
                ∫ ω, Finset.sum (Finset.Icc 2 (n + 1)) (fun i => f i ω) ∂μ := by
                  rfl
            _ = ∫ ω, (Finset.sum (Finset.Icc 2 n) (fun i => f i ω) + f (n + 1) ω)
                  ∂μ := by
                  refine integral_congr_ae (Filter.Eventually.of_forall ?_)
                  intro ω
                  simpa using
                    (Finset.sum_Icc_succ_top (by omega : 2 ≤ n + 1)
                      (fun i => f i ω))
            _ = ∫ ω, Finset.sum (Finset.Icc 2 n) (fun i => f i ω) ∂μ +
                  ∫ ω, f (n + 1) ω ∂μ := by
                  exact integral_add hsum_n_int hdiff_int
            _ = ∫ ω, SOptLib.epochSquaredDifferenceSum x index s n ω ∂μ +
                  ∫ ω,
                    ‖x (index s (n + 1)) ω - x (index s n) ω‖ ^ 2 ∂μ := by
                  rfl
        calc
          ∫ ω, ‖delta (index s (n + 1)) ω‖ ^ 2 ∂μ ≤
              ∫ ω, ‖delta (index s n) ω‖ ^ 2 ∂μ +
                c * ∫ ω,
                  ‖x (index s (n + 1)) ω - x (index s n) ω‖ ^ 2 ∂μ :=
            hstep s (n + 1) hj2 ht_le hvalid hprev_sq
          _ ≤
              (c * ∫ ω, SOptLib.epochSquaredDifferenceSum x index s n ω ∂μ + refresh) +
                c * ∫ ω,
                  ‖x (index s (n + 1)) ω - x (index s n) ω‖ ^ 2 ∂μ := by
              linarith [hprev_bound]
          _ =
              c * ∫ ω, SOptLib.epochSquaredDifferenceSum x index s (n + 1) ω ∂μ +
                refresh := by
              rw [hsum_succ]
              ring


-- From Staging/deltaSquare_scaled_le_epoch_alpha_square_budget.lean

-- Generalization plan (G0):
-- G0.1 naming: delta_square_scaled_le_epoch_alpha_square_budget
--   (orig was: deltaSquare_scaled_le_epoch_alpha_square_budget)
-- G0.2 typeclass level used:
--   E: none; the vector-valued estimator residual and iterate-difference
--     bounds have already been reduced to scalar real second-moment budgets.
--   measure: none; integration is consumed by the input scalar inequalities.
--   convexity: none; no convexity or smoothness structure is used beyond the
--     positive scalar smoothness parameter `L`.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional gradient, scaling a recursive
--      estimator delta-square bound into an epoch alpha-square budget.
--   2. variance-reduced Frank-Wolfe or proximal-gradient inner-loop analyses,
--      transporting estimator residual second moments through drift budgets.
-- G0.4 search trace:
--   queries: ["delta square scaled epoch budget",
--     "real scalar inequality multiply divide positive",
--     "delta second moment epoch budget bound"]
--   top hits: ["one_step_gap_bound_with_epoch_budget_of_delta_second_moment",
--     "residual_second_moment_sum_le_half_alpha_square_budget",
--     "epoch_recursive_estimator_second_moment_le_difference_sum",
--     "finite_active_delta_second_moment_le",
--     "dualNorm_mean_sq_le_second_moment_bound"]
--   coverage: partial — `one_step_gap_bound_with_epoch_budget_of_delta_second_moment`
--     substitutes a scaled delta term inside a base one-step gap inequality,
--     while this theorem directly composes the delta-to-epoch and
--     epoch-to-alpha-square scalar budgets after the `1 / (2L)` scaling.
-- G0.4 not-a-thin-wrapper rationale: the theorem packages the reusable
--   two-stage scalar transport from a delta second-moment estimate through an
--   epoch drift estimate into a final alpha-square budget with normalized
--   smoothness and batch coefficients.
-- G0.5 structural-content rationale: the statement exposes only the six
--   real scalar quantities and the two budget inequalities needed after all
--   algorithmic, Hilbert-space, and measure-theoretic work is discharged.
-- G0.5b name-body alignment: the name promises a theorem bounding a scaled
--   delta-square quantity by an epoch alpha-square budget, and the body proves
--   exactly that property.
-- G0.5c thin-wrapper self-detect: clean — body combines monotone scaling,
--   positive coefficient transport, field normalization, and a second budget
--   inequality rather than calling a single existing lemma.
-- G0.5d minimal-hypothesis check: all already minimal; `0 < L` supports the
--   reciprocal scaling and field normalization, and `0 < b` supports both the
--   nonnegative epoch-budget coefficient and division by the batch scalar.

/-- Scale a delta-square budget through an epoch drift budget into an alpha-square budget.

If `deltaSq` is bounded by `(L ^ 2 / b) * epochBudget` and `epochBudget` is
bounded by `D ^ 2 * alphaSqSum`, then multiplying the delta bound by
`1 / (2L)` normalizes the coefficient to `L / (2b)` and yields the final
alpha-square budget.

Layer: Layer1 | Gap: Level 1 (scalar residual-to-epoch budget transport)
Proof: scale the delta-square estimate by the nonnegative `1 / (2L)`,
  normalize the coefficient by ordered-field arithmetic, then scale the
  epoch-budget estimate by the nonnegative `L / (2b)` and compose.
Source: Mathlib ordered-field arithmetic and monotone multiplication APIs over `ℝ`
Used in: stochastic nonconvex conditional-gradient recursive estimator
  delta-square contribution after replacing epoch drift by stepsize-square mass
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem delta_square_scaled_le_epoch_alpha_square_budget
    (deltaSq epochBudget alphaSqSum L b D : ℝ)
    (hdelta : deltaSq ≤ (L ^ 2 / b) * epochBudget)
    (hepoch : epochBudget ≤ D ^ 2 * alphaSqSum)
    (hL_pos : 0 < L)
    (hb_pos : 0 < b) :
    (1 / (2 * L)) * deltaSq ≤
      (L / (2 * b)) * D ^ 2 * alphaSqSum := by
  have hcoef₁ : 0 ≤ (1 / (2 * L) : ℝ) := by
    have hden : 0 < 2 * L := by nlinarith
    exact div_nonneg zero_le_one (le_of_lt hden)
  have hb_ne : b ≠ 0 := ne_of_gt hb_pos
  have hL_ne : L ≠ 0 := ne_of_gt hL_pos
  have hscaled₁ :
      (1 / (2 * L)) * deltaSq ≤
        (L / (2 * b)) * epochBudget := by
    have hmul := mul_le_mul_of_nonneg_left hdelta hcoef₁
    calc
      (1 / (2 * L)) * deltaSq
          ≤ (1 / (2 * L)) * ((L ^ 2 / b) * epochBudget) := hmul
      _ = (L / (2 * b)) * epochBudget := by
          field_simp [hL_ne, hb_ne]
  have hcoef₂ : 0 ≤ (L / (2 * b) : ℝ) := by
    have hden : 0 < 2 * b := by nlinarith
    exact div_nonneg (le_of_lt hL_pos) (le_of_lt hden)
  have hscaled₂ :
      (L / (2 * b)) * epochBudget ≤
        (L / (2 * b)) * (D ^ 2 * alphaSqSum) :=
    mul_le_mul_of_nonneg_left hepoch hcoef₂
  calc
    (1 / (2 * L)) * deltaSq
        ≤ (L / (2 * b)) * epochBudget := hscaled₁
    _ ≤ (L / (2 * b)) * (D ^ 2 * alphaSqSum) := hscaled₂
    _ = (L / (2 * b)) * D ^ 2 * alphaSqSum := by
        ring


-- From Staging/integral_epochDiffSum_le_diameter_sq_mul_alpha_sq_sum.lean

open MeasureTheory
open scoped BigOperators

-- Generalization plan (G0):
-- G0.1 naming: integral_epochSquaredDifferenceSum_le_diameter_sq_mul_alpha_sq_sum
--   (orig was: integral_epochDiffSum_le_diameter_sq_mul_alpha_sq_sum). The
--   name refers to the standard epoch squared-difference accumulation and its
--   alpha-square diameter budget, with no paper theorem or algorithm marker.
-- G0.2 typeclass level used:
--   E: [NormedAddCommGroup E]; the proof only forms differences, norms, and
--      real squares of norms, with no scalar multiplication, inner products,
--      completeness, or finite-dimensional structure.
--   measure: arbitrary probability measure `(mu : Measure Omega)` via
--      [IsProbabilityMeasure mu], because the proof evaluates the integral of
--      each constant pointwise budget as the budget itself.
--   convexity: none; the result is a finite-sum expectation majorization.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional gradient within-epoch iterate-drift
--      expectation budgets from per-step diameter bounds.
--   2. variance-reduced mirror descent epochwise estimator-drift controls where
--      successive iterate differences are bounded by step sizes and a diameter.
-- G0.4 search trace:
--   queries: ["integral finite sum bound",
--     "integral epoch difference alpha square sum",
--     "epochSquaredDifferenceSum integral pointwise bound"]
--   top hits: ["finite_window_zero_mean_plus_quadratic_noise_integral_bound",
--     "integral_sum_telescope_bound_of_pointwise_lower_bound",
--     "finite_active_epochDiff_integral_le_scalar_sum",
--     "stochastic_active_epochDiff_integral_le_scalar_sum",
--     "SOptLib.epochSquaredDifferenceSum",
--     "SOptLib.epochSquaredDifferenceSum_def"]
--   coverage: partial — existing SOptLib telescope lemmas handle terminal
--     lower-bound and zero-mean-noise windows, while `epochSquaredDifferenceSum`
--     names the summand formula but does not integrate it or convert per-step
--     pointwise diameter bounds into the scalar alpha-square budget.
-- G0.4 not-a-thin-wrapper rationale: the theorem packages the reusable
--   quantifier structure that turns pointwise per-increment diameter bounds into
--   an expected finite-window quadratic-drift budget through integral
--   commutation, monotonicity, probability normalization, and scalar factoring.
-- G0.5 structural-content rationale: no new def or structure is introduced;
--   the theorem adds a reusable Layer1 bridge over the existing
--   `epochSquaredDifferenceSum` Model object.
-- G0.5c thin-wrapper self-detect: clean — body combines finite-sum Bochner
--   linearity, integral monotonicity against constant budgets, finite-sum order,
--   and real algebra, not a direct single-lemma alias.
-- G0.5d minimal-hypothesis check: all already minimal; integrability and the
--   pointwise bound are only required on the finite epoch interval, and the
--   probability typeclass is exactly the constant-integral normalization used.

/-- The integral of an epoch squared-difference sum is bounded by a diameter
square times the corresponding sum of predecessor step-size squares.

For an indexed path, if every successive squared increment inside an epoch is
integrable and pointwise bounded by `alpha (alphaIndex i)^2 * D^2`, then the
expectation of the accumulated epoch squared differences is at most
`D^2 * sum alpha^2`.

Layer: Layer1 | Gap: Level 1 (epoch squared-difference expectation budget)
Proof: commute the Bochner integral with the finite closed-interval sum, apply
  integral monotonicity to each pointwise constant budget on a probability
  measure, sum the inequalities, and factor the common diameter square.
Source: Mathlib Bochner finite-sum integral linearity, probability constant
  integrals, and finite-sum order algebra
Used in: stochastic nonconvex conditional-gradient within-epoch iterate-drift
  budget for estimator second-moment accumulation
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem integral_epochSquaredDifferenceSum_le_diameter_sq_mul_alpha_sq_sum
    {Omega E : Type*} [MeasurableSpace Omega] [NormedAddCommGroup E]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (x : Nat -> Omega -> E) (index : Nat -> Nat -> Nat)
    (s t : Nat) (alphaIndex : Nat -> Nat) (alpha : Nat -> Real) (D : Real)
    (hterm_int :
      forall i, i ∈ Finset.Icc 2 t ->
        Integrable
          (fun omega =>
            ‖x (index s i) omega - x (index s (i - 1)) omega‖ ^ 2) mu)
    (hpoint :
      forall i, i ∈ Finset.Icc 2 t -> forall omega,
        ‖x (index s i) omega - x (index s (i - 1)) omega‖ ^ 2 <=
          alpha (alphaIndex i) ^ 2 * D ^ 2) :
    ∫ omega, SOptLib.epochSquaredDifferenceSum x index s t omega ∂mu <=
      D ^ 2 * Finset.sum (Finset.Icc 2 t)
        (fun i => alpha (alphaIndex i) ^ 2) := by
  classical
  let term : Nat -> Omega -> Real := fun i omega =>
    ‖x (index s i) omega - x (index s (i - 1)) omega‖ ^ 2
  have hterm_int' :
      forall i, i ∈ Finset.Icc 2 t -> Integrable (term i) mu := by
    intro i hi
    simpa [term] using hterm_int i hi
  have hterm_bound :
      forall i, i ∈ Finset.Icc 2 t ->
        ∫ omega, term i omega ∂mu <= alpha (alphaIndex i) ^ 2 * D ^ 2 := by
    intro i hi
    have hconst_int :
        Integrable (fun _omega : Omega => alpha (alphaIndex i) ^ 2 * D ^ 2) mu :=
      integrable_const _
    have hle_int :
        ∫ omega, term i omega ∂mu <=
          ∫ _omega, alpha (alphaIndex i) ^ 2 * D ^ 2 ∂mu := by
      exact integral_mono (hterm_int' i hi) hconst_int (by
        intro omega
        exact hpoint i hi omega)
    simpa [integral_const, probReal_univ] using hle_int
  calc
    ∫ omega, SOptLib.epochSquaredDifferenceSum x index s t omega ∂mu
        = ∫ omega, Finset.sum (Finset.Icc 2 t) (fun i => term i omega) ∂mu := by
          simp [SOptLib.epochSquaredDifferenceSum_def, term]
    _ = Finset.sum (Finset.Icc 2 t) (fun i => ∫ omega, term i omega ∂mu) := by
          exact integral_finset_sum (s := Finset.Icc 2 t) (f := term) hterm_int'
    _ <= Finset.sum (Finset.Icc 2 t)
          (fun i => alpha (alphaIndex i) ^ 2 * D ^ 2) := by
          exact Finset.sum_le_sum hterm_bound
    _ = (Finset.sum (Finset.Icc 2 t)
          (fun i => alpha (alphaIndex i) ^ 2)) * D ^ 2 := by
          rw [Finset.sum_mul]
    _ = D ^ 2 * Finset.sum (Finset.Icc 2 t)
          (fun i => alpha (alphaIndex i) ^ 2) := by
          ring


-- From Staging/integral_oneStepGap_sourceForm_of_pointwise.lean

open MeasureTheory

-- Generalization plan (G0):
-- G0.1 naming: integral_one_step_gap_source_form_of_pointwise (orig was: integral_oneStepGap_sourceForm_of_pointwise)
-- G0.2 typeclass level used:
--   E: none; the lemma is scalar-valued after the algorithm has reduced norms and gaps to `ℝ`.
--   measure: arbitrary `Measure Ω` with `[IsProbabilityMeasure P]`, used only to integrate constants as themselves.
--   convexity: none; all convex/smooth facts enter through the pointwise one-step bound.
-- G0.3 reusability — could instantiate:
--   1. stochastic conditional-gradient one-step Wolfe-gap expectation bridge
--   2. stochastic mirror-descent or proximal-gradient one-step descent after estimator-error terms are exposed
-- G0.4 search trace:
--   queries: ["integral one step gap", "integral pointwise affine constant norm square"]
--   top hits: ["SOptLib.Glue.Probability.integral_le_integral_affine_combination", "SOptLib.Layer1.Telescope.expectation_bound_of_window_pathwise_bound", "SOptLib.Layer1.Telescope.integral_sum_telescope_bound_of_pointwise_lower_bound", "MeasureTheory.integral_mono", "MeasureTheory.integral_mono_ae"]
--   coverage: partial — overlaps in integral monotonicity/linearity but no hit subsumes the four-term source-form split with a probability-space constant.
-- G0.4 not-a-thin-wrapper rationale: packages integral monotonicity with a reusable four-term expectation expansion carrying a constant, square term, and norm term in the source-form shape.
-- G0.5 structural-content rationale: the theorem exposes the invariant that a pathwise one-step source bound preserves its algebraic decomposition after expectation.
-- G0.5c thin-wrapper self-detect: clean — body has multi-step new content combining monotonicity, integrability assembly, and integral expansion.
-- G0.5d minimal-hypothesis check: all already minimal; only integrability of the four scalar functions and a pointwise inequality are required.

/-- Integrate a pointwise one-step gap source-form bound and split its terms.

If a scaled gap is pointwise bounded by an objective drop, a scaled square
error, a deterministic constant, and a scaled norm error, then the same
source-form inequality holds after taking expectation under a probability
measure.

Layer: Layer1 | Gap: Level 1 (one-step source-form expectation bridge)
Proof: assemble integrability of the four-term upper bound, apply Bochner
  integral monotonicity, and split the upper integral using additivity,
  constant-scalar pull-out, and probability-space constant integration.
Source: Mathlib Bochner integral monotonicity and linearity APIs
Used in: stochastic conditional-gradient one-step Wolfe-gap expectation bridge
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem integral_one_step_gap_source_form_of_pointwise
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (gap drop sq norm_term : Ω → ℝ)
    (alpha sq_coeff c_sq c_norm : ℝ)
    (hgap_int : Integrable gap P)
    (hdrop_int : Integrable drop P)
    (hsq_int : Integrable sq P)
    (hnorm_int : Integrable norm_term P)
    (hpoint :
      ∀ ω,
        alpha * gap ω ≤
          ((drop ω + sq_coeff * sq ω) + c_sq) + c_norm * norm_term ω) :
    alpha * ∫ ω, gap ω ∂P ≤
      ((∫ ω, drop ω ∂P) + sq_coeff * ∫ ω, sq ω ∂P) + c_sq +
        c_norm * ∫ ω, norm_term ω ∂P := by
  let upper : Ω → ℝ := fun ω =>
    ((drop ω + sq_coeff * sq ω) + c_sq) + c_norm * norm_term ω
  have hleft_int : Integrable (fun ω => alpha * gap ω) P :=
    hgap_int.const_mul alpha
  have hdrop_sq_int : Integrable (fun ω => drop ω + sq_coeff * sq ω) P :=
    hdrop_int.add (hsq_int.const_mul sq_coeff)
  have hupper_int : Integrable upper P :=
    (hdrop_sq_int.add (integrable_const (c := c_sq))).add
      (hnorm_int.const_mul c_norm)
  have hmono :
      ∫ ω, alpha * gap ω ∂P ≤ ∫ ω, upper ω ∂P := by
    exact integral_mono hleft_int hupper_int hpoint
  have hupper_eq :
      ∫ ω, upper ω ∂P =
        ((∫ ω, drop ω ∂P) + sq_coeff * ∫ ω, sq ω ∂P) + c_sq +
          c_norm * ∫ ω, norm_term ω ∂P := by
    calc
      ∫ ω, upper ω ∂P
          =
          ∫ ω, (drop ω + sq_coeff * sq ω) + c_sq ∂P +
            ∫ ω, c_norm * norm_term ω ∂P := by
            exact integral_add
              (hdrop_sq_int.add (integrable_const (c := c_sq)))
              (hnorm_int.const_mul c_norm)
      _ =
          (∫ ω, drop ω + sq_coeff * sq ω ∂P + ∫ _ω, c_sq ∂P) +
            c_norm * ∫ ω, norm_term ω ∂P := by
            rw [integral_add hdrop_sq_int (integrable_const (c := c_sq))]
            rw [integral_const_mul]
      _ =
          ((∫ ω, drop ω ∂P) + sq_coeff * ∫ ω, sq ω ∂P) + c_sq +
            c_norm * ∫ ω, norm_term ω ∂P := by
            rw [integral_add hdrop_int (hsq_int.const_mul sq_coeff)]
            rw [integral_const_mul]
            simp [integral_const, probReal_univ, add_assoc]
  calc
    alpha * ∫ ω, gap ω ∂P
        = ∫ ω, alpha * gap ω ∂P := by
          rw [integral_const_mul]
    _ ≤ ∫ ω, upper ω ∂P := hmono
    _ =
      ((∫ ω, drop ω ∂P) + sq_coeff * ∫ ω, sq ω ∂P) + c_sq +
        c_norm * ∫ ω, norm_term ω ∂P := hupper_eq


-- From Staging/three_term_scalar_budget_le_alpha_square_add_penalty.lean

open scoped BigOperators

-- Generalization plan (G0):
-- G0.1 naming: three_term_scalar_budget_le_alpha_square_add_penalty
-- G0.2 typeclass level used:
--   E: none; the proof is scalar finite-sum algebra after all norm,
--     expectation, and update estimates have been discharged.
--   measure: none; expectation terms enter only through real-valued bounds on
--     the three scalar contributions.
--   convexity: none; no objective or feasible-set geometry is used.
-- G0.3 reusability — could instantiate:
--   1. finite-sum nonconvex conditional gradient, combining delta-square,
--      curvature, and L1 residual budgets in the Theorem 7.16 scalar step.
--   2. stochastic nonconvex conditional gradient, combining epoch-difference,
--      variance-floor, curvature, and estimator-residual contributions after
--      the one-step Wolfe-gap inequalities have been summed.
-- G0.4 search trace:
--   queries: ["three term scalar budget", "finite sum inequality alpha square penalty"]
--   top hits: ["finite_epochDifference_form_scalar_budget_theorem716",
--     "finite_source_form_scalar_budget_theorem716",
--     "active_delta_square_sum_le_half_alpha_square_budget",
--     "residual_second_moment_sum_le_half_alpha_square_budget",
--     "active_delta_l1_sum_le_epoch_difference_penalty",
--     "active_sum_scaled_alpha_sq_eq_global"]
--   coverage: partial — hits supply the target private theorem or separate
--     delta-square, alpha-square reindexing, and penalty fragments, but none
--     packages the reusable three-contribution finite-sum aggregation into
--     the `3 / 2` alpha-square plus penalty scalar budget.
-- G0.4 not-a-thin-wrapper rationale: the theorem adds the reusable invariant
--   that half-budget, full-budget, and penalty contributions over matching
--   nested active finite sums aggregate to the standard `3 / 2` budget form.
-- G0.5 structural-content rationale: the declaration exposes only the common
--   two-level finite-sum frame and scalar budget hypotheses, eliminating all
--   paper-local epoch, estimator, and maximum notation from the assembly step.
-- G0.5b name-body alignment: the theorem name promises a three-term scalar
--   budget bound by an alpha-square budget plus a penalty, and the statement
--   proves exactly that for nested finite sums.
-- G0.5c thin-wrapper self-detect: clean — body splits nested sums, combines
--   three independent budget hypotheses, and normalizes the `1 / 2 + 1`
--   coefficient rather than aliasing one Mathlib or SOptLib lemma.
-- G0.5d minimal-hypothesis check: all already minimal; each hypothesis is a
--   scalar bound on exactly one contribution, and no global analytic property
--   is assumed.

/-- Three nested scalar contributions combine into a `3 / 2` alpha-square
budget plus a penalty.

If one contribution is bounded by half of the global alpha-square mass, a
second by the full alpha-square mass, and a third by a penalty, all with the
same smoothness-diameter scale, then their pointwise sum over the same active
finite-sum frame is bounded by the scaled `3 / 2` alpha-square budget plus
the scaled penalty.

Layer: Layer1 | Gap: Level 0 (three-term scalar budget aggregation)
Proof: split the nested finite sum over addition, apply the three scalar
  contribution bounds, and normalize the `1 / 2 + 1` coefficient by ordered
  field arithmetic.
Source: Mathlib finite big-operator distributivity and ordered-field
  arithmetic
Used in: nonconvex stochastic conditional-gradient assembly of delta-square,
  curvature, and estimator-residual scalar budgets
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem three_term_scalar_budget_le_alpha_square_add_penalty
    {Aidx Bidx R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (epochs : Finset Aidx) (active : Aidx → Finset Bidx)
    (A B C : Aidx → Bidx → R) (alphaSq penalty L D : R)
    (hA :
      Finset.sum epochs (fun s => Finset.sum (active s) (fun j => A s j)) ≤
        L * D ^ 2 * (1 / 2 * alphaSq))
    (hB :
      Finset.sum epochs (fun s => Finset.sum (active s) (fun j => B s j)) ≤
        L * D ^ 2 * alphaSq)
    (hC :
      Finset.sum epochs (fun s => Finset.sum (active s) (fun j => C s j)) ≤
        L * D ^ 2 * penalty) :
    Finset.sum epochs
        (fun s => Finset.sum (active s) (fun j => A s j + B s j + C s j)) ≤
      L * D ^ 2 * (3 / 2 * alphaSq + penalty) := by
  classical
  calc
    Finset.sum epochs
        (fun s => Finset.sum (active s) (fun j => A s j + B s j + C s j))
        =
      Finset.sum epochs (fun s => Finset.sum (active s) (fun j => A s j)) +
        Finset.sum epochs (fun s => Finset.sum (active s) (fun j => B s j)) +
        Finset.sum epochs (fun s => Finset.sum (active s) (fun j => C s j)) := by
          simp only [Finset.sum_add_distrib]
    _ ≤
      L * D ^ 2 * (1 / 2 * alphaSq) +
        L * D ^ 2 * alphaSq +
        L * D ^ 2 * penalty := by
          linarith
    _ = L * D ^ 2 * (3 / 2 * alphaSq + penalty) := by
          ring


-- From Staging/scalar_budget_mono_penalty.lean

-- Generalization plan (G0):
-- G0.1 naming: scalar_budget_mono_penalty
-- G0.2 typeclass level used:
--   E: none; the proof is pure scalar ordered-semiring algebra after all
--     stochastic, norm, and finite-sum estimates have been discharged.
--   measure: none; expectations enter only through the scalar bound `hscalar`.
--   convexity: none; no objective or feasible-set geometry is used.
-- G0.3 reusability — could instantiate:
--   1. finite-sum nonconvex conditional gradient, replacing the corrected
--      epoch-difference penalty by the displayed source penalty in Theorem 7.16.
--   2. stochastic nonconvex conditional gradient, replacing corrected
--      estimator-residual penalties by printed epoch penalties after scalar
--      Wolfe-gap budgets have been assembled.
-- G0.4 search trace:
--   queries: ["scalar budget penalty", "real inequality monotone penalty"]
--   top hits: ["three_term_scalar_budget_le_alpha_square_add_penalty",
--     "finite_epochDifference_form_scalar_budget_theorem716",
--     "finite_source_form_scalar_budget_theorem716",
--     "expectedWolfeGapUpperBoundWithEpochPenalty_mono_epochPenalty",
--     "active_l1_error_sum_le_epoch_penalty_add_floor_mass"]
--   coverage: partial — `expectedWolfeGapUpperBoundWithEpochPenalty_mono_epochPenalty`
--     proves monotonicity for one concrete Wolfe-gap RHS template, while this
--     theorem isolates the reusable ordered-semiring transport for any scalar
--     budget of the form `coef * (base + penalty)`.
-- G0.4 not-a-thin-wrapper rationale: the theorem packages the reusable
--   invariant that a completed scalar budget remains valid when only the
--   penalty addend is enlarged under a nonnegative coefficient.
-- G0.5 structural-content rationale: the declaration exposes the common
--   scalar handoff from a corrected penalty to a displayed penalty without any
--   paper-local epoch, oracle, or Wolfe-gap notation.
-- G0.5b name-body alignment: the theorem name promises monotonicity of a
--   scalar budget in its penalty term, and the statement proves exactly that.
-- G0.5c thin-wrapper self-detect: clean — body composes transitivity,
--   additive monotonicity, and nonnegative left multiplication rather than
--   aliasing a single existing theorem or model-specific RHS lemma.
-- G0.5d minimal-hypothesis check: all already minimal; the only assumptions
--   are the source scalar bound, the penalty comparison, and coefficient
--   nonnegativity.

/-- A scalar budget with a nonnegative coefficient is monotone in its penalty
addend.

If `lhs` is bounded by `coef * (base + correctedPenalty)`, and the corrected
penalty is at most a displayed or literal penalty, then the same `lhs` is
bounded by the budget using the larger penalty whenever `coef` is nonnegative.

Layer: Layer1 | Gap: Level 0 (scalar penalty monotonicity)
Proof: enlarge the penalty by additive monotonicity, multiply the resulting
  inequality by the nonnegative coefficient, and compose with the existing
  scalar budget.
Source: Mathlib ordered-semiring monotonicity for addition and multiplication
Used in: nonconvex conditional-gradient scalar budget transfer from corrected
  epoch-difference penalties to displayed source penalties
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem scalar_budget_mono_penalty
    {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
    (lhs base correctedPenalty literalPenalty coef : R)
    (hscalar : lhs ≤ coef * (base + correctedPenalty))
    (hcoef_nonneg : 0 ≤ coef)
    (hpenalty : correctedPenalty ≤ literalPenalty) :
    lhs ≤ coef * (base + literalPenalty) := by
  exact hscalar.trans
    (mul_le_mul_of_nonneg_left
      (add_le_add_right hpenalty base) hcoef_nonneg)


-- From Staging/expected_bound_of_weighted_sum_bound.lean

-- Generalization plan (G0):
-- G0.1 naming: expected_bound_of_weighted_sum_bound
-- G0.2 typeclass level used:
--   E: none; the proof is scalar real algebra after the randomized-output
--      expectation has already been rewritten to a normalized weighted sum.
--   measure: none; measure/integrability hypotheses are consumed upstream by
--      the output-expectation expansion and do not enter this scalar transport.
--   convexity: none
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional gradient, final expected Wolfe-gap
--      normalization from a weighted numerator bound.
--   2. stochastic mirror descent, randomized stationarity-certificate bounds
--      after finite-window output expectation expansion.
-- G0.4 search trace:
--   queries: ["expected weighted sum bound", "normalized numerator inequality"]
--   top hits: ["weighted_gap_sum_bound_of_active_one_step_with_l1_floor",
--     "weighted_gap_sum_bound_of_active_one_step_with_variance_floor",
--     "expectedSelectedOutput_eq_inv_mul_Icc_weighted_sum",
--     "weighted_variance_sum_expectation_bound",
--     "expectedOutput_eq_weighted_sum_div",
--     "Convex.normalized_weighted_sum_mem",
--     "normalizedWeightedExpectedCertificate_eq_sum_normalized"]
--   coverage: partial — existing hits either prove the numerator bound,
--     construct or expand the normalized output expectation, or prove convex
--     feasibility/variance bounds; none packages the scalar transport from an
--     already-expanded normalized expectation through a separate numerator
--     bound and final normalized RHS identity.
-- G0.4 not-a-thin-wrapper rationale: the theorem ties together three reusable
--   invariants — output-expansion equality, weighted-numerator domination, and
--   caller-supplied normalized closed-form identity — rather than renaming a
--   single Mathlib or SOptLib lemma.
-- G0.5 structural-content rationale: the statement exposes the common
--   normalized expected-bound handoff point between stochastic output-law
--   lemmas and closed-form convergence displays.
-- G0.5c thin-wrapper self-detect: clean — body combines equality rewriting,
--   nonnegative inverse scaling of an inequality, and a final normalized-form
--   rewrite.
-- G0.5d minimal-hypothesis check: all already minimal; only positivity of the
--   normalizing scalar, one equality, one inequality, and one closed-form
--   equality are used.

/-- A normalized output expectation is bounded by any normalized numerator bound.

Once a randomized-output expectation has been rewritten as the inverse total
weight times a weighted numerator, an upper bound on that numerator transfers
through the nonnegative inverse denominator and any caller-provided closed form
for the normalized bound.

Layer: Layer1 | Gap: Level 1 (normalized expected weighted-sum bound)
Proof: rewrite the expectation by its weighted-sum expansion, multiply the
  numerator inequality by the nonnegative inverse normalizer, and rewrite the
  normalized numerator to the displayed closed form.
Source: Mathlib ordered real field inequalities and finite weighted-output
  normalization algebra
Used in: stochastic nonconvex conditional-gradient final expected Wolfe-gap
  bound after randomized output expansion and weighted numerator aggregation
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem expected_bound_of_weighted_sum_bound
    (alphaSum expected weightedSum numerator rhs : ℝ)
    (halpha_pos : 0 < alphaSum)
    (hexpected : expected = alphaSum⁻¹ * weightedSum)
    (hweighted : weightedSum ≤ numerator)
    (hnormalized : alphaSum⁻¹ * numerator = rhs) :
    expected ≤ rhs := by
  rw [hexpected]
  have hinv_nonneg : 0 ≤ alphaSum⁻¹ :=
    inv_nonneg.mpr (le_of_lt halpha_pos)
  calc
    alphaSum⁻¹ * weightedSum ≤ alphaSum⁻¹ * numerator :=
      mul_le_mul_of_nonneg_left hweighted hinv_nonneg
    _ = rhs := hnormalized


-- From Staging/epochCounter_succ_eq_div_of_divisibility_update.lean

namespace SOptLib

-- Generalization plan (G0):
-- G0.1 naming: epochCounter_succ_eq_div_of_divisibility_update (orig was:
--   rawProcess_succ_s_eq_div); the name describes the epoch-counter invariant
--   for a recursively updated process, without Algorithm 7.13 local names.
-- G0.2 typeclass level used:
--   E: no carrier space; this is natural-number counter arithmetic over an
--      arbitrary state type.
--   measure: none; the invariant is pathwise and uses no probability,
--      filtration, independence, measurability, or integrability structure.
--   convexity: none; no feasible-set or objective geometry is involved.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional gradient, identifying the epoch counter
--      stored by the refresh/recursive estimator process with natural division.
--   2. variance-reduced mirror descent or SVRG-style stochastic gradient
--      methods, proving that a stored epoch counter agrees with the block
--      quotient under fixed-length refresh schedules.
-- G0.4 search trace:
--   queries: ["epoch counter division",
--     "counter increments when divisible successor division"]
--   top hits: ["oneBasedCounter", "oneBasedCounter_eq",
--     "oneBasedCounter_init", "oneBasedCounter_update_other",
--     "oneBasedCounter_update_selected", "positiveTimeSucc",
--     "expectedOutput_eq_weighted_sum_div", "sum_div_sum_eq_one"]
--   coverage: partial — the hits cover one-based counter views, finite
--     weighted division, and fixed schedule objects, but none proves the
--     induction invariant for a recursive process whose counter increments
--     exactly when the successor time is divisible by the epoch length.
-- G0.4 not-a-thin-wrapper rationale: the theorem packages the reusable
--   quantifier structure of a state process, a counter projection, base
--   initialization, and the two divisibility-controlled update branches.
-- G0.5 structural-content rationale: the declaration records the load-bearing
--   invariant that fixed-length epoch-boundary increments realize the natural
--   quotient counter at every successor time.
-- G0.5c thin-wrapper self-detect: clean — the body is an induction combining
--   recursive update hypotheses with `Nat.succ_div_of_dvd` and
--   `Nat.succ_div_of_not_dvd`, not a direct alias of a single existing lemma.
-- G0.5d minimal-hypothesis check: all already minimal; the proof uses only the
--   pointwise base counter law and the two pointwise recursive update laws.

/-- A divisibility-updated epoch counter equals natural division at successor times.

If a recursive state process starts with counter `0` at time `1`, increments
the counter exactly when `T ∣ k + 1`, and otherwise leaves it unchanged, then
the counter stored at time `k + 1` is the quotient `k / T`.

Layer: Layer1 | Gap: Level 1 (recursive epoch-counter quotient invariant)
Proof: induct on the successor time, split on the divisibility test, and use
  Mathlib's successor-division lemmas for the quotient update.
Source: Mathlib natural-number division, modular divisibility, and recursive
  stochastic-optimization epoch schedules
Used in: stochastic nonconvex conditional-gradient refresh/recursive estimator
  process epoch-counter identification
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem epochCounter_succ_eq_div_of_divisibility_update
    {Ω State : Type*}
    (counter : State → ℕ) (process : ℕ → Ω → State) (T : ℕ)
    (hinit : ∀ ω, counter (process 1 ω) = 0)
    (hstep_dvd : ∀ k ω, T ∣ k + 1 →
      counter (process (k + 2) ω) = counter (process (k + 1) ω) + 1)
    (hstep_not_dvd : ∀ k ω, ¬ T ∣ k + 1 →
      counter (process (k + 2) ω) = counter (process (k + 1) ω))
    (k : ℕ) :
    ∀ ω, counter (process (k + 1) ω) = k / T := by
  intro ω
  induction k with
  | zero =>
      simpa using hinit ω
  | succ k ih =>
      by_cases hdiv : T ∣ k + 1
      · have hupdate := hstep_dvd k ω hdiv
        simp [hupdate, ih, Nat.succ_div_of_dvd hdiv]
      · have hupdate := hstep_not_dvd k ω hdiv
        simp [hupdate, ih, Nat.succ_div_of_not_dvd hdiv]

end SOptLib

-- Generalization plan (G0):
-- concept/name: selected-memory gradient-extrapolation pathwise telescope; orig
--   was `proposition56_gradient_extrapolation_telescope_pathwise_5_2_65_positive_domain`,
--   renamed away from theorem numbering and positive-domain setup fields while
--   keeping the domain terms selected memory and gradient extrapolation.
-- generality used: arbitrary sample-path type, finite coordinate type, and real
--   inner-product carrier; no measure, filtration, independence, integrability,
--   convexity, smoothness, oracle, or finite-dimensional hypotheses are used.
-- portable call pattern: randomized coordinate gradient-extrapolation,
--   SAGA/SARAH-style table memory, and accelerated sampled-memory proofs first
--   collapse current and lagged table updates to selected increments, then use a
--   coefficient bridge to telescope the lagged inner-product window; the sample
--   stream, iterate sequence, memory table, scalar weights, and bridge identity
--   change while the conclusion shape stays fixed.
-- counterargument checked: not paper-local traceability because the theorem is
--   paper-free and depends only on selected-update collapse hypotheses plus
--   finite-sum algebra; not a pure wrapper because it composes the current and
--   lagged selected-memory reductions with the weighted lagged inner-product
--   telescope. It is not fully covered by the staged scalar telescope, which
--   starts after the memory table has already been reduced to a delta sequence.
-- coverage search: searched catalog/SOptLib/Staging for `selected memory
--   telescope`, `weighted lagged inner`, `gradient extrapolation`, and
--   `selected update collapse`; closest hits were
--   `sum_Icc_weighted_lagged_inner_telescope_eq_terminal_sub`,
--   `sum_inner_selected_extrapolation_split`, and generic SOptLib objective
--   telescopes, all partial. LeanSearch returned `Finset.sum_range_by_parts`,
--   `Finset.sum_Ico_sub`, and inner-sum lemmas, which are proof ingredients but
--   do not include the sampled-memory bridge.
-- minimal hypotheses: algorithm update laws are weakened to two pointwise
--   selected-collapse equalities on the active window; all probability,
--   generated-process, side-condition record, and cardinality-specific fields
--   are removed.

/-- A selected memory gradient-extrapolation window telescopes pathwise.

If current and lagged memory-table changes collapse to their selected
coordinates, and the coefficients satisfy `theta t * alpha t / m = theta
(t - 1)`, then the full finite table sum telescopes to the terminal selected
increment minus the lagged residual sum.

Layer: Layer1 | Gap: Level 1 (selected-memory gradient-extrapolation telescope)
Proof: reduce each table sum to selected current and lagged increments using
  the supplied pointwise collapse hypotheses, then invoke the weighted lagged
  inner-product finite-sum telescope.
Source: Mathlib finite sums over natural intervals and real inner-product
  bilinearity
Used in: randomized gradient extrapolation and sampled finite-memory methods
  before expectation-level residual assembly
Book citation: book/FOML/RandomGradientExtrapolation.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random gradient extrapolation -/
theorem selectedMemory_gradientExtrapolation_telescope_pathwise
    {Ω iota E : Type*} [Fintype iota]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (theta alpha : ℕ → ℝ) (m : ℝ)
    (x : E) (xseq : ℕ → Ω → E) (memory : ℕ → Ω → iota → E)
    (sample : ℕ → Ω → iota) {k : ℕ} (hk : 1 ≤ k) (ω : Ω)
    (hcoeff :
      ∀ t, 2 ≤ t → t ≤ k →
        theta t * alpha t / m = theta (t - 1))
    (hcurrent :
      ∀ t, 1 ≤ t → t ≤ k →
        Finset.sum Finset.univ
            (fun i => ⟪xseq t ω - x, memory t ω i - memory (t - 1) ω i⟫_ℝ) =
          ⟪xseq t ω - x,
            memory t ω (sample t ω) - memory (t - 1) ω (sample t ω)⟫_ℝ)
    (hlagged :
      ∀ t, 1 ≤ t → t ≤ k →
        Finset.sum Finset.univ
            (fun i =>
              ⟪xseq t ω - x,
                memory (t - 1) ω i - memory (t - 2) ω i⟫_ℝ) =
          ⟪xseq t ω - x,
            memory (t - 1) ω (sample (t - 1) ω) -
              memory (t - 2) ω (sample (t - 1) ω)⟫_ℝ) :
    Finset.sum (Finset.Icc 1 k)
        (fun t =>
          theta t *
            Finset.sum Finset.univ
              (fun i =>
                ⟪xseq t ω - x,
                  (memory t ω i - memory (t - 1) ω i) -
                    (alpha t / m) •
                      (memory (t - 1) ω i - memory (t - 2) ω i)⟫_ℝ)) =
      theta k *
          ⟪xseq k ω - x,
            memory k ω (sample k ω) - memory (k - 1) ω (sample k ω)⟫_ℝ -
        Finset.sum (Finset.Icc 2 k)
          (fun t =>
            (theta t * alpha t / m) *
              ⟪xseq t ω - xseq (t - 1) ω,
                memory (t - 1) ω (sample (t - 1) ω) -
                  memory (t - 2) ω (sample (t - 1) ω)⟫_ℝ) := by
  classical
  let xseqω : ℕ → E := fun t => xseq t ω
  let delta : ℕ → E := fun t =>
    memory t ω (sample t ω) - memory (t - 1) ω (sample t ω)
  have hdelta_zero : delta 0 = 0 := by
    dsimp [delta]
    simp
  have hscalar :=
    sum_Icc_weighted_lagged_inner_telescope_eq_terminal_sub
      (theta := theta) (alpha := alpha) (m := m)
      (x := x) (xseq := xseqω) (delta := delta) (k := k)
      hk hcoeff hdelta_zero
  have hleft :
      Finset.sum (Finset.Icc 1 k)
          (fun t =>
            theta t *
              Finset.sum Finset.univ
                (fun i =>
                  ⟪xseq t ω - x,
                    (memory t ω i - memory (t - 1) ω i) -
                      (alpha t / m) •
                        (memory (t - 1) ω i - memory (t - 2) ω i)⟫_ℝ)) =
        Finset.sum (Finset.Icc 1 k)
          (fun t =>
            theta t *
              (⟪xseqω t - x, delta t⟫_ℝ -
                (alpha t / m) * ⟪xseqω t - x, delta (t - 1)⟫_ℝ)) := by
    refine Finset.sum_congr rfl ?_
    intro t htmem
    have ht1 : 1 ≤ t := (Finset.mem_Icc.mp htmem).1
    have htle : t ≤ k := (Finset.mem_Icc.mp htmem).2
    have hsplit :
        Finset.sum Finset.univ
            (fun i =>
              ⟪xseq t ω - x,
                (memory t ω i - memory (t - 1) ω i) -
                  (alpha t / m) •
                    (memory (t - 1) ω i - memory (t - 2) ω i)⟫_ℝ) =
          ⟪xseq t ω - x,
            memory t ω (sample t ω) - memory (t - 1) ω (sample t ω)⟫_ℝ -
            (alpha t / m) *
              Finset.sum Finset.univ
                (fun i =>
                  ⟪xseq t ω - x,
                    memory (t - 1) ω i - memory (t - 2) ω i⟫_ℝ) := by
      calc
        Finset.sum Finset.univ
            (fun i =>
              ⟪xseq t ω - x,
                (memory t ω i - memory (t - 1) ω i) -
                  (alpha t / m) •
                    (memory (t - 1) ω i - memory (t - 2) ω i)⟫_ℝ) =
          Finset.sum Finset.univ
            (fun i =>
              ⟪xseq t ω - x,
                memory t ω i - memory (t - 1) ω i⟫_ℝ -
                (alpha t / m) *
                  ⟪xseq t ω - x,
                    memory (t - 1) ω i - memory (t - 2) ω i⟫_ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            simp [inner_sub_right, inner_smul_right]
        _ =
          Finset.sum Finset.univ
              (fun i =>
                ⟪xseq t ω - x,
                  memory t ω i - memory (t - 1) ω i⟫_ℝ) -
            (alpha t / m) *
              Finset.sum Finset.univ
                (fun i =>
                  ⟪xseq t ω - x,
                    memory (t - 1) ω i - memory (t - 2) ω i⟫_ℝ) := by
            rw [Finset.sum_sub_distrib]
            congr 1
            rw [← Finset.mul_sum]
        _ =
          ⟪xseq t ω - x,
            memory t ω (sample t ω) - memory (t - 1) ω (sample t ω)⟫_ℝ -
            (alpha t / m) *
              Finset.sum Finset.univ
                (fun i =>
                  ⟪xseq t ω - x,
                    memory (t - 1) ω i - memory (t - 2) ω i⟫_ℝ) := by
            rw [hcurrent t ht1 htle]
    have hlag := hlagged t ht1 htle
    have hpred : t - 2 = t - 1 - 1 := by omega
    rw [hsplit, hlag]
    simp [xseqω, delta, hpred]
  calc
    Finset.sum (Finset.Icc 1 k)
        (fun t =>
          theta t *
            Finset.sum Finset.univ
              (fun i =>
                ⟪xseq t ω - x,
                  (memory t ω i - memory (t - 1) ω i) -
                    (alpha t / m) •
                      (memory (t - 1) ω i - memory (t - 2) ω i)⟫_ℝ)) =
      Finset.sum (Finset.Icc 1 k)
        (fun t =>
          theta t *
            (⟪xseqω t - x, delta t⟫_ℝ -
              (alpha t / m) * ⟪xseqω t - x, delta (t - 1)⟫_ℝ)) := hleft
    _ =
      theta k *
          ⟪xseq k ω - x,
            memory k ω (sample k ω) - memory (k - 1) ω (sample k ω)⟫_ℝ -
        Finset.sum (Finset.Icc 2 k)
          (fun t =>
            (theta t * alpha t / m) *
              ⟪xseq t ω - xseq (t - 1) ω,
                memory (t - 1) ω (sample (t - 1) ω) -
                  memory (t - 2) ω (sample (t - 1) ω)⟫_ℝ) := by
        simpa [xseqω, delta] using hscalar

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: weighted product-output saddle-gap Jensen assembly; orig was
--   theorem51_gap_weighted_output_pathwise_le_weighted_saddle_sum, renamed away
--   from theorem numbering and RPDG setup names while retaining the saddle-gap
--   product-output concept.
-- generality used: arbitrary finite output window, real weights and positive
--   normalizer, arbitrary primal and dual carriers, and a real inner-product
--   ambient space for the linear coupling. No measure, filtration,
--   independence, integrability, oracle, smoothness, finite-dimensional, or
--   algorithm-update hypotheses are used; convexity is consumed only through
--   the two already-proved component Jensen bounds.
-- portable call pattern: primal-dual gradient, mirror-prox, Fenchel-saddle, and
--   block-coordinate stochastic methods call the same step after constructing
--   primal and dual weighted outputs; the carriers, windows, weights, coupling
--   map, regularizer, dual penalty, and component Jensen witnesses change while
--   the normalized saddle-gap conclusion stays the same.
-- counterargument checked: this is not just paper-local traceability because
--   future algorithms repeatedly need to assemble convex primal/dual Jensen
--   bounds and affine coupling identities into one saddle-gap bound. It is not
--   a duplicate of Mathlib Jensen or SOptLib's one-function weighted Jensen,
--   since those prove the component bounds but do not express the product
--   saddle-gap algebra.
-- coverage search: searched project/catalog tokens "weighted saddle gap
--   Jensen", "saddleGap weighted product output", "linearCoupledSaddleValue",
--   and "convexOn weighted average"; relevant partial hits were
--   `SOptLib.saddleGap`, `SOptLib.linearCoupledSaddleValue`,
--   `convexOn_weighted_average_le_weighted_sum`, and
--   `sum_convexOn_weighted_average_le_weighted_sum`. LeanSearch returned
--   Mathlib `ConvexOn.map_sum_le` and `ConvexOn.map_centerMass_le`, which cover
--   finite Jensen only, not this assembled saddle-gap statement.
-- minimal hypotheses: retained exactly the positive-normalizer equality, the
--   primal and dual component Jensen inequalities, and the two affine coupling
--   weighted-average identities; nonnegative weights are not needed once those
--   four caller-proved facts are supplied.

/-- A weighted product output has saddle gap bounded by the normalized weighted
sum of pointwise saddle gaps for a linearly coupled saddle value.

The theorem packages the algebra after the primal and dual Jensen inequalities
and the affine coupling identities have been proved. It is independent of the
algorithm that produced the output window or the weighted averages.

Layer: Layer1 | Gap: Level 1 (weighted product-output saddle-gap Jensen assembly)
Proof: expand the named saddle gap and linearly coupled saddle value, rewrite
  the two affine coupling terms and normalized constants, then combine the
  primal and dual component Jensen inequalities by ordered real arithmetic.
Source: convex-analysis saddle-gap algebra, finite weighted Jensen outputs, and
  Mathlib finite-sum real arithmetic
Used in: random primal-dual gradient weighted product-output saddle-gap bound
  after primal regularizer Jensen and coordinatewise dual-conjugate Jensen
Book citation: book/FOML/RandomPrimalDualGradient.json#/main_theorem/proof/6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem saddleGap_weightedProductOutput_le_weighted_sum
    {T X Y E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Finset T) (γ : T → ℝ) (W : ℝ)
    (evalX : X → E) (regularizer : X → ℝ)
    (coupling : Y → E) (dualPenalty : Y → ℝ)
    (x : T → X) (y : T → Y) (xbar : X) (ybar : Y) (z : X × Y)
    (hW_pos : 0 < W)
    (hW_eq : W = ∑ t ∈ s, γ t)
    (hregularizer :
      regularizer xbar ≤ W⁻¹ * ∑ t ∈ s, γ t * regularizer (x t))
    (hdualPenalty :
      dualPenalty ybar ≤ W⁻¹ * ∑ t ∈ s, γ t * dualPenalty (y t))
    (hevalX :
      ⟪evalX xbar, coupling z.2⟫_ℝ =
        W⁻¹ * ∑ t ∈ s, γ t * ⟪evalX (x t), coupling z.2⟫_ℝ)
    (hcoupling :
      ⟪evalX z.1, coupling ybar⟫_ℝ =
        W⁻¹ * ∑ t ∈ s, γ t * ⟪evalX z.1, coupling (y t)⟫_ℝ) :
    saddleGap (linearCoupledSaddleValue evalX regularizer coupling dualPenalty)
        (xbar, ybar) z ≤
      W⁻¹ * ∑ t ∈ s, γ t *
        saddleGap (linearCoupledSaddleValue evalX regularizer coupling dualPenalty)
          (x t, y t) z := by
  classical
  have hW_ne : W ≠ 0 := ne_of_gt hW_pos
  have hW_norm : W⁻¹ * (∑ t ∈ s, γ t) = 1 := by
    rw [← hW_eq]
    exact inv_mul_cancel₀ hW_ne
  let regBar : ℝ := regularizer xbar
  let regSum : ℝ := W⁻¹ * ∑ t ∈ s, γ t * regularizer (x t)
  let xBar : ℝ := ⟪evalX xbar, coupling z.2⟫_ℝ
  let xSum : ℝ := W⁻¹ * ∑ t ∈ s, γ t * ⟪evalX (x t), coupling z.2⟫_ℝ
  let constDual : ℝ := dualPenalty z.2
  let constReg : ℝ := regularizer z.1
  let yBar : ℝ := ⟪evalX z.1, coupling ybar⟫_ℝ
  let ySum : ℝ := W⁻¹ * ∑ t ∈ s, γ t * ⟪evalX z.1, coupling (y t)⟫_ℝ
  let dualBar : ℝ := dualPenalty ybar
  let dualSum : ℝ := W⁻¹ * ∑ t ∈ s, γ t * dualPenalty (y t)
  have hreg' : regBar ≤ regSum := by
    simpa [regBar, regSum] using hregularizer
  have hdual' : dualBar ≤ dualSum := by
    simpa [dualBar, dualSum] using hdualPenalty
  have hx' : xBar = xSum := by
    simpa [xBar, xSum] using hevalX
  have hy' : yBar = ySum := by
    simpa [yBar, ySum] using hcoupling
  have hleft :
      saddleGap (linearCoupledSaddleValue evalX regularizer coupling dualPenalty)
          (xbar, ybar) z =
        regBar + xBar - constDual - constReg - yBar + dualBar := by
    simp [saddleGap, linearCoupledSaddleValue, regBar, xBar, constDual,
      constReg, yBar, dualBar]
    ring
  have hconstDual :
      W⁻¹ * (∑ t ∈ s, γ t * constDual) = constDual := by
    calc
      W⁻¹ * (∑ t ∈ s, γ t * constDual) =
          W⁻¹ * ((∑ t ∈ s, γ t) * constDual) := by
            rw [Finset.sum_mul]
      _ = (W⁻¹ * (∑ t ∈ s, γ t)) * constDual := by
            ring
      _ = constDual := by
            rw [hW_norm]
            ring
  have hconstReg :
      W⁻¹ * (∑ t ∈ s, γ t * constReg) = constReg := by
    calc
      W⁻¹ * (∑ t ∈ s, γ t * constReg) =
          W⁻¹ * ((∑ t ∈ s, γ t) * constReg) := by
            rw [Finset.sum_mul]
      _ = (W⁻¹ * (∑ t ∈ s, γ t)) * constReg := by
            ring
      _ = constReg := by
            rw [hW_norm]
            ring
  have hgap_each (t : T) :
      saddleGap (linearCoupledSaddleValue evalX regularizer coupling dualPenalty)
          (x t, y t) z =
        regularizer (x t) +
          ⟪evalX (x t), coupling z.2⟫_ℝ -
          constDual - constReg -
          ⟪evalX z.1, coupling (y t)⟫_ℝ +
          dualPenalty (y t) := by
    simp [saddleGap, linearCoupledSaddleValue, constDual, constReg]
    ring
  have hright :
      W⁻¹ * ∑ t ∈ s, γ t *
          saddleGap (linearCoupledSaddleValue evalX regularizer coupling dualPenalty)
            (x t, y t) z =
        regSum + xSum - constDual - constReg - ySum + dualSum := by
    calc
      W⁻¹ * ∑ t ∈ s, γ t *
          saddleGap (linearCoupledSaddleValue evalX regularizer coupling dualPenalty)
            (x t, y t) z =
          W⁻¹ * ∑ t ∈ s, γ t *
            (regularizer (x t) +
              ⟪evalX (x t), coupling z.2⟫_ℝ -
              constDual - constReg -
              ⟪evalX z.1, coupling (y t)⟫_ℝ +
              dualPenalty (y t)) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro t _ht
            rw [hgap_each t]
      _ = regSum + xSum - constDual - constReg - ySum + dualSum := by
            let A : T → ℝ := fun t => regularizer (x t)
            let B : T → ℝ := fun t => ⟪evalX (x t), coupling z.2⟫_ℝ
            let C : T → ℝ := fun t => ⟪evalX z.1, coupling (y t)⟫_ℝ
            let D : T → ℝ := fun t => dualPenalty (y t)
            have hsum_expand :
                (∑ t ∈ s, γ t *
                    (A t + B t - constDual - constReg - C t + D t)) =
                  (∑ t ∈ s, γ t * A t) +
                    (∑ t ∈ s, γ t * B t) -
                    (∑ t ∈ s, γ t * constDual) -
                    (∑ t ∈ s, γ t * constReg) -
                    (∑ t ∈ s, γ t * C t) +
                    (∑ t ∈ s, γ t * D t) := by
              simp [mul_add, mul_sub, Finset.sum_add_distrib,
                Finset.sum_sub_distrib]
            change
              W⁻¹ * (∑ t ∈ s, γ t *
                  (A t + B t - constDual - constReg - C t + D t)) =
                W⁻¹ * (∑ t ∈ s, γ t * A t) +
                  W⁻¹ * (∑ t ∈ s, γ t * B t) -
                  constDual - constReg -
                  W⁻¹ * (∑ t ∈ s, γ t * C t) +
                  W⁻¹ * (∑ t ∈ s, γ t * D t)
            rw [hsum_expand]
            nlinarith [hconstDual, hconstReg]
  rw [hleft, hright]
  nlinarith [hreg', hdual', hx', hy']

end SOptLib

-- Generalization plan (G0):
-- concept/name: sum_sampled_coordinate_two_time_increment_eq exposes the finite-coordinate
--   sum of a two-time increment whose support is carried by a current sampled
--   coordinate and a previous sampled coordinate; orig was
--   sampled_coordinate_two_time_increment_sum_branch.
-- generality used: finite coordinate type with decidable equality and an
--   additive commutative group target; no measure, convexity, smoothness,
--   norm, inner-product, module, or oracle assumptions are used.
-- portable call pattern: randomized block-coordinate primal-dual, coordinate
--   mirror-descent, and variance-reduced table-update proofs can reuse the
--   same branch-sum step after proving their pointwise current/previous
--   sampled-coordinate update equations.
-- counterargument checked: not only paper-local traceability because the
--   equal-or-distinct sampled-coordinate support split recurs in block
--   algorithms; not covered by Mathlib's `Fintype.sum_eq_add`, which requires
--   distinct selected coordinates and an arbitrary function rather than the
--   sum of two singleton branches.
-- coverage search: searched catalog/SOptLib/Staging for sampled coordinate,
--   two-time increment, branch sum, and finite sum ite; LeanSearch found
--   `Finset.sum_eq_add_of_mem`, `Fintype.sum_eq_add`, `Finset.sum_eq_add`, and
--   `Fintype.sum_dite_eq`, all partial because the needed statement permits
--   the current and previous coordinates to coincide.
-- minimal hypotheses: the original standing assumptions, probabilities,
--   Hilbert structure, finite-dimensionality, and real scalar coefficients are
--   reduced to the pointwise branch equation and finite coordinate summation.

/-- Sum a two-time coordinate increment supported on the current and previous samples.

If the pointwise increment `yt i - ytm1 i` is the sum of a singleton branch at
`sc` and a singleton branch at `sp`, then its total finite-coordinate sum is the
sum of the two selected payloads. The statement intentionally allows `sc = sp`,
in which case both payloads contribute at the same coordinate.

Layer: Layer1 | Gap: Level 1 (sampled-coordinate two-time branch summation)
Proof: rewrite the total increment by the pointwise branch equation, split the
  finite sum over addition, and evaluate each singleton branch with
  `Finset.sum_ite_eq`.
Source: Mathlib finite sums over finite types and decidable equality
Used in: randomized block-coordinate primal-dual historical coupling expansion
  for current and previous sampled dual-coordinate corrections
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized primal-dual gradient method -/
theorem sum_sampled_coordinate_two_time_increment_eq
    {I E : Type*} [Fintype I] [DecidableEq I] [AddCommGroup E]
    (yt ytm1 cur prev : I -> E) (sc sp : I)
    (hpoint : forall i : I,
      yt i - ytm1 i =
        (if i = sc then cur i else 0) + (if i = sp then prev i else 0)) :
    (∑ i : I, (yt i - ytm1 i)) = cur sc + prev sp := by
  classical
  calc
    (∑ i : I, (yt i - ytm1 i)) =
        ∑ i : I, ((if i = sc then cur i else 0) +
          (if i = sp then prev i else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          exact hpoint i
    _ =
        (∑ i : I, (if i = sc then cur i else 0)) +
          (∑ i : I, (if i = sp then prev i else 0)) := by
          rw [Finset.sum_add_distrib]
    _ = cur sc + prev sp := by
          simp

-- Generalization plan (G0):
-- concept/name: expected weighted-output norm correction controlled by a
--   weighted Bregman-budget average; orig was
--   theorem51_norm_correction_le_weighted_bregman_average, renamed away from
--   theorem numbering and random-primal-dual-gradient setup fields while
--   retaining the domain term "weighted output".
-- generality used: arbitrary sample type, finite index window, real
--   seminormed additive group carrier, abstract expectation functional with
--   monotonicity plus scalar and finite-sum linearity, nonnegative weights,
--   positive normalizer, pointwise weighted-average norm-square bound, and a
--   half-squared-norm lower bound by a Bregman-budget observable; no
--   probability measure, filtration, oracle law, convexity, smoothness beyond
--   the scalar `L`, inner product, completeness, or finite-dimensionality is
--   used.
-- portable call pattern: averaged-output convergence proofs for stochastic
--   mirror descent, randomized block primal-dual gradient, and proximal
--   stochastic methods call this after identifying a weighted output, proving a
--   pointwise weighted-average norm-square estimate, and lower-bounding
--   iterate distances by a Bregman divergence; the window, weights, expectation
--   operator, iterate family, output map, Bregman observable, and named expected
--   Bregman budget vary while the conclusion has the same shape.
-- counterargument checked: not paper-local traceability because the statement
--   packages a recurring proof-composition boundary; not a caller-side
--   expression because it internally combines the pointwise weighted-output
--   norm estimate, Bregman lower bounds, expectation monotonicity, and
--   expectation linearity, plus transport to a caller's named expected Bregman
--   budget. It is not a duplicate of the existing weighted norm-square Jensen
--   lemma, which stops before Bregman conversion and expectation transport.
-- coverage search: checked SOPTLIB_DESIGN.md, docs/knowledge/CATALOG.md,
--   SOptLib/Layer1/Telescope.lean, SOptLib/Model/Iterates.lean, staged
--   finitePrefixExpectation linearity/monotonicity APIs, and project tokens
--   `weighted output norm correction bregman average expectation finite sum`,
--   `weighted average norm square`, and `expected_bound_of_weighted_sum_bound`;
--   hits were partial: weighted-output squared-distance Jensen, finite-prefix
--   expectation linearity, and normalized scalar transport, but no theorem
--   covers the combined norm-correction-to-weighted-Bregman-average handoff.
-- minimal hypotheses: the expectation laws and per-index expected-budget
--   transport are exactly the algebra used after the caller instantiates a
--   concrete expectation; geometry is reduced to the pointwise norm-square
--   estimate and half-norm Bregman lower bound, with `E` weakened from Hilbert
--   space to a seminormed additive group.

/-- An expected weighted-output norm correction is bounded by a weighted
Bregman-budget average.

If a weighted output has a pointwise normalized weighted squared-distance bound,
and every constituent squared distance is controlled by twice a Bregman-budget
observable, then the expected smoothness norm correction is controlled by the
same normalized weighted named expected Bregman budget.

Layer: Layer1 | Gap: Level 1 (expected weighted-output norm correction)
Proof: convert each pointwise squared-distance term to twice its Bregman budget,
  scale the weighted-average norm bound by `L / 2`, then use expectation
  monotonicity, scalar linearity, finite-sum linearity, and the supplied
  per-index expected-budget transport.
Source: Mathlib ordered real arithmetic, finite sums, normed additive groups,
  and expectation-linearity patterns
Used in: randomized primal-dual gradient final expected primal-gap bound after
  weighted-output smoothness correction, and future weighted averaged-output
  stochastic optimization convergence proofs
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized primal-dual gradient -/
theorem expected_weighted_output_norm_correction_le_weighted_bregman_average
    {Ω κ E : Type*} [SeminormedAddCommGroup E]
    (Exp : (Ω → ℝ) → ℝ)
    (s : Finset κ) (γ : κ → ℝ)
    (x : κ → Ω → E) (xbar : Ω → E) (xstar : E)
    (B : κ → Ω → ℝ) (Bavg : κ → ℝ) (L W : ℝ)
    (hExp_mono : ∀ F G : Ω → ℝ, (∀ ω, F ω ≤ G ω) → Exp F ≤ Exp G)
    (hExp_const_mul : ∀ (c : ℝ) (F : Ω → ℝ),
      Exp (fun ω => c * F ω) = c * Exp F)
    (hExp_sum : ∀ F : κ → Ω → ℝ,
      Exp (fun ω => ∑ i ∈ s, F i ω) = ∑ i ∈ s, Exp (F i))
    (hL_nonneg : 0 ≤ L)
    (hW_pos : 0 < W)
    (hγ_nonneg : ∀ i ∈ s, 0 ≤ γ i)
    (hpoint : ∀ ω,
      ‖xbar ω - xstar‖ ^ 2 ≤
        W⁻¹ * ∑ i ∈ s, γ i * ‖x i ω - xstar‖ ^ 2)
    (hbreg_lower : ∀ i ∈ s, ∀ ω,
      (1 / 2 : ℝ) * ‖x i ω - xstar‖ ^ 2 ≤ B i ω)
    (htransport : ∀ i ∈ s, Exp (B i) = Bavg i) :
    Exp (fun ω => (L / 2) * ‖xbar ω - xstar‖ ^ 2) ≤
      L * W⁻¹ * ∑ i ∈ s, γ i * Bavg i := by
  classical
  have hW_inv_nonneg : 0 ≤ W⁻¹ := inv_nonneg.mpr hW_pos.le
  have hpath :
      ∀ ω,
        (L / 2) * ‖xbar ω - xstar‖ ^ 2 ≤
          L * W⁻¹ * ∑ i ∈ s, γ i * B i ω := by
    intro ω
    have hsum_norm_le :
        (∑ i ∈ s, γ i * ‖x i ω - xstar‖ ^ 2) ≤
          2 * ∑ i ∈ s, γ i * B i ω := by
      calc
        (∑ i ∈ s, γ i * ‖x i ω - xstar‖ ^ 2)
            ≤ ∑ i ∈ s, γ i * (2 * B i ω) := by
              refine Finset.sum_le_sum ?_
              intro i hi
              have hnorm_le :
                  ‖x i ω - xstar‖ ^ 2 ≤ 2 * B i ω := by
                have hb := hbreg_lower i hi ω
                nlinarith
              exact mul_le_mul_of_nonneg_left hnorm_le (hγ_nonneg i hi)
        _ = 2 * ∑ i ∈ s, γ i * B i ω := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro i _hi
              ring
    have hweighted_norm_le :
        W⁻¹ * (∑ i ∈ s, γ i * ‖x i ω - xstar‖ ^ 2) ≤
          W⁻¹ * (2 * ∑ i ∈ s, γ i * B i ω) :=
      mul_le_mul_of_nonneg_left hsum_norm_le hW_inv_nonneg
    have hnorm_to_breg :
        ‖xbar ω - xstar‖ ^ 2 ≤
          2 * (W⁻¹ * ∑ i ∈ s, γ i * B i ω) := by
      calc
        ‖xbar ω - xstar‖ ^ 2
            ≤ W⁻¹ * ∑ i ∈ s, γ i * ‖x i ω - xstar‖ ^ 2 := hpoint ω
        _ ≤ W⁻¹ * (2 * ∑ i ∈ s, γ i * B i ω) := hweighted_norm_le
        _ = 2 * (W⁻¹ * ∑ i ∈ s, γ i * B i ω) := by ring
    have hscale_nonneg : 0 ≤ L / 2 := by nlinarith
    have hscaled := mul_le_mul_of_nonneg_left hnorm_to_breg hscale_nonneg
    calc
      (L / 2) * ‖xbar ω - xstar‖ ^ 2
          ≤ (L / 2) * (2 * (W⁻¹ * ∑ i ∈ s, γ i * B i ω)) := hscaled
      _ = L * W⁻¹ * ∑ i ∈ s, γ i * B i ω := by ring
  calc
    Exp (fun ω => (L / 2) * ‖xbar ω - xstar‖ ^ 2)
        ≤ Exp (fun ω => L * W⁻¹ * ∑ i ∈ s, γ i * B i ω) :=
          hExp_mono _ _ hpath
    _ = L * W⁻¹ * ∑ i ∈ s, γ i * Exp (B i) := by
          rw [hExp_const_mul (L * W⁻¹)]
          rw [hExp_sum]
          congr 1
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [hExp_const_mul (γ i)]
    _ = L * W⁻¹ * ∑ i ∈ s, γ i * Bavg i := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [htransport i hi]

-- Generalization plan (G0):
-- concept/name: finite-prefix expectation weighted-output gap linearization;
--   orig was theorem51_weighted_saddle_gap_jensen_le_weighted_sum, renamed away
--   from theorem numbering and saddle-specific setup fields while preserving
--   the weighted-output expected-gap proof step.
-- generality used: arbitrary sample space, arbitrary finite output index set,
--   real weights and normalizer, an abstract real-valued finite-prefix
--   expectation functional with monotonicity plus scalar and finite-sum
--   linearity, a pathwise weighted-output gap bound, and per-index expectation
--   transport; no probability measure, filtration, independence, convexity,
--   smoothness, oracle, Hilbert, or finite-dimensional assumptions are used.
-- portable call pattern: weighted-output convergence proofs for stochastic
--   mirror descent, randomized primal-dual gradient, mirror-prox, and
--   proximal stochastic methods call this after a pathwise Jensen bound; the
--   process, horizon, weights, gap observable, expectation operator, and
--   named expected-gap family vary while the finite-prefix expectation
--   linearization conclusion stays the same.
-- counterargument checked: not paper-local traceability because it packages a
--   recurring composition boundary after Jensen and before convergence-rate
--   aggregation. It is not a pure wrapper around Mathlib/SOptLib linearity:
--   existing APIs provide monotonicity, scalar linearity, and finite-sum
--   exchange separately, but not the weighted-output gap handoff with
--   per-horizon transport to a named expected-gap family.
-- coverage search: searched SOPTLIB_DESIGN.md, docs/knowledge/CATALOG.md,
--   SOptLib/Layer1/Telescope.lean, staged finitePrefixExpectation APIs, and
--   project tokens `finitePrefixExpectation weighted gap`, `weighted output
--   gap expectation`, `saddle gap horizon transport`; LeanSearch query
--   "expectation of weighted finite sum bounded by weighted sum of
--   expectations" returned Mathlib conditional-expectation finite-sum and
--   Finset expectation/Jensen lemmas. Coverage is partial: raw linearity and
--   Jensen lemmas exist, but none states this finite-prefix weighted-output
--   expected-gap bridge.
-- minimal hypotheses: all global algorithm assumptions are reduced to the
--   pointwise bound, expectation monotonicity/linearity laws, and per-index
--   transport equalities actually used by the proof.

/-- A finite-prefix expected weighted-output gap is bounded by the weighted sum
of named expected gaps.

If a weighted output has a pathwise gap bounded by the normalized weighted sum
of indexed gap observables, and the finite-prefix expectation transports each
indexed observable to its named expected gap, then expectation monotonicity and
linearity give the normalized weighted expected-gap bound.

Layer: Layer1 | Gap: Level 1 (finite-prefix weighted-output expected-gap bridge)
Proof: apply expectation monotonicity to the pathwise weighted-output gap
  bound, pull the normalizer and finite weighted sum through the expectation,
  and rewrite each indexed expectation by the supplied horizon-transport
  equality.
Source: Mathlib finite-sum ordered real algebra and Bochner-expectation
  linearity patterns
Used in: randomized primal-dual gradient weighted-output saddle-gap expectation
  after pathwise Jensen, and future stochastic weighted-output convergence
  proofs after finite-horizon transport
Book citation: book/FOML/RandomPrimalDualGradient.json#/main_theorem/proof/6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized primal-dual gradient -/
theorem finitePrefixExpectation_weighted_output_gap_le_weighted_expected_gap
    {Ω T : Type*}
    (s : Finset T) (γ : T → ℝ) (W : ℝ)
    (Eprefix : (Ω → ℝ) → ℝ)
    (G : T → Ω → ℝ) (Gbar : Ω → ℝ) (EG : T → ℝ)
    (hEprefix_mono :
      ∀ F H : Ω → ℝ, (∀ ω, F ω ≤ H ω) → Eprefix F ≤ Eprefix H)
    (hEprefix_const_mul :
      ∀ (c : ℝ) (F : Ω → ℝ), Eprefix (fun ω => c * F ω) = c * Eprefix F)
    (hEprefix_sum :
      ∀ F : T → Ω → ℝ,
        Eprefix (fun ω => ∑ t ∈ s, F t ω) = ∑ t ∈ s, Eprefix (F t))
    (hpath :
      ∀ ω, Gbar ω ≤ W⁻¹ * ∑ t ∈ s, γ t * G t ω)
    (htransport : ∀ t ∈ s, Eprefix (G t) = EG t) :
    Eprefix Gbar ≤ W⁻¹ * ∑ t ∈ s, γ t * EG t := by
  classical
  calc
    Eprefix Gbar ≤
        Eprefix (fun ω => W⁻¹ * ∑ t ∈ s, γ t * G t ω) := by
      exact hEprefix_mono Gbar (fun ω => W⁻¹ * ∑ t ∈ s, γ t * G t ω) hpath
    _ = W⁻¹ * Eprefix (fun ω => ∑ t ∈ s, γ t * G t ω) := by
      exact hEprefix_const_mul W⁻¹ (fun ω => ∑ t ∈ s, γ t * G t ω)
    _ = W⁻¹ * ∑ t ∈ s, Eprefix (fun ω => γ t * G t ω) := by
      rw [hEprefix_sum (fun t ω => γ t * G t ω)]
    _ = W⁻¹ * ∑ t ∈ s, γ t * Eprefix (G t) := by
      refine congrArg (fun r => W⁻¹ * r) ?_
      refine Finset.sum_congr rfl ?_
      intro t _ht
      exact hEprefix_const_mul (γ t) (G t)
    _ = W⁻¹ * ∑ t ∈ s, γ t * EG t := by
      refine congrArg (fun r => W⁻¹ * r) ?_
      refine Finset.sum_congr rfl ?_
      intro t ht
      rw [htransport t ht]


-- Batch 2 promoted from Staging/uniform_output_bound_of_expected_descent.lean
-- Generalization plan (G0):
-- concept/name: uniform randomized-output certificate bound from expected
--   descent; orig was `randomized_output_bound_from_expected_descent`, renamed
--   away from the local theorem boundary while retaining the stochastic
--   optimization proof step.
-- generality used: ordered real scalar potentials and certificates indexed by
--   natural time; no measure, independence, integrability, convexity,
--   smoothness, oracle, update, Hilbert-space, or finite-dimensional
--   assumptions remain after the expected descent and output expansion have
--   been supplied by callers.
-- portable call pattern: nonconvex SGD, mirror descent, proximal-gradient, and
--   variance-reduced analyses can provide `A (N+1) + c * sum certificates <= A0`,
--   a terminal lower bound `Astar <= A (N+1)`, and a uniform-output expansion,
--   then call this theorem to obtain the randomized-output certificate bound.
-- counterargument checked: not paper-local traceability because the statement
--   has no algorithm objects or theorem numbers; not a pure wrapper because it
--   combines descent-to-numerator extraction, terminal lower-bound subtraction,
--   positive scaling, and the uniform-output normalization identity.
-- coverage search: searched CATALOG/SOptLib/Staging for `randomized output`,
--   `expected descent`, `terminal lower bound`, `normalized numerator`, and
--   exact weighted-output shapes; read `expectedOutput_eq_weighted_sum_div`,
--   `integral_sum_telescope_bound_of_pointwise_lower_bound`, and
--   `expected_bound_of_weighted_sum_bound`. Those hits are partial: they cover
--   output expansion, integral telescoping, or scaling an already-proved
--   numerator bound, but not the scalar descent plus terminal lower-bound
--   handoff packaged here. LeanSearch returned only unrelated average-risk and
--   Cesaro-average lemmas.
-- minimal hypotheses: positive horizon and positive descent coefficient are
--   exactly needed for the final normalization; no nonnegativity of the
--   certificate sequence is used.

open scoped BigOperators

/-- Uniform randomized-output certificates are bounded by expected descent.

If a terminal potential plus `c` times the finite certificate sum is bounded by
the initial potential, the terminal potential is bounded below by `Astar`, and
the output certificate is the uniform average over `{1, ..., N}`, then the
output certificate is bounded by `(A0 - Astar) / (c * N)`.

Layer: Layer1 | Gap: Level 1 (uniform randomized-output descent normalization)
Proof: subtract the terminal lower bound from the expected descent inequality,
  multiply the resulting numerator bound by the nonnegative normalizer
  `(c * N)⁻¹`, and rewrite the uniform average by field arithmetic.
Source: Mathlib finite sums over natural intervals and ordered real field
  arithmetic
Used in: nonconvex variance-reduced mirror descent final stationarity bound
  from expected descent and uniform randomized-output expansion
Book citation: book/FOML/NonconvexVarianceReducedMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex variance-reduced mirror descent -/
theorem uniform_output_bound_of_expected_descent
    (N : ℕ) (c A0 Astar outputCert : ℝ) (A cert : ℕ → ℝ)
    (hN_pos : 0 < N) (hc_pos : 0 < c)
    (hdescent :
      A (N + 1) + c * Finset.sum (Finset.Icc 1 N) cert ≤ A0)
    (hterminal : Astar ≤ A (N + 1))
    (hout :
      outputCert =
        (N : ℝ)⁻¹ * Finset.sum (Finset.Icc 1 N) cert) :
    outputCert ≤ (1 / (c * (N : ℝ))) * (A0 - Astar) := by
  classical
  let totalCert : ℝ := Finset.sum (Finset.Icc 1 N) cert
  have hweighted : c * totalCert ≤ A0 - Astar := by
    dsimp [totalCert]
    linarith
  have hN_real_pos : 0 < (N : ℝ) := by
    exact_mod_cast hN_pos
  have hscale_nonneg : 0 ≤ 1 / (c * (N : ℝ)) := by
    positivity
  rw [hout]
  calc
    (N : ℝ)⁻¹ * Finset.sum (Finset.Icc 1 N) cert =
        (1 / (c * (N : ℝ))) *
          (c * Finset.sum (Finset.Icc 1 N) cert) := by
          field_simp [hc_pos.ne', hN_real_pos.ne']
    _ ≤ (1 / (c * (N : ℝ))) * (A0 - Astar) :=
          mul_le_mul_of_nonneg_left hweighted hscale_nonneg


-- Batch 2 promoted from Staging/global_prefix_descent_of_epoch_descent.lean
-- Generalization plan (G0):
-- concept/name: fixed-length epoch descent converted to a one-based global prefix descent; orig was theorem_6_14_global_descent_from_epoch_descent.
-- generality used: natural fixed-length epoch indexing, real-valued potential and certificate sequences, scalar multiplier, and an initial potential upper bound; no measure, convexity, smoothness, oracle, or finite-dimensional assumptions.
-- portable call pattern: fixed-epoch convergence proofs for variance-reduced SGD, stochastic mirror descent, and proximal-gradient methods supply an epoch-local bound on `V` plus a within-epoch certificate sum and obtain the same global prefix bound after changing only `T`, `V`, `G`, `c`, and `initial`.
-- counterargument checked: this is not paper-local traceability because it packages the recurring fixed-epoch concatenation proof; it is not a one-line wrapper around Mathlib since it combines epoch decoding, prefix splitting, and induction over completed epochs.
-- coverage search: searched catalog/SOptLib for global prefix, epoch descent, epoch telescope, fixed-length block, and checked `summed_one_step_gap_bound_of_telescope`, `active_sum_objective_drop_add_scalar_budget`, `sum_Icc_one_add_eq_sum_Icc_one_add_shift`, and `global_index_epochOfIndex_stepOfIndex`; LeanSearch for fixed epoch local bound gave only unrelated infinite-sum/list bounds, so coverage is partial but not full.
-- minimal hypotheses: weakened the original initial equality to `V 1 ≤ initial`; all other hypotheses are needed to decode positive global indices and concatenate epoch-local sums.

/-- Epoch-local descent over fixed-length one-based blocks gives global prefix descent.

If every epoch block bounds the terminal potential plus the within-epoch
certificate sum by the potential at the epoch start, then every positive global
index satisfies the corresponding one-based prefix bound.

Layer: Layer1 | Gap: Level 1 (fixed-epoch descent to global prefix descent)
Proof: induct over completed epochs, split the global one-based prefix at the
  previous epoch boundary, compose the previous prefix bound with the current
  epoch descent, and decode an arbitrary positive global index by quotient and
  remainder.
Source: Mathlib finite sums over natural intervals and quotient-remainder
  arithmetic with SOptLib fixed-epoch indexing
Used in: nonconvex variance-reduced mirror descent conversion from per-epoch
  expected descent to an arbitrary global iteration prefix
Book citation: book/FOML/NonconvexVarianceReducedMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex variance-reduced mirror descent -/
theorem global_prefix_descent_of_epoch_descent
    (T : ℕ) (V G : ℕ → ℝ) (initial c : ℝ)
    (hT_pos : 0 < T)
    (hinitial : V 1 ≤ initial)
    (hEpoch :
      ∀ s t : ℕ, 1 ≤ t → t ≤ T →
        V (SOptLib.global_index T s (t + 1)) +
            c * Finset.sum (Finset.Icc 1 t)
              (fun j => G (SOptLib.global_index T s j))
          ≤ V (SOptLib.global_index T s 1)) :
    ∀ k : ℕ, 1 ≤ k →
      V (k + 1) + c * Finset.sum (Finset.Icc 1 k) G ≤ initial := by
  classical
  have hprefix :
      ∀ s t : ℕ, 1 ≤ t → t ≤ T →
        V (SOptLib.global_index T s (t + 1)) +
            c * Finset.sum (Finset.Icc 1 (SOptLib.global_index T s t)) G
          ≤ initial := by
    intro s
    induction s with
    | zero =>
        intro t ht_pos ht_epoch
        have hlocal :
            V (SOptLib.global_index T 0 (t + 1)) +
                c * Finset.sum (Finset.Icc 1 t)
                  (fun j => G (SOptLib.global_index T 0 j))
              ≤ V (SOptLib.global_index T 0 1) :=
          hEpoch 0 t ht_pos ht_epoch
        have hlocal' :
            V (SOptLib.global_index T 0 (t + 1)) +
                c * Finset.sum (Finset.Icc 1 (SOptLib.global_index T 0 t)) G
              ≤ V 1 := by
          simpa [SOptLib.global_index] using hlocal
        exact le_trans hlocal' hinitial
    | succ s ih =>
        intro t ht_pos ht_epoch
        let P : ℝ := Finset.sum (Finset.Icc 1 (SOptLib.global_index T s T)) G
        let L : ℝ :=
          Finset.sum (Finset.Icc 1 t)
            (fun j => G (SOptLib.global_index T (s + 1) j))
        have hprev :
            V (SOptLib.global_index T (s + 1) 1) + c * P ≤ initial := by
          have hprev0 := ih T (by exact Nat.succ_le_iff.mp hT_pos) le_rfl
          have hlink :
              SOptLib.global_index T s (T + 1) =
                SOptLib.global_index T (s + 1) 1 := by
            rw [SOptLib.global_index_def, SOptLib.global_index_def, Nat.succ_mul]
            omega
          rw [hlink] at hprev0
          simpa [P] using hprev0
        have hcurr :
            V (SOptLib.global_index T (s + 1) (t + 1)) + c * L
              ≤ V (SOptLib.global_index T (s + 1) 1) := by
          simpa [L] using hEpoch (s + 1) t ht_pos ht_epoch
        have hsplit :
            Finset.sum (Finset.Icc 1 (SOptLib.global_index T (s + 1) t)) G =
              P + L := by
          have h :=
            sum_Icc_one_add_eq_sum_Icc_one_add_shift
              G (SOptLib.global_index T s T) t
          simpa [P, L, SOptLib.global_index, Nat.succ_mul, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using h
        have hcombined :
            V (SOptLib.global_index T (s + 1) (t + 1)) + c * (P + L)
              ≤ initial := by
          have hlinear :
              V (SOptLib.global_index T (s + 1) (t + 1)) + c * L + c * P
                ≤ initial := by
            linarith
          have hrewrite :
              V (SOptLib.global_index T (s + 1) (t + 1)) + c * (P + L) =
                V (SOptLib.global_index T (s + 1) (t + 1)) + c * L + c * P := by
            ring
          rwa [hrewrite]
        rw [hsplit]
        exact hcombined
  intro k hk
  let s : ℕ := SOptLib.epochOfIndex T k
  let t : ℕ := SOptLib.stepOfIndex T k
  have ht_bounds : 1 ≤ t ∧ t ≤ T := by
    dsimp [t]
    exact SOptLib.stepOfIndex_mem_epoch (T := T) (k := k) hT_pos
  have hbound := hprefix s t ht_bounds.1 ht_bounds.2
  have hdecode : SOptLib.global_index T s t = k := by
    dsimp [s, t]
    simpa [SOptLib.stepOfIndex_eq_mod_add_one] using
      (SOptLib.global_index_epochOfIndex_stepOfIndex (T := T) (k := k) hk)
  have hdecode_succ : SOptLib.global_index T s (t + 1) = k + 1 := by
    unfold SOptLib.global_index at hdecode ⊢
    omega
  rw [← hdecode_succ]
  rw [← hdecode]
  exact hbound


-- From Staging/active_sum_scaled_alpha_sq_eq_global.lean

-- Generalization plan (G0):
-- G0.1 naming: active_sum_scaled_alpha_sq_eq_global (orig was:
--   stochastic_active_alpha_square_sum_eq_global). The name removes the
--   stochastic/paper theorem marker and names the active-coordinate to global
--   alpha-square budget transport used across conditional-gradient proofs.
-- G0.2 typeclass level used:
--   E: none; the proof is scalar finite-sum algebra.
--   measure: none; no integration or probability appears in this equality.
--   convexity: none; no geometric or convexity hypothesis is used.
-- G0.3 reusability — could instantiate:
--   1. finite-sum nonconvex conditional gradient, collecting active epoch
--      curvature terms into one global stepsize-square budget.
--   2. stochastic conditional gradient with recursive minibatches, transporting
--      active epoch variance-floor curvature terms to the global output window.
-- G0.4 search trace:
--   queries: ["active alpha square global", "Finset sum reindex multiply constant"]
--   top hits: ["stochastic_active_alpha_square_sum_eq_global",
--     "active_alpha_square_sum_eq_global_theorem716",
--     "integrable_const_mul_add_finset_sum_sub_finset_sum",
--     "integrable_finset_sum_const_mul"]
--   coverage: partial — target-file private lemmas are setup-specific; SOptLib
--     hits cover finite-sum integrability, not scalar reindexing of scaled
--     stepsize-square budgets.
-- G0.4 not-a-thin-wrapper rationale: the theorem packages an arbitrary
--   active/global partition identity with coefficient factoring and square-term
--   algebra, so call sites expose the budget transport instead of a local
--   `rw`/`ring` proof script.
-- G0.5 structural-content rationale: the declaration states the invariant that
--   any active-coordinate reindexing of alpha-square mass also transports the
--   smoothness-diameter scaled mass.
-- G0.5b name-body alignment: the theorem name promises an equality for scaled
--   active alpha-square sums, and the body proves exactly that equality.
-- G0.5c thin-wrapper self-detect: clean — body has multi-step finite-sum
--   congruence and scalar algebra beyond a direct alias of one existing lemma.
-- G0.5d minimal-hypothesis check: all already minimal; the only hypothesis is
--   the exact active/global alpha-square partition identity consumed by the
--   proof.

/-- A scaled active alpha-square sum reindexes to the scaled global alpha-square sum.

If the active coordinates `(i, j)` cover the global output window for the
alpha-square mass, then multiplying every active term by the same
smoothness-diameter scale `L * D^2` gives the same global scaled budget.

Layer: Layer1 | Gap: Level 0 (active-coordinate scalar budget reindexing)
Proof: rewrite the global alpha-square mass by the active/global partition,
  factor the common scale through the outer and inner finite sums, and finish
  by commutative semiring algebra.
Source: Mathlib finite big-operator scalar factoring over commutative semirings
Used in: nonconvex stochastic conditional-gradient collection of active epoch
  curvature terms into the global output-window alpha-square budget
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem active_sum_scaled_alpha_sq_eq_global
    {I J R : Type*} [CommSemiring R]
    (outer : Finset I) (inner : I → Finset J)
    (globalIndex : I → J → Nat) (alpha : Nat → R) (L D : R) (N : Nat)
    (hpartition :
      Finset.sum outer
          (fun i => Finset.sum (inner i)
            (fun j => alpha (globalIndex i j) ^ 2)) =
        Finset.sum (Finset.Icc 1 N) (fun k => alpha k ^ 2)) :
    Finset.sum outer
        (fun i => Finset.sum (inner i)
          (fun j => L * alpha (globalIndex i j) ^ 2 * D ^ 2)) =
      L * D ^ 2 * Finset.sum (Finset.Icc 1 N) (fun k => alpha k ^ 2) := by
  classical
  calc
    Finset.sum outer
        (fun i => Finset.sum (inner i)
          (fun j => L * alpha (globalIndex i j) ^ 2 * D ^ 2))
        = Finset.sum outer
            (fun i => Finset.sum (inner i)
              (fun j => (L * D ^ 2) * alpha (globalIndex i j) ^ 2)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
    _ = Finset.sum outer
        (fun i => (L * D ^ 2) *
          Finset.sum (inner i) (fun j => alpha (globalIndex i j) ^ 2)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [Finset.mul_sum]
    _ = (L * D ^ 2) *
        Finset.sum outer
          (fun i => Finset.sum (inner i)
            (fun j => alpha (globalIndex i j) ^ 2)) := by
          rw [Finset.mul_sum]
    _ = L * D ^ 2 * Finset.sum (Finset.Icc 1 N) (fun k => alpha k ^ 2) := by
          rw [hpartition]


-- From Staging/active_l1_error_sum_le_epoch_penalty_add_floor_mass.lean

-- Generalization plan (G0):
-- G0.1 naming: active_l1_error_sum_le_epoch_penalty_add_floor_mass
-- G0.2 typeclass level used:
--   E: none; the theorem is scalar finite-sum order algebra over `Real`.
--   measure: none; expectations have already been reduced to scalar `l1`
--     values before this aggregation step.
--   convexity: none; no convexity structure is used.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional gradient, aggregating active
--      estimator-error L1 contributions into an epoch penalty plus variance floor.
--   2. stochastic mirror descent or variance-reduced proximal-gradient,
--      collecting active minibatch residual L1 bounds into a full-window penalty
--      and a retained residual floor mass.
-- G0.4 search trace:
--   queries: ["active l1 error sum penalty floor mass",
--     "finset sum pointwise bound subset add mass",
--     "sum subset mul nonneg right le"]
--   top hits: ["normalizedOutputMass_sum_one",
--     "integrable_const_mul_add_finset_sum_sub_finset_sum",
--     "integral_sum_telescope_bound_of_pointwise_lower_bound",
--     "Finset.sum_subset_mul_nonneg_right_le",
--     "summed_one_step_gap_bound_of_telescope"]
--   coverage: partial — `Finset.sum_subset_mul_nonneg_right_le` supplies the
--     single-inner-set active-to-full enlargement, while no hit subsumes the
--     two-level pointwise aggregation with a separate floor coefficient times
--     the active mass.
-- G0.4 not-a-thin-wrapper rationale: the theorem packages the reusable
--   invariant that a pointwise active L1 error bound aggregates into a full
--   penalty window plus an unchanged active floor mass.
-- G0.5 structural-content rationale: the statement exposes the outer epoch
--   set, active/full inner windows, pointwise error bound, nonnegative missing
--   weights, and nonnegative penalty scale without paper setup notation.
-- G0.5b name-body alignment: the name promises an active L1-error sum bound
--   by an epoch penalty plus floor mass, and the theorem proves exactly that
--   scalar finite-sum inequality.
-- G0.5c thin-wrapper self-detect: clean — body combines nested pointwise
--   summation, finite-sum distributivity, active-to-full enlargement, and
--   monotone scaling by the penalty coefficient.
-- G0.5d minimal-hypothesis check: all already minimal; each hypothesis is
--   used directly at the corresponding pointwise, missing-term, or scale step.

/-- Aggregate active L1 error bounds into a full-window penalty plus floor mass.

If each active inner step has an L1 error bounded by a penalty contribution and
a floor contribution, and the active inner set sits inside a full inner window
whose missing weights are nonnegative, then the nested active sum is bounded by
the full-window penalty plus the same floor coefficient times active mass.

Layer: Layer1 | Gap: Level 1 (active-window L1 error aggregation)
Proof: sum the pointwise active bound, split the penalty and floor finite sums,
  enlarge the active penalty sum to the full inner window using nonnegative
  missing weights, and scale by the nonnegative penalty coefficient.
Source: Mathlib finite-sum order algebra and ordered real multiplication
Used in: stochastic nonconvex conditional-gradient active estimator-error L1
  aggregation with retained mini-batch variance floor
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem active_l1_error_sum_le_epoch_penalty_add_floor_mass
    {I J : Type*}
    (outer : Finset I) (active full : I → Finset J)
    (alpha l1 : I → J → ℝ) (M : I → ℝ) (L D floorCoeff : ℝ)
    (hpoint :
      ∀ i ∈ outer, ∀ j ∈ active i,
        alpha i j * D * l1 i j ≤
          L * D ^ 2 * (alpha i j * M i) + floorCoeff * alpha i j)
    (hsubset : ∀ i ∈ outer, active i ⊆ full i)
    (halpha_missing_nonneg :
      ∀ i ∈ outer, ∀ j ∈ full i, j ∉ active i → 0 ≤ alpha i j)
    (hM_nonneg : ∀ i ∈ outer, 0 ≤ M i)
    (hpenalty_nonneg : 0 ≤ L * D ^ 2) :
    (∑ i ∈ outer, ∑ j ∈ active i, alpha i j * D * l1 i j) ≤
      L * D ^ 2 *
        (∑ i ∈ outer, (∑ j ∈ full i, alpha i j) * M i) +
        floorCoeff *
          (∑ i ∈ outer, ∑ j ∈ active i, alpha i j) := by
  classical
  have hactive_to_full :
      (∑ i ∈ outer, ∑ j ∈ active i, alpha i j * M i) ≤
        ∑ i ∈ outer, (∑ j ∈ full i, alpha i j) * M i := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact Finset.sum_subset_mul_nonneg_right_le
      (active := active i) (full := full i) (a := alpha i) (M := M i)
      (hsubset := hsubset i hi)
      (ha_nonneg := halpha_missing_nonneg i hi)
      (hM_nonneg := hM_nonneg i hi)
  calc
    (∑ i ∈ outer, ∑ j ∈ active i, alpha i j * D * l1 i j)
        ≤
      ∑ i ∈ outer, ∑ j ∈ active i,
        (L * D ^ 2 * (alpha i j * M i) + floorCoeff * alpha i j) := by
          exact Finset.sum_le_sum (fun i hi =>
            Finset.sum_le_sum (fun j hj => hpoint i hi j hj))
    _ =
      L * D ^ 2 *
          (∑ i ∈ outer, ∑ j ∈ active i, alpha i j * M i) +
        floorCoeff *
          (∑ i ∈ outer, ∑ j ∈ active i, alpha i j) := by
          simp [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul,
            mul_assoc, mul_left_comm, mul_comm]
    _ ≤
      L * D ^ 2 *
          (∑ i ∈ outer, (∑ j ∈ full i, alpha i j) * M i) +
        floorCoeff *
          (∑ i ∈ outer, ∑ j ∈ active i, alpha i j) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hactive_to_full hpenalty_nonneg) le_rfl


-- From Staging/sum_scaled_l2_error_le_epoch_budget_add_variance_floor.lean

-- Generalization plan (G0):
-- G0.1 naming: sum_scaled_l2_error_le_epoch_budget_add_variance_floor
-- G0.2 typeclass level used:
--   E: none; Hilbert-space residuals have already been reduced to scalar
--     squared L2 error quantities.
--   measure: none; expectations enter only as real-valued `deltaSq` and
--     `epoch` scalars before this aggregation step.
--   convexity: none; no convexity or smoothness predicate is used beyond the
--     explicit positive scalar `L`.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional gradient, aggregating active
--      Lemma 7.5 squared estimator-error bounds into an epoch-difference
--      budget plus one mini-batch variance floor per active step.
--   2. variance-reduced proximal-gradient or stochastic mirror descent,
--      collecting nested inner-loop L2 residual bounds with a refresh variance
--      floor across active update windows.
-- G0.4 search trace:
--   queries: ["scaled l2 error epoch variance",
--     "Finset sum scaled square bound variance floor"]
--   top hits: ["epochRefresh_variance_floor",
--     "stochastic_active_delta_square_term_le_epochDiff_plus_variance",
--     "active_l1_error_sum_le_epoch_penalty_add_floor_mass",
--     "weighted_variance_sum_expectation_bound",
--     "summed_one_step_gap_bound_of_telescope"]
--   coverage: partial — hits cover single refresh variance bounds, L1 active
--     aggregation, or generic telescope/weighted variance sums, but none
--     subsumes the nested L2 pointwise-to-sum aggregation with scaling by
--     `1 / (2 * L)` and a cardinality-counted variance floor.
-- G0.4 not-a-thin-wrapper rationale: the theorem packages the reusable
--   invariant that a pointwise L2 residual bound with an epoch budget and a
--   constant variance floor remains valid after nested active-window summation
--   and smoothness scaling.
-- G0.5 structural-content rationale: the statement exposes the nested finite
--   windows, scalar residual budget, smoothness/batch denominators, and active
--   count identity without paper setup notation.
-- G0.5b name-body alignment: the name promises a scaled L2-error sum bound by
--   an epoch budget plus variance floor, and the theorem proves exactly that
--   real finite-sum inequality.
-- G0.5c thin-wrapper self-detect: clean — body combines pointwise monotone
--   scaling, nested finite-sum monotonicity, constant-floor splitting, and
--   ordered-field normalization.
-- G0.5d minimal-hypothesis check: all already minimal; `hL_pos` is used for
--   nonnegative scaling, and `hb_ne`/`hm_ne`/`hcount` are used only for the
--   denominator normalizations and active floor count.

/-- Aggregate nested L2 residual bounds into an epoch budget plus a variance
floor.

If each active inner residual square is bounded by an epoch-difference budget
and a constant variance floor, then after scaling by `1 / (2 * L)` and summing
over nested active windows, the result is bounded by the scaled epoch budget
plus the variance floor times the active step count.

Layer: Layer1 | Gap: Level 1 (nested L2 residual variance-floor aggregation)
Proof: multiply each pointwise residual bound by the nonnegative scale
  `1 / (2 * L)`, sum over nested finsets, split the constant floor from the
  nested sum, and rewrite the active count.
Source: Mathlib finite-sum order algebra and real ordered-field arithmetic
Used in: stochastic nonconvex conditional-gradient active squared
  estimator-error aggregation with Lemma 7.5 mini-batch variance floors
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem sum_scaled_l2_error_le_epoch_budget_add_variance_floor
    {I J : Type*} (outer : Finset I) (inner : I → Finset J)
    (L b m sigma N : ℝ) (deltaSq epoch : I → J → ℝ)
    (hL_pos : 0 < L) (hb_ne : b ≠ 0) (hm_ne : m ≠ 0)
    (hpoint :
      ∀ i ∈ outer, ∀ j ∈ inner i,
        deltaSq i j ≤ L ^ 2 / b * epoch i j + sigma ^ 2 / m)
    (hcount :
      Finset.sum outer (fun i => ((inner i).card : ℝ)) = N) :
    Finset.sum outer
        (fun i => Finset.sum (inner i)
          (fun j => (1 / (2 * L)) * deltaSq i j)) ≤
      Finset.sum outer
        (fun i => Finset.sum (inner i)
          (fun j => (L / (2 * b)) * epoch i j)) +
        N * sigma ^ 2 / (2 * L * m) := by
  classical
  let floor : ℝ := sigma ^ 2 / (2 * L * m)
  let Epoch : I → J → ℝ := fun i j => (L / (2 * b)) * epoch i j
  have hcoef_nonneg : 0 ≤ (1 / (2 * L) : ℝ) := by
    exact div_nonneg zero_le_one (by nlinarith [hL_pos])
  have hL_ne : L ≠ 0 := ne_of_gt hL_pos
  have htwoL_ne : 2 * L ≠ 0 := by nlinarith [hL_pos]
  have hpoint_scaled :
      ∀ i ∈ outer, ∀ j ∈ inner i,
        (1 / (2 * L)) * deltaSq i j ≤ Epoch i j + floor := by
    intro i hi j hj
    have hmul :=
      mul_le_mul_of_nonneg_left (hpoint i hi j hj) hcoef_nonneg
    calc
      (1 / (2 * L)) * deltaSq i j
          ≤ (1 / (2 * L)) *
              (L ^ 2 / b * epoch i j + sigma ^ 2 / m) := hmul
      _ = Epoch i j + floor := by
          dsimp [Epoch, floor]
          field_simp [hL_ne, htwoL_ne, hb_ne, hm_ne]
  have hsum_point :
      Finset.sum outer
          (fun i => Finset.sum (inner i)
            (fun j => (1 / (2 * L)) * deltaSq i j)) ≤
        Finset.sum outer
          (fun i => Finset.sum (inner i)
            (fun j => Epoch i j + floor)) := by
    exact Finset.sum_le_sum (fun i hi =>
      Finset.sum_le_sum (fun j hj => hpoint_scaled i hi j hj))
  have hsplit :
      Finset.sum outer
          (fun i => Finset.sum (inner i) (fun j => Epoch i j + floor)) =
        Finset.sum outer
          (fun i => Finset.sum (inner i) (fun j => Epoch i j)) +
        floor * Finset.sum outer (fun i => ((inner i).card : ℝ)) := by
    exact Finset.sum_sum_add_const
      (outer := outer) (inner := inner) (A := Epoch) (c := floor)
  calc
    Finset.sum outer
        (fun i => Finset.sum (inner i)
          (fun j => (1 / (2 * L)) * deltaSq i j))
        ≤
      Finset.sum outer
        (fun i => Finset.sum (inner i) (fun j => Epoch i j + floor)) :=
        hsum_point
    _ =
      Finset.sum outer
        (fun i => Finset.sum (inner i) (fun j => Epoch i j)) +
        floor * Finset.sum outer (fun i => ((inner i).card : ℝ)) := hsplit
    _ =
      Finset.sum outer
        (fun i => Finset.sum (inner i)
          (fun j => (L / (2 * b)) * epoch i j)) +
        N * sigma ^ 2 / (2 * L * m) := by
        rw [hcount]
        dsimp [Epoch, floor]
        ring


-- From Staging/integral_finset_epochDiff_le_sum_bounds.lean

-- Generalization plan (G0):
-- G0.1 naming: integral_finset_epoch_difference_le_sum_bounds (orig was:
--   stochastic_active_epochDiff_integral_le_scalar_sum). The name keeps the
--   recognized epoch-difference budget role while making the statement a
--   finite-index integral bound, with no paper theorem or algorithm marker.
-- G0.2 typeclass level used:
--   E: none; the theorem is scalar after upstream iterate-difference estimates
--      have produced real-valued summands and scalar budgets.
--   measure: arbitrary probability measure `(mu : Measure Omega)` via
--      [IsProbabilityMeasure mu], exactly for evaluating integrals of constant
--      scalar budgets.
--   convexity: none; the result is finite-sum expectation majorization.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional gradient within-epoch iterate-drift
--      expectation budgets from per-step diameter bounds.
--   2. variance-reduced mirror descent and SARAH/SPIDER-style epochwise
--      estimator-drift controls from pointwise step-size-square budgets.
-- G0.4 search trace:
--   queries: ["epoch difference integral bound",
--     "integral of finite sum bounded by sum pointwise bounds"]
--   top hits: ["integral_epochSquaredDifferenceSum_le_diameter_sq_mul_alpha_sq_sum",
--     "finite_window_zero_mean_plus_quadratic_noise_integral_bound",
--     "integral_sum_telescope_bound_of_pointwise_lower_bound",
--     "selected_block_second_moment_integral_le_sum_bounds",
--     "MeasureTheory.integral_finset_sum"]
--   coverage: strengthens integral_epochSquaredDifferenceSum_le_diameter_sq_mul_alpha_sq_sum —
--     this theorem works over any finite index set and scalar summands, rather
--     than only closed natural intervals of squared norm increments.
-- G0.4 not-a-thin-wrapper rationale: the theorem packages the reusable
--   quantifier structure converting per-index pointwise deterministic budgets
--   into an expected finite-window budget by integral finite-sum linearity,
--   integral monotonicity, probability normalization, and scalar factoring.
-- G0.5 structural-content rationale: no def or structure is introduced; the
--   theorem adds a Layer1 expectation-budget bridge over arbitrary finite
--   families of scalar epoch-difference summands.
-- G0.5c thin-wrapper self-detect: clean — body combines finite-sum Bochner
--   linearity, integral monotonicity against constant budgets, finite-sum order,
--   probability-space constant integrals, and real algebra.
-- G0.5d minimal-hypothesis check: all already minimal; integrability and
--   pointwise bounds are required only on the finite index set, and the
--   probability typeclass is exactly the constant-integral normalization used.

/-- A finite sum of epoch-difference summands has expectation bounded by the
corresponding deterministic scalar budget sum.

If every scalar summand in a finite epoch window is integrable and pointwise
bounded by `bound i * D^2`, then the expected finite sum is bounded by
`D^2 * sum bound`.

Layer: Layer1 | Gap: Level 1 (finite epoch-difference expectation budget)
Proof: commute the Bochner integral with the finite sum, apply integral
  monotonicity to each pointwise constant budget on a probability measure, sum
  the resulting inequalities, and factor the common scalar square.
Source: Mathlib Bochner finite-sum integral linearity, probability constant
  integrals, finite-sum order, and ordered-ring algebra
Used in: stochastic nonconvex conditional-gradient within-epoch iterate-drift
  budget for estimator second-moment accumulation
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem integral_finset_epoch_difference_le_sum_bounds
    {Omega I : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (idxs : Finset I) (epoch_diff : I -> Omega -> Real)
    (bound : I -> Real) (D : Real)
    (hterm_int :
      forall i, i ∈ idxs -> Integrable (epoch_diff i) mu)
    (hpoint :
      forall i, i ∈ idxs -> forall omega,
        epoch_diff i omega <= bound i * D ^ 2) :
    ∫ omega, Finset.sum idxs (fun i => epoch_diff i omega) ∂mu <=
      D ^ 2 * Finset.sum idxs bound := by
  classical
  have hterm_bound :
      forall i, i ∈ idxs ->
        ∫ omega, epoch_diff i omega ∂mu <= bound i * D ^ 2 := by
    intro i hi
    have hconst_int :
        Integrable (fun _omega : Omega => bound i * D ^ 2) mu :=
      integrable_const _
    have hle_int :
        ∫ omega, epoch_diff i omega ∂mu <=
          ∫ _omega, bound i * D ^ 2 ∂mu := by
      exact integral_mono (hterm_int i hi) hconst_int (by
        intro omega
        exact hpoint i hi omega)
    simpa [integral_const, probReal_univ] using hle_int
  calc
    ∫ omega, Finset.sum idxs (fun i => epoch_diff i omega) ∂mu
        = Finset.sum idxs (fun i => ∫ omega, epoch_diff i omega ∂mu) := by
          exact integral_finset_sum (s := idxs) (f := epoch_diff) hterm_int
    _ <= Finset.sum idxs (fun i => bound i * D ^ 2) := by
          exact Finset.sum_le_sum hterm_bound
    _ = (Finset.sum idxs bound) * D ^ 2 := by
          rw [Finset.sum_mul]
    _ = D ^ 2 * Finset.sum idxs bound := by
          ring


-- From Staging/active_epochDiff_scaled_sum_le_half_global_alpha_sq.lean

-- Generalization plan (G0):
-- G0.1 naming: active_epoch_difference_scaled_sum_le_half_global_alpha_sq
--   (orig was: stochastic_active_epochDiff_term_le_half_alpha_square_budget).
--   The name removes the stochastic/paper theorem marker and names the active
--   epoch-difference scaling budget in Mathlib-style snake_case.
-- G0.2 typeclass level used:
--   E: none; Hilbert-space and measure estimates have already been reduced to
--      scalar epoch-difference summands and scalar triangular budgets.
--   measure: none; integration is consumed upstream, and this theorem is a
--      deterministic finite-sum aggregation step.
--   convexity: none; no convexity or smoothness structure is used beyond the
--      explicit scalar `L`.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional gradient recursive minibatch
--      epoch-difference contribution to the Wolfe-gap budget.
--   2. variance-reduced mirror descent and SPIDER/SARAH inner-loop drift
--      budgets where local epoch-difference estimates are charged to a global
--      stepsize-square mass.
-- G0.4 search trace:
--   queries: ["nested sum scaled budget", "finset sum bound half square"]
--   top hits: ["sum_scaled_l2_error_le_epoch_budget_add_variance_floor",
--     "active_sum_scaled_alpha_sq_eq_global",
--     "residual_second_moment_sum_le_half_alpha_square_budget",
--     "integral_finset_epoch_difference_le_sum_bounds"]
--   coverage: partial — overlaps with residual_second_moment_sum_le_half_alpha_square_budget,
--     but this theorem strengthens that scalar aggregation shape by allowing a
--     real positive batch scalar and by exposing the unscaled epoch-difference
--     local budget before the common `L / (2 * b)` multiplier is applied.
-- G0.4 not-a-thin-wrapper rationale: the theorem packages the invariant that
--   unscaled local epoch-difference bounds aggregate through a nested local
--   budget and cancel the positive batch scalar to leave a half global
--   stepsize-square contribution.
-- G0.5 structural-content rationale: no def or structure is introduced; the
--   theorem exposes the active nested window, local epoch budget, global mass,
--   and smoothness/diameter scaling independently of any algorithm setup record.
-- G0.5b name-body alignment: the name promises a theorem bounding a scaled
--   active epoch-difference sum by a half global alpha-square budget, and the
--   body proves exactly that property.
-- G0.5c thin-wrapper self-detect: clean — body combines nested finite-sum
--   monotonicity, scalar factoring, triangular-budget transport, and
--   ordered-field cancellation, not a direct alias of one existing theorem.
-- G0.5d minimal-hypothesis check: all already minimal; `0 < b` is used for
--   coefficient nonnegativity and cancellation, `0 <= L` for monotone scaling,
--   the pointwise epoch bound is used only on active summands, and `hbudget`
--   is the direct nested local-budget sum bound consumed by the proof.

/-- A scaled active epoch-difference sum is controlled by a half global
stepsize-square budget.

If each active epoch-difference summand is bounded by `D^2` times its local
triangular predecessor budget, and the total triangular budget is at most
`b` times the global stepsize-square mass, then the common `L / (2 * b)`
scale cancels the batch budget and leaves the standard `1 / 2` global
contribution.

Layer: Layer1 | Gap: Level 1 (active epoch-difference triangular budget)
Proof: sum the pointwise local epoch-difference bounds after multiplying by the
  nonnegative common scale, apply the nested local-budget bound, and cancel the
  positive batch scalar by ordered-field arithmetic.
Source: Mathlib finite big-operator inequalities and real ordered-field
  arithmetic
Used in: stochastic nonconvex conditional-gradient epoch-difference contribution
  to the recursive minibatch Wolfe-gap budget
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem active_epoch_difference_scaled_sum_le_half_global_alpha_sq
    {I J : Type*} (outer : Finset I) (inner : I -> Finset J)
    (epoch localBudget : I -> J -> ℝ) (globalSq L b D : ℝ)
    (hb_pos : 0 < b)
    (hL_nonneg : 0 <= L)
    (hpoint :
      forall i, i ∈ outer -> forall j, j ∈ inner i ->
        epoch i j <= D ^ 2 * localBudget i j)
    (hbudget :
        Finset.sum outer
          (fun i => Finset.sum (inner i) (fun j => localBudget i j)) <=
        b * globalSq) :
    Finset.sum outer
        (fun i => Finset.sum (inner i)
          (fun j => (L / (2 * b)) * epoch i j)) <=
      L * D ^ 2 * (1 / 2 * globalSq) := by
  classical
  let c : ℝ := (L / (2 * b)) * D ^ 2
  have hb_ne : b ≠ 0 := ne_of_gt hb_pos
  have hscale_nonneg : 0 <= L / (2 * b) := by
    exact div_nonneg hL_nonneg (by positivity)
  have hc_nonneg : 0 <= c := by
    dsimp [c]
    exact mul_nonneg hscale_nonneg (sq_nonneg D)
  have hsum_to_budget :
      Finset.sum outer
          (fun i => Finset.sum (inner i)
            (fun j => (L / (2 * b)) * epoch i j)) <=
        c * Finset.sum outer
          (fun i => Finset.sum (inner i) (fun j => localBudget i j)) := by
    calc
      Finset.sum outer
          (fun i => Finset.sum (inner i)
            (fun j => (L / (2 * b)) * epoch i j))
          <=
        Finset.sum outer
          (fun i => Finset.sum (inner i)
            (fun j => c * localBudget i j)) := by
            exact Finset.sum_le_sum (fun i hi =>
              Finset.sum_le_sum (fun j hj => by
                have hscaled :=
                  mul_le_mul_of_nonneg_left (hpoint i hi j hj) hscale_nonneg
                dsimp [c] at hscaled ⊢
                nlinarith))
      _ = c * Finset.sum outer
            (fun i => Finset.sum (inner i) (fun j => localBudget i j)) := by
            simp [c, Finset.mul_sum, Finset.sum_mul, mul_comm]
  calc
    Finset.sum outer
        (fun i => Finset.sum (inner i)
          (fun j => (L / (2 * b)) * epoch i j))
        <= c * Finset.sum outer
            (fun i => Finset.sum (inner i) (fun j => localBudget i j)) :=
          hsum_to_budget
    _ <= c * (b * globalSq) := mul_le_mul_of_nonneg_left hbudget hc_nonneg
    _ = L * D ^ 2 * (1 / 2 * globalSq) := by
          dsimp [c]
          field_simp [hb_ne]


-- From Staging/active_triangular_prefix_budget_le_global_sq_sum.lean

-- Generalization plan (G0):
-- G0.1 naming: active_triangular_prefix_budget_le_global_sq_sum
-- G0.2 typeclass level used:
--   E: none; this is a real-valued finite-sum budget lemma, not a normed-space lemma.
--   measure: none; no measure-theoretic structure is used.
--   convexity: none; no convexity structure is used.
-- G0.3 reusability — could instantiate:
--   1. nonconvex stochastic conditional gradient epochwise predecessor stepsize-square budget
--   2. variance-reduced mirror descent inner-loop triangular stepsize accumulation
-- G0.4 search trace:
--   queries: ["active triangular prefix budget", "finite sum triangular local bound global square",
--     "active triangular predecessor sum"]
--   top hits: ["budget_bound_le_half_of_budget_choice",
--     "finite_window_zero_mean_plus_quadratic_noise_integral_bound",
--     "convexOn_weighted_average_le_weighted_sum",
--     "active_triangular_predecessor_sum_le_batch_mul_global_sum"]
--   coverage: partial — the predecessor hit proves local prefix counting from
--     prefix-closure hypotheses, while this theorem isolates the aggregation step
--     from arbitrary local triangular bounds to a global square budget.
-- G0.4 not-a-thin-wrapper rationale: the theorem packages the reusable invariant
--   that local triangular prefix bounds can be summed, reindexed into a global
--   square budget, and enlarged from a local scalar `T` to a global scalar `b`.
-- G0.5 structural-content rationale: the statement exposes the epoch family,
--   active inner windows, global index map, local triangular budget hypothesis, and
--   active/global reindexing equality without paper setup fields.
-- G0.5c thin-wrapper self-detect: clean — body combines finite-sum monotonicity,
--   scalar factoring, active/global reindexing, square nonnegativity, and ordered
--   scalar multiplication.
-- G0.5d minimal-hypothesis check: all already minimal; the local triangular
--   estimate, active/global reindexing equality, and scalar comparison are used
--   exactly at the aggregation step.

/-- Local triangular prefix square budgets aggregate to a global square budget.

If every active inner window has a lower-triangular predecessor square sum
bounded by `T` times its active square mass, and the active square masses
reindex to a global natural window, then any scalar `b ≥ T` bounds the total
triangular budget by `b` times the global square mass.

Layer: Layer1 | Gap: Level 1 (active-prefix triangular budget aggregation)
Proof: sum the local triangular inequalities, factor the common scalar, rewrite
  the active mass by the global reindexing identity, and enlarge the scalar
  using nonnegativity of the global square sum.
Source: Mathlib finite sums over natural intervals and ordered real
  multiplication
Used in: nonconvex stochastic conditional-gradient epochwise predecessor
  stepsize-square budget
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/main_theorem/proof/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic conditional gradient -/
theorem active_triangular_prefix_budget_le_global_sq_sum
    {I : Type*} (outer : Finset I) (inner : I → Finset ℕ)
    (globalIndex : I → ℕ → ℕ) (alpha : ℕ → ℝ) (T b : ℝ) (N : ℕ)
    (hlocal :
      ∀ s ∈ outer,
        Finset.sum (inner s)
            (fun j => Finset.sum (Finset.Icc 2 j)
              (fun i => alpha (globalIndex s (i - 1)) ^ 2)) ≤
          T * Finset.sum (inner s) (fun r => alpha (globalIndex s r) ^ 2))
    (hactive_eq_global :
      Finset.sum outer
          (fun s => Finset.sum (inner s)
            (fun r => alpha (globalIndex s r) ^ 2)) =
        Finset.sum (Finset.Icc 1 N) (fun k => alpha k ^ 2))
    (hT_le_b : T ≤ b) :
    Finset.sum outer
        (fun s => Finset.sum (inner s)
          (fun j => Finset.sum (Finset.Icc 2 j)
            (fun i => alpha (globalIndex s (i - 1)) ^ 2))) ≤
      b * Finset.sum (Finset.Icc 1 N) (fun k => alpha k ^ 2) := by
  classical
  let activeSq : ℝ :=
    Finset.sum outer
      (fun s => Finset.sum (inner s)
        (fun r => alpha (globalIndex s r) ^ 2))
  let globalSq : ℝ := Finset.sum (Finset.Icc 1 N) (fun k => alpha k ^ 2)
  have hsum_to_active :
      Finset.sum outer
          (fun s => Finset.sum (inner s)
            (fun j => Finset.sum (Finset.Icc 2 j)
              (fun i => alpha (globalIndex s (i - 1)) ^ 2))) ≤
        T * activeSq := by
    calc
      Finset.sum outer
          (fun s => Finset.sum (inner s)
            (fun j => Finset.sum (Finset.Icc 2 j)
              (fun i => alpha (globalIndex s (i - 1)) ^ 2)))
          ≤ Finset.sum outer
              (fun s => T *
                Finset.sum (inner s) (fun r => alpha (globalIndex s r) ^ 2)) := by
              exact Finset.sum_le_sum hlocal
      _ = T * activeSq := by
              dsimp [activeSq]
              rw [Finset.mul_sum]
  have hglobal_nonneg : 0 ≤ globalSq := by
    dsimp [globalSq]
    exact Finset.sum_nonneg (fun k _hk => sq_nonneg (alpha k))
  have hTb : T * globalSq ≤ b * globalSq :=
    mul_le_mul_of_nonneg_right hT_le_b hglobal_nonneg
  calc
    Finset.sum outer
        (fun s => Finset.sum (inner s)
          (fun j => Finset.sum (Finset.Icc 2 j)
            (fun i => alpha (globalIndex s (i - 1)) ^ 2)))
        ≤ T * activeSq := hsum_to_active
    _ = T * globalSq := by
      dsimp [activeSq, globalSq]
      rw [hactive_eq_global]
    _ ≤ b * globalSq := hTb


-- From Staging/weighted_gap_sum_bound_of_active_one_step_printed.lean

-- Generalization plan (G0):
-- G0.1 naming: weighted_gap_sum_bound_of_active_one_step_with_variance_floor
--   (kept planner name; the concept is a weighted active one-step gap
--   aggregation with the source/displayed variance-floor coefficient)
-- G0.2 typeclass level used:
--   E: none; Hilbert-space residuals and Wolfe gaps have already been reduced
--     to scalar real terms before this aggregation step.
--   measure: none; expectations enter only through scalar `weightedGap`,
--     `obj`, and `sq` quantities supplied by earlier stochastic lemmas.
--   convexity: none; no convexity or smoothness predicate is used except
--     through the explicit scalar budget hypotheses.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional gradient, summing active expected
--      Wolfe-gap one-step inequalities into the Theorem 7.17 numerator budget.
--   2. variance-reduced Frank-Wolfe or proximal-gradient inner loops,
--      aggregating active stochastic gap bounds with objective-drop,
--      second-moment, and deterministic stepsize-square budgets.
-- G0.4 search trace:
--   queries: ["weighted gap telescope",
--     "finset sum le telescope alpha square",
--     "summed one step gap bound telescope"]
--   top hits: ["finite_weighted_gap_sum_bound_theorem716",
--     "stochastic_weighted_gap_sum_bound_theorem717_printed",
--     "weighted_output_gap_le_initial_potential_add_noise",
--     "summed_one_step_gap_bound_of_telescope",
--     "residual_second_moment_sum_le_half_alpha_square_budget"]
--   coverage: partial — `summed_one_step_gap_bound_of_telescope` sums a
--     single flat descent/variance/correction inequality, while this theorem
--     packages active-window reindexing, three nested component budgets,
--     variance-floor retention, and penalty absorption.
-- G0.4 not-a-thin-wrapper rationale: the theorem adds the reusable invariant
--   that an active reindexed weighted-gap numerator is controlled by separate
--   objective, second-moment, alpha-square, penalty, and variance-floor budgets.
-- G0.5 structural-content rationale: the statement exposes the global output
--   window, active epoch windows, reindexing map, one-step bound, and aggregate
--   budget inequalities without paper setup notation.
-- G0.5b name-body alignment: the name promises a weighted active one-step gap
--   sum bound and the theorem proves exactly that scalar finite-sum bound.
-- G0.5c thin-wrapper self-detect: clean — body combines reindexing,
--   nested finite-sum monotonicity, component-sum splitting, budget
--   substitution, and penalty absorption.
-- G0.5d minimal-hypothesis check: all already minimal; every hypothesis is
--   used directly in the reindexing, one-step, component-budget, or final
--   penalty-absorption step.

/-- Bound a reindexed weighted gap sum from active one-step component budgets.

If a weighted global gap numerator reindexes onto active epoch windows, every
active term is bounded by objective-drop, second-moment, and alpha-square
components, and those components satisfy separate aggregate budgets, then the
global numerator is bounded by the objective budget, absorbed penalty budget,
and retained variance floor.

Layer: Layer1 | Gap: Level 1 (active weighted-gap budget aggregation)
Proof: rewrite the global weighted sum by the active-window partition, sum the
  one-step inequalities over the nested active windows, split component sums,
  apply the aggregate budgets, and absorb the second-moment and alpha-square
  budgets into the penalty budget.
Source: Mathlib finite big-operator inequalities and ordered real arithmetic
Used in: stochastic nonconvex conditional-gradient active expected Wolfe-gap
  numerator aggregation with the displayed mini-batch variance floor
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem weighted_gap_sum_bound_of_active_one_step_with_variance_floor
    {K I J : Type*} (global : Finset K) (outer : Finset I)
    (active : I → Finset J) (index : I → J → K)
    (weightedGap : K → ℝ) (obj sq alpha : I → J → ℝ)
    (objBudget sqBudget alphaBudget penaltyBudget varianceFloor : ℝ)
    (hpartition :
      Finset.sum global weightedGap =
        Finset.sum outer
          (fun i => Finset.sum (active i) (fun j => weightedGap (index i j))))
    (hstep :
      ∀ i ∈ outer, ∀ j ∈ active i,
        weightedGap (index i j) ≤ obj i j + sq i j + alpha i j)
    (hobj :
      Finset.sum outer (fun i => Finset.sum (active i) (fun j => obj i j)) ≤
        objBudget)
    (hsq :
      Finset.sum outer (fun i => Finset.sum (active i) (fun j => sq i j)) ≤
        sqBudget + varianceFloor)
    (halpha :
      Finset.sum outer (fun i => Finset.sum (active i) (fun j => alpha i j)) =
        alphaBudget)
    (hbudget : sqBudget + alphaBudget ≤ penaltyBudget) :
    Finset.sum global weightedGap ≤ objBudget + penaltyBudget + varianceFloor := by
  classical
  have hstep_sum :
      Finset.sum outer
          (fun i => Finset.sum (active i) (fun j => weightedGap (index i j))) ≤
        Finset.sum outer
          (fun i => Finset.sum (active i) (fun j => obj i j + sq i j + alpha i j)) := by
    exact Finset.sum_le_sum (fun i hi =>
      Finset.sum_le_sum (fun j hj => hstep i hi j hj))
  have hsplit :
      Finset.sum outer
          (fun i => Finset.sum (active i) (fun j => obj i j + sq i j + alpha i j)) =
        Finset.sum outer (fun i => Finset.sum (active i) (fun j => obj i j)) +
          Finset.sum outer (fun i => Finset.sum (active i) (fun j => sq i j)) +
          Finset.sum outer (fun i => Finset.sum (active i) (fun j => alpha i j)) := by
    simp only [Finset.sum_add_distrib]
  calc
    Finset.sum global weightedGap
        =
      Finset.sum outer
        (fun i => Finset.sum (active i) (fun j => weightedGap (index i j))) :=
        hpartition
    _ ≤
      Finset.sum outer
        (fun i => Finset.sum (active i) (fun j => obj i j + sq i j + alpha i j)) :=
        hstep_sum
    _ =
      Finset.sum outer (fun i => Finset.sum (active i) (fun j => obj i j)) +
        Finset.sum outer (fun i => Finset.sum (active i) (fun j => sq i j)) +
        Finset.sum outer (fun i => Finset.sum (active i) (fun j => alpha i j)) :=
        hsplit
    _ ≤ objBudget + (sqBudget + varianceFloor) + alphaBudget := by
        exact add_le_add (add_le_add hobj hsq) (le_of_eq halpha)
    _ ≤ objBudget + penaltyBudget + varianceFloor := by
        linarith [hbudget]


-- From Staging/weighted_gap_sum_bound_of_active_one_step_with_l1_floor.lean

-- Generalization plan (G0):
-- G0.1 naming: weighted_gap_sum_bound_of_active_one_step_with_l1_floor
--   (kept planner name; the concept is an active one-step weighted gap
--   aggregation retaining a separate L1 residual floor contribution).
-- G0.2 typeclass level used:
--   E: none; Hilbert-space residuals and Wolfe gaps have already been reduced
--     to scalar real terms before this Layer1 aggregation step.
--   measure: none; expectations enter only through scalar component functions
--     supplied by earlier stochastic lemmas.
--   convexity: none; no convexity or smoothness predicate is used except
--     through explicit scalar one-step and aggregate budget hypotheses.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional gradient, summing active expected
--      Wolfe-gap one-step inequalities while retaining the Lemma 7.5 L1 floor.
--   2. variance-reduced Frank-Wolfe or proximal-gradient inner loops,
--      aggregating active stochastic gap bounds with separate objective-drop,
--      second-moment, deterministic stepsize-square, and L1 residual budgets.
-- G0.4 search trace:
--   queries: ["weighted gap sum bound",
--     "finite sum weighted inequality l1 floor",
--     "active one step gap variance floor"]
--   top hits: ["weighted_gap_sum_bound_of_active_one_step_with_variance_floor",
--     "active_l1_error_sum_le_epoch_penalty_add_floor_mass",
--     "summed_one_step_gap_bound_of_telescope",
--     "stochastic_weighted_gap_sum_bound_theorem717_with_l1_floor",
--     "finite_weighted_gap_sum_bound_theorem716"]
--   coverage: partial — `weighted_gap_sum_bound_of_active_one_step_with_variance_floor`
--     has the same active-window partition skeleton but only three components
--     and one retained floor; `active_l1_error_sum_le_epoch_penalty_add_floor_mass`
--     proves the L1 component budget but does not combine the full numerator.
-- G0.4 not-a-thin-wrapper rationale: the theorem adds the reusable invariant
--   that an active reindexed weighted-gap numerator is controlled by four
--   separately proved component budgets plus independent variance and L1 floors.
-- G0.5 structural-content rationale: the statement exposes the global output
--   window, active epoch windows, reindexing map, one-step bound, component
--   aggregate budgets, and final budget absorption without paper setup notation.
-- G0.5b name-body alignment: the name promises a weighted active one-step gap
--   sum bound with an L1 floor and the theorem proves exactly that finite-sum
--   scalar bound.
-- G0.5c thin-wrapper self-detect: clean — body combines reindexing, nested
--   finite-sum monotonicity, four-component sum splitting, budget substitution,
--   and final floor-preserving absorption.
-- G0.5d minimal-hypothesis check: all already minimal; every hypothesis is
--   used directly in reindexing, one-step summation, component-budget
--   substitution, or final absorption.

/-- Bound a reindexed weighted gap sum with a retained L1 floor contribution.

If a weighted global gap numerator reindexes onto active epoch windows, every
active term is bounded by objective-drop, second-moment, alpha-square, and L1
components, and those components satisfy separate aggregate budgets, then the
global numerator is bounded by the absorbed deterministic budget plus both the
second-moment variance floor and the L1 floor mass.

Layer: Layer1 | Gap: Level 1 (active weighted-gap budget aggregation with L1 floor)
Proof: rewrite the global weighted sum by the active-window partition, sum the
  one-step inequalities over nested active windows, split the four component
  sums, apply the aggregate budgets, and retain the variance and L1 floors.
Source: Mathlib finite big-operator inequalities and ordered real arithmetic
Used in: stochastic nonconvex conditional-gradient active expected Wolfe-gap
  numerator aggregation with a retained mini-batch L1 residual floor
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem weighted_gap_sum_bound_of_active_one_step_with_l1_floor
    {K I J : Type*} (global : Finset K) (outer : Finset I)
    (active : I → Finset J) (index : I → J → K)
    (weightedGap : K → ℝ) (obj sq alpha l1 : I → J → ℝ)
    (objBudget sqBudget alphaBudget l1Budget varianceFloor floorMass
      totalBudget : ℝ)
    (hpartition :
      Finset.sum global weightedGap =
        Finset.sum outer
          (fun i => Finset.sum (active i) (fun j => weightedGap (index i j))))
    (hstep :
      ∀ i ∈ outer, ∀ j ∈ active i,
        weightedGap (index i j) ≤ obj i j + sq i j + alpha i j + l1 i j)
    (hobj :
      Finset.sum outer (fun i => Finset.sum (active i) (fun j => obj i j)) ≤
        objBudget)
    (hsq :
      Finset.sum outer (fun i => Finset.sum (active i) (fun j => sq i j)) ≤
        sqBudget + varianceFloor)
    (halpha :
      Finset.sum outer (fun i => Finset.sum (active i) (fun j => alpha i j)) =
        alphaBudget)
    (hl1 :
      Finset.sum outer (fun i => Finset.sum (active i) (fun j => l1 i j)) ≤
        l1Budget + floorMass)
    (hbudget : sqBudget + alphaBudget + l1Budget ≤ totalBudget) :
    Finset.sum global weightedGap ≤
      objBudget + totalBudget + varianceFloor + floorMass := by
  classical
  have hstep_sum :
      Finset.sum outer
          (fun i => Finset.sum (active i) (fun j => weightedGap (index i j))) ≤
        Finset.sum outer
          (fun i => Finset.sum (active i)
            (fun j => obj i j + sq i j + alpha i j + l1 i j)) := by
    exact Finset.sum_le_sum (fun i hi =>
      Finset.sum_le_sum (fun j hj => hstep i hi j hj))
  have hsplit :
      Finset.sum outer
          (fun i => Finset.sum (active i)
            (fun j => obj i j + sq i j + alpha i j + l1 i j)) =
        Finset.sum outer (fun i => Finset.sum (active i) (fun j => obj i j)) +
          Finset.sum outer (fun i => Finset.sum (active i) (fun j => sq i j)) +
          Finset.sum outer (fun i => Finset.sum (active i) (fun j => alpha i j)) +
          Finset.sum outer (fun i => Finset.sum (active i) (fun j => l1 i j)) := by
    simp only [Finset.sum_add_distrib]
  calc
    Finset.sum global weightedGap
        =
      Finset.sum outer
        (fun i => Finset.sum (active i) (fun j => weightedGap (index i j))) :=
        hpartition
    _ ≤
      Finset.sum outer
        (fun i => Finset.sum (active i)
          (fun j => obj i j + sq i j + alpha i j + l1 i j)) :=
        hstep_sum
    _ =
      Finset.sum outer (fun i => Finset.sum (active i) (fun j => obj i j)) +
        Finset.sum outer (fun i => Finset.sum (active i) (fun j => sq i j)) +
        Finset.sum outer (fun i => Finset.sum (active i) (fun j => alpha i j)) +
        Finset.sum outer (fun i => Finset.sum (active i) (fun j => l1 i j)) :=
        hsplit
    _ ≤ objBudget + (sqBudget + varianceFloor) + alphaBudget +
        (l1Budget + floorMass) := by
        exact add_le_add (add_le_add (add_le_add hobj hsq) (le_of_eq halpha)) hl1
    _ ≤ objBudget + totalBudget + varianceFloor + floorMass := by
        linarith [hbudget]


-- From Staging/weighted_gap_sum_bound_of_active_one_step_young_variance.lean

-- Generalization plan (G0):
-- G0.1 naming: weighted_gap_sum_bound_of_active_one_step_young_variance
--   (kept planner name; the concept is a weighted active one-step gap
--   aggregation after Young absorption doubles the variance-floor contribution).
-- G0.2 typeclass level used:
--   E: none; Hilbert-space Wolfe-gap and residual estimates have already been
--     reduced to scalar real one-step and budget inequalities.
--   measure: none; expectations enter only through scalar component functions
--     supplied by earlier stochastic lemmas.
--   convexity: none; no convexity or smoothness predicate is used except
--     through explicit scalar one-step and aggregate budget hypotheses.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional gradient, summing active expected
--      Wolfe-gap one-step inequalities after Young absorption of the residual
--      L1 term, with a doubled mini-batch variance floor.
--   2. variance-reduced Frank-Wolfe or proximal-gradient inner loops,
--      aggregating active stochastic gap bounds where a half second-moment
--      estimate is doubled by a Young-absorbed descent inequality.
-- G0.4 search trace:
--   queries: ["weighted gap sum Young variance",
--     "active one step weighted gap variance",
--     "finite sum inequality split components variance floor Young absorption",
--     "Finset sum less or equal split addition real arithmetic"]
--   top hits: ["weighted_gap_sum_bound_of_active_one_step_with_variance_floor",
--     "weighted_gap_sum_bound_of_active_one_step_with_l1_floor",
--     "summed_one_step_gap_bound_of_telescope",
--     "Finset.sum_le_sum",
--     "Finset.sum_le_sum_of_subset_of_nonneg"]
--   coverage: partial — existing active weighted-gap lemmas share the
--     reindexing skeleton but do not expose the `SqHalf`/`Sq` doubling that
--     turns a half variance floor into the Young-variance floor.
-- G0.4 not-a-thin-wrapper rationale: the theorem adds the reusable invariant
--   that a nested active-window one-step bound with a doubled second-moment
--   component is controlled by objective, half-square, Young alpha, and final
--   absorption budgets.
-- G0.5 structural-content rationale: the statement exposes the global output
--   window, active epoch windows, reindexing map, one-step bound, half-square
--   budget, doubling identity, Young alpha budget, and final absorption without
--   paper setup notation.
-- G0.5b name-body alignment: the name promises a weighted active one-step gap
--   sum bound for the Young-variance route and the theorem proves exactly that
--   finite-sum scalar bound.
-- G0.5c thin-wrapper self-detect: clean — body combines reindexing, nested
--   finite-sum monotonicity, three-component splitting, half-square doubling,
--   budget substitution, and Young-variance absorption.
-- G0.5d minimal-hypothesis check: all already minimal; every hypothesis is
--   used directly in reindexing, one-step summation, component-budget
--   substitution, square-term doubling, or final absorption.

/-- Bound a reindexed weighted gap sum after Young absorption doubles variance.

If a weighted global gap numerator reindexes onto active epoch windows, every
active term is bounded by objective-drop, doubled second-moment, and Young
alpha-square components, and the doubled second-moment component is related to
a half-scale budget, then the global numerator is bounded by the objective
budget, the absorbed deterministic Young budget, and the doubled variance
floor.

Layer: Layer1 | Gap: Level 1 (active weighted-gap Young-variance aggregation)
Proof: rewrite the global weighted sum by the active-window partition, sum the
  one-step inequalities over nested active windows, split component sums, double
  the half-scale second-moment budget, and absorb the deterministic Young
  terms into the final epoch budget.
Source: Mathlib finite big-operator inequalities and ordered real arithmetic
Used in: stochastic nonconvex conditional-gradient active expected Wolfe-gap
  numerator aggregation after Young absorption of the estimator-error L1 term
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem weighted_gap_sum_bound_of_active_one_step_young_variance
    {K I J : Type*} (global : Finset K) (outer : Finset I)
    (active : I → Finset J) (index : I → J → K)
    (weightedGap : K → ℝ) (obj sq sqHalf alphaYoung : I → J → ℝ)
    (objBudget coeff globalSq epochPenalty varianceFloor : ℝ)
    (hpartition :
      Finset.sum global weightedGap =
        Finset.sum outer
          (fun i => Finset.sum (active i) (fun j => weightedGap (index i j))))
    (hstep :
      ∀ i ∈ outer, ∀ j ∈ active i,
        weightedGap (index i j) ≤ obj i j + sq i j + alphaYoung i j)
    (hobj :
      Finset.sum outer (fun i => Finset.sum (active i) (fun j => obj i j)) ≤
        objBudget)
    (hsq_half :
      Finset.sum outer (fun i => Finset.sum (active i) (fun j => sqHalf i j)) ≤
        coeff * (1 / 2 * globalSq) + varianceFloor / 2)
    (hSq_eq :
      Finset.sum outer (fun i => Finset.sum (active i) (fun j => sq i j)) =
        2 * Finset.sum outer
          (fun i => Finset.sum (active i) (fun j => sqHalf i j)))
    (halphaYoung :
      Finset.sum outer (fun i => Finset.sum (active i) (fun j => alphaYoung i j)) =
        (3 / 2) * coeff * globalSq)
    (hbudget :
      coeff * globalSq + (3 / 2) * coeff * globalSq ≤
        coeff * (3 / 2 * globalSq + epochPenalty)) :
    Finset.sum global weightedGap ≤
      objBudget + coeff * (3 / 2 * globalSq + epochPenalty) + varianceFloor := by
  classical
  have hstep_sum :
      Finset.sum outer
          (fun i => Finset.sum (active i) (fun j => weightedGap (index i j))) ≤
        Finset.sum outer
          (fun i => Finset.sum (active i)
            (fun j => obj i j + sq i j + alphaYoung i j)) := by
    exact Finset.sum_le_sum (fun i hi =>
      Finset.sum_le_sum (fun j hj => hstep i hi j hj))
  have hsplit :
      Finset.sum outer
          (fun i => Finset.sum (active i)
            (fun j => obj i j + sq i j + alphaYoung i j)) =
        Finset.sum outer (fun i => Finset.sum (active i) (fun j => obj i j)) +
          Finset.sum outer (fun i => Finset.sum (active i) (fun j => sq i j)) +
          Finset.sum outer (fun i => Finset.sum (active i) (fun j => alphaYoung i j)) := by
    simp only [Finset.sum_add_distrib]
  have hsq :
      Finset.sum outer (fun i => Finset.sum (active i) (fun j => sq i j)) ≤
        coeff * globalSq + varianceFloor := by
    calc
      Finset.sum outer (fun i => Finset.sum (active i) (fun j => sq i j))
          =
        2 * Finset.sum outer
          (fun i => Finset.sum (active i) (fun j => sqHalf i j)) := hSq_eq
      _ ≤ 2 * (coeff * (1 / 2 * globalSq) + varianceFloor / 2) := by
          exact mul_le_mul_of_nonneg_left hsq_half (by norm_num)
      _ = coeff * globalSq + varianceFloor := by ring
  calc
    Finset.sum global weightedGap
        =
      Finset.sum outer
        (fun i => Finset.sum (active i) (fun j => weightedGap (index i j))) :=
        hpartition
    _ ≤
      Finset.sum outer
        (fun i => Finset.sum (active i)
          (fun j => obj i j + sq i j + alphaYoung i j)) :=
        hstep_sum
    _ =
      Finset.sum outer (fun i => Finset.sum (active i) (fun j => obj i j)) +
        Finset.sum outer (fun i => Finset.sum (active i) (fun j => sq i j)) +
        Finset.sum outer (fun i => Finset.sum (active i) (fun j => alphaYoung i j)) :=
        hsplit
    _ ≤ objBudget + (coeff * globalSq + varianceFloor) +
        (3 / 2) * coeff * globalSq := by
        exact add_le_add (add_le_add hobj hsq) (le_of_eq halphaYoung)
    _ ≤ objBudget + coeff * (3 / 2 * globalSq + epochPenalty) +
        varianceFloor := by
        linarith [hbudget]

/-- An accelerated two-Bregman recurrence becomes a composite gap recurrence
under a reference-point model bound.

If the raw accelerated composite recurrence has been obtained from the
upper-model, two-Bregman descent, and residual-tail hypotheses, and the
linearized model plus Bregman curvature term is bounded by the composite
objective at the reference point, then the recurrence can be written directly
for the objective gap `Psi xBar - Psi xRef`.

Layer: Layer1 | Gap: Level 1 (accelerated composite gap recurrence)
Proof: invoke the raw accelerated two-Bregman recurrence, scale the pointwise
  model bound by the nonnegative acceleration weight, and rearrange the scalar
  objective terms into a reference-point gap recurrence.
Source: Lan accelerated composite-gradient estimate-sequence algebra and
  Mathlib real inner-product/order arithmetic APIs
Used in: stochastic accelerated gradient descent one-step Bregman recurrence
  at an optimal reference point before finite-window telescoping
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem accelerated_composite_gap_recurrence_of_two_bregman_descent_of_model_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Psi f h : E → ℝ) (V : E → E → ℝ) (grad : E → E)
    (alpha gamma mu L M : ℝ)
    (prevBar prevCenter xUnder z xPlus xBar xRef g eta : E)
    (halpha_nonneg : 0 ≤ alpha)
    (hgamma_pos : 0 < gamma)
    (hnoise_decomp : g = grad xUnder + eta)
    (hUpper :
      Psi xBar ≤
        (1 - alpha) * Psi prevBar +
          alpha * (f xUnder + ⟪grad xUnder, z - xUnder⟫_ℝ + h z) +
          (L / 2) * (alpha * ‖z - xPlus‖) ^ 2 +
          M * (alpha * ‖z - xPlus‖))
    (htwo_bregman :
      gamma * (⟪g, z⟫_ℝ + h z) +
          (gamma * mu) * V xUnder z + (1 : ℝ) * V prevCenter z ≤
        gamma * (⟪g, xRef⟫_ℝ + h xRef) +
          (gamma * mu) * V xUnder xRef +
          (1 : ℝ) * V prevCenter xRef -
            ((gamma * mu) + (1 : ℝ)) * V z xRef)
    (htail :
      L / 2 * (alpha * ‖z - xPlus‖) ^ 2 +
          M * (alpha * ‖z - xPlus‖) -
          alpha * ((1 / gamma) * V prevCenter z + mu * V xUnder z) -
          alpha * ⟪eta, z - xPlus⟫_ℝ ≤
        alpha * gamma * (M + ‖eta‖) ^ 2 /
          (2 * (1 + mu * gamma - L * alpha * gamma)))
    (hmodel_bound :
      f xUnder + ⟪grad xUnder, xRef - xUnder⟫_ℝ + h xRef +
          mu * V xUnder xRef ≤
        Psi xRef) :
    Psi xBar - Psi xRef ≤
      (1 - alpha) * (Psi prevBar - Psi xRef) +
        alpha / gamma *
          (V prevCenter xRef - (1 + mu * gamma) * V z xRef) +
        alpha * gamma * (M + ‖eta‖) ^ 2 /
          (2 * (1 + mu * gamma - L * alpha * gamma)) +
        alpha * ⟪eta, xRef - xPlus⟫_ℝ := by
  have hrec :=
    accelerated_composite_recurrence_of_two_bregman_descent
      Psi f h V grad alpha gamma mu L M prevBar prevCenter xUnder z xPlus
      xBar xRef g eta halpha_nonneg hgamma_pos hnoise_decomp hUpper
      htwo_bregman htail
  have hmodel_scaled :
      alpha *
        (f xUnder + ⟪grad xUnder, xRef - xUnder⟫_ℝ + h xRef +
          mu * V xUnder xRef) ≤
        alpha * Psi xRef :=
    mul_le_mul_of_nonneg_left hmodel_bound halpha_nonneg
  linarith

/-- An accelerated weighted Bregman window is bounded by its initial budget.

For a scalar potential sequence `Vseq`, a coefficient bridge gives a weighted
finite-window telescope. After rewriting an attached one-based window to
`Finset.Icc`, dropping a nonnegative terminal weighted tail, and scaling by a
nonnegative outer coefficient, the whole window is bounded by the normalized
initial potential budget.

Layer: Layer1 | Gap: Level 1 (accelerated Bregman-window initial budget)
Proof: apply the weighted scalar telescope with terminal tail, drop the
  nonnegative terminal contribution, reindex the attached finite window, scale
  by the nonnegative outer coefficient, and normalize the initial coefficient.
Source: Mathlib finite sums over natural intervals and ordered-field
  arithmetic, with the SOptLib weighted scalar telescope
Used in: stochastic accelerated gradient descent expected-gap proof after the
  pathwise lower-model reduction, where the weighted Bregman window is replaced
  by the initial potential budget
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem accelerated_bregman_window_le_initial_budget
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (c beta Vseq : ℕ → R) (GammaK gammaOne initialV : R)
    (k : ℕ) (hk : 1 ≤ k)
    (hGammaK_nonneg : 0 ≤ GammaK)
    (hV_nonneg : ∀ n, 1 ≤ n → n < k → 0 ≤ Vseq n)
    (hc_mono : ∀ n, 1 ≤ n → n < k → c (n + 1) ≤ c n * beta n)
    (htail_nonneg : 0 ≤ c k * beta k * Vseq k)
    (hc_one : c 1 = 1 / gammaOne)
    (hV_zero : Vseq 0 = initialV) :
    GammaK *
        Finset.sum (Finset.Icc 1 k).attach (fun t =>
          c t.1 * (Vseq (t.1 - 1) - beta t.1 * Vseq t.1)) ≤
      GammaK / gammaOne * initialV := by
  classical
  have hattach :
      Finset.sum (Finset.Icc 1 k).attach (fun t =>
          c t.1 * (Vseq (t.1 - 1) - beta t.1 * Vseq t.1)) =
        Finset.sum (Finset.Icc 1 k) (fun t =>
          c t * (Vseq (t - 1) - beta t * Vseq t)) := by
    simpa using
      (Finset.sum_attach (Finset.Icc 1 k)
        (fun t : ℕ => c t * (Vseq (t - 1) - beta t * Vseq t)))
  have htelescope :
      Finset.sum (Finset.Icc 1 k) (fun t =>
          c t * (Vseq (t - 1) - beta t * Vseq t)) ≤
        c 1 * Vseq 0 :=
    le_trans
      (sum_weighted_sub_mul_le_first_sub_tail c beta Vseq k hk
        hV_nonneg hc_mono)
      (sub_le_self (c 1 * Vseq 0) htail_nonneg)
  have hscaled :
      GammaK *
          Finset.sum (Finset.Icc 1 k) (fun t =>
            c t * (Vseq (t - 1) - beta t * Vseq t)) ≤
        GammaK * (c 1 * Vseq 0) :=
    mul_le_mul_of_nonneg_left htelescope hGammaK_nonneg
  have hinitial :
      GammaK * (c 1 * Vseq 0) = GammaK / gammaOne * initialV := by
    rw [hc_one, hV_zero]
    ring
  calc
    GammaK *
        Finset.sum (Finset.Icc 1 k).attach (fun t =>
          c t.1 * (Vseq (t.1 - 1) - beta t.1 * Vseq t.1))
        =
      GammaK *
        Finset.sum (Finset.Icc 1 k) (fun t =>
          c t * (Vseq (t - 1) - beta t * Vseq t)) := by
          rw [hattach]
    _ ≤ GammaK * (c 1 * Vseq 0) := hscaled
    _ = GammaK / gammaOne * initialV := hinitial

/-- A nonnegative scalar multiple of a finite sum has expectation bounded by
the same scalar multiple of the summed per-index expectation budgets.

If every summand in a finite window is integrable and its integral is bounded
by a deterministic budget, then the integral of the scaled finite window is
bounded by the scaled sum of those budgets.

Layer: Layer1 | Gap: Level 1 (scaled finite-window expectation aggregation)
Proof: commute the Bochner integral through the finite sum, apply the per-index
  integral bounds with `Finset.sum_le_sum`, and preserve the inequality under
  multiplication by the nonnegative scale.
Source: Mathlib Bochner integral finite-sum linearity and ordered real
  finite-sum algebra
Used in: stochastic accelerated gradient descent residual-window aggregation
  after one-step Delta expectation bounds
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem integral_scaled_finset_sum_le_scaled_sum_of_integral_bounds
    {Omega I : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    (idxs : Finset I) (summand : I -> Omega -> Real) (bound : I -> Real)
    (scale : Real)
    (hsummand_int :
      forall i, i ∈ idxs -> Integrable (summand i) mu)
    (hsummand_bound :
      forall i, i ∈ idxs -> ∫ omega, summand i omega ∂mu <= bound i)
    (hscale_nonneg : 0 <= scale) :
    ∫ omega, scale * Finset.sum idxs (fun i => summand i omega) ∂mu <=
      scale * Finset.sum idxs bound := by
  classical
  have hsum_bound :
      Finset.sum idxs (fun i => ∫ omega, summand i omega ∂mu) <=
        Finset.sum idxs bound := by
    exact Finset.sum_le_sum hsummand_bound
  calc
    ∫ omega, scale * Finset.sum idxs (fun i => summand i omega) ∂mu
        = scale * ∫ omega, Finset.sum idxs (fun i => summand i omega) ∂mu := by
          rw [integral_const_mul]
    _ = scale * Finset.sum idxs (fun i => ∫ omega, summand i omega ∂mu) := by
          rw [integral_finset_sum idxs hsummand_int]
    _ <= scale * Finset.sum idxs bound := by
          exact mul_le_mul_of_nonneg_left hsum_bound hscale_nonneg

/-- A two-center prox step gives the accelerated composite gap recurrence.

This is the deterministic assembly layer above the normalized gap recurrence:
the raw upper model is rewritten through the accelerated average identity, the
convex two-center prox minimizer gives the Bregman descent inequality, the
weighted displacement and completion-square facts absorb the stochastic tail,
and the existing gap recurrence theorem supplies the telescopable boundary.

Layer: Layer1 | Gap: Level 1 (two-center prox-step gap recurrence assembly)
Proof: normalize the upper model with `xBar - xUnder = alpha • (z - xPlus)`,
  derive the two-center Bregman descent inequality from the abstract argmin
  theorem, absorb the smooth/noise tail, and invoke the composite gap recurrence.
Source: Lan accelerated composite-gradient estimate-sequence algebra,
  Mathlib convex segment calculus, and real inner-product/order arithmetic APIs
Used in: stochastic accelerated gradient descent generated-kernel prox step
  before the finite-window Bregman telescope
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/steps/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem accelerated_composite_gap_recurrence_of_two_center_prox_step
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (Psi f h : E → ℝ) (V : E → E → ℝ) (objGrad bregGrad : E → E)
    (alpha gamma mu L M : ℝ)
    (prevBar prevCenter xUnder z xRef xPlus xBar g eta : E)
    (halpha_nonneg : 0 ≤ alpha)
    (hgamma_pos : 0 < gamma)
    (hmu_nonneg : 0 ≤ mu)
    (hp_convex : ConvexOn ℝ X (fun u => gamma * (⟪g, u⟫_ℝ + h u)))
    (hz_mem : z ∈ X)
    (hxRef_mem : xRef ∈ X)
    (hnoise_decomp : g = objGrad xUnder + eta)
    (hV_segment_deriv :
      ∀ (a z u : E), z ∈ X →
        let d : E := u - z
        let β : ℝ → ℝ := fun t =>
          if _ht : t ∈ Set.Icc (0 : ℝ) 1 then
            V a (AffineMap.lineMap z u t) - V a z
          else 0
        HasDerivWithinAt β
          ⟪bregGrad z - bregGrad a, d⟫_ℝ
          (Set.Icc (0 : ℝ) 1) 0)
    (hV_three :
      ∀ a b c : E,
        V a c = V a b + ⟪bregGrad b - bregGrad a, c - b⟫_ℝ + V b c)
    (h_opt :
      ∀ u, u ∈ X →
        gamma * (⟪g, z⟫_ℝ + h z) +
            (gamma * mu) * V xUnder z + (1 : ℝ) * V prevCenter z ≤
          gamma * (⟪g, u⟫_ℝ + h u) +
            (gamma * mu) * V xUnder u + (1 : ℝ) * V prevCenter u)
    (havg_under : xBar - xUnder = alpha • (z - xPlus))
    (hUpper_raw :
      Psi xBar ≤
        (1 - alpha) * Psi prevBar +
          alpha * (f xUnder + ⟪objGrad xUnder, z - xUnder⟫_ℝ + h z) +
          (L / 2) * ‖xBar - xUnder‖ ^ 2 +
          M * ‖xBar - xUnder‖)
    (hweighted_absorb :
      ((1 + mu * gamma) / (2 * gamma)) * ‖z - xPlus‖ ^ 2 ≤
        (1 / gamma) * V prevCenter z + mu * V xUnder z)
    (hDeltaSquare :
      alpha *
          (M * ‖z - xPlus‖ - ⟪eta, z - xPlus⟫_ℝ -
            (1 + mu * gamma - L * alpha * gamma) /
              (2 * gamma) * ‖z - xPlus‖ ^ 2) ≤
        alpha * gamma * (M + ‖eta‖) ^ 2 /
          (2 * (1 + mu * gamma - L * alpha * gamma)))
    (hmodel_bound :
      f xUnder + ⟪objGrad xUnder, xRef - xUnder⟫_ℝ + h xRef +
          mu * V xUnder xRef ≤
        Psi xRef) :
    Psi xBar - Psi xRef ≤
      (1 - alpha) * (Psi prevBar - Psi xRef) +
        alpha / gamma *
          (V prevCenter xRef - (1 + mu * gamma) * V z xRef) +
        alpha * gamma * (M + ‖eta‖) ^ 2 /
          (2 * (1 + mu * gamma - L * alpha * gamma)) +
        alpha * ⟪eta, xRef - xPlus⟫_ℝ := by
  let breg : ℝ := (1 / gamma) * V prevCenter z + mu * V xUnder z
  let D : ℝ := 1 + mu * gamma - L * alpha * gamma
  have hnorm_avg_under :
      ‖xBar - xUnder‖ = alpha * ‖z - xPlus‖ := by
    rw [havg_under, norm_smul]
    simp [Real.norm_eq_abs, abs_of_nonneg halpha_nonneg]
  have hUpper :
      Psi xBar ≤
        (1 - alpha) * Psi prevBar +
          alpha * (f xUnder + ⟪objGrad xUnder, z - xUnder⟫_ℝ + h z) +
          (L / 2) * (alpha * ‖z - xPlus‖) ^ 2 +
          M * (alpha * ‖z - xPlus‖) := by
    simpa [hnorm_avg_under] using hUpper_raw
  have hgamma_nonneg : 0 ≤ gamma := le_of_lt hgamma_pos
  let p : E → ℝ := fun u => gamma * (⟪g, u⟫_ℝ + h u)
  have htwo_bregman_raw :=
    two_bregman_argmin_descent
      X p V bregGrad (by simpa [p] using hp_convex)
      (uHat := z) (xTilde := xUnder) (yTilde := prevCenter)
      (mu1 := gamma * mu) (mu2 := (1 : ℝ))
      hz_mem (mul_nonneg hgamma_nonneg hmu_nonneg) (by norm_num)
      hV_segment_deriv hV_three (by
        intro u hu
        simpa [p] using h_opt u hu) xRef hxRef_mem
  have htwo_bregman :
      gamma * (⟪g, z⟫_ℝ + h z) +
          (gamma * mu) * V xUnder z + (1 : ℝ) * V prevCenter z ≤
        gamma * (⟪g, xRef⟫_ℝ + h xRef) +
          (gamma * mu) * V xUnder xRef +
          (1 : ℝ) * V prevCenter xRef -
            ((gamma * mu) + (1 : ℝ)) * V z xRef := by
    simpa [p] using htwo_bregman_raw
  have hBregScaled :
      alpha * (((D + L * alpha * gamma) / (2 * gamma)) *
          ‖z - xPlus‖ ^ 2) ≤
        alpha * breg := by
    have hident :
        ((D + L * alpha * gamma) / (2 * gamma)) * ‖z - xPlus‖ ^ 2 =
          ((1 + mu * gamma) / (2 * gamma)) * ‖z - xPlus‖ ^ 2 := by
      dsimp [D]
      ring
    rw [hident]
    exact mul_le_mul_of_nonneg_left hweighted_absorb halpha_nonneg
  have htail :
      L / 2 * (alpha * ‖z - xPlus‖) ^ 2 +
          M * (alpha * ‖z - xPlus‖) -
          alpha * ((1 / gamma) * V prevCenter z + mu * V xUnder z) -
          alpha * ⟪eta, z - xPlus⟫_ℝ ≤
        alpha * gamma * (M + ‖eta‖) ^ 2 /
          (2 * (1 + mu * gamma - L * alpha * gamma)) := by
    have htail0 :=
      smooth_quadratic_tail_absorption_of_bregman_and_completion_square
        (a := alpha) (L := L) (M := M) (gamma := gamma) (D := D)
        (breg := breg) (tailNoise := (0 : ℝ)) (δ := eta)
        (d := z - xPlus) hgamma_pos hBregScaled hDeltaSquare
    simpa [breg, D] using htail0
  exact
    accelerated_composite_gap_recurrence_of_two_bregman_descent_of_model_bound
      Psi f h V objGrad alpha gamma mu L M
      prevBar prevCenter xUnder z xPlus xBar xRef g eta
      halpha_nonneg hgamma_pos hnoise_decomp hUpper htwo_bregman htail
      hmodel_bound

/-- A one-step Bregman recurrence controls the scaled state square.

If the current endpoint has a one-sided squared-distance lower bound through
the Bregman term and the one-step recurrence still contains the negative
terminal Bregman contribution, then the scaled endpoint state square is bounded
by the previous gap, previous Bregman budget, stochastic tail, noise inner
product, and the live current objective decrement.

Layer: Layer1 | Gap: Level 1 (Bregman recurrence to metric state-square step)
Proof: scale the pointwise squared-distance-to-Bregman lower bound by the
  nonnegative recurrence coefficient, normalize the scalar coefficient, isolate
  the terminal Bregman budget from the recurrence, and compose the inequalities.
Source: Lan accelerated stochastic-gradient estimate-sequence algebra and
  Mathlib real inner-product/order arithmetic APIs
Used in: stochastic accelerated gradient descent conversion of a one-step
  Bregman recurrence into terminal state-square control before telescoping
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/steps/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem state_sq_step_of_bregman_recurrence
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Psi : E → ℝ) (V : E → E → ℝ)
    (alpha gamma mu L M : ℝ)
    (prevX prevBar z xStar xPlus xBar eta : E)
    (hgamma_ne : gamma ≠ 0)
    (hcoef_nonneg : 0 ≤ alpha * (1 + mu * gamma) / (2 * gamma))
    (hsq_to_V : ‖z - xStar‖ ^ 2 ≤ 2 * V z xStar)
    (hbreg :
      Psi xBar - Psi xStar ≤
        (1 - alpha) * (Psi prevBar - Psi xStar) +
          alpha / gamma *
            (V prevX xStar - (1 + mu * gamma) * V z xStar) +
          alpha * gamma * (M + ‖eta‖) ^ 2 /
            (2 * (1 + mu * gamma - L * alpha * gamma)) +
          alpha * ⟪eta, xStar - xPlus⟫_ℝ) :
    alpha * (1 + mu * gamma) / (2 * gamma) * ‖z - xStar‖ ^ 2 ≤
      (1 - alpha) * (Psi prevBar - Psi xStar) +
        alpha / gamma * V prevX xStar +
        alpha * gamma * (M + ‖eta‖) ^ 2 /
          (2 * (1 + mu * gamma - L * alpha * gamma)) +
        alpha * ⟪eta, xStar - xPlus⟫_ℝ -
        (Psi xBar - Psi xStar) := by
  have hmetric :
      alpha * (1 + mu * gamma) / (2 * gamma) * ‖z - xStar‖ ^ 2 ≤
        alpha / gamma * ((1 + mu * gamma) * V z xStar) := by
    have hmul := mul_le_mul_of_nonneg_left hsq_to_V hcoef_nonneg
    calc
      alpha * (1 + mu * gamma) / (2 * gamma) * ‖z - xStar‖ ^ 2
          ≤ alpha * (1 + mu * gamma) / (2 * gamma) * (2 * V z xStar) := hmul
      _ = alpha / gamma * ((1 + mu * gamma) * V z xStar) := by
            field_simp [hgamma_ne]
  have hV_budget :
      alpha / gamma * ((1 + mu * gamma) * V z xStar) ≤
        (1 - alpha) * (Psi prevBar - Psi xStar) +
          alpha / gamma * V prevX xStar +
          alpha * gamma * (M + ‖eta‖) ^ 2 /
            (2 * (1 + mu * gamma - L * alpha * gamma)) +
          alpha * ⟪eta, xStar - xPlus⟫_ℝ -
          (Psi xBar - Psi xStar) := by
    nlinarith
  exact hmetric.trans hV_budget

/-- Finite-window weighted state control closes a two-component state-square
integrability induction.

Suppose the current state-square term at time `n + 1` can be extracted from an
integrable finite window of nonnegative weighted state-square terms, and the
companion state-square term at time `n + 1` is integrable whenever the previous
companion term and current state term are integrable. Then both components are
integrable at every natural time.

Layer: Layer1 | Gap: Level 1 (finite-window state-square integrability induction)
Proof: use strong induction on time; for the successor state, extract the
  terminal nonnegative summand from the integrable weighted finite window, then
  apply the supplied companion-state transport step.
Source: Mathlib natural-number strong induction, finite-sum order, and Bochner
  integrability closure APIs
Used in: stochastic accelerated gradient descent generated-state L2
  regularity after a finite-window Bregman/Gamma telescope
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem finite_window_state_sq_integrable_of_weighted_window_recurrence
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (stateSq xBarSq : ℕ → Ω → ℝ) (coeff : ℕ → ℝ)
    (hstate_zero : Integrable (stateSq 0) P)
    (hxBar_zero : Integrable (xBarSq 0) P)
    (hweighted_window :
      ∀ n : ℕ,
        (∀ m : ℕ, m < n + 1 →
          Integrable (stateSq m) P ∧ Integrable (xBarSq m) P) →
        Integrable
          (fun ω => Finset.sum (Finset.Icc 1 (n + 1))
            (fun t => coeff t * stateSq t ω)) P)
    (hstateSq_meas : ∀ n : ℕ, AEStronglyMeasurable (stateSq n) P)
    (hcoeff_pos : ∀ n : ℕ, 0 < coeff (n + 1))
    (hcoeff_nonneg :
      ∀ n : ℕ, ∀ t ∈ Finset.Icc 1 (n + 1), 0 ≤ coeff t)
    (hstateSq_nonneg :
      ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ t ∈ Finset.Icc 1 (n + 1), 0 ≤ stateSq t ω)
    (hxBar_step :
      ∀ n : ℕ,
        Integrable (xBarSq n) P →
        Integrable (stateSq (n + 1)) P →
        Integrable (xBarSq (n + 1)) P) :
    ∀ n : ℕ, Integrable (stateSq n) P ∧ Integrable (xBarSq n) P := by
  classical
  intro n
  refine Nat.strong_induction_on n ?_
  intro k ih
  cases k with
  | zero =>
      exact ⟨hstate_zero, hxBar_zero⟩
  | succ n =>
      have hprefix :
          ∀ m : ℕ, m < n + 1 →
            Integrable (stateSq m) P ∧ Integrable (xBarSq m) P := by
        intro m hm
        exact ih m hm
      have hstate_succ :
          Integrable (stateSq (n + 1)) P := by
        have hsum := hweighted_window n hprefix
        have hk_mem : n + 1 ∈ Finset.Icc 1 (n + 1) := by
          simp
        exact
          integrable_of_le_integrable_weighted_finset_sum
            (s := Finset.Icc 1 (n + 1)) (k := n + 1) (c := coeff)
            (Y := stateSq) hk_mem hsum (hstateSq_meas (n + 1))
            (hcoeff_pos n) (hcoeff_nonneg n) (hstateSq_nonneg n)
      have ih_n :
          Integrable (stateSq n) P ∧ Integrable (xBarSq n) P :=
        ih n (Nat.lt_succ_self n)
      exact ⟨hstate_succ, hxBar_step n ih_n.2 hstate_succ⟩

/-- Positive-time auxiliary squared L2 regularity follows from recursive state
L2 regularity and a predecessor transport step.

If both components of a recursive state are square-integrable around a fixed
center at every natural time, and each positive-time auxiliary point inherits
square-integrability from the previous state, then the auxiliary point is
square-integrable at every positive time.

Layer: Layer1 | Gap: Level 1 (positive-time auxiliary L2 closure)
Proof: reindex a positive natural time as the successor of its predecessor,
  read the two recursive state L2 facts at that predecessor, and apply the
  supplied auxiliary transport step.
Source: Mathlib natural-number subtype reindexing and Bochner integrability APIs
Used in: stochastic accelerated gradient descent auxiliary multiplier
  square-integrability after recursive generated-state L2 closure
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem positive_time_auxiliary_sq_integrable_of_recursive_state_l2
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {P : Measure Ω}
    (xStar : E) (state stateBar : ℕ → Ω → E)
    (xPlus : {n : ℕ // 1 ≤ n} → Ω → E)
    (hstate_l2 :
      ∀ n : ℕ,
        Integrable (fun ω => ‖xStar - state n ω‖ ^ 2) P ∧
          Integrable (fun ω => ‖xStar - stateBar n ω‖ ^ 2) P)
    (hxPlus_step :
      ∀ n : ℕ,
        Integrable (fun ω => ‖xStar - state n ω‖ ^ 2) P →
        Integrable (fun ω => ‖xStar - stateBar n ω‖ ^ 2) P →
        Integrable
          (fun ω =>
            ‖xStar -
              xPlus ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n)⟩ ω‖ ^ 2) P) :
    ∀ t : {n : ℕ // 1 ≤ n},
      Integrable (fun ω => ‖xStar - xPlus t ω‖ ^ 2) P := by
  intro t
  let n : ℕ := t.1 - 1
  have ht :
      (⟨n + 1, Nat.succ_le_succ (Nat.zero_le n)⟩ : {m : ℕ // 1 ≤ m}) = t := by
    apply Subtype.ext
    exact Nat.sub_add_cancel t.2
  have hprev := hstate_l2 n
  simpa [ht] using hxPlus_step n hprev.1 hprev.2

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: weighted-potential inequality rescaling with endpoint coefficient
--   normalization; orig was weighted_potential_contraction_rescale_to_eq37.
-- generality used: finite index type and real scalar coefficients only; no measure,
--   convexity, smoothness, oracle, or Hilbert-space structure is used by the proof.
-- portable call pattern: accelerated stochastic/proximal convergence proofs can
--   convert a weighted terminal/initial potential recursion into a normalized
--   distance-plus-memory contraction by changing only the endpoint coefficient
--   identities and the distance/memory observables.
-- counterargument checked: not paper-local traceability because it packages the
--   monotone rescaling, finite-sum coefficient distribution, and initial endpoint
--   factorization; not a new formula def because no recognized mathematical
--   object is being named.
-- coverage search: queried Mathlib LeanSearch for nonnegative scalar inequality
--   scaling and finite-sum coefficient rewriting, plus project/SOptLib catalog
--   searches for weighted potential, endpoint coefficients, rescale, and
--   contraction; hits were primitive `mul_le_mul_of_nonneg_left` and unrelated
--   telescope/coefficient lemmas, with no full statement covering this shape.
-- minimal hypotheses: all hypotheses are pointwise scalar facts; only
--   `0 <= scale * alphaPow`, the weighted inequality, and four endpoint
--   coefficient identities are used.

/-- Rescale a weighted potential inequality and normalize endpoint coefficients.

If a weighted terminal potential is bounded by a weighted initial potential, then
multiplication by a nonnegative scale preserves the inequality. Coefficient
identities at the terminal endpoint and the initial endpoint rewrite the result
as a normalized contraction with a remaining power factor.

Layer: Layer1 | Gap: Level 1 (weighted-potential endpoint coefficient normalization)
Proof: multiply the weighted inequality by the nonnegative combined scale,
  distribute the scale through finite sums, and rewrite the four endpoint
  coefficient identities.
Source: Mathlib ordered-ring inequality scaling and finite-sum algebra
Used in: randomized accelerated proximal inner-loop potential contraction
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/proof_components/14
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal point -/
theorem weightedPotentialInequality_rescale_endpoint_coefficients
    {ι : Type*} [Fintype ι]
    (scale alphaPow aT bT a0 b0 cD cM cD0 cM0 : ℝ)
    (Ds D0 : ℝ) (Ms M0 : ι → ℝ)
    (hscale_nonneg : 0 ≤ scale * alphaPow)
    (hweighted :
      aT * Ds + Finset.sum Finset.univ (fun i => bT * Ms i) ≤
        a0 * D0 + Finset.sum Finset.univ (fun i => b0 * M0 i))
    (hterminal_dist : scale * alphaPow * aT = cD)
    (hterminal_mem : scale * alphaPow * bT = cM)
    (hinitial_dist : scale * a0 = cD0)
    (hinitial_mem : scale * b0 = cM0) :
    cD * Ds + Finset.sum Finset.univ (fun i => cM * Ms i) ≤
      alphaPow *
        (cD0 * D0 + Finset.sum Finset.univ (fun i => cM0 * M0 i)) := by
  classical
  have hscaled := mul_le_mul_of_nonneg_left hweighted hscale_nonneg
  have hleft :
      (scale * alphaPow) *
          (aT * Ds + Finset.sum Finset.univ (fun i => bT * Ms i)) =
        cD * Ds + Finset.sum Finset.univ (fun i => cM * Ms i) := by
    calc
      (scale * alphaPow) *
          (aT * Ds + Finset.sum Finset.univ (fun i => bT * Ms i))
          =
          (scale * alphaPow * aT) * Ds +
            Finset.sum Finset.univ
              (fun i => (scale * alphaPow * bT) * Ms i) := by
            rw [mul_add, Finset.mul_sum]
            congr 1
            · ring
            · apply Finset.sum_congr rfl
              intro i _hi
              ring
      _ = cD * Ds + Finset.sum Finset.univ (fun i => cM * Ms i) := by
            rw [hterminal_dist, hterminal_mem]
  have hright :
      (scale * alphaPow) *
          (a0 * D0 + Finset.sum Finset.univ (fun i => b0 * M0 i)) =
        alphaPow *
          (cD0 * D0 + Finset.sum Finset.univ (fun i => cM0 * M0 i)) := by
    calc
      (scale * alphaPow) *
          (a0 * D0 + Finset.sum Finset.univ (fun i => b0 * M0 i))
          =
          alphaPow *
            ((scale * a0) * D0 +
              Finset.sum Finset.univ (fun i => (scale * b0) * M0 i)) := by
            rw [mul_add, Finset.mul_sum, mul_add, Finset.mul_sum]
            congr 1
            · ring
            · apply Finset.sum_congr rfl
              intro i _hi
              ring
      _ = alphaPow *
            (cD0 * D0 + Finset.sum Finset.univ (fun i => cM0 * M0 i)) := by
            rw [hinitial_dist, hinitial_mem]
  rwa [hleft, hright] at hscaled

/-- Snake-case compatibility wrapper for endpoint-coefficient weighted-potential rescaling.

Layer: Layer1 | Gap: Level 1 (weighted-potential endpoint coefficient normalization)
Proof: delegates to `weightedPotentialInequality_rescale_endpoint_coefficients`;
  the explicit finset parameter is retained for callers that previously supplied
  `s := Finset.univ`.
Source: Mathlib ordered-ring inequality scaling and finite-sum algebra
Used in: randomized accelerated proximal inner-loop potential contraction
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/proof_components/14
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal point -/
theorem weighted_potential_inequality_rescale_endpoint_coefficients
    {ι : Type*} [Fintype ι]
    (s : Finset ι)
    (scale alphaPow aT bT a0 b0 cD cM cD0 cM0 : ℝ)
    (Ds D0 : ℝ) (Ms M0 : ι → ℝ)
    (hscale_nonneg : 0 ≤ scale * alphaPow)
    (hweighted :
      aT * Ds + Finset.sum Finset.univ (fun i => bT * Ms i) ≤
        a0 * D0 + Finset.sum Finset.univ (fun i => b0 * M0 i))
    (hterminal_dist : scale * alphaPow * aT = cD)
    (hterminal_mem : scale * alphaPow * bT = cM)
    (hinitial_dist : scale * a0 = cD0)
    (hinitial_mem : scale * b0 = cM0) :
    cD * Ds + Finset.sum Finset.univ (fun i => cM * Ms i) ≤
      alphaPow *
        (cD0 * D0 + Finset.sum Finset.univ (fun i => cM0 * M0 i)) :=
  weightedPotentialInequality_rescale_endpoint_coefficients
    scale alphaPow aT bT a0 b0 cD cM cD0 cM0 Ds D0 Ms M0
    hscale_nonneg hweighted hterminal_dist hterminal_mem hinitial_dist hinitial_mem

end SOptLib

/-- A normalized nonnegative weighted lower-model sum is bounded by the optimum value.

If every lower-model value in a finite window is bounded above by `PsiStar`,
the coefficients are nonnegative, and their total mass is `1 / Gamma`, then
the `Gamma`-scaled weighted lower-model sum is bounded by `PsiStar`.

Layer: Layer1 | Gap: Level 1 (estimate-sequence lower-model normalization)
Proof: compare the weighted sum termwise using nonnegative coefficients, factor
  the constant optimum value out of the finite sum, and cancel the positive
  scale against the inverse coefficient mass.
Source: Mathlib finite big-operator inequalities and ordered real field algebra
Used in: stochastic accelerated gradient descent estimate-sequence lower-model
  aggregation at the selected optimizer
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem weighted_lower_model_sum_le_optimum_of_coeff_sum
    {ι Ω : Type*} (s : Finset ι)
    (lPsi : ι → Ω → ℝ) (PsiStar : ℝ) (coeff : ι → ℝ) (Gamma : ℝ) (ω : Ω)
    (hGamma_pos : 0 < Gamma)
    (hcoeff_nonneg : ∀ i ∈ s, 0 ≤ coeff i)
    (hmodel_le : ∀ i ∈ s, lPsi i ω ≤ PsiStar)
    (hsum_coeff : Finset.sum s coeff = 1 / Gamma) :
    Gamma * Finset.sum s (fun i => coeff i * lPsi i ω) ≤ PsiStar := by
  have hterm_le :
      Finset.sum s (fun i => coeff i * lPsi i ω) ≤
        Finset.sum s (fun i => coeff i * PsiStar) := by
    exact Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_left (hmodel_le i hi) (hcoeff_nonneg i hi)
  have hconst_sum :
      Finset.sum s (fun i => coeff i * PsiStar) =
        Finset.sum s coeff * PsiStar := by
    exact (Finset.sum_mul s coeff PsiStar).symm
  calc
    Gamma * Finset.sum s (fun i => coeff i * lPsi i ω)
        ≤ Gamma * Finset.sum s (fun i => coeff i * PsiStar) := by
          exact mul_le_mul_of_nonneg_left hterm_le (le_of_lt hGamma_pos)
    _ = Gamma * ((1 / Gamma) * PsiStar) := by
          rw [hconst_sum, hsum_coeff]
    _ = PsiStar := by
          field_simp [ne_of_gt hGamma_pos]

/-- A pathwise lower-model aggregate bound converts a pre-gap inequality into
an optimum-gap inequality.

If an objective value minus a lower-model aggregate is bounded by an initial
term, a Bregman telescope term, and an error term, then any pointwise upper
bound of the aggregate by the optimum value turns the same right-hand side into
a bound on the objective gap to that optimum value.

Layer: Layer1 | Gap: Level 1 (pathwise lower-model substitution)
Proof: compare `objectiveValue - optimumValue` with
  `objectiveValue - lowerModelSum` using the pointwise lower-model bound, then
  compose with the supplied pre-gap pathwise inequality by ordered real
  arithmetic.
Source: convex-optimization estimate-sequence algebra and Mathlib ordered real
  arithmetic
Used in: stochastic accelerated gradient descent estimate-sequence proof after
  lower-model aggregation and before Bregman finite-window telescoping
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem pathwise_gap_bound_after_lower_model
    {Ω : Type*}
    (objectiveValue lowerModelSum initialTerm bregmanSum residualSum : Ω → ℝ)
    (optimumValue : ℝ) (ω : Ω)
    (hpath :
      objectiveValue ω - lowerModelSum ω ≤
        initialTerm ω + bregmanSum ω + residualSum ω)
    (hlower : lowerModelSum ω ≤ optimumValue) :
    objectiveValue ω - optimumValue ≤
      initialTerm ω + bregmanSum ω + residualSum ω := by
  linarith

/-- A pathwise accelerated finite-window bound from one-step recurrences.

If a scalar process satisfies an AC-SA style one-step recurrence and the weights
`Γ` obey `Γ_{t+1} = (1 - α_{t+1}) Γ_t`, then the value at time `k`, after
subtracting the normalized model window, is bounded by the initial potential
and the normalized `B` and `D` windows.

Layer: Layer1 | Gap: Level 1 (accelerated finite-window recurrence telescope)
Proof: first prove the scalar Γ-weighted telescope by induction over `k`;
  then rewrite the natural-number sums as positive-time attached windows.
Source: finite sums over natural intervals and ordered real-field arithmetic
Used in: accelerated stochastic approximation pathwise Proposition 4.3
  window bound after the one-step model recurrence
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, accelerated stochastic approximation -/
theorem accelerated_pathwise_window_bound_of_one_step
    {Ω : Type*}
    (A : ℕ → Ω → ℝ)
    (L B D : {n : ℕ // 1 ≤ n} → Ω → ℝ)
    (alpha gamma : ℕ → ℝ)
    (Gamma : {n : ℕ // 1 ≤ n} → ℝ)
    (k : ℕ) (hk : 1 ≤ k) (ω : Ω)
    (halpha_le_one : ∀ t, 1 ≤ t → alpha t ≤ 1)
    (hgamma_ne : ∀ t, 1 ≤ t → gamma t ≠ 0)
    (hGamma_ne : ∀ t : {n : ℕ // 1 ≤ n}, Gamma t ≠ 0)
    (hGamma_one : Gamma ⟨1, le_rfl⟩ = 1)
    (halpha_one : alpha 1 = 1)
    (hGamma_succ :
      ∀ t (ht : 1 ≤ t),
        Gamma ⟨t + 1, Nat.succ_le_succ (Nat.zero_le t)⟩ =
          (1 - alpha (t + 1)) * Gamma ⟨t, ht⟩)
    (hstep : ∀ t (ht : 1 ≤ t),
      A t ω ≤ (1 - alpha t) * A (t - 1) ω + alpha t * L ⟨t, ht⟩ ω +
        alpha t / gamma t * B ⟨t, ht⟩ ω + D ⟨t, ht⟩ ω) :
    A k ω - Gamma ⟨k, hk⟩ *
        Finset.sum (Finset.Icc 1 k).attach (fun t =>
          let τ : {n : ℕ // 1 ≤ n} := ⟨t.1, (Finset.mem_Icc.mp t.2).1⟩
          alpha t.1 / Gamma τ * L τ ω) ≤
      Gamma ⟨k, hk⟩ * (1 - alpha 1) * A 0 ω +
        Gamma ⟨k, hk⟩ *
          Finset.sum (Finset.Icc 1 k).attach (fun t =>
            let τ : {n : ℕ // 1 ≤ n} := ⟨t.1, (Finset.mem_Icc.mp t.2).1⟩
            alpha t.1 / (gamma t.1 * Gamma τ) * B τ ω) +
        Gamma ⟨k, hk⟩ *
          Finset.sum (Finset.Icc 1 k).attach (fun t =>
            let τ : {n : ℕ // 1 ≤ n} := ⟨t.1, (Finset.mem_Icc.mp t.2).1⟩
            D τ ω / Gamma τ) := by
  classical
  let Lterm : ℕ → ℝ := fun n =>
    if hn : 1 ≤ n then L ⟨n, hn⟩ ω else 0
  let Bterm : ℕ → ℝ := fun n =>
    if hn : 1 ≤ n then B ⟨n, hn⟩ ω else 0
  let Dterm : ℕ → ℝ := fun n =>
    if hn : 1 ≤ n then D ⟨n, hn⟩ ω else 0
  let GammaNat : ℕ → ℝ := fun n =>
    if hn : 1 ≤ n then Gamma ⟨n, hn⟩ else 1
  have hGamma_ne_nat : ∀ t, 1 ≤ t → GammaNat t ≠ 0 := by
    intro t ht
    dsimp [GammaNat]
    simp [ht, hGamma_ne ⟨t, ht⟩]
  have hGamma_one_nat : GammaNat 1 = 1 := by
    simpa [GammaNat] using hGamma_one
  have hGamma_succ_nat :
      ∀ t, 1 ≤ t → GammaNat (t + 1) = (1 - alpha (t + 1)) * GammaNat t := by
    intro t ht
    have ht1 : 1 ≤ t + 1 := Nat.succ_le_succ (Nat.zero_le t)
    simp [GammaNat, ht, ht1, hGamma_succ t ht]
  have hstep_nat : ∀ t, 1 ≤ t →
      A t ω ≤ (1 - alpha t) * A (t - 1) ω + alpha t * Lterm t +
        alpha t / gamma t * Bterm t + Dterm t := by
    intro t ht
    simpa [Lterm, Bterm, Dterm, ht] using hstep t ht
  have htelescope :
      A k ω - GammaNat k *
          Finset.sum (Finset.Icc 1 k)
            (fun t => alpha t / GammaNat t * Lterm t) ≤
        GammaNat k * (1 - alpha 1) * A 0 ω +
          GammaNat k *
            Finset.sum (Finset.Icc 1 k)
              (fun t => alpha t / (gamma t * GammaNat t) * Bterm t) +
          GammaNat k *
            Finset.sum (Finset.Icc 1 k)
              (fun t => Dterm t / GammaNat t) := by
    let SL : ℕ → ℝ := fun m =>
      Finset.sum (Finset.Icc 1 m) (fun t => alpha t / GammaNat t * Lterm t)
    let SB : ℕ → ℝ := fun m =>
      Finset.sum (Finset.Icc 1 m) (fun t => alpha t / (gamma t * GammaNat t) * Bterm t)
    let SD : ℕ → ℝ := fun m =>
      Finset.sum (Finset.Icc 1 m) (fun t => Dterm t / GammaNat t)
    change
      A k ω - GammaNat k * SL k ≤
        GammaNat k * (1 - alpha 1) * A 0 ω + GammaNat k * SB k + GammaNat k * SD k
    refine Nat.le_induction ?base ?step_ind k hk
    · have hstep1 := hstep_nat 1 le_rfl
      have hstep1' :
          A 1 ω ≤ Lterm 1 + (1 / gamma 1) * Bterm 1 + Dterm 1 := by
        simpa [halpha_one] using hstep1
      rw [one_div] at hstep1'
      simp [SL, SB, SD, hGamma_one_nat, halpha_one]
      linarith
    · intro n hn ih
      have hn1 : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
      have hcoef_nonneg : 0 ≤ 1 - alpha (n + 1) := by
        exact sub_nonneg.mpr (halpha_le_one (n + 1) hn1)
      have hrec := hGamma_succ_nat n hn
      have hGtop : GammaNat (n + 1) ≠ 0 := hGamma_ne_nat (n + 1) hn1
      have hγtop : gamma (n + 1) ≠ 0 := hgamma_ne (n + 1) hn1
      have hSL_succ :
          SL (n + 1) =
            SL n + alpha (n + 1) / GammaNat (n + 1) * Lterm (n + 1) := by
        dsimp [SL]
        rw [Finset.sum_Icc_succ_top hn1]
      have hSB_succ :
          SB (n + 1) =
            SB n + alpha (n + 1) / (gamma (n + 1) * GammaNat (n + 1)) *
              Bterm (n + 1) := by
        dsimp [SB]
        rw [Finset.sum_Icc_succ_top hn1]
      have hSD_succ :
          SD (n + 1) =
            SD n + Dterm (n + 1) / GammaNat (n + 1) := by
        dsimp [SD]
        rw [Finset.sum_Icc_succ_top hn1]
      have htopL :
          GammaNat (n + 1) *
              (alpha (n + 1) / GammaNat (n + 1) * Lterm (n + 1)) =
            alpha (n + 1) * Lterm (n + 1) := by
        field_simp [hGtop]
      have htopB :
          GammaNat (n + 1) *
              (alpha (n + 1) / (gamma (n + 1) * GammaNat (n + 1)) *
                Bterm (n + 1)) =
            alpha (n + 1) / gamma (n + 1) * Bterm (n + 1) := by
        field_simp [hγtop, hGtop]
      have htopD :
          GammaNat (n + 1) * (Dterm (n + 1) / GammaNat (n + 1)) =
            Dterm (n + 1) := by
        field_simp [hGtop]
      have hih_scaled :=
        mul_le_mul_of_nonneg_left ih hcoef_nonneg
      have hstep_top :
          A (n + 1) ω ≤
            (1 - alpha (n + 1)) * A n ω + alpha (n + 1) * Lterm (n + 1) +
              alpha (n + 1) / gamma (n + 1) * Bterm (n + 1) + Dterm (n + 1) := by
        simpa using hstep_nat (n + 1) hn1
      calc
        A (n + 1) ω - GammaNat (n + 1) * SL (n + 1)
            = A (n + 1) ω -
                GammaNat (n + 1) *
                  (SL n + alpha (n + 1) / GammaNat (n + 1) * Lterm (n + 1)) := by
                rw [hSL_succ]
        _ = A (n + 1) ω - GammaNat (n + 1) * SL n -
              alpha (n + 1) * Lterm (n + 1) := by
                rw [mul_add, htopL]
                ring
        _ ≤ (1 - alpha (n + 1)) * (A n ω - GammaNat n * SL n) +
              alpha (n + 1) / gamma (n + 1) * Bterm (n + 1) + Dterm (n + 1) := by
                rw [hrec]
                nlinarith
        _ ≤ (1 - alpha (n + 1)) *
                (GammaNat n * (1 - alpha 1) * A 0 ω + GammaNat n * SB n +
                  GammaNat n * SD n) +
              alpha (n + 1) / gamma (n + 1) * Bterm (n + 1) + Dterm (n + 1) := by
                nlinarith
        _ =
            GammaNat (n + 1) * (1 - alpha 1) * A 0 ω +
              (GammaNat (n + 1) * SB n +
                alpha (n + 1) / gamma (n + 1) * Bterm (n + 1)) +
              (GammaNat (n + 1) * SD n + Dterm (n + 1)) := by
                rw [hrec]
                ring
        _ =
            GammaNat (n + 1) * (1 - alpha 1) * A 0 ω +
              GammaNat (n + 1) * SB (n + 1) +
              GammaNat (n + 1) * SD (n + 1) := by
                rw [hSB_succ, hSD_succ]
                rw [mul_add, mul_add, htopB, htopD]
  have hGk : GammaNat k = Gamma ⟨k, hk⟩ := by
    simp [GammaNat, hk]
  have hLsum :
      Finset.sum (Finset.Icc 1 k)
          (fun t => alpha t / GammaNat t * Lterm t) =
        Finset.sum (Finset.Icc 1 k).attach (fun t =>
          let τ : {n : ℕ // 1 ≤ n} := ⟨t.1, (Finset.mem_Icc.mp t.2).1⟩
          alpha t.1 / Gamma τ * L τ ω) := by
    let FL : ℕ → ℝ := fun n =>
      if hn : 1 ≤ n then
        alpha n / Gamma ⟨n, hn⟩ * L ⟨n, hn⟩ ω
      else 0
    calc
      Finset.sum (Finset.Icc 1 k)
          (fun t => alpha t / GammaNat t * Lterm t)
          =
        Finset.sum (Finset.Icc 1 k) FL := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          have hnpos : 1 ≤ n := (Finset.mem_Icc.mp hn).1
          simp [FL, Lterm, GammaNat, hnpos]
      _ = Finset.sum (Finset.Icc 1 k).attach (fun t => FL t.1) := by
          exact (Finset.sum_attach (Finset.Icc 1 k) FL).symm
      _ =
        Finset.sum (Finset.Icc 1 k).attach (fun t =>
          let τ : {n : ℕ // 1 ≤ n} := ⟨t.1, (Finset.mem_Icc.mp t.2).1⟩
          alpha t.1 / Gamma τ * L τ ω) := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          have htpos : 1 ≤ t.1 := (Finset.mem_Icc.mp t.2).1
          simp [FL, htpos]
  have hBsum :
      Finset.sum (Finset.Icc 1 k)
          (fun t => alpha t / (gamma t * GammaNat t) * Bterm t) =
        Finset.sum (Finset.Icc 1 k).attach (fun t =>
          let τ : {n : ℕ // 1 ≤ n} := ⟨t.1, (Finset.mem_Icc.mp t.2).1⟩
          alpha t.1 / (gamma t.1 * Gamma τ) * B τ ω) := by
    let FB : ℕ → ℝ := fun n =>
      if hn : 1 ≤ n then
        alpha n / (gamma n * Gamma ⟨n, hn⟩) * B ⟨n, hn⟩ ω
      else 0
    calc
      Finset.sum (Finset.Icc 1 k)
          (fun t => alpha t / (gamma t * GammaNat t) * Bterm t)
          =
        Finset.sum (Finset.Icc 1 k) FB := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          have hnpos : 1 ≤ n := (Finset.mem_Icc.mp hn).1
          simp [FB, Bterm, GammaNat, hnpos]
      _ = Finset.sum (Finset.Icc 1 k).attach (fun t => FB t.1) := by
          exact (Finset.sum_attach (Finset.Icc 1 k) FB).symm
      _ =
        Finset.sum (Finset.Icc 1 k).attach (fun t =>
          let τ : {n : ℕ // 1 ≤ n} := ⟨t.1, (Finset.mem_Icc.mp t.2).1⟩
          alpha t.1 / (gamma t.1 * Gamma τ) * B τ ω) := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          have htpos : 1 ≤ t.1 := (Finset.mem_Icc.mp t.2).1
          simp [FB, htpos]
  have hDsum :
      Finset.sum (Finset.Icc 1 k)
          (fun t => Dterm t / GammaNat t) =
        Finset.sum (Finset.Icc 1 k).attach (fun t =>
          let τ : {n : ℕ // 1 ≤ n} := ⟨t.1, (Finset.mem_Icc.mp t.2).1⟩
          D τ ω / Gamma τ) := by
    let FD : ℕ → ℝ := fun n =>
      if hn : 1 ≤ n then
        D ⟨n, hn⟩ ω / Gamma ⟨n, hn⟩
      else 0
    calc
      Finset.sum (Finset.Icc 1 k)
          (fun t => Dterm t / GammaNat t)
          =
        Finset.sum (Finset.Icc 1 k) FD := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          have hnpos : 1 ≤ n := (Finset.mem_Icc.mp hn).1
          simp [FD, Dterm, GammaNat, hnpos]
      _ = Finset.sum (Finset.Icc 1 k).attach (fun t => FD t.1) := by
          exact (Finset.sum_attach (Finset.Icc 1 k) FD).symm
      _ =
        Finset.sum (Finset.Icc 1 k).attach (fun t =>
          let τ : {n : ℕ // 1 ≤ n} := ⟨t.1, (Finset.mem_Icc.mp t.2).1⟩
          D τ ω / Gamma τ) := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          have htpos : 1 ≤ t.1 := (Finset.mem_Icc.mp t.2).1
          simp [FD, htpos]
  simpa [hGk, hLsum, hBsum, hDsum] using htelescope

/-- A nonnegative terminal coordinate dominated by a Gamma-scaled telescope
envelope is integrable.

If the finite-window correction sum is integrable and the terminal coordinate is
pointwise bounded above by a deterministic initial budget plus that window,
scaled by `Gamma`, then the terminal coordinate is integrable.

Layer: Layer1 | Gap: Level 1 (Gamma-scaled telescope envelope integrability)
Proof: build integrability of the Gamma-scaled envelope from the deterministic
  initial budget and the integrable finite-window correction, then apply
  domination after converting nonnegative order bounds into real norm bounds.
Source: Mathlib Bochner integrability closure and real-valued domination APIs
Used in: stochastic accelerated gradient descent terminal state-square
  integrability after the finite-window Bregman telescope
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem integrable_terminal_state_sq_of_gamma_telescope_envelope
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (s : Finset ℕ) (k : ℕ) (Gamma initial : ℝ)
    (window : ℕ → Ω → ℝ) (Y : ℕ → Ω → ℝ)
    (hterminal_meas : AEStronglyMeasurable (Y k) P)
    (hwindow_int :
      Integrable (fun ω => Finset.sum s (fun t => window t ω)) P)
    (hterminal_nonneg : ∀ᵐ ω ∂P, 0 ≤ Y k ω)
    (hterminal_le :
      ∀ᵐ ω ∂P,
        Y k ω ≤ Gamma * (initial + Finset.sum s (fun t => window t ω))) :
    Integrable (Y k) P := by
  have henv_int :
      Integrable
        (fun ω => Gamma * (initial + Finset.sum s (fun t => window t ω))) P := by
    exact ((integrable_const (c := initial)).add hwindow_int).const_mul Gamma
  refine henv_int.mono' hterminal_meas ?_
  filter_upwards [hterminal_nonneg, hterminal_le] with ω hY_nonneg hY_le
  have henv_nonneg :
      0 ≤ Gamma * (initial + Finset.sum s (fun t => window t ω)) :=
    le_trans hY_nonneg hY_le
  simpa [Real.norm_of_nonneg hY_nonneg, Real.norm_of_nonneg henv_nonneg] using hY_le

/-- A pathwise accelerated telescope with finite residual budgets gives an
expected gap bound.

If a nonnegative gap is pointwise dominated by a Bregman/telescope term plus a
finite residual sum, the telescope term is bounded by `A`, and each residual
summand has an expectation bound, then the gap is integrable and its expectation
is bounded by the deterministic budget `B_e`.

Layer: Layer1 | Gap: Level 1 (accelerated expected-gap telescope bridge)
Proof: prove residual-sum integrability, exchange the finite sum with the
  Bochner integral, scale the per-index bounds by the nonnegative Γ factor, and
  derive gap integrability from nonnegative domination before applying integral
  monotonicity.
Source: Mathlib Bochner integral finite-sum linearity, integral monotonicity,
  and ordered real arithmetic
Used in: stochastic accelerated gradient descent expected suboptimality after
  the pathwise Bregman telescope and one-step residual expectation bounds
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem accelerated_expected_gap_bound_of_pathwise_telescope
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (s : Finset ι)
    (gap bregmanTerm residualSum : Ω → ℝ)
    (residualTerm : ι → Ω → ℝ)
    (residualBudget : ι → ℝ)
    (expectedGap A GammaK B_e : ℝ)
    (hgap_aestrong : AEStronglyMeasurable gap μ)
    (hgap_nonneg : ∀ ω, 0 ≤ gap ω)
    (hpath : ∀ ω, gap ω ≤ bregmanTerm ω + residualSum ω)
    (hbregman_bound : ∀ ω, bregmanTerm ω ≤ A)
    (hresidualSum :
      ∀ ω, residualSum ω = GammaK * Finset.sum s (fun i => residualTerm i ω))
    (hresidual_int : ∀ i ∈ s, Integrable (residualTerm i) μ)
    (hresidual_bound :
      ∀ i ∈ s, ∫ ω, residualTerm i ω ∂μ ≤ residualBudget i)
    (hGamma_nonneg : 0 ≤ GammaK)
    (hexpectedGap : expectedGap = ∫ ω, gap ω ∂μ)
    (hB_e : B_e = A + GammaK * Finset.sum s residualBudget) :
    Integrable gap μ ∧ expectedGap ≤ B_e := by
  classical
  have hsum_int :
      Integrable
        (fun ω => Finset.sum s (fun i => residualTerm i ω)) μ := by
    exact MeasureTheory.integrable_finset_sum
      (s := s) (f := fun i ω => residualTerm i ω) hresidual_int
  have hresidual_fun :
      residualSum =
        fun ω => GammaK * Finset.sum s (fun i => residualTerm i ω) := by
    funext ω
    exact hresidualSum ω
  have hresidualSum_int : Integrable residualSum μ := by
    rw [hresidual_fun]
    exact hsum_int.const_mul GammaK
  have hupper_int : Integrable (fun ω => A + residualSum ω) μ :=
    (integrable_const (c := A)).add hresidualSum_int
  have hpoint : ∀ ω, gap ω ≤ A + residualSum ω := by
    intro ω
    have hp := hpath ω
    have hb := hbregman_bound ω
    linarith
  have hgap_int : Integrable gap μ :=
    hupper_int.mono' hgap_aestrong
      (by
        filter_upwards with ω
        rw [Real.norm_of_nonneg (hgap_nonneg ω)]
        exact hpoint ω)
  have hmain :
      ∫ ω, gap ω ∂μ ≤ ∫ ω, A + residualSum ω ∂μ :=
    integral_mono hgap_int hupper_int hpoint
  have hresidual_integral :
      ∫ ω, residualSum ω ∂μ =
        GammaK * Finset.sum s (fun i => ∫ ω, residualTerm i ω ∂μ) := by
    rw [hresidual_fun, integral_const_mul]
    rw [integral_finset_sum]
    exact hresidual_int
  have hsum_bound :
      Finset.sum s (fun i => ∫ ω, residualTerm i ω ∂μ) ≤
        Finset.sum s residualBudget := by
    exact Finset.sum_le_sum hresidual_bound
  have hresidual_bound_total :
      ∫ ω, residualSum ω ∂μ ≤ GammaK * Finset.sum s residualBudget := by
    rw [hresidual_integral]
    exact mul_le_mul_of_nonneg_left hsum_bound hGamma_nonneg
  have hupper_eval :
      ∫ ω, A + residualSum ω ∂μ =
        A + ∫ ω, residualSum ω ∂μ := by
    rw [integral_add (integrable_const (c := A)) hresidualSum_int]
    simp [integral_const, probReal_univ]
  refine ⟨hgap_int, ?_⟩
  calc
    expectedGap = ∫ ω, gap ω ∂μ := hexpectedGap
    _ ≤ ∫ ω, A + residualSum ω ∂μ := hmain
    _ = A + ∫ ω, residualSum ω ∂μ := hupper_eval
    _ ≤ A + GammaK * Finset.sum s residualBudget := by
          linarith
    _ = B_e := hB_e.symm

/-- Finite-window weighted state control closes a two-component state-square
integrability induction.

Suppose the current state-square term at time `n + 1` can be extracted from an
integrable finite window of nonnegative weighted state-square terms, and the
companion state-square term at time `n + 1` is integrable whenever the previous
companion term and current state term are integrable. Then both components are
integrable at every natural time.

Layer: Layer1 | Gap: Level 1 (finite-window state-square integrability induction)
Proof: use strong induction on time; for the successor state, extract the
  terminal nonnegative summand from the integrable weighted finite window, then
  apply the supplied companion-state transport step.
Source: Mathlib natural-number strong induction, finite-sum order, and Bochner
  integrability closure APIs
Used in: stochastic accelerated gradient descent generated-state L2
  regularity after a finite-window Bregman/Gamma telescope
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem finite_window_state_sq_integrable_of_source_bregman_recurrence
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (stateSq xBarSq : ℕ → Ω → ℝ) (coeff : ℕ → ℝ)
    (hstate_zero : Integrable (stateSq 0) P)
    (hxBar_zero : Integrable (xBarSq 0) P)
    (hweighted_window :
      ∀ n : ℕ,
        (∀ m : ℕ, m < n + 1 →
          Integrable (stateSq m) P ∧ Integrable (xBarSq m) P) →
        Integrable
          (fun ω => Finset.sum (Finset.Icc 1 (n + 1))
            (fun t => coeff t * stateSq t ω)) P)
    (hstateSq_meas : ∀ n : ℕ, AEStronglyMeasurable (stateSq n) P)
    (hcoeff_pos : ∀ n : ℕ, 0 < coeff (n + 1))
    (hcoeff_nonneg :
      ∀ n : ℕ, ∀ t ∈ Finset.Icc 1 (n + 1), 0 ≤ coeff t)
    (hstateSq_nonneg :
      ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ t ∈ Finset.Icc 1 (n + 1), 0 ≤ stateSq t ω)
    (hxBar_step :
      ∀ n : ℕ,
        Integrable (xBarSq n) P →
        Integrable (stateSq (n + 1)) P →
        Integrable (xBarSq (n + 1)) P) :
    ∀ n : ℕ, Integrable (stateSq n) P ∧ Integrable (xBarSq n) P := by
  classical
  intro n
  refine Nat.strong_induction_on n ?_
  intro k ih
  cases k with
  | zero =>
      exact ⟨hstate_zero, hxBar_zero⟩
  | succ n =>
      have hprefix :
          ∀ m : ℕ, m < n + 1 →
            Integrable (stateSq m) P ∧ Integrable (xBarSq m) P := by
        intro m hm
        exact ih m hm
      have hstate_succ :
          Integrable (stateSq (n + 1)) P := by
        have hsum := hweighted_window n hprefix
        have hk_mem : n + 1 ∈ Finset.Icc 1 (n + 1) := by
          simp
        exact
          integrable_of_le_integrable_weighted_finset_sum
            (s := Finset.Icc 1 (n + 1)) (k := n + 1) (c := coeff)
            (Y := stateSq) hk_mem hsum (hstateSq_meas (n + 1))
            (hcoeff_pos n) (hcoeff_nonneg n) (hstateSq_nonneg n)
      have ih_n :
          Integrable (stateSq n) P ∧ Integrable (xBarSq n) P :=
        ih n (Nat.lt_succ_self n)
      exact ⟨hstate_succ, hxBar_step n ih_n.2 hstate_succ⟩

/-- Positive-time auxiliary squared L2 regularity follows from recursive state
L2 regularity and a predecessor transport step.

If both components of a recursive state are square-integrable around a fixed
center at every natural time, and each positive-time auxiliary point inherits
square-integrability from the previous state, then the auxiliary point is
square-integrable at every positive time.

Layer: Layer1 | Gap: Level 1 (positive-time auxiliary L2 closure)
Proof: reindex a positive natural time as the successor of its predecessor,
  read the two recursive state L2 facts at that predecessor, and apply the
  supplied auxiliary transport step.
Source: Mathlib natural-number subtype reindexing and Bochner integrability APIs
Used in: stochastic accelerated gradient descent auxiliary multiplier
  square-integrability after recursive generated-state L2 closure
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem xplus_sq_integrable_of_recursive_state_l2
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {P : Measure Ω}
    (xStar : E) (state stateBar : ℕ → Ω → E)
    (xPlus : {n : ℕ // 1 ≤ n} → Ω → E)
    (hstate_l2 :
      ∀ n : ℕ,
        Integrable (fun ω => ‖xStar - state n ω‖ ^ 2) P ∧
          Integrable (fun ω => ‖xStar - stateBar n ω‖ ^ 2) P)
    (hxPlus_step :
      ∀ n : ℕ,
        Integrable (fun ω => ‖xStar - state n ω‖ ^ 2) P →
        Integrable (fun ω => ‖xStar - stateBar n ω‖ ^ 2) P →
        Integrable
          (fun ω =>
            ‖xStar -
              xPlus ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n)⟩ ω‖ ^ 2) P) :
    ∀ t : {n : ℕ // 1 ≤ n},
      Integrable (fun ω => ‖xStar - xPlus t ω‖ ^ 2) P := by
  intro t
  let n : ℕ := t.1 - 1
  have ht :
      (⟨n + 1, Nat.succ_le_succ (Nat.zero_le n)⟩ : {m : ℕ // 1 ≤ m}) = t := by
    apply Subtype.ext
    exact Nat.sub_add_cancel t.2
  have hprev := hstate_l2 n
  simpa [ht] using hxPlus_step n hprev.1 hprev.2

namespace SOptLib

/-- A conditional-gradient stop index is bounded by the ceiling of a checked
inner-loop budget scalar.

If zero diameter stops at the first inner iterate, and every positive horizon
has a shifted Wolfe-gap witness below the standard `6 * beta * diameter^2`
budget, then the selected stopping index performs at most `ceil q` updates
whenever `q` is the checked budget scalar.

Layer: Layer1 | Gap: Level 1 (conditional-gradient stop-index ceiling bridge)
Proof: split on whether `ceil q` is zero. The zero case forces zero diameter
  from the checked quotient; the positive case turns the shifted small-gap
  witness at horizon `ceil q` into a stopping witness by real-field ceiling
  arithmetic.
Source: Frank-Wolfe conditional-gradient stopping calculus and Mathlib natural
  ceiling/order arithmetic over real scalars
Used in: stochastic conditional-gradient sliding conditional-gradient performed-update count
  after the shifted weighted Wolfe-gap telescope
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem conditionalGradientStopIndex_sub_one_le_ceil_of_budgetScalar
    {E : Type*}
    (diameter : ℝ) (wolfeGap : E → ℝ) (innerIterate : ℕ → E)
    (stopIndex : ℕ) (beta eta q : ℝ)
    (hbeta : 0 < beta) (heta : 0 < eta)
    (hq : conditionalGradientInnerIterationBudgetScalar beta eta diameter q)
    (hstop_le :
      ∀ {t : ℕ}, 1 ≤ t → wolfeGap (innerIterate t) ≤ eta → stopIndex ≤ t)
    (hzero_stop : diameter = 0 → stopIndex ≤ 1)
    (hshifted_gap :
      ∀ {T : ℕ}, 1 ≤ T →
        ∃ j : ℕ, 1 ≤ j ∧ j ≤ T ∧
          wolfeGap (innerIterate (j + 1)) ≤
            6 * beta * diameter ^ 2 / (((T + 1 : ℕ) : ℝ))) :
    stopIndex - 1 ≤ Nat.ceil q := by
  classical
  let A : ℝ := 6 * beta * diameter ^ 2
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    nlinarith [le_of_lt hbeta, sq_nonneg diameter]
  rcases hq with ⟨hηne, hq_mul_raw⟩
  have hq_mul : q * eta = A := by
    simpa [A] using hq_mul_raw
  have hq_eq : q = A / eta := by
    rw [← hq_mul]
    field_simp [ne_of_gt heta]
  have hq_nonneg : 0 ≤ q := by
    rw [hq_eq]
    exact div_nonneg hA_nonneg (le_of_lt heta)
  by_cases hceil0 : Nat.ceil q = 0
  · have hq_le_zero : q ≤ 0 := by
      simpa [hceil0] using (Nat.le_ceil q)
    have hq0 : q = 0 := le_antisymm hq_le_zero hq_nonneg
    have hA0 : A = 0 := by
      have htmp : (0 : ℝ) = A := by simpa [hq0] using hq_mul
      exact htmp.symm
    have hDsq0 : diameter ^ 2 = 0 := by
      dsimp [A] at hA0
      nlinarith [hA0, hbeta]
    have hD0 : diameter = 0 := by
      nlinarith [hDsq0, sq_nonneg diameter]
    have hfind : stopIndex ≤ 1 := hzero_stop hD0
    have htarget : stopIndex - 1 ≤ 0 := by
      omega
    simpa [hceil0] using htarget
  · have hTpos : 1 ≤ Nat.ceil q := by omega
    obtain ⟨j, hj1, hjT, hgap⟩ := hshifted_gap hTpos
    let d : ℝ := ((Nat.ceil q + 1 : ℕ) : ℝ)
    have hdpos : 0 < d := by
      dsimp [d]
      exact_mod_cast Nat.succ_pos (Nat.ceil q)
    have hq_le_T : q ≤ (Nat.ceil q : ℝ) := Nat.le_ceil q
    have hT_le_d : (Nat.ceil q : ℝ) ≤ d := by
      dsimp [d]
      exact_mod_cast Nat.le_succ (Nat.ceil q)
    have hq_le_d : q ≤ d := le_trans hq_le_T hT_le_d
    have hq_div_le_one : q / d ≤ 1 := by
      field_simp [ne_of_gt hdpos]
      exact hq_le_d
    have hscalar :
        6 * beta * diameter ^ 2 / (((Nat.ceil q + 1 : ℕ) : ℝ)) ≤ eta := by
      have hrewrite : 6 * beta * diameter ^ 2 = q * eta := by
        simpa [A] using hq_mul.symm
      rw [hrewrite]
      change q * eta / d ≤ eta
      have hcalc : q / d * eta ≤ 1 * eta := by
        exact mul_le_mul_of_nonneg_right hq_div_le_one (le_of_lt heta)
      have heq : q * eta / d = q / d * eta := by field_simp [ne_of_gt hdpos]
      linarith
    have hgap_eta : wolfeGap (innerIterate (j + 1)) ≤ eta := by
      exact le_trans hgap hscalar
    have hfind : stopIndex ≤ j + 1 :=
      hstop_le (by omega) hgap_eta
    omega

/-- A shifted minimum Wolfe-gap bound at the ceiling horizon gives a finite
one-based stopping index.

For a positive tolerance, choose the standard conditional-gradient horizon
`max 1 ceil (6 * beta * diameter^2 / eta)`.  If every positive horizon has a
performed-update witness whose shifted Wolfe gap is bounded by the corresponding
`6 * beta * diameter^2 / (T + 1)` quantity, then some one-based iterate has gap
at most `eta`.

Layer: Layer1 | Gap: Level 1 (conditional-gradient stopping existence from shifted min-gap)
Proof: use the positive ceiling horizon to turn the scalar
  `6 * beta * diameter^2 / (T + 1)` bound into `eta`, then compose it with the
  shifted small-gap witness and return the one-based index `j + 1`.
Source: Frank-Wolfe conditional-gradient Wolfe-gap stopping calculus and
  Mathlib natural ceiling/order arithmetic over real scalars
Used in: stochastic conditional-gradient sliding CndG inner-loop termination
  after the shifted weighted Wolfe-gap telescope
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem cndG_terminates_of_shifted_min_wolfeGap_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (diameter : ℝ) (wolfeGap : E → ℝ) (innerIterate : ℕ → E)
    (beta eta : ℝ)
    (heta : 0 < eta)
    (hshifted_min :
      ∀ {T : ℕ}, 1 ≤ T →
        ∃ j : ℕ, 1 ≤ j ∧ j ≤ T ∧
          wolfeGap (innerIterate (j + 1)) ≤
            6 * beta * diameter ^ 2 / (((T + 1 : ℕ) : ℝ))) :
    ∃ t : ℕ, 1 ≤ t ∧ wolfeGap (innerIterate t) ≤ eta := by
  let T : ℕ := max 1 (Nat.ceil ((6 * beta * diameter ^ 2) / eta))
  have hT_pos : 1 ≤ T := by
    exact Nat.le_max_left 1 (Nat.ceil ((6 * beta * diameter ^ 2) / eta))
  have hstop_scalar :
      6 * beta * diameter ^ 2 / (((T + 1 : ℕ) : ℝ)) ≤ eta := by
    have hceil : (6 * beta * diameter ^ 2) / eta ≤ (T : ℝ) := by
      simpa [T] using le_positive_ceil_max_one ((6 * beta * diameter ^ 2) / eta)
    have heta_nonneg : 0 ≤ eta := le_of_lt heta
    have heta_ne : eta ≠ 0 := ne_of_gt heta
    have hA_le_etaT : 6 * beta * diameter ^ 2 ≤ eta * (T : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hceil heta_nonneg
      have hleft : eta * ((6 * beta * diameter ^ 2) / eta) =
          6 * beta * diameter ^ 2 := by
        field_simp [heta_ne]
      nlinarith
    have hT_le_succ : (T : ℝ) ≤ (((T + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.le_succ T
    have hA_le_eta_succ :
        6 * beta * diameter ^ 2 ≤ eta * (((T + 1 : ℕ) : ℝ)) := by
      have hmul := mul_le_mul_of_nonneg_left hT_le_succ heta_nonneg
      nlinarith
    have hden_pos : 0 < (((T + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.succ_pos T
    rw [div_le_iff₀ hden_pos]
    exact hA_le_eta_succ
  obtain ⟨j, hj_pos, _hj_le, hgap⟩ := hshifted_min hT_pos
  exact ⟨j + 1, by omega, le_trans hgap hstop_scalar⟩

/-- A `2 / (t + 1)` residual recurrence gives the standard `2*A/(t+1)` rate.

If a real residual sequence satisfies
`Delta (t+1) <= (1 - 2/(t+1)) * Delta t + (A/2) * (2/(t+1))^2` for every
positive time `t`, and `A` is nonnegative, then `Delta (t+1) <= 2*A/(t+1)`.

Layer: Layer1 | Gap: Level 1 (two-over-successor scalar residual recurrence)
Proof: induction over positive natural time. The base case uses the recurrence
  at `t = 1`, where the stepsize is one; the successor step substitutes the
  induction hypothesis and closes by ordered-field arithmetic.
Source: Conditional-gradient and Frank-Wolfe scalar recurrence algebra with
  Mathlib natural-number casts and real ordered-field arithmetic
Used in: stochastic conditional-gradient sliding inner-loop residual bound
  after deriving the CndG one-step residual recursion
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem two_div_succ_residual_bound_of_recursion
    (Delta : ℕ → ℝ) (A : ℝ)
    (hA_nonneg : 0 ≤ A)
    (hrec : ∀ t, 1 ≤ t →
      let lam : ℝ := (2 : ℝ) / (((t + 1 : ℕ) : ℝ))
      Delta (t + 1) ≤ (1 - lam) * Delta t + (A / 2) * lam ^ 2)
    {t : ℕ} (ht : 1 ≤ t) :
    Delta (t + 1) ≤ 2 * A / (((t + 1 : ℕ) : ℝ)) := by
  refine Nat.le_induction ?base ?step t ht
  · have hrec_one := hrec 1 le_rfl
    have hbase : Delta (1 + 1) ≤ A / 2 := by
      norm_num at hrec_one ⊢
      exact hrec_one
    have htarget : A / 2 ≤ 2 * A / (((1 + 1 : ℕ) : ℝ)) := by
      norm_num
      linarith
    exact le_trans hbase htarget
  · intro n _hn ih
    let lam : ℝ := (2 : ℝ) / (((n + 1 + 1 : ℕ) : ℝ))
    have hn1 : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
    have hrec_step := hrec (n + 1) hn1
    have hcoef_nonneg : 0 ≤ 1 - lam := by
      have htwo_le : (2 : ℝ) ≤ (((n + 1 + 1 : ℕ) : ℝ)) := by
        exact_mod_cast (show 2 ≤ n + 1 + 1 by omega)
      have hden_pos : 0 < (((n + 1 + 1 : ℕ) : ℝ)) := by
        exact_mod_cast Nat.succ_pos (n + 1)
      have hle_one : lam ≤ 1 := by
        dsimp [lam]
        have hdiv :
            (2 : ℝ) / (((n + 1 + 1 : ℕ) : ℝ)) ≤
              (((n + 1 + 1 : ℕ) : ℝ)) / (((n + 1 + 1 : ℕ) : ℝ)) :=
          div_le_div_of_nonneg_right htwo_le (le_of_lt hden_pos)
        calc
          (2 : ℝ) / (((n + 1 + 1 : ℕ) : ℝ)) ≤
              (((n + 1 + 1 : ℕ) : ℝ)) / (((n + 1 + 1 : ℕ) : ℝ)) := hdiv
          _ = 1 := div_self (ne_of_gt hden_pos)
      exact sub_nonneg.mpr hle_one
    have hmul_ih :
        (1 - lam) * Delta (n + 1) ≤
          (1 - lam) * (2 * A / (((n + 1 : ℕ) : ℝ))) := by
      exact mul_le_mul_of_nonneg_left ih hcoef_nonneg
    have hbound :
        Delta (n + 1 + 1) ≤
          (1 - lam) * (2 * A / (((n + 1 : ℕ) : ℝ))) +
            (A / 2) * lam ^ 2 := by
      have hrec_norm :
          Delta (n + 1 + 1) ≤
            (1 - lam) * Delta (n + 1) + (A / 2) * lam ^ 2 := by
        simpa [lam] using hrec_step
      nlinarith [hrec_norm, hmul_ih]
    have hscalar :
        (1 - lam) * (2 * A / (((n + 1 : ℕ) : ℝ))) +
            (A / 2) * lam ^ 2 ≤
          2 * A / (((n + 1 + 1 : ℕ) : ℝ)) := by
      have hden1_pos : 0 < (((n + 1 : ℕ) : ℝ)) := by
        exact_mod_cast Nat.succ_pos n
      have hden2_pos : 0 < (((n + 1 + 1 : ℕ) : ℝ)) := by
        exact_mod_cast Nat.succ_pos (n + 1)
      dsimp [lam]
      field_simp [ne_of_gt hden1_pos, ne_of_gt hden2_pos]
      ring_nf
      have hdiff :
          -(A * ((2 + n : ℕ) : ℝ) * 2) +
              A * ((2 + n : ℕ) : ℝ) ^ 2 +
              A * ((1 + n : ℕ) : ℝ) -
              A * ((2 + n : ℕ) : ℝ) * ((1 + n : ℕ) : ℝ) =
            -A := by
        norm_num
        ring_nf
      nlinarith [hA_nonneg, hdiff]
    exact le_trans hbound hscalar

/-- A normalized shifted Wolfe one-step inequality controls a triangular gap sum.

Given an iterate sequence, a potential `phi`, a gap certificate, and a reference
point `xMin`, assume the terminal shifted potential is nonnegative, the shifted
potential has the usual `2*A/(t+1)` residual rate on the summation window, and
each performed update satisfies the normalized Wolfe-step decrease inequality.
Then the weighted performed-update gap sum over `Icc 1 T` is bounded by
`3*T*A`.

Layer: Layer1 | Gap: Level 1 (shifted Wolfe-gap weighted-sum aggregation)
Proof: multiply each normalized one-step Wolfe inequality by
  `j*(j+2)/2`, rewrite it into the scalar shifted Delta-step normal form, and
  invoke the finite shifted weighted telescope.
Source: Mathlib finite sums over natural intervals and real ordered-field arithmetic
Used in: stochastic conditional-gradient sliding inner-loop convergence after
  the shifted one-step Wolfe decrease and residual-rate estimates
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem shifted_weighted_wolfeGap_sum_le_of_normalized_step
    {E : Type*} (iterate : ℕ → E) (phi : E → ℝ) (wolfeGap : E → ℝ)
    (xMin : E) (A : ℝ) (T : ℕ)
    (hA_nonneg : 0 ≤ A)
    (hDelta_terminal_nonneg : 0 ≤ phi (iterate (T + 2)) - phi xMin)
    (hDelta_bound : ∀ j, j ∈ Finset.Icc 1 T →
      phi (iterate (j + 1)) - phi xMin ≤ 2 * A / (((j + 1 : ℕ) : ℝ)))
    (hstep : ∀ j, j ∈ Finset.Icc 1 T →
      (2 / (((j + 2 : ℕ) : ℝ))) * wolfeGap (iterate (j + 1)) ≤
        (phi (iterate (j + 1)) - phi xMin) -
          (phi (iterate (j + 2)) - phi xMin) +
            (A / 2) * (2 / (((j + 2 : ℕ) : ℝ))) ^ 2) :
    Finset.sum (Finset.Icc 1 T)
        (fun j => (j : ℝ) * wolfeGap (iterate (j + 1))) ≤
      3 * (T : ℝ) * A := by
  classical
  let Delta : ℕ → ℝ := fun n => phi (iterate n) - phi xMin
  let gap : ℕ → ℝ := fun j => wolfeGap (iterate (j + 1))
  have hweighted_step : ∀ j, j ∈ Finset.Icc 1 T →
      (j : ℝ) * gap j ≤
        ((j : ℝ) * (((j + 2 : ℕ) : ℝ)) / 2) *
            (Delta (j + 1) - Delta (j + 2)) +
          A * (j : ℝ) / (((j + 2 : ℕ) : ℝ)) := by
    intro j hj
    let den : ℝ := (((j + 2 : ℕ) : ℝ))
    let c : ℝ := (j : ℝ) * den / 2
    have hden_pos : 0 < den := by
      dsimp [den]
      exact_mod_cast Nat.succ_pos (j + 1)
    have hc_nonneg : 0 ≤ c := by
      dsimp [c, den]
      positivity
    have hw_norm :
        (2 / den) * gap j ≤
          Delta (j + 1) - Delta (j + 2) + (A / 2) * (2 / den) ^ 2 := by
      simpa [Delta, gap, den, Nat.add_assoc, add_comm, add_left_comm, add_assoc]
        using hstep j hj
    have hmul := mul_le_mul_of_nonneg_left hw_norm hc_nonneg
    have hleft : c * ((2 / den) * gap j) = (j : ℝ) * gap j := by
      dsimp [c]
      field_simp [ne_of_gt hden_pos]
    have hright :
        c * (Delta (j + 1) - Delta (j + 2) + (A / 2) * (2 / den) ^ 2) =
          ((j : ℝ) * (((j + 2 : ℕ) : ℝ)) / 2) *
              (Delta (j + 1) - Delta (j + 2)) +
            A * (j : ℝ) / (((j + 2 : ℕ) : ℝ)) := by
      dsimp [c, den]
      field_simp [ne_of_gt hden_pos]
    nlinarith [hmul, hleft, hright]
  simpa [Delta, gap] using
    SOptLib.weighted_sum_le_three_mul_of_shifted_delta_step
      T A Delta gap hA_nonneg hDelta_terminal_nonneg
      (fun j hj => hDelta_bound j hj)
      hweighted_step

/-- An active-epoch predecessor residual bound absorbs into one tenth of the
global predecessor mass.

If each active residual is bounded by `b⁻¹` times its lower-triangular
predecessor mass, the active masses reindex to a global window, active sets are
prefix-closed subsets of `Icc 1 T`, and `b = 10*T`, then the window residual
sum is at most one tenth of the window mass.

Layer: Layer1 | Gap: Level 1 (active-epoch predecessor residual absorption)
Proof: reindex the residual sum to active epochs, sum the pointwise predecessor
  bounds, apply the multi-epoch triangular predecessor counting lemma, and
  cancel the `10*T` batch ratio in `ℝ`.
Source: Mathlib finite big-operator inequalities and ordered-field arithmetic
Used in: variance-reduced stochastic conditional-gradient residual absorption
  from epoch predecessor-prefix estimates
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/main_theorem/proof/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic conditional gradient -/
theorem sum_delta_le_ratio_sum_tilde_of_active_epoch_predecessor_bound_core
    {A K : Type*} (epochs : Finset A) (active : A → Finset ℕ)
    (idx : A → ℕ → K) (window : Finset K) (T b : ℕ)
    (tilde delta : K → ℝ) (P : A → ℕ → Prop)
    (hT_pos : 0 < T)
    (hb_choice : b = 10 * T)
    (hdelta_reindex :
      Finset.sum window delta =
        Finset.sum epochs (fun s =>
          Finset.sum (active s) (fun j => delta (idx s j))))
    (htilde_reindex :
      Finset.sum window tilde =
        Finset.sum epochs (fun s =>
          Finset.sum (active s) (fun j => tilde (idx s j))))
    (hactive : ∀ s r, r ∈ active s ↔ r ∈ Finset.Icc 1 T ∧ P s r)
    (hprefix : ∀ s {i j : ℕ}, i ≤ j → P s j → P s i)
    (hdelta_bound :
      ∀ s ∈ epochs, ∀ j ∈ active s,
        delta (idx s j) ≤
          (b : ℝ)⁻¹ *
            Finset.sum (Finset.Icc 2 j) (fun i => tilde (idx s (i - 1))))
    (htilde_nonneg : ∀ s ∈ epochs, ∀ r ∈ active s, 0 ≤ tilde (idx s r)) :
    Finset.sum window delta ≤ (1 / 10) * Finset.sum window tilde := by
  classical
  let triangleSum : ℝ :=
    Finset.sum epochs
      (fun s => Finset.sum (active s)
        (fun j => Finset.sum (Finset.Icc 2 j)
          (fun i => tilde (idx s (i - 1)))))
  have htri :
      triangleSum ≤ (T : ℝ) * Finset.sum window tilde := by
    dsimp [triangleSum]
    exact
      active_triangular_predecessor_sum_le_batch_mul_global_sum
        (epochs := epochs) (active := active) (T := T) (b := T)
        (idx := idx) (a := tilde) (P := P) (window := window)
        hactive hprefix htilde_reindex.symm (le_refl T) htilde_nonneg
  have hdelta_nested :
      Finset.sum epochs (fun s =>
          Finset.sum (active s) (fun j => delta (idx s j))) ≤
        (b : ℝ)⁻¹ * triangleSum := by
    calc
      Finset.sum epochs (fun s =>
          Finset.sum (active s) (fun j => delta (idx s j)))
          ≤ Finset.sum epochs (fun s =>
              Finset.sum (active s) (fun j =>
                (b : ℝ)⁻¹ *
                  Finset.sum (Finset.Icc 2 j)
                    (fun i => tilde (idx s (i - 1))))) := by
              exact Finset.sum_le_sum (fun s hs =>
                Finset.sum_le_sum (fun j hj => hdelta_bound s hs j hj))
      _ = (b : ℝ)⁻¹ * triangleSum := by
              dsimp [triangleSum]
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro s _hs
              rw [Finset.mul_sum]
  have hscale_tri :
      (b : ℝ)⁻¹ * triangleSum ≤
        (b : ℝ)⁻¹ * ((T : ℝ) * Finset.sum window tilde) := by
    exact mul_le_mul_of_nonneg_left htri (inv_nonneg.mpr (Nat.cast_nonneg b))
  have hratio :
      (b : ℝ)⁻¹ * ((T : ℝ) * Finset.sum window tilde) =
        (1 / 10) * Finset.sum window tilde := by
    have hT_ne : (T : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hT_pos)
    rw [hb_choice]
    norm_num
    field_simp [hT_ne]
  calc
    Finset.sum window delta
        = Finset.sum epochs (fun s =>
          Finset.sum (active s) (fun j => delta (idx s j))) := hdelta_reindex
    _ ≤ (b : ℝ)⁻¹ * triangleSum := hdelta_nested
    _ ≤ (b : ℝ)⁻¹ * ((T : ℝ) * Finset.sum window tilde) := hscale_tri
    _ = (1 / 10) * Finset.sum window tilde := hratio

/-- The standard SOptLib active-epoch partition absorbs predecessor residuals
into one tenth of the output-window mass.

This is the `global_index`/`activeEpochSteps` specialization of
`sum_delta_le_ratio_sum_tilde_of_active_epoch_predecessor_bound_core`; it
reconstructs the active-window reindexing from the canonical epoch decoder.

Layer: Layer1 | Gap: Level 1 (standard active-epoch predecessor residual absorption)
Proof: reconstruct the canonical active-epoch/output-window partition, invoke
  the abstract residual absorption theorem, and discharge prefix-closure for
  `global_index` by natural-number arithmetic.
Source: Mathlib finite big-operator inequalities and SOptLib epoch-index
  decoder APIs
Used in: variance-reduced stochastic conditional-gradient residual absorption
  over the theorem output window
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/main_theorem/proof/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic conditional gradient -/
theorem sum_delta_le_ratio_sum_tilde_of_active_epoch_predecessor_bound
    (T N b : ℕ) (tilde delta : ℕ → ℝ)
    (hT_pos : 0 < T)
    (hb_choice : b = 10 * T)
    (hdelta_epoch :
      ∀ s j, s ∈ Finset.Icc 0 N →
        j ∈ SOptLib.activeEpochSteps T N (SOptLib.global_index T) s →
          delta (SOptLib.global_index T s j) ≤
            (b : ℝ)⁻¹ *
              Finset.sum (Finset.Icc 2 j)
                (fun i => tilde (SOptLib.global_index T s (i - 1))))
    (htilde_nonneg : ∀ k ∈ Finset.Icc 1 N, 0 ≤ tilde k) :
    Finset.sum (Finset.Icc 1 N) delta ≤
      (1 / 10) * Finset.sum (Finset.Icc 1 N) tilde := by
  classical
  let active : ℕ → Finset ℕ := SOptLib.activeEpochSteps T N (SOptLib.global_index T)
  have hstep_mem_epoch :
      ∀ {k : ℕ}, k ∈ Finset.Icc 1 N →
        SOptLib.stepOfIndex T k ∈ Finset.Icc 1 T := by
    intro k _hk
    exact Finset.mem_Icc.mpr
      (SOptLib.stepOfIndex_mem_epoch (T := T) (k := k) hT_pos)
  have hleft :
      ∀ k ∈ Finset.Icc 1 N,
        SOptLib.global_index T
          (SOptLib.epochOfIndex T k) (SOptLib.stepOfIndex T k) = k := by
    intro k hk
    simpa [SOptLib.stepOfIndex_eq_mod_add_one] using
      (SOptLib.global_index_epochOfIndex_stepOfIndex
        (T := T) (k := k) (Finset.mem_Icc.mp hk).1)
  have hmem :
      ∀ k ∈ Finset.Icc 1 N,
        SOptLib.epochOfIndex T k ∈ Finset.Icc 0 N ∧
          SOptLib.stepOfIndex T k ∈ active (SOptLib.epochOfIndex T k) := by
    intro k hk
    constructor
    · rw [SOptLib.epochOfIndex_eq_div]
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, by
        have hdiv : (k - 1) / T ≤ k - 1 := Nat.div_le_self (k - 1) T
        have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
        exact le_trans hdiv (by omega)⟩
    · dsimp [active]
      exact SOptLib.stepOfIndex_mem_activeEpochSteps
        (T := T) (N := N)
        (globalIndex := SOptLib.global_index T)
        (epochOfIndex := SOptLib.epochOfIndex T)
        (stepOfIndex := SOptLib.stepOfIndex T)
        hstep_mem_epoch (fun {k} hk => hleft k hk) hk
  have hright :
      ∀ {s j : ℕ}, s ∈ Finset.Icc 0 N → j ∈ active s →
        SOptLib.global_index T s j ∈ Finset.Icc 1 N ∧
          SOptLib.epochOfIndex T (SOptLib.global_index T s j) = s ∧
            SOptLib.stepOfIndex T (SOptLib.global_index T s j) = j := by
    intro s j _hs hj
    have hj_epoch :
        1 ≤ j ∧ j ≤ T := by
      exact SOptLib.activeEpochSteps_mem_epoch (T := T) (N := N)
        (globalIndex := SOptLib.global_index T) (s := s) (j := j) hj
    have hidx_pos : 1 ≤ SOptLib.global_index T s j := by
      simp [SOptLib.global_index_def]
      omega
    constructor
    · exact
        SOptLib.global_index_mem_output_window_of_active_epoch_step
          (T := T) (N := N) (globalIndex := SOptLib.global_index T)
          (s := s) (j := j) hidx_pos hj
    · constructor
      · simpa [SOptLib.global_index_def] using
          (SOptLib.epochOfIndex_mul_add_eq_of_pos_le
            (T := T) (s := s) (j := j) hj_epoch.1 hj_epoch.2)
      · exact SOptLib.nat_stepOf_globalIndex_eq
          (T := T) (s := s) (j := j) hj_epoch.1 hj_epoch.2
  have hdelta_reindex :
      Finset.sum (Finset.Icc 1 N) delta =
        Finset.sum (Finset.Icc 0 N)
          (fun s => Finset.sum (active s)
            (fun j => delta (SOptLib.global_index T s j))) := by
    simpa [active] using
      SOptLib.sum_output_window_eq_sum_active_epoch_steps
        (R := ℝ) (N := N) (S := N) (A := delta)
        (activeEpochSteps := active)
        (globalIndex := SOptLib.global_index T)
        (epochOfIndex := SOptLib.epochOfIndex T)
        (stepOfIndex := SOptLib.stepOfIndex T)
        hmem hleft hright
  have htilde_reindex :
      Finset.sum (Finset.Icc 1 N) tilde =
        Finset.sum (Finset.Icc 0 N)
          (fun s => Finset.sum (active s)
            (fun j => tilde (SOptLib.global_index T s j))) := by
    simpa [active] using
      SOptLib.sum_output_window_eq_sum_active_epoch_steps
        (R := ℝ) (N := N) (S := N) (A := tilde)
        (activeEpochSteps := active)
        (globalIndex := SOptLib.global_index T)
        (epochOfIndex := SOptLib.epochOfIndex T)
        (stepOfIndex := SOptLib.stepOfIndex T)
        hmem hleft hright
  have hactive :
      ∀ s r, r ∈ active s ↔
        r ∈ Finset.Icc 1 T ∧ SOptLib.global_index T s r ≤ N := by
    intro s r
    simp [active, SOptLib.mem_activeEpochSteps]
  have hprefix :
      ∀ s {i j : ℕ}, i ≤ j →
        SOptLib.global_index T s j ≤ N →
          SOptLib.global_index T s i ≤ N := by
    intro s i j hij hjN
    exact SOptLib.global_index_le_of_step_le (T := T) (s := s) hij hjN
  have htilde_active_nonneg :
      ∀ s ∈ Finset.Icc 0 N, ∀ r ∈ active s,
        0 ≤ tilde (SOptLib.global_index T s r) := by
    intro s _hs r hr
    have hr_epoch :
        1 ≤ r ∧ r ≤ T := by
      exact SOptLib.activeEpochSteps_mem_epoch (T := T) (N := N)
        (globalIndex := SOptLib.global_index T) (s := s) (j := r) hr
    have hidx_pos : 1 ≤ SOptLib.global_index T s r := by
      simp [SOptLib.global_index_def]
      omega
    have hwin : SOptLib.global_index T s r ∈ Finset.Icc 1 N :=
      SOptLib.global_index_mem_output_window_of_active_epoch_step
        (T := T) (N := N) (globalIndex := SOptLib.global_index T)
        (s := s) (j := r) hidx_pos hr
    exact htilde_nonneg _ hwin
  exact
    sum_delta_le_ratio_sum_tilde_of_active_epoch_predecessor_bound_core
      (epochs := Finset.Icc 0 N) (active := active)
      (idx := fun s j => SOptLib.global_index T s j)
      (window := Finset.Icc 1 N) (T := T) (b := b)
      (tilde := tilde) (delta := delta)
      (P := fun s r => SOptLib.global_index T s r ≤ N)
      hT_pos hb_choice hdelta_reindex htilde_reindex hactive hprefix
      (fun s hs j hj => hdelta_epoch s j hs hj) htilde_active_nonneg

end SOptLib

-- Phase 4 merged from focused staging declarations.

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: accelerated_gamma_terminal_raw_bound_of_telescope_and_distance
--   exposes the scalar Gamma-normalized terminal bound obtained by combining
--   an accelerated raw telescope with a distance-telescope budget; orig was
--   partB_pathwise_gamma_terminal_raw_coeff_bound, renamed away from Part B
--   and paper-local setup fields.
-- generality used: all data are real scalar streams over natural time plus a
--   positive-time Gamma value; no measure, independence, integrability,
--   convexity, smoothness, oracle, topology, normed-space, or finite-dimensional
--   assumptions are used by this algebraic proof-composition step.
-- portable call pattern: accelerated stochastic-gradient, accelerated mirror,
--   and variance-reduced pathwise proofs can provide a raw Gamma telescope,
--   terminal Gamma positivity, finite-window Gamma/alpha nonzeroness, the
--   alpha-one boundary cancellation, and a weighted distance telescope while
--   changing the concrete gradient, noise, residual, and distance streams.
-- counterargument checked: this is not merely paper traceability because the
--   conclusion packages the recurring transition from raw Gamma telescope to
--   terminal raw bound after distance domination; the only full existing hit
--   was the local private theorem, while the staged scalar division helper
--   covers only one internal normalization substep.
-- coverage search: searched `terminal objective gap bound from raw gamma
--   telescope distance telescope raw gradient noise residual`, `distance
--   telescope terminal bound raw gradient raw noise residual`, and `divide
--   inequality positive gamma subtract multiplied sum upper bound`; closest
--   hits were SOptLib `summed_one_step_gap_bound_of_telescope` and
--   `accelerated_expected_gap_bound_of_pathwise_telescope`, plus staged
--   `div_sub_le_sum_of_sub_mul_le_mul_sum`, all partial rather than full.
-- minimal hypotheses: nonzeroness is required only on the finite window
--   denominators used to rewrite the retained raw-gradient sum, positivity is
--   required only to divide by terminal Gamma, the boundary cancellation is
--   exactly `alpha 1 = 1`, and the distance budget is a single pointwise
--   scalar inequality.

/-- A raw accelerated Gamma telescope and a distance budget give a terminal raw bound.

The theorem abstracts the finite-window algebra in which the raw telescope
contains a retained gradient sum, a weighted distance-difference sum, and a
combined noise/residual sum.  After the `alpha 1 = 1` boundary cancellation
and a distance telescope bound, the terminal quantity divided by the terminal
Gamma is bounded by the distance budget minus the raw gradient sum plus the
raw noise and residual sums.

Layer: Layer1 | Gap: Level 1 (Gamma-normalized accelerated terminal telescope)
Proof: identify the raw telescope sums with the named gradient, distance,
  noise, and residual sums by finite-sum congruence, apply positive Gamma
  scalar normalization, and substitute the distance budget by ordered real
  arithmetic.
Source: Mathlib finite-sum congruence, ordered-field normalization, and
  linear real arithmetic
Used in: nonconvex stochastic accelerated gradient descent after the raw
  Part B Gamma telescope and before coefficient simplification of the
  gradient and oracle-noise budgets
Book citation: book/FOML/NonconvexStochasticAcceleratedGD.json#/main_theorem/proof/18
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic accelerated gradient descent -/
theorem accelerated_gamma_terminal_raw_bound_of_telescope_and_distance
    (A alpha beta gamma gradCoeff noiseCoeff distDiff : ℕ → ℝ)
    (gradSq noiseSq residualTerm : (t : ℕ) → 1 ≤ t → ℝ)
    (Gamma : (t : ℕ) → 1 ≤ t → ℝ) (N : ℕ) (hN : 1 ≤ N) (dist : ℝ)
    (hGamma_pos : 0 < Gamma N hN)
    (hGamma_ne : ∀ t (ht : t ∈ Finset.Icc 1 N),
      Gamma t (Finset.mem_Icc.mp ht).1 ≠ 0)
    (halpha_ne : ∀ t, t ∈ Finset.Icc 1 N → alpha t ≠ 0)
    (halpha_one : alpha 1 = 1)
    (htelescope :
      let GammaNat : ℕ → ℝ := fun t => if ht : 1 ≤ t then Gamma t ht else 1
      let Lterm : ℕ → ℝ := fun t =>
        if ht : 1 ≤ t then
          -(beta t / alpha t) * gradCoeff t * gradSq t ht
        else 0
      let Bterm : ℕ → ℝ := fun t => if _ht : 1 ≤ t then distDiff t else 0
      let Dterm : ℕ → ℝ := fun t =>
        if ht : 1 ≤ t then noiseCoeff t * noiseSq t ht + residualTerm t ht else 0
      A N - Gamma N hN *
          Finset.sum (Finset.Icc 1 N) (fun t => alpha t / GammaNat t * Lterm t) ≤
        Gamma N hN * (1 - alpha 1) * A 0 +
          Gamma N hN *
            Finset.sum (Finset.Icc 1 N)
              (fun t => alpha t / (gamma t * GammaNat t) * Bterm t) +
          Gamma N hN *
            Finset.sum (Finset.Icc 1 N) (fun t => Dterm t / GammaNat t))
    (hdistance :
      Finset.sum (Finset.Icc 1 N).attach (fun k =>
        alpha k.1 / (gamma k.1 * Gamma k.1 (Finset.mem_Icc.mp k.2).1) *
          distDiff k.1) ≤ dist) :
    A N / Gamma N hN ≤
      dist -
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          (Gamma k.1 (Finset.mem_Icc.mp k.2).1)⁻¹ *
            beta k.1 * gradCoeff k.1 * gradSq k.1 (Finset.mem_Icc.mp k.2).1) +
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          (Gamma k.1 (Finset.mem_Icc.mp k.2).1)⁻¹ *
            noiseCoeff k.1 * noiseSq k.1 (Finset.mem_Icc.mp k.2).1) +
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          (Gamma k.1 (Finset.mem_Icc.mp k.2).1)⁻¹ *
            residualTerm k.1 (Finset.mem_Icc.mp k.2).1) := by
  classical
  let GammaNat : ℕ → ℝ := fun t => if ht : 1 ≤ t then Gamma t ht else 1
  let Lterm : ℕ → ℝ := fun t =>
    if ht : 1 ≤ t then
      -(beta t / alpha t) * gradCoeff t * gradSq t ht
    else 0
  let Bterm : ℕ → ℝ := fun t => if _ht : 1 ≤ t then distDiff t else 0
  let Dterm : ℕ → ℝ := fun t =>
    if ht : 1 ≤ t then noiseCoeff t * noiseSq t ht + residualTerm t ht else 0
  let rawGrad : ℝ :=
    Finset.sum (Finset.Icc 1 N).attach (fun k =>
      (Gamma k.1 (Finset.mem_Icc.mp k.2).1)⁻¹ *
        beta k.1 * gradCoeff k.1 * gradSq k.1 (Finset.mem_Icc.mp k.2).1)
  let distanceSum : ℝ :=
    Finset.sum (Finset.Icc 1 N).attach (fun k =>
      alpha k.1 / (gamma k.1 * Gamma k.1 (Finset.mem_Icc.mp k.2).1) *
        distDiff k.1)
  let rawNoise : ℝ :=
    Finset.sum (Finset.Icc 1 N).attach (fun k =>
      (Gamma k.1 (Finset.mem_Icc.mp k.2).1)⁻¹ *
        noiseCoeff k.1 * noiseSq k.1 (Finset.mem_Icc.mp k.2).1)
  let residual : ℝ :=
    Finset.sum (Finset.Icc 1 N).attach (fun k =>
      (Gamma k.1 (Finset.mem_Icc.mp k.2).1)⁻¹ *
        residualTerm k.1 (Finset.mem_Icc.mp k.2).1)
  have hbase :
      A N - Gamma N hN * (-rawGrad) ≤
        Gamma N hN * distanceSum + Gamma N hN * rawNoise + Gamma N hN * residual := by
    have htel' :
        A N - Gamma N hN *
            Finset.sum (Finset.Icc 1 N) (fun t => alpha t / GammaNat t * Lterm t) ≤
          Gamma N hN * (1 - alpha 1) * A 0 +
            Gamma N hN *
              Finset.sum (Finset.Icc 1 N)
                (fun t => alpha t / (gamma t * GammaNat t) * Bterm t) +
            Gamma N hN *
              Finset.sum (Finset.Icc 1 N) (fun t => Dterm t / GammaNat t) := by
      simpa [GammaNat, Lterm, Bterm, Dterm] using htelescope
    have hLsum :
        Finset.sum (Finset.Icc 1 N) (fun t => alpha t / GammaNat t * Lterm t) =
          -rawGrad := by
      calc
        Finset.sum (Finset.Icc 1 N) (fun t => alpha t / GammaNat t * Lterm t) =
            Finset.sum (Finset.Icc 1 N).attach
              (fun k => alpha k.1 / GammaNat k.1 * Lterm k.1) := by
                simpa using
                  (Finset.sum_attach (s := Finset.Icc 1 N)
                    (f := fun t => alpha t / GammaNat t * Lterm t)).symm
        _ =
            Finset.sum (Finset.Icc 1 N).attach (fun k =>
              -((Gamma k.1 (Finset.mem_Icc.mp k.2).1)⁻¹ *
                beta k.1 * gradCoeff k.1 *
                  gradSq k.1 (Finset.mem_Icc.mp k.2).1)) := by
              refine Finset.sum_congr rfl ?_
              intro k _hk
              have hk1 : 1 ≤ k.1 := (Finset.mem_Icc.mp k.2).1
              have hαne : alpha k.1 ≠ 0 := halpha_ne k.1 k.2
              have hΓne : Gamma k.1 hk1 ≠ 0 := hGamma_ne k.1 k.2
              dsimp [GammaNat, Lterm]
              simp [hk1]
              field_simp [hαne, hΓne]
        _ = -rawGrad := by
              simp [rawGrad, Finset.sum_neg_distrib]
    have hBsum :
        Finset.sum (Finset.Icc 1 N)
            (fun t => alpha t / (gamma t * GammaNat t) * Bterm t) =
          distanceSum := by
      calc
        Finset.sum (Finset.Icc 1 N)
            (fun t => alpha t / (gamma t * GammaNat t) * Bterm t) =
            Finset.sum (Finset.Icc 1 N).attach
              (fun k => alpha k.1 / (gamma k.1 * GammaNat k.1) * Bterm k.1) := by
                simpa using
                  (Finset.sum_attach (s := Finset.Icc 1 N)
                    (f := fun t => alpha t / (gamma t * GammaNat t) * Bterm t)).symm
        _ = distanceSum := by
              dsimp [distanceSum]
              refine Finset.sum_congr rfl ?_
              intro k _hk
              have hk1 : 1 ≤ k.1 := (Finset.mem_Icc.mp k.2).1
              dsimp [GammaNat, Bterm]
              simp [hk1]
    have hDsum :
        Finset.sum (Finset.Icc 1 N) (fun t => Dterm t / GammaNat t) =
          rawNoise + residual := by
      calc
        Finset.sum (Finset.Icc 1 N) (fun t => Dterm t / GammaNat t) =
            Finset.sum (Finset.Icc 1 N).attach (fun k => Dterm k.1 / GammaNat k.1) := by
              simpa using
                (Finset.sum_attach (s := Finset.Icc 1 N)
                  (f := fun t => Dterm t / GammaNat t)).symm
        _ =
            Finset.sum (Finset.Icc 1 N).attach (fun k =>
              (Gamma k.1 (Finset.mem_Icc.mp k.2).1)⁻¹ *
                  noiseCoeff k.1 * noiseSq k.1 (Finset.mem_Icc.mp k.2).1 +
                (Gamma k.1 (Finset.mem_Icc.mp k.2).1)⁻¹ *
                  residualTerm k.1 (Finset.mem_Icc.mp k.2).1) := by
              refine Finset.sum_congr rfl ?_
              intro k _hk
              have hk1 : 1 ≤ k.1 := (Finset.mem_Icc.mp k.2).1
              dsimp [GammaNat, Dterm]
              simp [hk1, div_eq_mul_inv]
              ring
        _ = rawNoise + residual := by
              simp [rawNoise, residual, Finset.sum_add_distrib]
    calc
      A N - Gamma N hN * (-rawGrad)
          = A N - Gamma N hN *
              Finset.sum (Finset.Icc 1 N) (fun t => alpha t / GammaNat t * Lterm t) := by
              rw [hLsum]
      _ ≤ Gamma N hN * (1 - alpha 1) * A 0 +
            Gamma N hN *
              Finset.sum (Finset.Icc 1 N)
                (fun t => alpha t / (gamma t * GammaNat t) * Bterm t) +
            Gamma N hN *
              Finset.sum (Finset.Icc 1 N) (fun t => Dterm t / GammaNat t) := htel'
      _ = Gamma N hN * distanceSum + Gamma N hN * rawNoise + Gamma N hN * residual := by
            rw [hBsum, hDsum, halpha_one]
            ring
  have hnorm :
      A N / Gamma N hN + rawGrad ≤ distanceSum + rawNoise + residual := by
    have hdiv :=
      div_sub_le_sum_of_sub_mul_le_mul_sum
        (A := A N) (L := -rawGrad) (C := distanceSum) (B := rawNoise)
        (D := residual) (gamma := Gamma N hN) hGamma_pos hbase
    linarith
  have hdist' : distanceSum ≤ dist := by
    simpa [distanceSum] using hdistance
  change A N / Gamma N hN ≤ dist - rawGrad + rawNoise + residual
  linarith


-- Generalization plan (G0):
-- concept/name: terminal_bound_with_simplified_gradient_noise_of_raw_bound
--   exposes the scalar upper-bound simplification that replaces a retained
--   raw gradient penalty and raw noise term by simplified gradient and noise
--   budgets; orig was partB_pathwise_gamma_terminal_bound, renamed away from
--   Part B and all paper-local setup fields.
-- generality used: seven real scalars and three order hypotheses are all the
--   proof uses; there are no measure, independence, integrability, convexity,
--   smoothness, oracle, topology, normed-space, or finite-dimensional
--   assumptions.
-- portable call pattern: accelerated stochastic-gradient, accelerated mirror,
--   and variance-reduced pathwise proofs can call this after a raw terminal
--   telescope bound and separate coefficient comparisons, while changing the
--   concrete terminal quantity, distance budget, gradient sum, noise sum, and
--   residual expression.
-- counterargument checked: this is not just paper-local traceability because
--   it packages a recurring ordered-real transition after telescoping; it is
--   not a pure rename of Mathlib because the needed contract combines a raw
--   terminal bound with two monotone substitutions in opposite-signed terms.
-- coverage search: searched `terminal bound simplified gradient noise raw
--   bound scalar inequalities`, `real upper bound replace terms by larger
--   bounds`, and LeanSearch `real inequality replace two terms by upper
--   bounds in an additive upper bound`; closest hits were the local private
--   theorem, staged `accelerated_gamma_terminal_raw_bound_of_telescope_and_distance`,
--   and generic additive/order lemmas, all partial rather than full.
-- minimal hypotheses: all hypotheses are pointwise scalar inequalities; no
--   positivity or nonzeroness assumptions are needed for this final
--   simplification once the raw and coefficient bounds are supplied.

/-- A raw terminal bound with gradient and noise coefficient comparisons gives
the corresponding simplified terminal bound.

If a terminal quantity is bounded by `dist - rawGrad + rawNoise + residual`,
then any lower bound `gradBudget ≤ rawGrad` and upper bound
`rawNoise ≤ noiseBudget` may be substituted into the opposite-signed gradient
and noise slots.

Layer: Layer1 | Gap: Level 1 (scalar terminal-bound coefficient simplification)
Proof: use ordered real arithmetic to combine the raw terminal bound with the
  lower gradient-budget comparison and the upper noise-budget comparison.
Source: Mathlib ordered real linear arithmetic
Used in: nonconvex stochastic accelerated gradient descent after the Part B
  raw Gamma terminal telescope and before isolating the weighted search-gradient
  sum
Book citation: book/FOML/NonconvexStochasticAcceleratedGD.json#/main_theorem/proof/20
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic accelerated gradient descent -/
theorem terminal_bound_with_simplified_gradient_noise_of_raw_bound
    (terminal dist rawGrad gradBudget rawNoise noiseBudget residual : ℝ)
    (hraw : terminal ≤ dist - rawGrad + rawNoise + residual)
    (hgrad : gradBudget ≤ rawGrad)
    (hnoise : rawNoise ≤ noiseBudget) :
    terminal ≤ dist - gradBudget + noiseBudget + residual := by
  linarith


-- Generalization plan (G0):
-- concept/name: isolate a retained weighted sum from a nonnegative terminal upper bound; orig was partB_pathwise_weighted_gradient_le_noise_residual
-- generality used: real ordered additive arithmetic only; no carrier typeclasses, measures, convexity, smoothness, oracle, or finite-dimensional assumptions are used
-- portable call pattern: accelerated or telescoping stochastic-optimization proofs after a pathwise terminal bound `terminal <= dist - weightedSum + noise + residual` and a minimizer or feasibility argument proving `0 <= terminal`
-- counterargument checked: the proof is short, but it is not paper-local traceability because the same scalar isolation step recurs after terminal-gap telescopes; it is not covered by the adjacent coefficient-simplification lemma, which still concludes a terminal upper bound
-- coverage search: queried "weighted sum less equal noise residual nonnegative terminal bound", "isolate weighted gradient sum terminal nonnegative pathwise terminal bound", and the precise terminal/nonnegative inequality shape; hits were local/private theorem, related terminal_bound_with_simplified_gradient_noise_of_raw_bound, and unrelated finite-sum telescopes, with no full duplicate
-- minimal hypotheses: all already minimal; the caller-side minimizer and positive Gamma assumptions are compressed to the pointwise scalar hypothesis `0 <= terminal`

/-- A nonnegative terminal bound isolates the retained weighted sum.

If a terminal quantity is nonnegative and is bounded above by a distance budget
minus a weighted sum plus noise and residual terms, then the weighted sum is
bounded by the distance, noise, and residual budgets.

Layer: Layer1 | Gap: Level 1 (scalar terminal-bound weighted-sum isolation)
Proof: combine the terminal nonnegativity and terminal upper bound by ordered real arithmetic.
Source: Mathlib ordered real linear arithmetic
Used in: nonconvex stochastic accelerated gradient descent after the convex Part B terminal pathwise recursion and before converting the weighted search-gradient numerator into the randomized output bound
Book citation: book/FOML/NonconvexStochasticAcceleratedGD.json#/main_theorem/proof/steps/22
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, nonconvex stochastic accelerated gradient descent -/
theorem weighted_sum_le_noise_residual_of_nonneg_terminal_bound
    (terminal weightedSum dist noise residual : ℝ)
    (hterminal_nonneg : 0 ≤ terminal)
    (hpath : terminal ≤ dist - weightedSum + noise + residual) :
    weightedSum ≤ dist + noise + residual := by
  linarith

end SOptLib

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: finite constant-scaled sum bound from pointwise drop-plus-noise bounds; orig was theorem69_weighted_descent_telescope_bound_of_fixed_step.
-- generality used: arbitrary finite index type with real-valued gap, drop, and noise functions; no measure, convexity, smoothness, oracle, or vector-space assumptions are used.
-- portable call pattern: convergence proofs that have per-time weighted stationarity bounds `c * gap i <= drop i + noise i` and a finite-window aggregate drop budget call this before normalizing an output distribution; the index type, gap, drop, noise, scalar, and budget change while the conclusion shape remains fixed.
-- counterargument checked: this is more than paper-local traceability because it packages the recurring finite-window aggregation step; it is not a pure wrapper around `Finset.sum_le_sum` because it also factors the constant and absorbs an independent aggregate budget.
-- coverage search: searched "finset constant multiply sum less equal telescope add sum pointwise less equal aggregate budget", "weighted gap sum bound pointwise drop noise aggregate telescope budget", and LeanSearch "finite sum pointwise inequality sum drop bounded by budget implies constant times sum gap bounded by budget plus sum noise"; top hits were `Finset.sum_le_sum`, `summed_one_step_gap_bound_of_telescope`, `active_sum_objective_drop_add_scalar_budget`, and active-window budget lemmas, all partial rather than this flat constant-scaled statement.
-- minimal hypotheses: all already minimal for the real scalar use; no nonnegativity of the scalar is needed because the scaled inequality is supplied pointwise.

/-- Aggregate constant-scaled pointwise bounds with a finite drop budget.

If every indexed term satisfies `c * gap i <= drop i + noise i`, and the total
drop is bounded by `budget`, then the constant-scaled finite gap sum is bounded
by the budget plus the finite noise sum.

Layer: Layer1 | Gap: Level 1 (finite-window scaled descent aggregation)
Proof: factor the constant through the finite sum, apply `Finset.sum_le_sum` to
  the pointwise bounds, split the sum over addition, and absorb the aggregate
  drop budget by monotonicity of addition.
Source: Mathlib finite big-operator distributivity and ordered real arithmetic
Used in: nonconvex stochastic block mirror descent finite-window projected-gradient numerator aggregation after fixed-time descent bounds and objective-drop telescoping
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, nonconvex stochastic block mirror descent -/
theorem finset_const_mul_sum_le_telescope_add_sum_of_pointwise_le
    {α : Type*} (s : Finset α) (c budget : ℝ)
    (gap drop noise : α → ℝ)
    (hpoint : ∀ i ∈ s, c * gap i ≤ drop i + noise i)
    (hdrop : Finset.sum s drop ≤ budget) :
    c * Finset.sum s gap ≤ budget + Finset.sum s noise := by
  classical
  calc
    c * Finset.sum s gap = Finset.sum s (fun i => c * gap i) := by
      rw [Finset.mul_sum]
    _ ≤ Finset.sum s (fun i => drop i + noise i) := by
      exact Finset.sum_le_sum hpoint
    _ = Finset.sum s drop + Finset.sum s noise := by
      rw [Finset.sum_add_distrib]
    _ ≤ budget + Finset.sum s noise := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right hdrop (Finset.sum s noise)

end SOptLib

/-- Aggregate a finite-window pointwise bound with two independently budgeted telescope sums.

If a retained total is bounded by the finite sum of pointwise gaps, each gap is
bounded by two drop terms, two retained budget terms, and a correction, and the
two drop sums have scalar budgets, then the retained total is bounded by the
sum of those scalar budgets plus the retained finite sums minus the correction
sum.

Layer: Layer1 | Gap: Level 1 (finite-window two-telescope budget aggregation)
Proof: sum the pointwise inequalities, split finite sums over addition and
  subtraction, then compose the two aggregate telescope budgets by ordered-real
  arithmetic.
Source: Mathlib finite big-operator distributivity and ordered real arithmetic
Used in: stochastic saddle-point maximized-regret pathwise budget after combining the stochastic mirror step, the auxiliary residual mirror step, and the two prox telescopes
Book citation: book/FOML/StochasticConvexConcaveSaddlePoint.json#/key_lemmas/1/proof/11
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic convex-concave saddle point mirror descent -/
theorem two_telescope_pathwise_budget_of_pointwise_combined_bounds
    {τ : Type*} (times : Finset τ)
    (gap dz dv q1 q2 correction : τ → ℝ)
    (budgetZ budgetV total : ℝ)
    (htotal : total ≤ Finset.sum times gap)
    (hpoint : ∀ t ∈ times,
      gap t ≤ dz t + dv t + q1 t + q2 t - correction t)
    (hbudgetZ : Finset.sum times dz ≤ budgetZ)
    (hbudgetV : Finset.sum times dv ≤ budgetV) :
    total ≤
      budgetZ + budgetV + Finset.sum times q1 + Finset.sum times q2 -
        Finset.sum times correction := by
  classical
  have hsumPoint :
      Finset.sum times gap ≤
        Finset.sum times (fun t => dz t + dv t + q1 t + q2 t - correction t) := by
    exact Finset.sum_le_sum hpoint
  have hsplit :
      Finset.sum times (fun t => dz t + dv t + q1 t + q2 t - correction t) =
        Finset.sum times dz + Finset.sum times dv +
          Finset.sum times q1 + Finset.sum times q2 -
            Finset.sum times correction := by
    simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  linarith

/-- A normalized weighted gap sum is bounded by a normalized max-regret certificate.

If every pointwise gap is bounded by a regret summand, all finite-window weights
are nonnegative, and the weighted regret sum is bounded by `maxRegret`, then
the same positive normalizer bounds the weighted gap sum by `maxRegret`.

Layer: Layer1 | Gap: Level 0 (normalized weighted finite-sum regret handoff)
Proof: scale the pointwise gap inequalities by nonnegative weights, sum them
  over the finite window, compose with the max-regret certificate, and multiply
  by the nonnegative inverse of the positive normalizer.
Source: Mathlib `Finset.sum_le_sum` and ordered real scalar multiplication
Used in: stochastic convex-concave saddle-point mirror descent when converting pointwise saddle-gap subgradient bounds into the selected maximized-regret numerator before normalized output estimates
Book citation: book/FOML/StochasticConvexConcaveSaddlePoint.json#/main_theorem/proof
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent for stochastic convex-concave saddle point problems -/
theorem weighted_gap_sum_le_inv_max_regret_of_pointwise_le
    {T : Type*} (times : Finset T)
    (gamma gap regretTerm : T → ℝ) (weightSum maxRegret : ℝ)
    (hgamma_nonneg : ∀ t ∈ times, 0 ≤ gamma t)
    (hweightSum_pos : 0 < weightSum)
    (hpoint : ∀ t ∈ times, gap t ≤ regretTerm t)
    (hmaxRegret :
      Finset.sum times (fun t => gamma t * regretTerm t) ≤ maxRegret) :
    weightSum⁻¹ * Finset.sum times (fun t => gamma t * gap t) ≤
      weightSum⁻¹ * maxRegret := by
  classical
  have hsum :
      Finset.sum times (fun t => gamma t * gap t) ≤
        Finset.sum times (fun t => gamma t * regretTerm t) := by
    refine Finset.sum_le_sum ?_
    intro t ht
    exact mul_le_mul_of_nonneg_left (hpoint t ht) (hgamma_nonneg t ht)
  have hnormalizer_nonneg : 0 ≤ weightSum⁻¹ :=
    inv_nonneg.mpr (le_of_lt hweightSum_pos)
  exact mul_le_mul_of_nonneg_left (le_trans hsum hmaxRegret) hnormalizer_nonneg

namespace SOptLib

/-- A weighted-average convex-concave saddle gap is bounded by normalized
maximized regret.

If the averaged primal and dual outputs are the weighted averages of feasible
iterates, Jensen bounds the cross gap against any selected comparison pair by
the normalized weighted sum of pointwise cross gaps. A supplied regret bound for
that weighted sum then gives the final normalized regret estimate.

Layer: Layer1 | Gap: Level 1 (convex-concave weighted-output saddle-gap to regret)
Proof: apply finite weighted Jensen separately to the primal payoff and the
  negated dual payoff, add the two inequalities, distribute the finite sums,
  and compose with the supplied normalized weighted-regret bound.
Source: Mathlib finite Jensen inequality `ConvexOn.map_sum_le`, SOptLib
  carrier totalization, and finite-sum ordered real algebra
Used in: stochastic convex-concave saddle-point mirror descent when converting
  the weighted average output saddle gap into the selected maximized regret
  before martingale and deterministic regret estimates are combined
Book citation: book/FOML/StochasticConvexConcaveSaddlePoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent for stochastic convex-concave
  saddle point problems -/
theorem saddleGap_weightedAverage_le_inv_max_regret_of_convex_concave
    {T EX EY : Type*}
    [AddCommGroup EX] [Module ℝ EX]
    [AddCommGroup EY] [Module ℝ EY]
    (s : Finset T) (γ : T → ℝ) (W regret : ℝ)
    (X : Set EX) (Y : Set EY)
    (L : {x : EX // x ∈ X} → {y : EY // y ∈ Y} → ℝ)
    (x : T → {x : EX // x ∈ X}) (y : T → {y : EY // y ∈ Y})
    (xbar xStar : {x : EX // x ∈ X}) (ybar yStar : {y : EY // y ∈ Y})
    (hL_convex_x :
      ConvexOn ℝ X (totalizeOn X (fun x' => L x' yStar)))
    (hL_concave_y :
      ConvexOn ℝ Y
        (fun y' => -(totalizeOn Y (fun y'' => L xStar y'') y')))
    (hγ_nonneg : ∀ t ∈ s, 0 ≤ γ t)
    (hW_pos : 0 < W)
    (hW_eq : W = ∑ t ∈ s, γ t)
    (hxbar :
      xbar.1 = W⁻¹ • Finset.sum s (fun t => γ t • (x t).1))
    (hybar :
      ybar.1 = W⁻¹ • Finset.sum s (fun t => γ t • (y t).1))
    (hregret :
      W⁻¹ * Finset.sum s (fun t =>
        γ t * SOptLib.saddleGap L (x t, y t) (xStar, yStar)) ≤ W⁻¹ * regret) :
    SOptLib.saddleGap L (xbar, ybar) (xStar, yStar) ≤ W⁻¹ * regret := by
  classical
  change L xbar yStar - L xStar ybar ≤ W⁻¹ * regret
  have hregret_raw :
      W⁻¹ * Finset.sum s (fun t =>
        γ t * (L (x t) yStar - L xStar (y t))) ≤ W⁻¹ * regret := by
    simpa [SOptLib.saddleGap] using hregret
  have hJx :
      L xbar yStar ≤
        W⁻¹ * Finset.sum s (fun t => γ t * L (x t) yStar) := by
    have hraw :=
      convexOn_weighted_average_le_weighted_sum
        (hf := hL_convex_x) (s := s) (γ := γ)
        (p := fun t => (x t).1) (xbar := xbar.1) (W := W)
        hγ_nonneg (fun t _ht => (x t).2) hW_pos hW_eq hxbar
    simpa [totalizeOn_of_mem X (fun x' => L x' yStar) xbar.2] using hraw
  have hJy :
      -L xStar ybar ≤
        W⁻¹ * Finset.sum s (fun t => γ t * (-L xStar (y t))) := by
    have hraw :=
      convexOn_weighted_average_le_weighted_sum
        (hf := hL_concave_y) (s := s) (γ := γ)
        (p := fun t => (y t).1) (xbar := ybar.1) (W := W)
        hγ_nonneg (fun t _ht => (y t).2) hW_pos hW_eq hybar
    simpa [totalizeOn_of_mem Y (fun y'' => L xStar y'') ybar.2] using hraw
  have hadd := add_le_add hJx hJy
  have hsum_eq :
      W⁻¹ * Finset.sum s (fun t => γ t * L (x t) yStar) +
          W⁻¹ * Finset.sum s (fun t => γ t * (-L xStar (y t))) =
        W⁻¹ * Finset.sum s (fun t =>
          γ t * (L (x t) yStar - L xStar (y t))) := by
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro t ht
    ring
  calc
    L xbar yStar - L xStar ybar =
        L xbar yStar + (-L xStar ybar) := by ring
    _ ≤
        W⁻¹ * Finset.sum s (fun t => γ t * L (x t) yStar) +
          W⁻¹ * Finset.sum s (fun t => γ t * (-L xStar (y t))) := hadd
    _ =
        W⁻¹ * Finset.sum s (fun t =>
          γ t * (L (x t) yStar - L xStar (y t))) := hsum_eq
    _ ≤ W⁻¹ * regret := hregret_raw

end SOptLib
