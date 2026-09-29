import SOptLib.Layer1.Telescope

open scoped BigOperators InnerProductSpace

-- Generalization plan (G0):
-- concept/name: weighted gradient-square budget telescope from one-step descent; orig was rsgd_pointwise_weighted_budget_telescope
-- generality used: arbitrary finite index set and real-valued objective on a real inner-product space; the proof uses only pointwise one-step inequalities, finite sums, and an objective terminal lower bound, with no measure, convexity, smoothness, oracle, or finite-dimensional assumptions
-- portable call pattern: stochastic-gradient, noisy-gradient, and mirror-style finite-window proofs call this after supplying a one-step gradient-square descent inequality, the corresponding output weights, a finite objective-drop telescope, and a lower bound on the terminal potential; the carrier, iterates, coefficients, and correction terms vary while the conclusion shape stays fixed
-- counterargument checked: not paper-local traceability or a caller-side wrapper because it packages the recurring gradient-square/residual-square/cross-term aggregation step; `summed_one_step_gap_bound_of_telescope` is only the internal generic sum engine and does not expose this contract
-- coverage search: queried weighted gradient-square finite sum with one-step descent, residual budget, and terminal lower bound; `summed_one_step_gap_bound_of_telescope` was the closest partial SOptLib hit, while Mathlib returned only unrelated finite-sum inequalities
-- minimal hypotheses: typeclass assumptions are limited to `NormedAddCommGroup` and `InnerProductSpace ℝ`; all algorithm, smoothness, oracle, and endpoint facts are pointwise hypotheses

/-- Aggregate a weighted gradient-square descent budget over a finite window.

If each one-step gradient-square coefficient is scaled into its output weight,
the one-step inequality controls that coefficient by an objective drop, a
residual-square term, and a gradient-residual correction, and the scaled
objective drops telescope to `initial - terminal`, then a lower bound on the
terminal potential gives the corresponding finite-window weighted budget.

Layer: Layer1 | Gap: Level 1 (weighted gradient-square descent telescope)
Proof: rewrite the weighted gradient term using the supplied scaling identity,
apply the finite-window one-step telescope, and use the terminal lower bound to
remove the tail.
Source: Mathlib real inner-product algebra, finite big-operator distributivity, and ordered real arithmetic
Used in: stochastic-gradient finite-window stationarity bounds after the pathwise one-step descent estimate and before taking expectations or cancelling the residual cross term
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/key_lemmas/0/proof/6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning - two-phase randomized stochastic gradient descent -/
theorem weighted_gradient_budget_telescope_of_one_step_descent
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Finset ι) (f : E → ℝ)
    (x xnext grad residual : ι → E)
    (scale : ℝ) (weight coefficient variance correction : ι → ℝ)
    (initial lower terminal : ℝ)
    (hweight : ∀ i ∈ s, weight i = scale * coefficient i)
    (hstep : ∀ i ∈ s,
      scale * (coefficient i * ‖grad i‖ ^ 2) ≤
        scale * (f (x i) - f (xnext i)) +
          variance i * ‖residual i‖ ^ 2 -
          correction i * ⟪grad i, residual i⟫_ℝ)
    (htelescope :
      ∑ i ∈ s, scale * (f (x i) - f (xnext i)) =
        initial - terminal)
    (hterminal_lower : lower ≤ terminal) :
    ∑ i ∈ s, weight i * ‖grad i‖ ^ 2 ≤
      initial - lower +
        ∑ i ∈ s, variance i * ‖residual i‖ ^ 2 -
        ∑ i ∈ s, correction i * ⟪grad i, residual i⟫_ℝ := by
  have hpoint :
      ∀ i ∈ s,
        weight i * ‖grad i‖ ^ 2 ≤
          scale * (f (x i) - f (xnext i)) +
            variance i * ‖residual i‖ ^ 2 -
            correction i * ⟪grad i, residual i⟫_ℝ := by
    intro i hi
    calc
      weight i * ‖grad i‖ ^ 2 =
          scale * (coefficient i * ‖grad i‖ ^ 2) := by
            rw [hweight i hi]
            ring
      _ ≤
          scale * (f (x i) - f (xnext i)) +
            variance i * ‖residual i‖ ^ 2 -
            correction i * ⟪grad i, residual i⟫_ℝ := hstep i hi
  have htelescope' :
      ∑ i ∈ s, scale * (f (x i) - f (xnext i)) =
        (initial - lower) - (terminal - lower) := by
    linarith [htelescope]
  exact
    summed_one_step_gap_bound_of_telescope
      (s := s)
      (gap := fun i => weight i * ‖grad i‖ ^ 2)
      (descent := fun i => scale * (f (x i) - f (xnext i)))
      (variance := fun i => variance i * ‖residual i‖ ^ 2)
      (correction := fun i => correction i * ⟪grad i, residual i⟫_ℝ)
      (initial := initial - lower) (terminal := terminal - lower) hpoint
      htelescope' (sub_nonneg.mpr hterminal_lower)
