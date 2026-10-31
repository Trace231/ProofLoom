import SOptLib.Glue.Probability.finiteUniformAverage_function_eval_eq
noncomputable section

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: zero finite-uniform average after coordinate evaluation of a function row; orig was the PAGE-local `finiteUniformAverage_function_eval_eq_zero_of_average_zero`.
-- generality used: finite types `α` and `β`, a chosen coordinate `j : α`, and an additive commutative group with real module structure `V`; no topology, measure, convexity, smoothness, or oracle assumptions are used.
-- portable call pattern: finite-product sampling proofs can replace the row index type, value type, and centered response function while reusing that a zero-mean coordinate function remains centered under a uniformly sampled function row.
-- counterargument checked: this is not a caller-side wrapper because it packages the centered consequence used repeatedly by variance proofs; the existing coordinate-marginal equality theorem does not state the zero conclusion, and no Mathlib/SOptLib duplicate was found.
-- coverage search: searched `finite uniform average function evaluation coordinate zero`, `finiteUniformAverage`, and `Fintype.sum_prod_type`; the existing `finite_uniform_average_function_eval_eq` theorem supplies the marginal equality, so coverage is partial and this corollary is distinct.
-- minimal hypotheses: `[Fintype α] [Fintype β] [Fintype (α → β)] [Nonempty β]
-- [AddCommMonoid V] [Module ℝ V]`; the proof uses no stronger structure.

/-- A zero finite-uniform average remains zero after evaluating a uniformly sampled
function row at any fixed coordinate.

Layer: Glue | Gap: Level 1 (finite-product centered coordinate cancellation)
Proof: Rewrite the row average with the coordinate-marginal identity and then use the zero-average hypothesis.
Source: Mathlib finite-type sums and scalar modules, via SOptLib's finite-uniform coordinate marginal theorem
Used in: recursive finite-product gradient-estimator variance calculations, where each sampled row coordinate contributes a centered component-gradient difference
Book citation: book/research/PAGE.json#/algorithm_spec
Origin algorithm: Li, Bao, Zhang, and Richtárik, PAGE: A Simple and Optimal Probabilistic Gradient Estimator for Nonconvex Optimization -/
theorem finite_uniform_average_function_eval_eq_zero_of_average_zero
    {α β V : Type*} [Fintype α] [Fintype β] [Fintype (α → β)] [Nonempty β]
    [AddCommMonoid V] [Module ℝ V]
    (j : α) (f : β → V)
    (hmean : finiteUniformAverage f = 0) :
    finiteUniformAverage (fun r : α → β => f (r j)) = 0 := by
  classical
  rw [finite_uniform_average_function_eval_eq (α := α) (β := β) (V := V) j f]
  exact hmean

end SOptLib
