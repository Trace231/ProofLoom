import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace

open MeasureTheory

namespace SOptLib

/-- Validation-error event for empirical and exact vector certificates.

For an abstract run/output descriptor `R`, validation index `I`, sample space
`Ω`, and normed additive target `E`, this names the product-space event where
some validation certificate discrepancy has squared norm at least
`lambda * sigma ^ 2 / T`.

Layer: Model | Concept: Objective
Proof: (definitional construction; set-builder wrapper for an existential
  non-strict squared-norm tail event)
Source: Mathlib normed additive groups, real arithmetic, and set-builder APIs
  for vector-valued validation tail events
Used in: nonconvex stochastic mirror descent post-optimization validation error
  event comparing empirical and exact projected-gradient certificates
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
def validationErrorEvent {R Ω E : Type*} [NormedAddCommGroup E]
    (I : Type*) (emp exact : R → I → Ω → E)
    (sigma T lambda : ℝ) : Set (R × Ω) :=
  {p |
    ∃ s : I,
      ‖emp p.1 s p.2 - exact p.1 s p.2‖ ^ 2 ≥
        lambda * sigma ^ 2 / T}

/-- Probability mass of a validation-error event under an abstract law.

This model-level wrapper records the common validation pattern that the
selected stopping/sample joint law is evaluated on a post-optimization
validation error event.

Layer: Model | Concept: Objective
Proof: (definitional construction; apply the supplied measure to the supplied
  validation-error event)
Source: Mathlib measure theory API for evaluating measures on sets
Used in: nonconvex stochastic mirror descent post-optimization validation
  probability for the selected randomized output certificate
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
noncomputable def validationErrorProbability
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (A : Set α) : ENNReal :=
  μ A

/-- Strict validation-error event for empirical and exact vector certificates.

For an abstract run/output descriptor `R`, validation index `I`, sample space
`Ω`, and normed additive target `E`, this names the product-space event where
some validation certificate discrepancy has squared norm strictly above
`lambda * sigma ^ 2 / T`.

Layer: Model | Concept: Objective
Proof: (definitional construction; set-builder wrapper for an existential strict squared-norm tail event)
Source: Mathlib normed additive groups, real arithmetic, and set-builder APIs for vector-valued validation tail events
Used in: nonconvex stochastic mirror descent strict post-optimization validation event comparing empirical and exact projected-gradient certificates
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, nonconvex stochastic mirror descent -/
def validationStrictErrorEvent {R Ω E : Type*} [NormedAddCommGroup E]
    (I : Type*) (emp exact : R → I → Ω → E)
    (sigma T lambda : ℝ) : Set (R × Ω) :=
  {p |
    ∃ s : I,
      ‖emp p.1 s p.2 - exact p.1 s p.2‖ ^ 2 >
        lambda * sigma ^ 2 / T}

/-- A strict existential real-threshold event is contained in the corresponding non-strict event.

For an abstract object type `α`, validation index type `ι`, error functional
`err`, and threshold, the event that some validation error is strictly above
the threshold is a subset of the event that some validation error is at least
the threshold.

Layer: Model | Gap: Level 0 (strict-to-non-strict validation threshold event)
Proof: unpack the existential witness for the strict event and weaken the
  strict real inequality with `le_of_lt`.
Source: Mathlib order theory for real inequalities and set-builder extensional
  event predicates
Used in: nonconvex stochastic mirror descent validation event comparison between
  strict Markov-safe and paper-literal non-strict post-optimization errors
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem validationStrictErrorEvent_subset_validationErrorEvent
    {α ι : Type*} (err : α → ι → ℝ) (threshold : ℝ) :
    {a : α | ∃ i : ι, threshold < err a i} ⊆
      {a : α | ∃ i : ι, threshold ≤ err a i} := by
  rintro a ⟨i, hi⟩
  exact ⟨i, le_of_lt hi⟩

/-- Probability mass of a strict validation-error event under an abstract law.

This model-level wrapper records the common validation pattern that the
selected stopping/sample joint law is evaluated on the strict post-optimization
validation error event.

Layer: Model | Concept: Objective
Proof: (definitional construction; apply the supplied measure to the supplied
  strict validation-error event)
Source: Mathlib measure theory API for evaluating measures on sets
Used in: nonconvex stochastic mirror descent strict post-optimization
  validation probability for the selected randomized output certificate
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
noncomputable def validationStrictErrorProbability
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (A : Set α) : ENNReal :=
  μ A

end SOptLib
