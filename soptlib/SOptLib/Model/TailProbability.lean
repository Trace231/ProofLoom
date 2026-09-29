import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Fintype.Basic
import SOptLib.Model.Selection

open MeasureTheory
open scoped BigOperators

namespace SOptLib

/-- Non-strict all-index tail event for a family of normed certificates.

For an abstract run index `ι`, joint stopping/sample state `α × Ω`,
certificate `stat : α → ι → Ω → E`, and threshold `threshold`, this names the
event where every indexed certificate has squared norm at least the threshold.

Layer: Model | Concept: Objective
Proof: (definitional construction; set-builder wrapper for a universal non-strict squared-norm tail event)
Source: Mathlib norm notation, real-order, and set-builder APIs for normed certificate tail events
Used in: nonconvex stochastic mirror descent all-runs optimization tail event for exact projected-gradient certificates across independent runs
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, nonconvex stochastic mirror descent -/
def all_runs_tail_event {ι α Ω E : Type*} [Norm E]
    (stat : α → ι → Ω → E) (threshold : ℝ) : Set (α × Ω) :=
  {p | ∀ s : ι, ‖stat p.1 s p.2‖ ^ 2 ≥ threshold}

/-- Probability mass of an all-index non-strict squared-norm tail event.

For an abstract joint law on stopping choices and sample randomness, indexed
certificates `stat`, and threshold `threshold`, this names the probability that
every indexed certificate has squared norm at least the threshold.

Layer: Model | Concept: Objective
Proof: (definitional construction; evaluate the joint measure on the universal non-strict squared-norm tail event)
Source: Mathlib measure evaluation, product measurable-space, norm, and real-order APIs for probability of tail events
Used in: nonconvex stochastic mirror descent all-runs optimization tail probability for exact projected-gradient certificates across independent runs
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, nonconvex stochastic mirror descent -/
noncomputable def all_runs_tail_probability
    {ι α Ω E : Type*} [MeasurableSpace α] [MeasurableSpace Ω] [Norm E]
    (ν : Measure (α × Ω)) (stat : α → ι → Ω → E) (threshold : ℝ) : ENNReal :=
  ν (SOptLib.all_runs_tail_event stat threshold)

/-- A tail event for an attained pointwise lower bound is the corresponding
all-coordinate tail event.

If `m ω` is below every coordinate value `v i ω` and is attained by some
coordinate at each `ω`, then crossing a threshold by `m` is equivalent to every
coordinate crossing that threshold.

Layer: Model | Gap: Level 0 (attained finite minimum tail event equivalence)
Proof: one direction composes the threshold bound with the pointwise lower-bound
  hypothesis; the reverse direction evaluates the universal tail condition at
  an attaining coordinate and rewrites by attainment.
Source: Mathlib real linear-order and set extensionality APIs for finite
  minimum tail events
Used in: nonconvex stochastic mirror descent conversion from the paper finite
  minimum exact projected-gradient event to the all-runs event
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem min_tail_event_eq_all
    {ι Ω : Type*} [Fintype ι]
    (v : ι → Ω → ℝ) (m : Ω → ℝ) (c : ℝ)
    (hle : ∀ ω i, m ω ≤ v i ω)
    (hattained : ∀ ω, ∃ i : ι, m ω = v i ω) :
    {ω : Ω | c ≤ m ω} = {ω : Ω | ∀ i : ι, c ≤ v i ω} := by
  ext ω
  constructor
  · intro hω i
    exact le_trans hω (hle ω i)
  · intro hω
    rcases hattained ω with ⟨i, hi⟩
    simpa [hi] using hω i

/-- Strict selected-output tail event for a normed stationarity certificate.

For an abstract selected index `α`, sample space `Ω`, joint law `ν`, certificate
`stat : α → Ω → E`, and real threshold, this names the event where the selected
certificate norm-square is strictly above the threshold.

Layer: Model | Concept: Objective
Proof: (definitional construction; set-builder wrapper for a selected
  norm-square strict tail event under a joint law)
Source: Mathlib norm and real-order APIs for strict tail events on product
  sample spaces
Used in: nonconvex stochastic mirror descent selected-output strict
  stationarity tail event for the exact projected-gradient certificate
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
def selected_strict_tail_event
    {α Ω E : Type*} [MeasurableSpace (α × Ω)] [Norm E]
    (_ν : Measure (α × Ω)) (stat : α → Ω → E) (threshold : ℝ) :
    Set (α × Ω) :=
  {p | ‖stat p.1 p.2‖ ^ 2 > threshold}

/-- Strict selected-output tail probability expands as a finite weighted selector sum.

For a finite selected-index law `p`, a sample law `μ`, and a normed
stationarity certificate `stat`, the strict joint tail probability is the sum
of strict fiber probabilities weighted by the selector mass. The hypothesis
`hpw` rewrites PMF masses into the real weights used by paper formulas.

Layer: Model | Gap: Level 1 (finite selected strict-tail probability expansion)
Proof: unfold the selected strict-tail wrappers and reuse the finite
  PMF/product-measure fiber expansion for strict norm-square failure events.
Source: Mathlib probability mass functions, product measures, and finite sums
  for discrete-continuous joint laws
Used in: nonconvex stochastic mirror descent selected-output strict
  stationarity tail probability over independent stopping vectors and sample randomness
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem selected_strict_tail_probability_finite_sum
    {α Ω E : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace Ω] [Norm E]
    (p : PMF α) (w : α → ℝ) (μ : Measure Ω) [SFinite μ]
    (stat : α → Ω → E) (threshold : ℝ)
    (hpw : ∀ a : α, p a = ENNReal.ofReal (w a)) :
    SOptLib.strictSelectedTailProbability
        (SOptLib.selected_joint_measure p μ)
        (SOptLib.selected_strict_tail_event
          (SOptLib.selected_joint_measure p μ) stat threshold) =
      ∑ a : α, ENNReal.ofReal (w a) *
        μ {ω | ‖stat a ω‖ ^ 2 > threshold} := by
  simpa [SOptLib.strictSelectedTailProbability, SOptLib.selected_joint_measure,
    SOptLib.selected_strict_tail_event]
    using SOptLib.selectedStrictTailProbability_eq_finiteSum
      (p := p) (w := w) (μ := μ)
      (A := fun a : α => {ω | ‖stat a ω‖ ^ 2 > threshold}) hpw

/-- Selected-output tail event for a normed stationarity certificate.

For an abstract selected index `α`, sample space `Ω`, joint law `ν`, certificate
`stat : α → Ω → E`, and real threshold, this names the event where the selected
certificate norm-square is at least the threshold.

Layer: Model | Concept: Objective
Proof: (definitional construction; set-builder wrapper for a selected
  norm-square non-strict tail event under a joint law)
Source: Mathlib norm and real-order APIs for non-strict tail events on product
  sample spaces
Used in: nonconvex stochastic mirror descent selected-output stationarity tail
  event for the exact projected-gradient certificate
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
def selected_tail_event
    {α Ω E : Type*} [MeasurableSpace (α × Ω)] [Norm E]
    (_ν : Measure (α × Ω)) (stat : α → Ω → E) (threshold : ℝ) :
    Set (α × Ω) :=
  {p | ‖stat p.1 p.2‖ ^ 2 ≥ threshold}

/-- Membership in the selected-output tail event is the non-strict squared-norm
threshold predicate.

Layer: Model | Gap: Level 0 (selected-output tail event membership)
Proof: by rfl after unfolding `selected_tail_event`
Source: Mathlib norm and real-order APIs for non-strict tail events on product
  sample spaces
Used in: nonconvex stochastic mirror descent selected-output stationarity tail
  event simplification for exact projected-gradient certificates
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
@[simp]
theorem mem_selected_tail_event
    {α Ω E : Type*} [MeasurableSpace (α × Ω)] [Norm E]
    {ν : Measure (α × Ω)} {stat : α → Ω → E} {threshold : ℝ}
    {p : α × Ω} :
    p ∈ selected_tail_event ν stat threshold ↔
      ‖stat p.1 p.2‖ ^ 2 ≥ threshold := by
  rfl

/-- Probability mass of a selected-output non-strict tail event.

For an abstract selected index, sample randomness, joint law, and normed
stationarity certificate, this names the probability of the event where the
selected certificate squared norm is at least the threshold.

Layer: Model | Concept: Objective
Proof: (definitional construction; apply the joint law to the canonical
  selected non-strict squared-norm tail event)
Source: Mathlib measure theory API for evaluating product-space events and
  norm/order APIs for squared-norm tail predicates
Used in: nonconvex stochastic mirror descent selected-output stationarity tail
  probability for exact projected-gradient certificates
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
noncomputable def selected_tail_probability
    {α Ω E : Type*} [MeasurableSpace (α × Ω)] [Norm E]
    (ν : Measure (α × Ω)) (stat : α → Ω → E) (threshold : ℝ) : ENNReal :=
  ν (selected_tail_event ν stat threshold)

/-- Selected-output tail probability expands as a finite weighted selector sum.

For a finite selected-index law `p`, a sample law `μ`, and a normed
stationarity certificate `stat`, the non-strict joint tail probability is the
sum of fiber probabilities weighted by the selector mass. The hypothesis `hpw`
rewrites PMF masses into the real weights used by paper formulas.

Layer: Model | Gap: Level 1 (finite selected tail probability expansion)
Proof: split the selected product event into finitely many selector fibers and
  use `Measure.prod_prod` with the PMF singleton mass formula on each fiber.
Source: Mathlib probability mass functions, product measures, and finite sums
  for discrete-continuous joint laws
Used in: nonconvex stochastic mirror descent selected-output stationarity tail
  probability over independent stopping vectors and sample randomness
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem selected_tail_probability_finite_sum
    {α Ω E : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace Ω] [Norm E]
    (p : PMF α) (w : α → ℝ) (μ : Measure Ω) [SFinite μ]
    (stat : α → Ω → E) (threshold : ℝ)
    (hpw : ∀ a : α, p a = ENNReal.ofReal (w a)) :
    SOptLib.selected_tail_probability
        (SOptLib.selected_joint_measure p μ) stat threshold =
      ∑ a : α, ENNReal.ofReal (w a) *
        μ {ω | ‖stat a ω‖ ^ 2 ≥ threshold} := by
  simpa [SOptLib.selected_tail_probability, SOptLib.selected_joint_measure,
    SOptLib.selected_tail_event]
    using SOptLib.selectedTailProbability_eq_finiteSum
      (p := p) (w := w) (μ := μ)
      (A := fun a : α => {ω | ‖stat a ω‖ ^ 2 ≥ threshold}) hpw

end SOptLib
