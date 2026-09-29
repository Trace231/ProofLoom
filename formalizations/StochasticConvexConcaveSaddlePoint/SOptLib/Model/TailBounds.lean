import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open MeasureTheory
open scoped BigOperators

namespace SOptLib

/-- Joint index/sample strict tail event for a real-valued observable.

For an abstract output index `α`, sample space `Ω`, observable
`f : α × Ω → ℝ`, and threshold `t`, this names the event where the joint
observable is strictly above the threshold.

Layer: Model | Concept: Objective
Proof: (definitional construction; set-builder wrapper for a joint strict real
  tail event)
Source: Mathlib real-order and set-builder APIs for strict tail events
Used in: randomized stochastic mirror descent one-run stopping/sample Markov
  strict tail probability for the exact projected-gradient certificate
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
def jointStrictTailEvent {α Ω : Type*} (f : α × Ω → ℝ) (t : ℝ) : Set (α × Ω) :=
  {p | f p > t}

/-- A strict real tail event is contained in the corresponding non-strict tail event.

For any real-valued observable on an abstract index space, exceeding a threshold
strictly implies exceeding the same threshold non-strictly. This records the
order-theoretic inclusion independently of the particular stochastic model that
supplies the observable.

Layer: Model | Gap: Level 0 (strict tail event inclusion)
Proof: introduce a point in the strict tail event and weaken `<` to `≤` using
  the real-order lemma `le_of_lt`.
Source: Mathlib real linear-order API for strict and non-strict inequalities
Used in: nonconvex stochastic mirror descent one-run exact projected-gradient
  tail event comparison between strict Markov-safe and paper-literal events
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem strictTailEvent_subset_tailEvent {α : Type*} (f : α → ℝ) (t : ℝ) :
    {x | f x > t} ⊆ {x | f x ≥ t} := by
  intro x hx
  exact le_of_lt (show f x > t from hx)

/-- Probability mass of a strict joint tail event under an abstract joint law.

This model-level wrapper records the common pattern that a randomized output
tail bound is evaluated by applying the stopping/sample joint measure to the
strict tail event.

Layer: Model | Concept: Objective
Proof: (definitional construction; apply the joint measure to the supplied
  strict tail event)
Source: Mathlib measure theory API for evaluating measures on sets
Used in: nonconvex stochastic mirror descent one-run randomized stopping strict
  tail probability for the exact projected-gradient certificate
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
noncomputable def jointStrictTailProbability
    {β : Type*} [MeasurableSpace β] (μ : Measure β) (A : Set β) : ENNReal :=
  μ A

/-- Finite weighted sum of strict one-run tail probabilities over stopping times.

For a finite stopping index type, real weights, a sample-space measure, an
observable depending on the stopping index and sample point, and a threshold,
this is the finite `∑ R, ofReal (w R) * μ {ω | f R ω > t}` expansion used by
strict randomized-output tail probabilities.

Layer: Model | Concept: Objective
Proof: (definitional construction; finite weighted sum of measured strict
  tail events)
Source: Mathlib finite sums, extended nonnegative reals, and measure evaluation
  on set-builder strict tail events
Used in: nonconvex stochastic mirror descent one-run randomized stopping strict
  tail probability for the exact projected-gradient certificate
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
noncomputable def finiteStoppingStrictTailProbabilitySum
    {times Ω : Type*} [Fintype times] [MeasurableSpace Ω]
    (w : times → ℝ) (μ : Measure Ω) (f : times → Ω → ℝ) (t : ℝ) : ENNReal :=
  ∑ R : times, ENNReal.ofReal (w R) * μ {ω | f R ω > t}

/-- Joint index/sample non-strict tail event for a real-valued observable.

For an abstract output index `α`, sample space `Ω`, observable
`f : α × Ω → ℝ`, and threshold `t`, this names the event where the joint
observable is at least the threshold.

Layer: Model | Concept: Objective
Proof: (definitional construction; set-builder wrapper for a joint non-strict
  real tail event)
Source: Mathlib real-order and set-builder APIs for tail events
Used in: randomized stochastic mirror descent one-run stopping/sample Markov
  tail probability for the exact projected-gradient certificate
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
def jointTailEvent {α Ω : Type*} (f : α × Ω → ℝ) (t : ℝ) : Set (α × Ω) :=
  {p | f p ≥ t}

/-- Probability mass of a non-strict joint tail event under an abstract joint law.

This model-level wrapper records the common pattern that a randomized output
tail bound is evaluated by applying the stopping/sample joint measure to the
non-strict tail event.

Layer: Model | Concept: Objective
Proof: (definitional construction; apply the joint measure to the supplied
  non-strict tail event)
Source: Mathlib measure theory API for evaluating measures on sets
Used in: nonconvex stochastic mirror descent one-run randomized stopping
  non-strict tail probability for the exact projected-gradient certificate
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
noncomputable def jointTailProbability
    {β : Type*} [MeasurableSpace β] (μ : Measure β) (A : Set β) : ENNReal :=
  μ A

/-- Finite weighted sum of one-run tail probabilities over stopping times.

For a finite stopping index type, real weights, a sample-space measure, an
observable depending on the stopping index and sample point, and a threshold,
this is the finite `∑ R, ofReal (w R) * μ {ω | f R ω ≥ t}` expansion used by
randomized-output tail probabilities.

Layer: Model | Concept: Objective
Proof: (definitional construction; finite weighted sum of measured non-strict
  tail events)
Source: Mathlib finite sums, extended nonnegative reals, and measure evaluation
  on set-builder tail events
Used in: nonconvex stochastic mirror descent one-run randomized stopping tail
  probability for the exact projected-gradient certificate
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
noncomputable def finiteStoppingTailProbabilitySum
    {times Ω : Type*} [Fintype times] [MeasurableSpace Ω]
    (w : times → ℝ) (μ : Measure Ω) (f : times → Ω → ℝ) (t : ℝ) : ENNReal :=
  ∑ R : times, ENNReal.ofReal (w R) * μ {ω | f R ω ≥ t}

private theorem pmf_toMeasure_prod_fiber_event_eq_sum
    {α Ω : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace Ω] (p : PMF α) (μ : Measure Ω) [SFinite μ]
    (A : α → Set Ω) :
    (p.toMeasure.prod μ) {q : α × Ω | q.2 ∈ A q.1} =
      ∑ a : α, p a * μ (A a) := by
  classical
  let B : Finset α → Set (α × Ω) :=
    fun s => {q | q.1 ∈ (s : Set α) ∧ q.2 ∈ A q.1}
  have hB_univ : B Finset.univ = {q : α × Ω | q.2 ∈ A q.1} := by
    ext q
    simp [B]
  have hB :
      ∀ s : Finset α,
        (p.toMeasure.prod μ) (B s) = ∑ a ∈ s, p a * μ (A a) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simp [B]
    | insert a s ha ih =>
        let F : Set (α × Ω) := ({a} : Set α) ×ˢ (Set.univ : Set Ω)
        have hF_meas : NullMeasurableSet F (p.toMeasure.prod μ) := by
          have hF : MeasurableSet F := by
            exact (measurableSet_singleton a).prod MeasurableSet.univ
          exact hF.nullMeasurableSet
        have hsplit :=
          measure_inter_add_diff₀
            (μ := p.toMeasure.prod μ) (s := B (insert a s)) (t := F) hF_meas
        have h_inter : B (insert a s) ∩ F = ({a} : Set α) ×ˢ A a := by
          ext q
          by_cases hqa : q.1 = a
          · simp [B, F, hqa]
          · simp [B, F, hqa]
        have h_diff : B (insert a s) \ F = B s := by
          ext q
          by_cases hqa : q.1 = a
          · simp [B, F, hqa, ha]
          · simp [B, F, hqa]
        have hprod :
            (p.toMeasure.prod μ) (({a} : Set α) ×ˢ A a) = p a * μ (A a) := by
          rw [Measure.prod_prod]
          rw [PMF.toMeasure_apply_singleton p a (measurableSet_singleton a)]
        rw [← hsplit, h_inter, h_diff, hprod, ih]
        simp [Finset.sum_insert, ha]
  calc
    (p.toMeasure.prod μ) {q : α × Ω | q.2 ∈ A q.1}
        = (p.toMeasure.prod μ) (B Finset.univ) := by rw [hB_univ]
    _ = ∑ a : α, p a * μ (A a) := by
        simpa using hB Finset.univ

/-- A finite stopping/sample joint tail probability expands as a weighted fiber sum.

For a finite stopping law `p`, a sample law `μ`, and abstract tail fibers
`A : α → Set Ω`, the product-measure probability of the joint fiber event is
the finite sum of the fiber probabilities weighted by the stopping masses. The
hypothesis `hpw` connects PMF masses to the real weights used in paper formulas.

Layer: Model | Gap: Level 1 (finite stopping non-strict tail product expansion)
Proof: unfold the joint tail probability wrapper, apply the finite
  PMF/product-measure fiber expansion, and rewrite the PMF masses through `hpw`.
Source: Mathlib probability mass functions, product measures, singleton masses,
  and finite sums for discrete-continuous joint laws
Used in: nonconvex stochastic mirror descent one-run randomized stopping tail
  probability for the exact projected-gradient certificate
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem jointTailProbability_eq_finiteSum
    {α Ω : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace Ω]
    (p : PMF α) (w : α → ℝ) (μ : Measure Ω) [SFinite μ]
    (A : α → Set Ω)
    (hpw : ∀ a : α, p a = ENNReal.ofReal (w a)) :
    jointTailProbability (p.toMeasure.prod μ) {q : α × Ω | q.2 ∈ A q.1} =
      ∑ a : α, ENNReal.ofReal (w a) * μ (A a) := by
  calc
    jointTailProbability (p.toMeasure.prod μ) {q : α × Ω | q.2 ∈ A q.1} =
        (p.toMeasure.prod μ) {q : α × Ω | q.2 ∈ A q.1} := by
          rfl
    _ = ∑ a : α, p a * μ (A a) := by
          exact pmf_toMeasure_prod_fiber_event_eq_sum p μ A
    _ = ∑ a : α, ENNReal.ofReal (w a) * μ (A a) := by
          simp [hpw]

/-- A joint stopping/sample tail probability has the finite weighted-sum expansion.

For a finite stopping PMF `p`, sample law `μ`, observable `f`, and threshold
`t`, the product-measure probability of the non-strict joint tail event is the
weighted sum of non-strict fiber probabilities. The bridge hypothesis `hpw`
identifies PMF masses with the real-valued weights used in paper formulas.

Layer: Model | Gap: Level 1 (public finite stopping non-strict-tail product expansion)
Proof: specialize the reusable finite PMF/product-measure non-strict-tail
  expansion and expose it under the public wrapper name used by algorithm
  backfills.
Source: Mathlib probability mass functions, product measures, finite sums, and
  non-strict real tail events
Used in: nonconvex stochastic mirror descent one-run randomized stopping
  non-strict tail probability for the exact projected-gradient certificate
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem jointTailProbability_eq_finiteSum_public
    {α Ω : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace Ω]
    (p : PMF α) (w : α → ℝ) (μ : Measure Ω) [SFinite μ]
    (f : α → Ω → ℝ) (t : ℝ)
    (hpw : ∀ a : α, p a = ENNReal.ofReal (w a)) :
    jointTailProbability
        (p.toMeasure.prod μ)
        (jointTailEvent (fun q : α × Ω => f q.1 q.2) t) =
      finiteStoppingTailProbabilitySum w μ f t := by
  simpa [jointTailEvent, finiteStoppingTailProbabilitySum] using
    (jointTailProbability_eq_finiteSum
      (p := p) (w := w) (μ := μ)
      (A := fun a : α => {ω : Ω | f a ω ≥ t}) hpw)

/-- A finite stopping/sample strict-tail probability expands as a weighted fiber sum.

For a finite stopping law `p`, a sample law `μ`, a real-valued observable, and
a strict threshold, the product-measure probability of the joint strict-tail
event is the finite sum of the strict fiber probabilities weighted by the
stopping masses. The hypothesis `hpw` connects PMF masses to the real weights
used in paper formulas.

Layer: Model | Gap: Level 1 (finite stopping strict-tail product expansion)
Proof: unfold the joint strict-tail probability and strict finite-sum wrappers,
  apply the finite PMF/product-measure fiber expansion, and rewrite the PMF
  masses through `hpw`.
Source: Mathlib probability mass functions, product measures, finite sums, and
  real strict-order set-builder tails
Used in: nonconvex stochastic mirror descent one-run randomized stopping strict
  tail probability for the exact projected-gradient certificate
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem jointStrictTailProbability_eq_finiteSum
    {α Ω : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace Ω]
    (p : PMF α) (w : α → ℝ) (μ : Measure Ω) [SFinite μ]
    (f : α → Ω → ℝ) (t : ℝ)
    (hpw : ∀ a : α, p a = ENNReal.ofReal (w a)) :
    jointStrictTailProbability
        (p.toMeasure.prod μ)
        (jointStrictTailEvent (fun q : α × Ω => f q.1 q.2) t) =
      finiteStoppingStrictTailProbabilitySum w μ f t := by
  calc
    jointStrictTailProbability
        (p.toMeasure.prod μ)
        (jointStrictTailEvent (fun q : α × Ω => f q.1 q.2) t) =
        (p.toMeasure.prod μ) {q : α × Ω | q.2 ∈ {ω | f q.1 ω > t}} := by
          rfl
    _ = ∑ a : α, p a * μ {ω | f a ω > t} := by
          exact pmf_toMeasure_prod_fiber_event_eq_sum p μ (fun a => {ω | f a ω > t})
    _ = finiteStoppingStrictTailProbabilitySum w μ f t := by
          simp [finiteStoppingStrictTailProbabilitySum, hpw]

/-- A strict joint stopping/sample tail probability has the finite weighted-sum expansion.

For a finite stopping PMF `p`, sample law `μ`, observable `f`, and strict
threshold `t`, the product-measure probability of the strict joint tail event
is the weighted sum of strict fiber probabilities. The bridge hypothesis `hpw`
identifies PMF masses with the real-valued weights used in paper formulas.

Layer: Model | Gap: Level 1 (public finite stopping strict-tail product expansion)
Proof: specialize the reusable finite PMF/product-measure strict-tail expansion
  and expose it under the public wrapper name used by algorithm backfills.
Source: Mathlib probability mass functions, product measures, finite sums, and
  strict real tail events
Used in: nonconvex stochastic mirror descent one-run randomized stopping strict
  tail probability for the exact projected-gradient certificate
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem jointStrictTailProbability_eq_finiteSum_public
    {α Ω : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace Ω]
    (p : PMF α) (w : α → ℝ) (μ : Measure Ω) [SFinite μ]
    (f : α → Ω → ℝ) (t : ℝ)
    (hpw : ∀ a : α, p a = ENNReal.ofReal (w a)) :
    jointStrictTailProbability
        (p.toMeasure.prod μ)
        (jointStrictTailEvent (fun q : α × Ω => f q.1 q.2) t) =
      finiteStoppingStrictTailProbabilitySum w μ f t := by
  exact jointStrictTailProbability_eq_finiteSum p w μ f t hpw

/-- Canonical product law of a finite or countable stopping draw and sample randomness.

For an abstract stopping distribution `p : PMF α` and sample law `μ`, this names
the joint measure `p.toMeasure.prod μ` on `α × Ω` used for randomized-output
probabilities.

Layer: Model | Concept: Filtration
Proof: (definitional construction; product measure of a PMF law and sample law)
Source: Mathlib probability mass functions and product-measure construction APIs
Used in: nonconvex stochastic mirror descent one-run randomized stopping and
  sample joint law for exact projected-gradient tail probabilities
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
noncomputable def stoppingSampleJointMeasure
    {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    (p : PMF α) (μ : Measure Ω) : Measure (α × Ω) :=
  p.toMeasure.prod μ

/-- Tail event for a real-valued finite-minimum observable exceeding a threshold.

For an abstract joint index/sample type `β`, a real observable `fmin : β → ℝ`
already representing a finite minimum, and a threshold `t`, this names the
event where the finite-minimum certificate is at least `t`.

Layer: Model | Concept: Objective
Proof: (definitional construction; set-builder wrapper for a non-strict real
  tail event of a finite-minimum observable)
Source: Mathlib real-order and set-builder APIs for finite-minimum tail events
Used in: nonconvex stochastic mirror descent all-runs optimization tail event
  for the exact projected-gradient finite-minimum certificate
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
def finiteMinTailEvent {β : Type*} (fmin : β → ℝ) (t : ℝ) : Set β :=
  {p | fmin p ≥ t}

/-- Probability mass of a stopping-vector tail event under the PMF/sample product law.

For an abstract stopping-vector distribution `p`, a sample law `μ`, and a joint
event `A` on stopping vectors and samples, this names the measure
`p.toMeasure.prod μ A` used for finite-minimum optimization tail events.

Layer: Model | Concept: Objective
Proof: (definitional construction; evaluate the PMF/sample product measure on
  the supplied joint tail event)
Source: Mathlib probability mass functions and product-measure APIs for joint
  laws of discrete stopping draws and sample randomness
Used in: nonconvex stochastic mirror descent optimization finite-minimum tail
  probability under the stopping-vector and sample joint law
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
noncomputable def stoppingVectorTailProbability
    {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    (p : PMF α) (μ : Measure Ω) (A : Set (α × Ω)) : ENNReal :=
  (p.toMeasure.prod μ) A

/-- Strict all-index tail event for a family of real-valued observables.

For an abstract run index `ι`, sample or stopping/sample state `β`, observable
`f : β → ι → ℝ`, and threshold `t`, this names the event where every indexed
run certificate is strictly above the threshold.

Layer: Model | Concept: Objective
Proof: (definitional construction; set-builder wrapper for a universal strict
  real tail event over indexed runs)
Source: Mathlib real-order and set-builder APIs for universal strict tail events
Used in: nonconvex stochastic mirror descent all-runs strict optimization tail
  event for exact projected-gradient certificates across independent runs
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
def allRunsStrictTailEvent {ι β : Type*} (f : β → ι → ℝ) (t : ℝ) : Set β :=
  {p | ∀ s : ι, f p s > t}

/-- Strict tail event for a real-valued finite-minimum observable exceeding a threshold.

For an abstract joint index/sample type `β`, a real observable `fmin : β → ℝ`
already representing a finite minimum, and a threshold `t`, this names the
event where the finite-minimum certificate is strictly above `t`.

Layer: Model | Concept: Objective
Proof: (definitional construction; set-builder wrapper for a strict real tail
  event of a finite-minimum observable)
Source: Mathlib real-order and set-builder APIs for strict finite-minimum tail events
Used in: nonconvex stochastic mirror descent all-runs strict optimization tail
  event for the exact projected-gradient finite-minimum certificate
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
def finiteMinStrictTailEvent {β : Type*} (fmin : β → ℝ) (t : ℝ) : Set β :=
  {p | fmin p > t}

/-- Probability mass of a strict stopping-vector tail event under a PMF/sample product law.

For an abstract stopping-vector distribution `p`, a sample law `μ`, and a strict
joint event `A` on stopping vectors and samples, this names the product-measure
mass `p.toMeasure.prod μ A` used for finite-minimum optimization tail events.

Layer: Model | Concept: Objective
Proof: (definitional construction; evaluate the PMF/sample product measure on
  the supplied strict joint tail event)
Source: Mathlib probability mass functions and product-measure APIs for joint
  laws of discrete stopping draws and sample randomness
Used in: nonconvex stochastic mirror descent strict optimization finite-minimum
  tail probability under the stopping-vector and sample joint law
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
noncomputable def stoppingVectorStrictTailProbability
    {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    (p : PMF α) (μ : Measure Ω) (A : Set (α × Ω)) : ENNReal :=
  (p.toMeasure.prod μ) A

end SOptLib
