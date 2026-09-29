import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import SOptLib.Glue.Probability
import SOptLib.Model.Iterates
import SOptLib.Model.BlockSampling

open MeasureTheory
open scoped BigOperators

namespace SOptLib

/-- Canonical selected-output joint law of a stopping draw and sample randomness.

For an abstract randomized selector distribution `p : PMF α` and sample law
`μ`, this names the product measure `p.toMeasure.prod μ` on `α × Ω` used to
measure selected-output tail and validation events.

Layer: Model | Concept: Filtration
Proof: (definitional construction; product measure of the selector PMF law and
  the ambient sample law)
Source: Mathlib probability mass functions and product-measure construction APIs
Used in: nonconvex stochastic mirror descent selected-output stationarity and
  validation tail probabilities under the randomized stopping-vector law
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
noncomputable def selected_joint_measure
    {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    (p : PMF α) (μ : Measure Ω) : Measure (α × Ω) :=
  p.toMeasure.prod μ

/-- Predicate that an epsilon-indexed failure probability is bounded by `Λ`.

This model-level wrapper records the paper convention that an `(ε,Λ)` solution
is certified by bounding the probability of failing the epsilon stationarity
test by the tolerance `Λ`.

Layer: Model | Concept: Objective
Proof: (definitional construction; compare the supplied epsilon-indexed
  failure probability with `ENNReal.ofReal Λ`)
Source: Mathlib ENNReal ordered coercion API for extended nonnegative failure
  probabilities
Used in: two-phase randomized stochastic mirror descent failure-probability
  guarantee for selected epsilon-stationarity output
Book citation: book/FOML/StochasticMirrorDescent.json#/main_theorem/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
def IsEpsilonLambdaSolution
    (failureProbability : ℝ → ENNReal) (ε Λ : ℝ) : Prop :=
  failureProbability ε ≤ ENNReal.ofReal Λ

/-- Failure event for a selected stationarity certificate exceeding an epsilon threshold.

For an abstract selection index `α`, sample space `Ω`, and stationarity map
`stationarity : α → Ω → E`, this is the joint event on `α × Ω` where the squared
norm of the selected stationarity certificate is strictly larger than `ε`.

Layer: Model | Concept: Objective
Proof: (definitional construction; set-builder wrapper for a squared-norm
  stationarity tail event on a selected index/sample pair)
Source: Mathlib normed-type and set-builder APIs for squared norm tail events
Used in: randomized stochastic mirror descent selected-output stationarity
  failure probability for the `(ε,Λ)` solution guarantee
Book citation: book/FOML/StochasticMirrorDescent.json#/main_theorem/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
def epsilonSolutionFailureEvent
    {α Ω E : Type*} [Norm E] (stationarity : α → Ω → E) (ε : ℝ) :
    Set (α × Ω) :=
  {p | ‖stationarity p.1 p.2‖ ^ 2 > ε}

/-- Probability mass of an epsilon-solution failure event under an abstract joint law.

This model-level wrapper records the common pattern that a selected output
fails an epsilon stationarity condition by measuring a failure event on the
joint index/sample space.

Layer: Model | Concept: Objective
Proof: (definitional construction; apply the joint measure to the supplied
  epsilon-solution failure event)
Source: Mathlib measure theory API for evaluating measures on sets
Used in: randomized stochastic mirror descent selected-output stationarity
  failure probability for the `(ε,Λ)` solution guarantee
Book citation: book/FOML/StochasticMirrorDescent.json#/main_theorem/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
noncomputable def epsilonSolutionFailureProbability
    {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    (μ : Measure (α × Ω)) (failureEvent : Set (α × Ω)) : ENNReal :=
  μ failureEvent

/-- Probability mass of a strict selected-output tail event under an abstract joint law.

This model-level wrapper records the common pattern that a selected randomized
output tail bound is the joint-law mass of a strict event on the selected index
and sample randomness.

Layer: Model | Concept: Objective
Proof: (definitional construction; apply the selected joint measure to the
  supplied strict tail event)
Source: Mathlib measure theory API for evaluating measures on product-space
  events
Used in: nonconvex stochastic mirror descent selected-output strict
  stationarity tail probability for the exact projected-gradient certificate
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
noncomputable def strictSelectedTailProbability
    {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    (μ : Measure (α × Ω)) (event : Set (α × Ω)) : ENNReal :=
  μ event

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

/-- Epsilon-solution failure probability expands as a finite weighted stopping-index sum.

For a finite stopping-index law `p`, a sample law `μ`, and a stationarity
certificate indexed by the stopping outcome, the joint PMF/sample failure
probability is the finite sum of fiber probabilities weighted by the stopping
mass.  The hypothesis `hpw` rewrites PMF masses into the real weights used by
paper formulas.

Layer: Model | Gap: Level 1 (finite stopping-vector epsilon-failure expansion)
Proof: split the product event into finitely many stopping-index fibers and
  use `Measure.prod_prod` with the PMF singleton mass formula on each fiber.
Source: Mathlib probability mass functions, product measures, and finite sums
  for discrete-continuous joint laws
Used in: nonconvex stochastic mirror descent selected-output epsilon failure
  probability over independent stopping vectors and sample randomness
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem epsilonSolutionFailureProbabilityFiniteSum
    {α Ω E : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace Ω] [Norm E]
    (p : PMF α) (w : α → ℝ) (μ : Measure Ω) [SFinite μ]
    (stationarity : α → Ω → E) (ε : ℝ)
    (hpw : ∀ a : α, p a = ENNReal.ofReal (w a)) :
    (p.toMeasure.prod μ)
        (epsilonSolutionFailureEvent (stationarity := stationarity) ε) =
      ∑ a : α, ENNReal.ofReal (w a) *
        μ {ω | ‖stationarity a ω‖ ^ 2 > ε} := by
  classical
  let A : α → Set Ω := fun a => {ω | ‖stationarity a ω‖ ^ 2 > ε}
  calc
    (p.toMeasure.prod μ)
        (epsilonSolutionFailureEvent (stationarity := stationarity) ε)
        = (p.toMeasure.prod μ) {q : α × Ω | q.2 ∈ A q.1} := by
          simp [epsilonSolutionFailureEvent, A]
    _ = ∑ a : α, p a * μ (A a) := by
          exact pmf_toMeasure_prod_fiber_event_eq_sum p μ A
    _ = ∑ a : α, ENNReal.ofReal (w a) *
        μ {ω | ‖stationarity a ω‖ ^ 2 > ε} := by
          simp [A, hpw]

/-- Epsilon-failure event mass over a finite selector/sample product law is a weighted fiber sum.

For a finite selector law `p`, sample law `μ`, and abstract failure fibers
`A : α → Set Ω`, the product-measure mass of the selected fiber event equals
the finite sum of the fiber probabilities weighted by the selector masses. The
hypothesis `hpw` rewrites the PMF masses into the real weights used by paper
formulas.

Layer: Model | Gap: Level 1 (finite selector epsilon-failure fiber expansion)
Proof: unfold the selected-joint-law wrapper, use the finite PMF
  product-measure fiber expansion, then rewrite PMF masses with `hpw`.
Source: Mathlib probability mass functions, product measures, singleton masses,
  and finite sums for discrete-continuous joint laws
Used in: nonconvex stochastic mirror descent selected-output epsilon failure
  probability over independent stopping vectors and sample randomness
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem epsilonSolutionFailureProbability_eq_finiteSum
    {α Ω : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace Ω]
    (p : PMF α) (w : α → ℝ) (μ : Measure Ω) [SFinite μ]
    (A : α → Set Ω)
    (hpw : ∀ a : α, p a = ENNReal.ofReal (w a)) :
    (selected_joint_measure p μ) {q : α × Ω | q.2 ∈ A q.1} =
      ∑ a : α, ENNReal.ofReal (w a) * μ (A a) := by
  calc
    (selected_joint_measure p μ) {q : α × Ω | q.2 ∈ A q.1} =
        (p.toMeasure.prod μ) {q : α × Ω | q.2 ∈ A q.1} := by
          simp [selected_joint_measure]
    _ = ∑ a : α, p a * μ (A a) := by
          exact pmf_toMeasure_prod_fiber_event_eq_sum p μ A
    _ = ∑ a : α, ENNReal.ofReal (w a) * μ (A a) := by
          simp [hpw]

/-- A finite selected-output tail probability expands as a weighted fiber sum.

For a finite selector law `p`, sample law `μ`, and abstract selected-tail
fibers `A : α → Set Ω`, the selected product-law mass of the fiber event equals
the finite sum of the fiber probabilities weighted by the selector masses. The
hypothesis `hpw` rewrites PMF masses into the real weights used by paper
formulas.

Layer: Model | Gap: Level 1 (finite selected-tail fiber expansion)
Proof: reuse the finite selector/sample product-measure expansion and rewrite
  selector PMF masses with `hpw`.
Source: Mathlib probability mass functions, product measures, singleton
  masses, and finite sums for discrete-continuous joint laws
Used in: nonconvex stochastic mirror descent selected-output stationarity tail
  probability over independent stopping vectors and sample randomness
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem selectedTailProbability_eq_finiteSum
    {α Ω : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace Ω]
    (p : PMF α) (w : α → ℝ) (μ : Measure Ω) [SFinite μ]
    (A : α → Set Ω)
    (hpw : ∀ a : α, p a = ENNReal.ofReal (w a)) :
    (selected_joint_measure p μ) {q : α × Ω | q.2 ∈ A q.1} =
      ∑ a : α, ENNReal.ofReal (w a) * μ (A a) := by
  exact epsilonSolutionFailureProbability_eq_finiteSum
    (p := p) (w := w) (μ := μ) (A := A) hpw

/-- A finite selected strict-tail probability expands as a weighted fiber sum.

For a finite selected-index law `p`, a sample law `μ`, and abstract strict
failure fibers `A : α → Set Ω`, the product joint-law mass of the selected
fiber event is the finite sum of the fiber probabilities weighted by the
selector masses. The hypothesis `hpw` rewrites PMF masses into the real
weights used by paper formulas.

Layer: Model | Gap: Level 1 (finite selected strict-tail fiber expansion)
Proof: unfold the selected strict-tail probability wrapper and reuse the
  finite PMF/product-measure fiber expansion, rewriting selector masses with
  `hpw`.
Source: Mathlib probability mass functions, product measures, singleton
  masses, and finite sums for discrete-continuous joint laws
Used in: nonconvex stochastic mirror descent selected-output strict
  stationarity tail probability over independent stopping vectors and sample randomness
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem selectedStrictTailProbability_eq_finiteSum
    {α Ω : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace Ω]
    (p : PMF α) (w : α → ℝ) (μ : Measure Ω) [SFinite μ]
    (A : α → Set Ω)
    (hpw : ∀ a : α, p a = ENNReal.ofReal (w a)) :
    strictSelectedTailProbability
        (selected_joint_measure p μ) {q : α × Ω | q.2 ∈ A q.1} =
      ∑ a : α, ENNReal.ofReal (w a) * μ (A a) := by
  simpa [strictSelectedTailProbability]
    using epsilonSolutionFailureProbability_eq_finiteSum
      (p := p) (w := w) (μ := μ) (A := A) hpw

/-- Normalized PMF over an arbitrary finite output window.

For real weights on a finite set `times`, this is the selected-output law on
the subtype of indices in `times` whose mass at `k` is the raw weight at `k`
divided by the finite total weight over `times`.

Layer: Model | Concept: Probability
Proof: finite PMF from normalized real weights, with nonnegativity and total
  mass derived from pointwise nonnegativity on the finite window and positivity
  of the finite denominator.
Source: Mathlib probability mass functions, finite sets, and finite-sum
  normalization over real weights
Used in: randomized selected-output laws for stochastic optimization algorithms -/
noncomputable def normalizedFiniteWindowPMF
    {T : Type*} [DecidableEq T]
    (times : Finset T) (weight : T → ℝ)
    (hweight_nonneg : ∀ k, k ∈ times → 0 ≤ weight k)
    (hden : 0 < Finset.sum times weight) :
    PMF {k : T // k ∈ times} :=
  PMF.ofFintypeOfReal
    (fun R : {k : T // k ∈ times} =>
      weight R.1 / Finset.sum times weight)
    (fun R =>
      div_nonneg (hweight_nonneg R.1 R.2) (le_of_lt hden))
    (by
      classical
      have hreindex :
          (∑ R : {k : T // k ∈ times}, weight R.1) =
            Finset.sum times weight := by
        simpa using Finset.sum_attach (s := times) (f := weight)
      calc
        (∑ R : {k : T // k ∈ times}, weight R.1 / Finset.sum times weight)
            = (∑ R : {k : T // k ∈ times}, weight R.1) /
                Finset.sum times weight := by
              rw [← Finset.sum_div]
        _ = 1 := by
              rw [hreindex, div_self (ne_of_gt hden)])

/-- The finite-window PMF is the finite real-weight PMF with normalized masses. -/
@[simp]
theorem normalizedFiniteWindowPMF_def
    {T : Type*} [DecidableEq T]
    (times : Finset T) (weight : T → ℝ)
    (hweight_nonneg : ∀ k, k ∈ times → 0 ≤ weight k)
    (hden : 0 < Finset.sum times weight) :
    normalizedFiniteWindowPMF times weight hweight_nonneg hden =
      PMF.ofFintypeOfReal
        (fun R : {k : T // k ∈ times} =>
          weight R.1 / Finset.sum times weight)
        (fun R =>
          div_nonneg (hweight_nonneg R.1 R.2) (le_of_lt hden))
        (by
          classical
          have hreindex :
              (∑ R : {k : T // k ∈ times}, weight R.1) =
                Finset.sum times weight := by
            simpa using Finset.sum_attach (s := times) (f := weight)
          calc
            (∑ R : {k : T // k ∈ times}, weight R.1 / Finset.sum times weight)
                = (∑ R : {k : T // k ∈ times}, weight R.1) /
                    Finset.sum times weight := by
                  rw [← Finset.sum_div]
            _ = 1 := by
                  rw [hreindex, div_self (ne_of_gt hden)]) := by
  rfl

/-- The finite-window PMF assigns each window index its normalized real weight. -/
@[simp]
theorem normalizedFiniteWindowPMF_apply
    {T : Type*} [DecidableEq T]
    (times : Finset T) (weight : T → ℝ)
    (hweight_nonneg : ∀ k, k ∈ times → 0 ≤ weight k)
    (hden : 0 < Finset.sum times weight)
    (R : {k : T // k ∈ times}) :
    normalizedFiniteWindowPMF times weight hweight_nonneg hden R =
      ENNReal.ofReal (weight R.1 / Finset.sum times weight) := by
  rfl

/-- A supplied finite-window PMF has the normalized real-weight atom formula.

For a finite support `times` and real weights, this predicate records that each
subtype atom has mass `ENNReal.ofReal (weight k / sum weight)`.  It is a
contract for an externally supplied randomized-output law, independent of how
that law was constructed.

Layer: Model | Concept: Probability
Proof: (definitional construction; pointwise PMF atom formula for normalized
  real weights on a finite support subtype)
Source: Mathlib probability mass functions, finite sets, and finite-sum
  normalization over real weights
Used in: randomized selected-output law interfaces before finite-window
  expectation and stationarity-tail arguments
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
def FiniteWindowPMFSpec
    {T : Type*} (times : Finset T) (weight : T → ℝ)
    (p : PMF {k : T // k ∈ times}) : Prop :=
  ∀ R : {k : T // k ∈ times},
    p R = ENNReal.ofReal (weight R.1 / Finset.sum times weight)

/-- Characterization of the finite-window PMF specification. -/
@[simp] theorem FiniteWindowPMFSpec_def
    {T : Type*} (times : Finset T) (weight : T → ℝ)
    (p : PMF {k : T // k ∈ times}) :
    FiniteWindowPMFSpec times weight p ↔
      ∀ R : {k : T // k ∈ times},
        p R = ENNReal.ofReal (weight R.1 / Finset.sum times weight) :=
  Iff.rfl

/-- The normalized finite-window PMF satisfies the finite-window PMF specification.

Layer: Model | Gap: Level 0 (normalized finite-window PMF specification bridge)
Proof: unfold the specification and apply the existing finite-window PMF atom
  evaluation theorem.
Source: Mathlib probability mass functions, finite sets, and finite-sum
  normalization over real weights
Used in: admissible randomized selected-output law construction before
  finite-window expectation and stationarity-tail arguments
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
theorem normalizedFiniteWindowPMF_spec
    {T : Type*} [DecidableEq T]
    (times : Finset T) (weight : T → ℝ)
    (hweight_nonneg : ∀ k, k ∈ times → 0 ≤ weight k)
    (hden : 0 < Finset.sum times weight) :
    FiniteWindowPMFSpec times weight
      (SOptLib.normalizedFiniteWindowPMF times weight hweight_nonneg hden) := by
  intro R
  exact SOptLib.normalizedFiniteWindowPMF_apply times weight hweight_nonneg hden R

/-- Real weights on a finite support are admissible for normalized selection.

For a finite support `times` and real weights, admissibility bundles
nonnegativity on the selected support with strict positivity of the finite total
mass.  This is the standard input contract before turning finite real weights
into a normalized randomized-output law.

Layer: Model | Concept: Probability
Proof: (definitional construction; conjunction of support nonnegativity and
  positive finite total mass for normalized real weights)
Source: Mathlib finite sets, ordered real sums, and probability mass function
  normalization APIs
Used in: randomized selected-output law construction from finite real weights
  before finite-window expectation and stationarity-tail arguments
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
def FiniteWindowWeightsAdmissible
    {T : Type*} (times : Finset T) (weight : T → ℝ) : Prop :=
  (∀ k, k ∈ times → 0 ≤ weight k) ∧
    0 < Finset.sum times weight

@[simp] theorem FiniteWindowWeightsAdmissible_def
    {T : Type*} (times : Finset T) (weight : T → ℝ) :
    FiniteWindowWeightsAdmissible times weight ↔
      (∀ k, k ∈ times → 0 ≤ weight k) ∧
        0 < Finset.sum times weight :=
  Iff.rfl

namespace FiniteWindowWeightsAdmissible

/-- Construct admissible finite-window weights from support nonnegativity and
one strictly positive supported weight.

Layer: Model | Gap: Level 0 (finite-window admissible weight construction)
Proof: combine the nonnegativity hypothesis with Mathlib's strict positivity
criterion for finite sums.
Source: Mathlib finite sets and ordered real sums for PMF normalization
Used in: randomized selected-output PMF construction from nonnegative weights
  with a positive active weight
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
theorem of_nonneg_of_pos
    {T : Type*} {times : Finset T} {weight : T → ℝ}
    (h_nonneg : ∀ k, k ∈ times → 0 ≤ weight k)
    {k : T} (hk : k ∈ times) (hk_pos : 0 < weight k) :
    FiniteWindowWeightsAdmissible times weight :=
  ⟨h_nonneg, Finset.sum_pos' h_nonneg ⟨k, hk, hk_pos⟩⟩

/-- Admissible finite-window weights are nonnegative on their support.

Layer: Model | Gap: Level 0 (finite-window admissible weight support bound)
Proof: unfold the admissibility predicate and take the first conjunct.
Source: Mathlib finite sets and ordered real weights for PMF normalization
Used in: randomized selected-output PMF construction from admissible finite
  weights
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
theorem nonneg
    {T : Type*} {times : Finset T} {weight : T → ℝ}
    (h : FiniteWindowWeightsAdmissible times weight) :
    ∀ k, k ∈ times → 0 ≤ weight k :=
  h.1

/-- Admissible finite-window weights have positive total mass.

Layer: Model | Gap: Level 0 (finite-window admissible weight positive mass)
Proof: unfold the admissibility predicate and take the second conjunct.
Source: Mathlib finite sets and ordered real sums for PMF normalization
Used in: randomized selected-output PMF construction from admissible finite
  weights
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
theorem sum_pos
    {T : Type*} {times : Finset T} {weight : T → ℝ}
    (h : FiniteWindowWeightsAdmissible times weight) :
    0 < Finset.sum times weight :=
  h.2

end FiniteWindowWeightsAdmissible

/-- The normalized finite-window PMF built from admissible weights satisfies the PMF spec.

For a finite support `times`, admissible real weights give the canonical
normalized selector law.  This theorem packages the lower-level nonnegativity
and positive-denominator hypotheses into the finite-window admissibility
contract used by randomized-output algorithms.

Layer: Model | Gap: Level 0 (admissible finite-window PMF specification bridge)
Proof: project the admissibility bundle into the nonnegativity and positive
  denominator hypotheses required by the normalized finite-window PMF spec.
Source: Mathlib probability mass functions, finite sets, and finite-sum
  normalization over real weights
Used in: randomized selected-output law construction from admissible finite
  weights before finite-window expectation and stationarity-tail arguments
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
theorem finiteWindowPMFSpec_of_normalizedFiniteWindowPMF
    {T : Type*} [DecidableEq T]
    (times : Finset T) (weight : T → ℝ)
    (h : FiniteWindowWeightsAdmissible times weight) :
    FiniteWindowPMFSpec times weight
      (SOptLib.normalizedFiniteWindowPMF times weight
        (FiniteWindowWeightsAdmissible.nonneg h)
        (FiniteWindowWeightsAdmissible.sum_pos h)) := by
  exact normalizedFiniteWindowPMF_spec times weight
    (FiniteWindowWeightsAdmissible.nonneg h)
    (FiniteWindowWeightsAdmissible.sum_pos h)

/-- The PMF measure induced by normalized real weights has real singleton mass equal to the weight.

For a finite measurable type, nonnegative real weights summing to one define a
PMF through `PMF.ofFintypeOfReal`; after converting the associated measure atom
back to `Real`, each singleton has the original real mass.

Layer: Model | Gap: Level 0 (finite real-weight PMF real singleton mass)
Proof: evaluate the singleton by `PMF.toMeasure_apply_singleton`, rewrite the
  finite real-weight PMF atom with `PMF.ofFintypeOfReal_apply`, then simplify
  `ENNReal.toReal (ENNReal.ofReal _)` using nonnegativity.
Source: Mathlib probability mass functions, singleton measurable sets, and
  extended nonnegative real coercion APIs
Used in: randomized selected-output laws for stochastic optimization algorithms
  when finite PMF atoms are rewritten as real weights inside expectation bounds
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
@[simp]
theorem ofFintypeOfReal_toMeasure_real_singleton
    {T : Type*} [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
    (mass : T → ℝ)
    (hmass_nonneg : ∀ t, 0 ≤ mass t)
    (hmass_sum : ∑ t, mass t = 1)
    (t : T) :
    (PMF.ofFintypeOfReal mass hmass_nonneg hmass_sum).toMeasure.real ({t} : Set T) =
      mass t := by
  rw [Measure.real_def]
  rw [PMF.toMeasure_apply_singleton
    (PMF.ofFintypeOfReal mass hmass_nonneg hmass_sum) t (measurableSet_singleton t)]
  simp [PMF.ofFintypeOfReal_apply, hmass_nonneg t]

/-- A finite-window selected-output expectation expands as a normalized weighted sum.

For nonnegative weights on a finite output window with positive total
mass, the expectation of a real certificate evaluated at the selected output
time equals the inverse denominator times the finite weighted sum of the fiber
expectations.

Layer: Model | Gap: Level 1 (finite-window selected-output expectation expansion)
Proof: expand the selector-first product integral through the finite PMF/sample
  product law, rewrite normalized finite-window singleton masses, reindex through
  the subtype window, and factor the common denominator.
Source: Mathlib product-measure Bochner integration, finite PMF atoms, and
  finite-sum normalization APIs
Used in: stochastic nonconvex conditional-gradient randomized Wolfe-gap
  expectation over a finite output window
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem finiteWindowSelectedOutputExpectation_eq_weighted_sum
    {Ω E : Type*} [MeasurableSpace Ω]
    (times : Finset ℕ) (α : ℕ → ℝ) (P : Measure Ω) [SFinite P]
    (x : ℕ → Ω → E) (gap : E → ℝ)
    (hα_nonneg : ∀ k, k ∈ times → 0 ≤ α k)
    (hden : 0 < Finset.sum times α)
    (hgap_int :
      ∀ R : {k : ℕ // k ∈ times},
        Integrable (fun ω => gap (x R.1 ω)) P) :
    ∫ q : {k : ℕ // k ∈ times} × Ω,
        gap (x q.1.1 q.2) ∂
          ((normalizedFiniteWindowPMF times α hα_nonneg hden).toMeasure.prod P) =
      (Finset.sum times α)⁻¹ *
        Finset.sum times
          (fun k => α k * ∫ ω, gap (x k ω) ∂P) := by
  classical
  let W : ℝ := Finset.sum times α
  let ι : Type := {k : ℕ // k ∈ times}
  let ν : Measure ι :=
    (normalizedFiniteWindowPMF times α hα_nonneg hden).toMeasure
  let p : ι → ℝ := fun R => α R.1 / W
  have hν_singleton : ∀ R : ι, ν.real ({R} : Set ι) = p R := by
    intro R
    have hmass_nonneg : 0 ≤ α R.1 / W := by
      exact div_nonneg (hα_nonneg R.1 R.2) (le_of_lt (by simpa [W] using hden))
    rw [Measure.real_def]
    rw [PMF.toMeasure_apply_singleton
      (normalizedFiniteWindowPMF times α hα_nonneg hden)
      R (measurableSet_singleton R)]
    simp [p, W, hmass_nonneg]
  have hprod :
      ∫ q : ι × Ω, gap (x q.1.1 q.2) ∂(ν.prod P) =
        Finset.sum Finset.univ
          (fun R : ι => p R * ∫ ω, gap (x R.1 ω) ∂P) := by
    have hswap :
        ∫ q : ι × Ω, gap (x q.1.1 q.2) ∂(ν.prod P) =
          ∫ q : Ω × ι, gap (x q.2.1 q.1) ∂(P.prod ν) := by
      simpa using
        (MeasureTheory.integral_prod_swap (μ := P) (ν := ν)
      (f := fun q : Ω × ι => gap (x q.2.1 q.1)))
    rw [hswap]
    exact integral_selected_finite_index_prod_eq_sum_weights
      (μ := P) (ν := ν) (p := p)
      (F := fun R : ι => fun ω => gap (x R.1 ω))
      hν_singleton (by simpa [ι] using hgap_int)
  have hreindex :
      Finset.sum Finset.univ
          (fun R : ι => p R * ∫ ω, gap (x R.1 ω) ∂P) =
        Finset.sum times
          (fun k => (α k / W) * ∫ ω, gap (x k ω) ∂P) := by
    simpa [ι, p] using
      (Finset.sum_attach (s := times)
        (f := fun k => (α k / W) * ∫ ω, gap (x k ω) ∂P))
  calc
    ∫ q : {k : ℕ // k ∈ times} × Ω,
        gap (x q.1.1 q.2) ∂
          ((normalizedFiniteWindowPMF times α hα_nonneg hden).toMeasure.prod P)
        = Finset.sum times
            (fun k => (α k / W) * ∫ ω, gap (x k ω) ∂P) := by
          simpa [ν, W] using hprod.trans hreindex
    _ = Finset.sum times
            (fun k => W⁻¹ * (α k * ∫ ω, gap (x k ω) ∂P)) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          field_simp [W, ne_of_gt hden]
    _ = W⁻¹ * Finset.sum times
            (fun k => α k * ∫ ω, gap (x k ω) ∂P) := by
          rw [Finset.mul_sum]
    _ = (Finset.sum times α)⁻¹ *
        Finset.sum times
          (fun k => α k * ∫ ω, gap (x k ω) ∂P) := by
          simp [W]

end SOptLib

namespace SOptLib

/-- Uniform finite average of a function over all elements of a finite type.

This names the real-module expression `(card ι)⁻¹ • ∑ i, g i`, the finite
uniform average used when a component index is sampled uniformly from a finite
population.

Layer: Model | Concept: Selection
Proof: (definitional construction; inverse-cardinality scalar multiplying the
  finite sum over `Finset.univ`)
Source: Mathlib finite sums and real scalar actions on additive monoids
Used in: randomized accelerated proximal-point current component sampling
  average for the inner finite-sum gradient estimator
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
noncomputable def finiteUniformAverage {ι β : Type*} [Fintype ι]
    [AddCommMonoid β] [Module ℝ β] (g : ι → β) : β :=
  (Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ g

/-- The uniform finite average unfolds to inverse cardinality times the finite sum.

Layer: Model | Gap: Level 0 (finite uniform average unfolding)
Proof: by rfl after unfolding `finiteUniformAverage`.
Source: Mathlib finite sums and real scalar actions on additive monoids
Used in: randomized accelerated proximal-point current component sampling
  average for the inner finite-sum gradient estimator
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
@[simp] theorem finiteUniformAverage_def {ι β : Type*} [Fintype ι]
    [AddCommMonoid β] [Module ℝ β] (g : ι → β) :
    finiteUniformAverage g =
      (Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ g :=
  rfl

/-- Uniform finite average of a one-hot update.

This is the finite-uniform sampling identity for replacing exactly one component
value `b` by `a`.

Layer: Model | Gap: Level 0 (finite uniform one-hot average)
Proof: rewrite the one-hot sum as the constant sum plus a single delta term, then
  cancel the finite cardinality scalar.
Source: Mathlib finite sums and real scalar actions on additive groups
Used in: randomized accelerated proximal-point current component sampling
  average for the inner finite-sum gradient estimator
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem finiteUniformAverage_ite_eq_inv_card_smul_sub_add
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℝ V]
    (i : ι) (a b : V) :
    finiteUniformAverage (fun j : ι => if i = j then a else b) =
      ((Fintype.card ι : ℝ)⁻¹) • (a - b) + b := by
  classical
  have hsum_delta :
      Finset.sum Finset.univ (fun j : ι => if i = j then a - b else (0 : V)) = a - b := by
    simpa using (Finset.sum_ite_eq (i := i) (f := fun _j : ι => a - b))
  have hsum :
      Finset.sum Finset.univ (fun j : ι => if i = j then a else b) =
        (Fintype.card ι : ℝ) • b + (a - b) := by
    calc
      Finset.sum Finset.univ (fun j : ι => if i = j then a else b)
          =
        Finset.sum Finset.univ (fun j : ι => b + if i = j then a - b else (0 : V)) := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          by_cases hij : i = j
          · simp [hij]
          · simp [hij]
      _ =
        Finset.sum Finset.univ (fun _j : ι => b) +
          Finset.sum Finset.univ (fun j : ι => if i = j then a - b else 0) := by
          rw [Finset.sum_add_distrib]
      _ = (Fintype.card ι : ℝ) • b + (a - b) := by
          rw [Finset.sum_const, Finset.card_univ, hsum_delta,
            ← Nat.cast_smul_eq_nsmul ℝ]
  have hcard_ne : (Fintype.card ι : ℝ) ≠ 0 := by
    have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
    exact_mod_cast Nat.ne_of_gt hpos
  rw [finiteUniformAverage_def, hsum]
  calc
    ((Fintype.card ι : ℝ)⁻¹) •
          ((Fintype.card ι : ℝ) • b + (a - b)) =
        ((Fintype.card ι : ℝ)⁻¹) • ((Fintype.card ι : ℝ) • b) +
          ((Fintype.card ι : ℝ)⁻¹) • (a - b) := by
      rw [smul_add]
    _ = ((Fintype.card ι : ℝ)⁻¹) • (a - b) + b := by
      rw [smul_smul]
      have hmul : (Fintype.card ι : ℝ)⁻¹ * (Fintype.card ι : ℝ) = 1 := by
        field_simp [hcard_ne]
      rw [hmul, one_smul, add_comm]

/-- A finite uniform average of strictly positive real weights is strictly positive.

For a nonempty finite index type, if every component weight is positive, then
the named SOptLib uniform finite average is positive.

Layer: Model | Gap: Level 0 (finite uniform average strict positivity)
Proof: unfold `finiteUniformAverage`, apply strict positivity of a finite sum
  over `Finset.univ`, and multiply by the positive inverse cardinality.
Source: Mathlib finite sums, finite type cardinality, and ordered real-field APIs
Used in: nonconvex variance-reduced mirror descent aggregate smoothness positivity from positive component smoothness constants
Book citation: book/FOML/NonconvexVarianceReducedMirrorDescent.json#/assumptions/5
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, nonconvex variance-reduced mirror descent -/
theorem finiteUniformAverage_pos {ι : Type*} [Fintype ι] [Nonempty ι]
    (w : ι → ℝ) (hpos : ∀ i : ι, 0 < w i) :
    0 < finiteUniformAverage w := by
  classical
  rw [finiteUniformAverage_def]
  have hsum_pos : 0 < ∑ i : ι, w i := by
    exact Finset.sum_pos (fun i _ => hpos i) Finset.univ_nonempty
  have hcard_pos : 0 < (Fintype.card ι : ℝ) := by
    exact Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr inferInstance)
  have hinv_pos : 0 < (Fintype.card ι : ℝ)⁻¹ := inv_pos.mpr hcard_pos
  simpa [smul_eq_mul] using mul_pos hinv_pos hsum_pos

end SOptLib

namespace SOptLib

namespace FiniteWindowWeightsAdmissible

/-- Constant unit weights are admissible on any nonempty finite selector support.

For a nonempty finite window `times`, every unit weight is nonnegative and the
finite total mass is positive, so the constant-one weights satisfy the
finite-window admissibility contract used to normalize randomized selectors.

Layer: Model | Gap: Level 0 (constant finite-window selector weights)
Proof: use a supported point supplied by `times.Nonempty` as the strictly
  positive atom in `FiniteWindowWeightsAdmissible.of_nonneg_of_pos`.
Source: Mathlib finite sets and ordered real finite-sum positivity APIs
Used in: randomized selected-output law construction for uniform stopping-time
  selectors before normalized finite-window PMF construction
Book citation: book/FOML/NonconvexVarianceReducedMirrorDescent.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex variance-reduced mirror descent -/
theorem const_one {T : Type*} (times : Finset T) (htimes : times.Nonempty) :
    FiniteWindowWeightsAdmissible times (fun _ : T => (1 : ℝ)) := by
  rcases htimes with ⟨k, hk⟩
  exact
    FiniteWindowWeightsAdmissible.of_nonneg_of_pos
      (times := times)
      (weight := fun _ : T => (1 : ℝ))
      (fun _ _ => by positivity)
      (k := k)
      hk
      (by positivity)

end FiniteWindowWeightsAdmissible

/-- Uniform PMF over a nonempty finite window, expressed through the SOptLib finite-window API.

For a finite support `times`, this is the normalized finite-window PMF with
constant-one weights on the support subtype `{k // k ∈ times}`.

Layer: Model | Concept: Probability
Proof: (definitional construction; specialize the finite-window normalized
  real-weight PMF to constant-one weights using nonempty-support admissibility)
Source: Mathlib probability mass functions, finite sets, and finite-sum
  normalization over real weights
Used in: randomized selected-output law construction for uniform stopping-time
  selectors before finite-window expectation and stationarity-tail arguments
Book citation: book/FOML/NonconvexVarianceReducedMirrorDescent.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex variance-reduced mirror descent -/
noncomputable def uniformFiniteWindowPMF
    {T : Type*} [DecidableEq T] (times : Finset T) (htimes : times.Nonempty) :
    PMF {k : T // k ∈ times} :=
  SOptLib.normalizedFiniteWindowPMF times (fun _ : T => (1 : ℝ))
    (SOptLib.FiniteWindowWeightsAdmissible.nonneg
      (SOptLib.FiniteWindowWeightsAdmissible.const_one times htimes))
    (SOptLib.FiniteWindowWeightsAdmissible.sum_pos
      (SOptLib.FiniteWindowWeightsAdmissible.const_one times htimes))

/-- The uniform finite-window PMF is the normalized finite-window PMF for unit weights. -/
@[simp]
theorem uniformFiniteWindowPMF_def
    {T : Type*} [DecidableEq T] (times : Finset T) (htimes : times.Nonempty) :
    uniformFiniteWindowPMF times htimes =
      SOptLib.normalizedFiniteWindowPMF times (fun _ : T => (1 : ℝ))
        (SOptLib.FiniteWindowWeightsAdmissible.nonneg
          (SOptLib.FiniteWindowWeightsAdmissible.const_one times htimes))
        (SOptLib.FiniteWindowWeightsAdmissible.sum_pos
          (SOptLib.FiniteWindowWeightsAdmissible.const_one times htimes)) := by
  rfl

/-- The uniform finite-window PMF assigns each window index the normalized unit mass. -/
@[simp]
theorem uniformFiniteWindowPMF_apply
    {T : Type*} [DecidableEq T] (times : Finset T) (htimes : times.Nonempty)
    (R : {k : T // k ∈ times}) :
    uniformFiniteWindowPMF times htimes R =
      ENNReal.ofReal ((1 : ℝ) / Finset.sum times (fun _ : T => (1 : ℝ))) := by
  rw [uniformFiniteWindowPMF_def]
  exact
    SOptLib.normalizedFiniteWindowPMF_apply
      times
      (fun _ : T => (1 : ℝ))
      (SOptLib.FiniteWindowWeightsAdmissible.nonneg
        (SOptLib.FiniteWindowWeightsAdmissible.const_one times htimes))
      (SOptLib.FiniteWindowWeightsAdmissible.sum_pos
        (SOptLib.FiniteWindowWeightsAdmissible.const_one times htimes))
      R

/-- The uniform finite-window PMF satisfies the constant-one normalized-mass spec.

Layer: Model | Gap: Level 0 (uniform finite-window PMF specification bridge)
Proof: apply the finite-window normalized PMF specification theorem after
  discharging weight admissibility with the constant-one admissibility lemma.
Source: Mathlib probability mass functions, finite sets, and finite-sum
  normalization over real weights
Used in: randomized selected-output law construction for uniform stopping-time
  selectors before finite-window expectation and stationarity-tail arguments
Book citation: book/FOML/NonconvexVarianceReducedMirrorDescent.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex variance-reduced mirror descent -/
theorem uniformFiniteWindowPMF_spec
    {T : Type*} [DecidableEq T] (times : Finset T) (htimes : times.Nonempty) :
    SOptLib.FiniteWindowPMFSpec times (fun _ : T => (1 : ℝ))
      (SOptLib.uniformFiniteWindowPMF times htimes) := by
  exact
    SOptLib.finiteWindowPMFSpec_of_normalizedFiniteWindowPMF
      times
      (fun _ : T => (1 : ℝ))
      (SOptLib.FiniteWindowWeightsAdmissible.const_one times htimes)

end SOptLib

namespace SOptLib

/-- The integral at a uniformly selected time in `Icc 1 T` equals the integral
of the zero-based finite uniform average of the corresponding fibers.

Layer: Model | Gap: Level 1 (one-based uniform selected-output integral reindexing)
Proof: expand the uniform finite-window product integral as a normalized sum, reindex `Icc 1 T` by subtraction to `Fin T`, and commute the finite sum with the integral using fiber integrability.
Source: Mathlib product-measure Bochner integration and finite-sum reindexing, together with SOptLib finite-window PMF and finite-uniform-average APIs
Used in: randomized-output recursive-momentum and stochastic-gradient bounds that replace a uniformly selected positive time by the average certificate over zero-based iterates
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec/output
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STOchastic Recursive Momentum -/
theorem integral_uniform_Icc_one_selected_output_eq_integral_finiteUniformAverage
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [SFinite mu] (T : Nat) (hT : 0 < T)
    (Y : Nat -> Omega -> Real)
    (hfib : forall i : Fin T, Integrable (fun omega => Y i.val omega) mu) :
    (∫ q : {t : Nat // t ∈ Finset.Icc 1 T} × Omega,
          Y (q.1.1 - 1) q.2 ∂
        selected_joint_measure
          (uniformFiniteWindowPMF (Finset.Icc 1 T)
            (by exact Finset.nonempty_Icc.mpr (Nat.succ_le_iff.mpr hT)))
          mu) =
      ∫ omega, finiteUniformAverage (fun i : Fin T => Y i.val omega) ∂mu := by
  classical
  have htimes : (Finset.Icc 1 T).Nonempty :=
    Finset.nonempty_Icc.mpr (Nat.succ_le_iff.mpr hT)
  have hnonneg :
      forall k, k ∈ Finset.Icc 1 T ->
        0 <= (fun _ : Nat => (1 : Real)) k := by
    intro k hk
    norm_num
  have hden :
      0 < Finset.sum (Finset.Icc 1 T) (fun _ : Nat => (1 : Real)) := by
    exact Finset.sum_pos (fun k hk => by norm_num) htimes
  have hfib_window :
      forall R : {k : Nat // k ∈ Finset.Icc 1 T},
        Integrable (fun omega => Y (R.1 - 1) omega) mu := by
    intro R
    have hbounds := Finset.mem_Icc.mp R.2
    have hlt : R.1 - 1 < T := by omega
    exact hfib ⟨R.1 - 1, hlt⟩
  have hselected :=
    finiteWindowSelectedOutputExpectation_eq_weighted_sum
      (times := Finset.Icc 1 T) (α := fun _ : Nat => (1 : Real))
      (P := mu) (x := fun k omega => Y (k - 1) omega)
      (gap := fun z : Real => z) hnonneg hden hfib_window
  calc
    (∫ q : {t : Nat // t ∈ Finset.Icc 1 T} × Omega,
          Y (q.1.1 - 1) q.2 ∂
        selected_joint_measure
          (uniformFiniteWindowPMF (Finset.Icc 1 T)
            (by exact Finset.nonempty_Icc.mpr (Nat.succ_le_iff.mpr hT)))
          mu) =
        (Finset.sum (Finset.Icc 1 T) (fun _ : Nat => (1 : Real)))⁻¹ *
          Finset.sum (Finset.Icc 1 T)
            (fun k => (1 : Real) * ∫ omega, Y (k - 1) omega ∂mu) := by
      simpa [selected_joint_measure, uniformFiniteWindowPMF_def] using hselected
    _ = (∫ omega, finiteUniformAverage (fun i : Fin T => Y i.val omega) ∂mu) := by
      have hden_eq :
          Finset.sum (Finset.Icc 1 T) (fun _ : Nat => (1 : Real)) =
            (T : Real) := by
        rw [Finset.sum_const]
        have hcard : (Finset.Icc 1 T).card = T := by
          rw [Nat.card_Icc]
          omega
        simp [hcard]
      have hreindex :
          Finset.sum (Finset.Icc 1 T)
              (fun k => ∫ omega, Y (k - 1) omega ∂mu) =
            Finset.sum Finset.univ
              (fun i : Fin T => ∫ omega, Y i.val omega ∂mu) := by
        have hIcc_range :
            Finset.sum (Finset.Icc 1 T)
                (fun k => ∫ omega, Y (k - 1) omega ∂mu) =
              Finset.sum (Finset.range T)
                (fun n => ∫ omega, Y n omega ∂mu) := by
          refine Finset.sum_bij (fun k _hk => k - 1) ?_ ?_ ?_ ?_
          · intro k hk
            rw [Finset.mem_range]
            change k - 1 < T
            have hbounds := Finset.mem_Icc.mp hk
            omega
          · intro a ha b hb hab
            change a - 1 = b - 1 at hab
            have habounds := Finset.mem_Icc.mp ha
            have hbbounds := Finset.mem_Icc.mp hb
            omega
          · intro n hn
            refine ⟨n + 1, ?_, ?_⟩
            · rw [Finset.mem_Icc]
              rw [Finset.mem_range] at hn
              omega
            · simp
          · intro k hk
            rfl
        have hfin_range :
            Finset.sum Finset.univ
                (fun i : Fin T => ∫ omega, Y i.val omega ∂mu) =
              Finset.sum (Finset.range T)
                (fun n => ∫ omega, Y n omega ∂mu) := by
          rw [Finset.sum_fin_eq_sum_range]
          refine Finset.sum_congr rfl ?_
          intro n hn
          simp [Finset.mem_range.mp hn]
        exact hIcc_range.trans hfin_range.symm
      have havg :
          (∫ omega, finiteUniformAverage (fun i : Fin T => Y i.val omega) ∂mu) =
            (T : Real)⁻¹ *
              Finset.sum Finset.univ
                (fun i : Fin T => ∫ omega, Y i.val omega ∂mu) := by
        calc
          (∫ omega, finiteUniformAverage (fun i : Fin T => Y i.val omega) ∂mu) =
              ∫ omega, (Fintype.card (Fin T) : Real)⁻¹ *
                  Finset.sum Finset.univ (fun i : Fin T => Y i.val omega) ∂mu := by
            simp [finiteUniformAverage_def, smul_eq_mul]
          _ = (Fintype.card (Fin T) : Real)⁻¹ *
              ∫ omega, Finset.sum Finset.univ (fun i : Fin T => Y i.val omega) ∂mu := by
            rw [MeasureTheory.integral_const_mul]
          _ = (Fintype.card (Fin T) : Real)⁻¹ *
              Finset.sum Finset.univ
                (fun i : Fin T => ∫ omega, Y i.val omega ∂mu) := by
            rw [MeasureTheory.integral_finset_sum]
            intro i hi
            exact hfib i
          _ = (T : Real)⁻¹ *
              Finset.sum Finset.univ
                (fun i : Fin T => ∫ omega, Y i.val omega ∂mu) := by
            simp
      rw [havg, hden_eq]
      simp [hreindex]

end SOptLib

-- Phase 4 merged from focused staging declarations.

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: finite-window selected-output expectation transported from a
--   prefix law to a stream law; orig was
--   `finiteWindowSelectedOutputExpectation_eq_stream_weighted_sum_of_prefix_law`,
--   kept because it exposes the normalized finite-window selection and
--   prefix-law-to-stream-law expectation contract without paper-specific terms.
-- generality used: arbitrary measurable stream and prefix spaces, an arbitrary
--   finite set of natural output times, deterministic real weights, an
--   arbitrary stream measure, prefix and stream output observables into an
--   arbitrary target type, and a real certificate `gap`; no convexity,
--   smoothness, oracle, filtration, probability, Hilbert, or finite-dimensional
--   assumptions are used.
-- portable call pattern: randomized-output stochastic optimization proofs first
--   expand a normalized finite-window selected expectation over a finite prefix
--   law, then replace the resulting weighted prefix expectations by one
--   weighted generated-stream expectation; the output times, weights, prefix
--   projection, observables, and certificate change while the conclusion shape
--   stays fixed.
-- counterargument checked: not merely paper-local traceability because it
--   packages the recurring composition of finite-window selection expansion and
--   prefix-law transport; not a pure wrapper because neither Mathlib nor SOptLib
--   had a single declaration combining normalized selected-output expectation
--   with a prefix-compatible stream observable.
-- coverage search: searched `finite window selected output expectation equals
--   stream weighted sum prefix law`, `selected output expectation normalized
--   weighted sum finite window`, and `sum mul integral map equals integral sum
--   mul prefix ae compatibility`; relevant hits were
--   `SOptLib.finiteWindowSelectedOutputExpectation_eq_weighted_sum`,
--   `SOptLib.expectedSelectedOutput_eq_inv_mul_Icc_weighted_sum`, and
--   `Finset.sum_smul_integral_map_eq_integral_sum_smul_of_ae`, all partial but
--   no full selected-prefix-to-stream composition.
-- minimal hypotheses: all already minimal for the composed APIs: prefix-law
--   integrability for each selected fiber, a.e. measurability of the prefix map,
--   a.e. compatibility of prefix and stream observables, weight nonnegativity,
--   and positive total weight.

/-- A normalized finite-window selected-output expectation over a prefix law
equals the corresponding weighted stream-law expectation.

For nonnegative finite-window weights with positive total mass, a selected
prefix observable expands to the normalized weighted sum of prefix-law fiber
expectations.  If those prefix observables agree almost everywhere with stream
observables after a prefix map, the finite weighted sum transports to one
stream-law integral.

Layer: Model | Gap: Level 1 (finite-window selected prefix-to-stream expectation)
Proof: compose `finiteWindowSelectedOutputExpectation_eq_weighted_sum` with
  `Finset.sum_smul_integral_map_eq_integral_sum_smul_of_ae` and rewrite the
  attached finite sum from scalar multiplication to real multiplication.
Source: Mathlib product-measure Bochner integration, finite PMF normalization,
  measure-map integration, and finite-sum integral linearity APIs
Used in: randomized stochastic accelerated-gradient output selection where the
  selected prefix search-gradient certificate is rewritten as one generated
  stream weighted-gradient expectation
Book citation: book/FOML/NonconvexStochasticAcceleratedGD.json#/main_theorem/proof/17
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic accelerated gradient descent
  (Algorithm 6.4 and Theorem 6.12) -/
theorem finiteWindowSelectedOutputExpectation_eq_stream_weighted_sum_of_prefix_law
    {Ω Pref E : Type*} [MeasurableSpace Ω] [MeasurableSpace Pref]
    (times : Finset ℕ) (α : ℕ → ℝ) (P : Measure Ω) [SFinite P]
    (prefixMap : Ω → Pref)
    (xPref : ℕ → Pref → E) (xStream : ℕ → Ω → E) (gap : E → ℝ)
    (hprefix : AEMeasurable prefixMap P)
    (hα_nonneg : ∀ k, k ∈ times → 0 ≤ α k)
    (hden : 0 < Finset.sum times α)
    (hgap_int :
      ∀ R : {k : ℕ // k ∈ times},
        Integrable (fun pref => gap (xPref R.1 pref)) (Measure.map prefixMap P))
    (hcompat :
      ∀ k, k ∈ times →
        (fun ω => gap (xPref k (prefixMap ω))) =ᵐ[P]
          fun ω => gap (xStream k ω)) :
    (∫ q : {k : ℕ // k ∈ times} × Pref,
        gap (xPref q.1.1 q.2) ∂
          ((normalizedFiniteWindowPMF times α hα_nonneg hden).toMeasure.prod
            (Measure.map prefixMap P))) =
      (Finset.sum times α)⁻¹ *
        (∫ ω, Finset.sum times.attach (fun k =>
          α k.1 * gap (xStream k.1 ω)) ∂P) := by
  classical
  have hselected :=
    SOptLib.finiteWindowSelectedOutputExpectation_eq_weighted_sum
      (times := times) (α := α) (P := Measure.map prefixMap P)
      (x := xPref) (gap := gap) hα_nonneg hden hgap_int
  have hprefix_to_stream :
      Finset.sum times
          (fun k => α k * ∫ pref, gap (xPref k pref) ∂Measure.map prefixMap P) =
        (∫ ω, Finset.sum times.attach (fun k =>
          α k.1 * gap (xStream k.1 ω)) ∂P) := by
    have htransport :=
      Finset.sum_smul_integral_map_eq_integral_sum_smul_of_ae
        (P := P) (prefixMap := prefixMap) (s := times.attach)
        (w := fun k : {k : ℕ // k ∈ times} => α k.1)
        (Fpref := fun k pref => gap (xPref k.1 pref))
        (Fstream := fun k ω => gap (xStream k.1 ω))
        hprefix
        (by
          intro k _hk
          exact hgap_int k)
        (by
          intro k _hk
          exact hcompat k.1 k.2)
    calc
      Finset.sum times
          (fun k => α k * ∫ pref, gap (xPref k pref) ∂Measure.map prefixMap P)
          =
        Finset.sum times.attach (fun k =>
          α k.1 • ∫ pref, gap (xPref k.1 pref) ∂Measure.map prefixMap P) := by
            rw [← Finset.sum_attach]
            simp [smul_eq_mul]
      _ = (∫ ω, Finset.sum times.attach (fun k =>
          α k.1 * gap (xStream k.1 ω)) ∂P) := by
            simpa [smul_eq_mul] using htransport
  calc
    (∫ q : {k : ℕ // k ∈ times} × Pref,
        gap (xPref q.1.1 q.2) ∂
          ((normalizedFiniteWindowPMF times α hα_nonneg hden).toMeasure.prod
            (Measure.map prefixMap P)))
        =
      (Finset.sum times α)⁻¹ *
        Finset.sum times
          (fun k => α k * ∫ pref, gap (xPref k pref) ∂Measure.map prefixMap P) :=
        hselected
    _ =
      (Finset.sum times α)⁻¹ *
        (∫ ω, Finset.sum times.attach (fun k =>
          α k.1 * gap (xStream k.1 ω)) ∂P) := by
        rw [hprefix_to_stream]

end SOptLib

-- Phase 4 batch 1 merge from Staging/FiniteWindowPMFSpec_denominator_ne_zero.lean
namespace SOptLib

-- Generalization plan (G0):
-- concept/name: finite-window PMF specification forces a nonzero normalizing denominator; orig was outputDenominator_ne_zero_of_outputLawSpec.
-- generality used: arbitrary index type `T`, finite window `times : Finset T`, real weight function, and an externally supplied `PMF` on the support subtype; no measure, convexity, oracle, or algorithm setup assumptions.
-- portable call pattern: randomized-output or stopping-time proofs that accept an externally supplied finite-window PMF with normalized atom formula can prove the finite weight denominator is nonzero before converting ENNReal atoms to real masses.
-- counterargument checked: not paper-local because it is a consequence of the reusable `FiniteWindowPMFSpec` contract; not a pure wrapper because it derives a well-definedness fact about any external PMF, and no existing SOptLib theorem states this direction.
-- coverage search: searched "finite window PMF normalized atoms denominator nonzero", "PMF finite support weights sum one denominator nonzero", and "FiniteWindowPMFSpec denominator nonzero sum weights"; hits covered constructors/specs (`normalizedFiniteWindowPMF_spec`, `finiteWindowPMFSpec_of_normalizedFiniteWindowPMF`) and normalized mass sums, but not denominator nonzero from an external spec.
-- minimal hypotheses: all already minimal; the proof uses only the pointwise atom formula and `PMF.support_nonempty`.

/-- A finite-window PMF atom specification has a nonzero normalizing denominator.

If an externally supplied PMF has atoms equal to real weights divided by the
finite-window sum, then that finite-window sum cannot be zero.  Otherwise every
PMF atom would be zero, contradicting nonempty support of a PMF.

Layer: Model | Gap: Level 0 (finite-window PMF denominator nonzero)
Proof: assume the denominator is zero, rewrite each normalized atom as
  `ENNReal.ofReal 0`, and contradict `PMF.support_nonempty`.
Source: Mathlib probability mass functions, ENNReal coercions, real division by
  zero, and finite-sum normalization over real weights
Used in: nonconvex stochastic block mirror descent randomized-output law before
  converting the selected-output PMF atoms from ENNReal to real singleton masses
Book citation: book/FOML/NonconvexStochasticBlockMirrorDescent.json#/assumptions/15
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic block mirror descent -/
theorem FiniteWindowPMFSpec.denominator_ne_zero
    {T : Type*} (times : Finset T) (weight : T → ℝ)
    (p : PMF {k : T // k ∈ times})
    (hp : FiniteWindowPMFSpec times weight p) :
    Finset.sum times weight ≠ 0 := by
  classical
  intro hden
  rcases PMF.support_nonempty p with ⟨R, hR⟩
  have hp_zero : p R = 0 := by
    have hRspec := hp R
    simpa [FiniteWindowPMFSpec, hden] using hRspec
  exact hR hp_zero

end SOptLib

-- Phase 4 batch 1 merge from Staging/FiniteWindowPMFSpec_denominator_pos_of_nonneg.lean
namespace SOptLib

-- Generalization plan (G0):
-- concept/name: finite-window PMF specification plus nonnegative support weights forces a positive normalizing denominator; orig was outputDenominator_pos_of_outputLawSpec.
-- generality used: arbitrary index type `T`, finite window `times : Finset T`, real weight function, and externally supplied `PMF` on the support subtype; no measure, convexity, oracle, or algorithm setup assumptions.
-- portable call pattern: randomized-output or stopping-time proofs that first prove raw output weights are nonnegative on their finite support can turn any externally supplied normalized finite-window PMF specification into strict denominator positivity.
-- counterargument checked: not paper-local because it composes the reusable `FiniteWindowPMFSpec` atom contract with finite-sum nonnegativity; not a pure wrapper because future selected-output proofs need the positivity conclusion before real-mass conversion and denominator division.
-- coverage search: searched "finite window PMF normalized atoms denominator nonzero", "PMF finite support weights sum one denominator nonzero", "finite window PMFSpec denominator positive nonnegative weights", and Mathlib semantic search "if a finite sum of real numbers is nonnegative and not zero then it is positive"; existing hits covered the nonzero direction, admissible constructors, or generic sum positivity ingredients, but not this PMF-spec-to-positive-denominator contract.
-- minimal hypotheses: all already minimal; pointwise nonnegativity on `times` gives `0 ≤ sum`, and `FiniteWindowPMFSpec.denominator_ne_zero` supplies the only nonzero premise.

/-- A nonnegative finite-window PMF atom specification has a positive normalizing denominator.

If every real weight on the finite support is nonnegative and an externally
supplied PMF has the normalized real-weight atom formula, then the finite sum
of weights is strictly positive.

Layer: Model | Gap: Level 0 (finite-window PMF positive denominator)
Proof: combine finite-sum nonnegativity of the support weights with
  `FiniteWindowPMFSpec.denominator_ne_zero`, then use ordered-real trichotomy.
Source: Mathlib finite sums over ordered real weights and probability mass
  function support via the SOptLib finite-window PMF specification API
Used in: nonconvex stochastic block mirror descent randomized-output law after
  proving raw output weights are nonnegative and before converting selected
  PMF atoms from ENNReal to real singleton masses
Book citation: book/FOML/NonconvexStochasticBlockMirrorDescent.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic block mirror descent -/
theorem FiniteWindowPMFSpec.denominator_pos_of_nonneg
    {T : Type*} (times : Finset T) (weight : T → ℝ)
    (p : PMF {k : T // k ∈ times})
    (hweight_nonneg : ∀ k, k ∈ times → 0 ≤ weight k)
    (hp : FiniteWindowPMFSpec times weight p) :
    0 < Finset.sum times weight := by
  have hnonneg : 0 ≤ Finset.sum times weight :=
    Finset.sum_nonneg hweight_nonneg
  have hne : Finset.sum times weight ≠ 0 :=
    FiniteWindowPMFSpec.denominator_ne_zero times weight p hp
  exact lt_of_le_of_ne hnonneg hne.symm

end SOptLib

-- Phase 4 batch 1 merge from Staging/FiniteWindowPMFSpec_toMeasure_real_singleton.lean
namespace SOptLib

-- Generalization plan (G0):
-- concept/name: finite-window PMF specification converts normalized ENNReal atoms into real singleton masses; orig was outputLawSpec_real_singleton.
-- generality used: arbitrary index type `T`, finite support `times : Finset T`, real weights, an externally supplied PMF on the support subtype, and measurable singleton instances; no convexity, smoothness, oracle, filtration, or algorithm setup assumptions.
-- portable call pattern: randomized-output and stopping-time proofs with an external finite-window PMF can rewrite selector singleton real measures as `weight k / sum weights` once support weights are nonnegative.
-- counterargument checked: not paper-local because it is the reusable real-measure view of `FiniteWindowPMFSpec`; not covered by the constructor-specific `ofFintypeOfReal_toMeasure_real_singleton`, which applies only to PMFs built directly by `PMF.ofFintypeOfReal`.
-- coverage search: searched "FiniteWindowPMFSpec toMeasure real singleton mass nonnegative weights", "PMFSpec singleton toMeasure real FiniteWindowPMFSpec", and "Measure real_def PMF toMeasure apply singleton toReal ofReal nonnegative"; hits covered `FiniteWindowPMFSpec`, denominator positivity, and direct `PMF.ofFintypeOfReal` singleton masses, but not this external-spec bridge.
-- minimal hypotheses: support nonnegativity is used only to derive positivity of the denominator and nonnegativity of the normalized mass; measurable singleton instances are exactly what `PMF.toMeasure_apply_singleton` needs.

/-- A finite-window PMF specification gives real singleton mass equal to the normalized weight.

For an externally supplied PMF satisfying `FiniteWindowPMFSpec`, nonnegative
support weights let the PMF's measure atom be converted from `ENNReal` to the
real normalized mass `weight k / sum weight`.

Layer: Model | Gap: Level 0 (finite-window PMF real singleton mass)
Proof: derive denominator positivity from the finite-window PMF specification,
  evaluate the PMF measure on a singleton, rewrite the atom by the spec, and
  use `ENNReal.toReal_ofReal` under normalized-mass nonnegativity.
Source: Mathlib probability mass functions, singleton measurable sets,
  extended nonnegative real coercions, and SOptLib finite-window PMF specs
Used in: nonconvex stochastic block mirror descent randomized-output law when
  converting the selected stopping index from normalized ENNReal atoms to real
  singleton masses inside the expected stationarity expansion
Book citation: book/FOML/NonconvexStochasticBlockMirrorDescent.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic block mirror descent -/
theorem FiniteWindowPMFSpec.toMeasure_real_singleton
    {T : Type*} [MeasurableSpace T] [MeasurableSingletonClass T]
    (times : Finset T) (weight : T → ℝ)
    (p : PMF {k : T // k ∈ times})
    (hweight_nonneg : ∀ k, k ∈ times → 0 ≤ weight k)
    (hp : FiniteWindowPMFSpec times weight p) :
    ∀ R : {k : T // k ∈ times},
      p.toMeasure.real ({R} : Set {k : T // k ∈ times}) =
        weight R.1 / Finset.sum times weight := by
  intro R
  have hden_pos : 0 < Finset.sum times weight :=
    FiniteWindowPMFSpec.denominator_pos_of_nonneg times weight p hweight_nonneg hp
  have hmass_nonneg : 0 ≤ weight R.1 / Finset.sum times weight :=
    div_nonneg (hweight_nonneg R.1 R.2) (le_of_lt hden_pos)
  rw [Measure.real_def]
  rw [PMF.toMeasure_apply_singleton p R (measurableSet_singleton R)]
  rw [hp R]
  exact ENNReal.toReal_ofReal hmass_nonneg

end SOptLib

