import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Continuous
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Order.Filter.Extr
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Order.Compact
import SOptLib.Model.Carrier
import SOptLib.Model.Diameter

open MeasureTheory
open scoped InnerProductSpace

namespace SOptLib

open MeasureTheory


/-- Objective kernel obtained by composing a fixed decision parameter with a
sampled random variable.
Layer: Model | Concept: Objective
Proof: (definitional construction; per-sample objective evaluation kernel)
Source: Mathlib Bochner integral primitives for stochastic objectives
Used in: stochastic mirror descent objective expectation definitions
Book citation: book/FOML/StochasticMirrorDescent.json#/assumptions/1/math
Origin algorithm: FOML stochastic mirror descent -/
def objectiveKernel
    {Ω X S : Type*} [MeasurableSpace Ω]
    (F : X → S → ℝ) (ξ : Ω → S) (x : X) : Ω → ℝ :=
  fun ω => F x (ξ ω)

/-- Paper-level well-definedness predicate for an objective expectation.
Layer: Model | Gap: Level 0 (objective integrability predicate)
Proof: definitional expansion
Source: Mathlib Bochner integral primitives for stochastic objectives
Used in: stochastic mirror descent objective well-definedness
Book citation: book/FOML/StochasticMirrorDescent.json#/assumptions/1/math
Origin algorithm: FOML stochastic mirror descent -/
def objectiveWellDefined
    {Ω X S : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : X → S → ℝ) (ξ : Ω → S) (x : X) : Prop :=
  Integrable (objectiveKernel F ξ x) μ

/-- Objective expectation `x ↦ ∫ ω, F x (ξ ω) ∂μ` for an abstract stochastic
objective kernel.
Layer: Model | Concept: Objective
Proof: (definitional construction; integral of the objective kernel against the sample measure)
Source: Mathlib Bochner integral primitives for stochastic objectives
Used in: stochastic mirror descent objective expectation and sample transport
Book citation: book/FOML/StochasticMirrorDescent.json#/assumptions/1/math
Origin algorithm: FOML stochastic mirror descent -/
noncomputable def objectiveExpectation
    {Ω X S : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : X → S → ℝ) (ξ : Ω → S) (x : X) : ℝ :=
  ∫ ω, objectiveKernel F ξ x ω ∂μ

/-- Definitional formula for the objective kernel.
Layer: Model | Gap: Level 0 (objective kernel formula)
Proof: projection reduction
Source: Mathlib Bochner integral primitives for stochastic objectives
Used in: stochastic mirror descent objective kernel bridges
Book citation: book/FOML/StochasticMirrorDescent.json#/assumptions/1/math
Origin algorithm: FOML stochastic mirror descent -/
@[simp]
theorem objectiveKernel_apply
    {Ω X S : Type*} [MeasurableSpace Ω]
    (F : X → S → ℝ) (ξ : Ω → S) (x : X) (ω : Ω) :
    objectiveKernel F ξ x ω = F x (ξ ω) := by
  rfl

/-- Definitional formula for the objective expectation as a Bochner integral.
Layer: Model | Gap: Level 0 (objective expectation formula)
Proof: expand the canonical objective expectation definition
Source: Mathlib Bochner integral primitives for stochastic objectives
Used in: stochastic mirror descent objective expectation bridge
Book citation: book/FOML/StochasticMirrorDescent.json#/assumptions/1/math
Origin algorithm: FOML stochastic mirror descent -/
theorem objectiveExpectation_def
    {Ω X S : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : X → S → ℝ) (ξ : Ω → S) (x : X) :
    objectiveExpectation μ F ξ x = ∫ ω, F x (ξ ω) ∂μ := by
  rfl

/-- The objective expectation is the integral of the staged objective kernel.
Layer: Model | Gap: Level 0 (objective expectation/kernel bridge)
Proof: definitional expansion
Source: Mathlib Bochner integral primitives for stochastic objectives
Used in: stochastic mirror descent objective expectation bridge
Book citation: book/FOML/StochasticMirrorDescent.json#/assumptions/1/math
Origin algorithm: FOML stochastic mirror descent -/
theorem objectiveExpectation_eq_integral_kernel
    {Ω X S : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : X → S → ℝ) (ξ : Ω → S) (x : X) :
    objectiveExpectation μ F ξ x = ∫ ω, objectiveKernel F ξ x ω ∂μ := by
  rfl

/-- Paper-level stochastic objective as an expected loss over sampled data.

`paperObjective μ F ξ x` names the objective value obtained by averaging the
kernel `F x ·` along the stochastic sample map `ξ`.

Layer: Model | Concept: Objective
Proof: (definitional construction; paper objective wrapper around
  `objectiveExpectation` for the expected stochastic loss)
Source: Mathlib measure theory integration and measure APIs
Used in: stochastic mirror descent objective setup for the paper objective `f`
  as an expectation over oracle samples
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
noncomputable def paperObjective
    {Ω X S : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : X → S → ℝ) (ξ : Ω → S) (x : X) : ℝ :=
  objectiveExpectation μ F ξ x

/-- The paper objective is definitionally the Bochner expectation of the stochastic kernel.

For any candidate `x`, `paperObjective μ F ξ x` unfolds to the expected value
`∫ ω, F x (ξ ω) ∂μ`, matching the paper notation for an objective defined as
an expectation over sampled data.

Layer: Model | Gap: Level 0 (objective expectation definitional bridge)
Proof: by rfl after unfolding `paperObjective`.
Source: Mathlib MeasureTheory Bochner integral notation and definitions
Used in: stochastic mirror descent identification of the paper objective with
  the expected stochastic loss
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem paperObjective_def
    {Ω X S : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : X → S → ℝ) (ξ : Ω → S) (x : X) :
    paperObjective μ F ξ x = ∫ ω, F x (ξ ω) ∂μ := by
  rfl

/-- A paper objective expectation is well-defined when its sampled objective kernel is
integrable.

For a fixed decision `x`, integrability of `ω ↦ F x (ξ ω)` is exactly the
paper-facing well-definedness condition for the objective built from `F` and
the data stream `ξ`.

Layer: Model | Gap: Level 0 (paper objective well-definedness bridge)
Proof: unfold `objectiveWellDefined` and `objectiveKernel`; the supplied
  integrability hypothesis is the desired condition.
Source: Mathlib MeasureTheory integrability definitions
Used in: stochastic mirror descent paper objective well-definedness for the
  expected loss model
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem paperObjective_wellDefined
    {Ω X S : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : X → S → ℝ) (ξ : Ω → S) (x : X)
    (h_wellDefined : Integrable (fun ω => F x (ξ ω)) μ) :
    objectiveWellDefined μ F ξ x := by
  simpa [objectiveWellDefined, objectiveKernel] using h_wellDefined

/-- A selected minimizer `xStar` and its objective value `fStar` induce the
paper-facing optimum-value model: `fStar` lower-bounds all objective values, and
the selected point satisfies any optimality predicate definitionally equivalent
to `f x = fStar`.
Layer: Model | Gap: Level 0 (optimizer/value bridge)
Proof: rewrite the declared optimum value and apply the minimizer certificate.
Source: Mathlib order primitives for abstract objective values.
Used in: stochastic mirror descent canonical optimizer and optimum value
Book citation: book/FOML/StochasticMirrorDescent.json#/setup/problem/math
Origin algorithm: FOML stochastic mirror descent -/
theorem optimizerValueModel
    {X R : Type*} [Preorder R]
    (f : X → R) (xStar : X) (fStar : R) (IsOptimal : X → Prop)
    (hfStar : fStar = f xStar)
    (hIsOptimal : ∀ x : X, IsOptimal x ↔ f x = fStar)
    (hmin : ∀ z : X, f xStar ≤ f z) :
    (∀ z : X, fStar ≤ f z) ∧ IsOptimal xStar := by
  constructor
  · intro z
    simpa [hfStar] using hmin z
  · exact (hIsOptimal xStar).2 hfStar.symm

/-- Paper-facing optimality predicate asserting that an iterate attains the
reference objective value `fStar`.

This reusable canonical form records the statement `f x = fStar` for
preorder-valued objectives, matching the book-level optimality condition.

Layer: Model | Concept: Objective
Proof: (definitional construction; canonical equality predicate for an objective
  value attaining `fStar`)
Source: Mathlib order/preorder and propositional equality APIs
Used in: stochastic mirror descent paper-facing optimality statement for the
  returned iterate objective value
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
def IsOptimalValue
    {X R : Type*} [Preorder R] (f : X → R) (fStar : R) (x : X) : Prop :=
  f x = fStar

/-- Source-backed argmin selector packages a known optimizer as an abstract minimizer witness.

Given a preorder-valued objective `f`, a source point, and a proof that the
source point minimizes `f`, this definition returns the selected optimum point
as a subtype carrying its global minimality certificate.

Layer: Model | Concept: Objective
Proof: (definitional construction; subtype wrapper for a source-backed global
  argmin certificate)
Source: Mathlib order theory and subtype APIs
Used in: stochastic mirror descent source-backed minimizer selection and optimum
  value extraction
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
def argminSelectorOfSource
    {X R : Type*} [Preorder R]
    (f : X → R) (source : X) (hsource : ∀ z : X, f source ≤ f z) :
    {x : X // ∀ z : X, f x ≤ f z} :=
  ⟨source, hsource⟩

/-- Canonical extraction of the paper optimizer `xStar` from an abstract argmin witness.

Layer: Model | Concept: Objective
Proof: (definitional construction; subtype projection from an argmin certificate to its optimizer value)
Source: Mathlib subtype and dependent pair projection APIs
Used in: stochastic mirror descent canonical optimizer `xStar` selection from an argmin certificate
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
def selectedOptimizer
    {X : Type*} {P : X → Prop} (argmin : {x : X // P x}) : X :=
  argmin.1

/-- A selected optimizer preserves the certification predicate carried by its subtype witness.

For any certified candidate `argmin : {x : X // P x}`, the model-level selector
`selectedOptimizer argmin` still satisfies `P`.

Layer: Model | Gap: Level 0 (selected optimizer certification projection)
Proof: unfold `selectedOptimizer` and simplify the subtype witness projection,
  using the proof component `argmin.2`.
Source: Mathlib subtype coercion and simplification APIs
Used in: stochastic mirror descent objective minimizer certificate extraction
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem selectedOptimizer_spec
    {X : Type*} {P : X → Prop} (argmin : {x : X // P x}) :
    P (selectedOptimizer argmin) := by
  simpa [selectedOptimizer] using argmin.2

/-- Any minimizer has the selected optimizer value when the declared optimum is a global lower bound.

If `x` minimizes `f`, `fStar` is the value at a selected optimizer `xStar`, and
`fStar` lower-bounds all objective values, then the objective value at `x`
equals `fStar`.

Layer: Model | Gap: Level 0 (optimizer value identification by antisymmetry)
Proof: apply `le_antisymm`; the upper bound comes from minimality of `x` at
  `xStar`, and the lower bound comes from the global optimum-value lower bound
  at `x`.
Source: Mathlib order theory for partial orders and antisymmetry
Used in: stochastic mirror descent objective minimizer value certification
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem eq_optimizerValue_of_minimizer
    {X R : Type*} [PartialOrder R]
    (f : X → R) (xStar x : X) (fStar : R)
    (hfStar : fStar = f xStar)
    (hmin : ∀ z : X, f x ≤ f z) (hopt : ∀ z : X, fStar ≤ f z) :
    f x = fStar := by
  exact le_antisymm (by simpa [hfStar] using hmin xStar) (by simpa using hopt x)

/-- Paper-level expectation operator as a Bochner integral.

For an abstract probability or measure space `Ω`, `expectation μ Z` denotes the
paper expectation of a scalar or vector-valued random variable `Z : Ω → R`,
implemented by Mathlib's Bochner integral.

Layer: Model | Concept: Objective
Proof: (definitional construction; paper expectation operator wrapped around
  the Bochner integral notation `∫ ω, Z ω ∂μ`)
Source: Mathlib measure theory Bochner integral API
Used in: stochastic mirror descent expected objective and oracle-error terms
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
noncomputable def expectation
    {Ω R : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    (μ : Measure Ω) (Z : Ω → R) : R :=
  ∫ ω, Z ω ∂μ

/-- The paper expectation notation unfolds to Mathlib's Bochner integral.

For any measure `μ` and integrand `Z`, `expectation μ Z` is definitionally
the integral `∫ ω, Z ω ∂μ`.

Layer: Model | Gap: Level 0 (paper expectation notation)
Proof: by rfl after unfolding expectation.
Source: Mathlib measure theory Bochner integral notation
Used in: stochastic mirror descent expected objective and oracle-error terms
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem expectation_def
    {Ω R : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    (μ : Measure Ω) (Z : Ω → R) :
    expectation μ Z = ∫ ω, Z ω ∂μ := by
  rfl

/-- Paper-level well-definedness predicate for Bochner expectations.

`expectationWellDefined μ Z` records that the random quantity `Z` has a
well-defined expectation under `μ`, implemented as Mathlib integrability.

Layer: Model | Concept: Objective
Proof: (definitional construction; paper-level expectation well-definedness
  wrapper around `Integrable Z μ`)
Source: Mathlib measure theory Bochner integration and integrability APIs
Used in: stochastic mirror descent expected objective well-definedness checks
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
def expectationWellDefined
    {Ω R : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    (μ : Measure Ω) (Z : Ω → R) : Prop :=
  Integrable Z μ

/-- Paper-level expectation well-definedness is exactly Mathlib integrability.

Layer: Model | Gap: Level 0 (expectation well-definedness as integrability)
Proof: by rfl after unfolding expectationWellDefined.
Source: Mathlib measure theory Bochner integrability APIs
Used in: stochastic mirror descent objective-kernel expectation well-definedness
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem expectationWellDefined_iff_integrable
    {Ω R : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    (μ : Measure Ω) (Z : Ω → R) :
    expectationWellDefined μ Z ↔ Integrable Z μ := by
  rfl

/-- An objective-kernel well-definedness hypothesis gives a well-defined paper expectation.

For a fixed decision `x`, the sampled objective `ω ↦ F x (ξ ω)` is
expectation-well-defined whenever the corresponding objective-kernel
well-definedness predicate holds.

Layer: Model | Gap: Level 0 (objective kernel expectation well-definedness)
Proof: by simplification after unfolding `expectationWellDefined`,
  `objectiveWellDefined`, and `objectiveKernel`.
Source: Mathlib measure theory integrability and expectation predicate APIs
Used in: stochastic mirror descent sample objective expectation well-definedness
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem expectationWellDefined_objectiveKernel_of_objectiveWellDefined
    {Ω X S : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : X → S → ℝ) (ξ : Ω → S) (x : X)
    (h_obj : objectiveWellDefined μ F ξ x) :
    expectationWellDefined μ (fun ω => F x (ξ ω)) := by
  simpa [expectationWellDefined, objectiveWellDefined, objectiveKernel] using h_obj

/-- Ambient totalization of a sampled objective kernel from a feasible carrier.

Turns a carrier-indexed sampled objective `F : {x : E // x ∈ X} → S → ℝ` into
an ambient objective on `E` by totalizing through the feasible set `X`.

Layer: Model | Concept: Objective
Proof: (definitional construction; sampled objective totalized from the
  feasible carrier to the ambient decision space via `carrierTotalizeOn`)
Source: Mathlib set subtype and function construction APIs
Used in: stochastic mirror descent sampled objective evaluation on ambient
  iterates and prox candidates
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
noncomputable def objectiveAmbient
    {E S : Type*} (X : Set E) (F : {x : E // x ∈ X} → S → ℝ) (s : S) :
    E → ℝ :=
  carrierTotalizeOn X (fun x => F x s)

/-- The totalized sampled objective agrees with the carrier objective on feasible points.

If `x ∈ X`, evaluating the ambient objective built from `F` at `x` is the same
as evaluating `F` on the corresponding feasible subtype point.

Layer: Model | Gap: Level 0 (ambient objective feasible-point rewrite)
Proof: by simplification after unfolding `objectiveAmbient` and
  `carrierTotalizeOn`, using the membership proof `hx` to select the carrier
  branch.
Source: Mathlib Set subtype coercions and `simp` normalization APIs
Used in: stochastic mirror descent objective evaluation on feasible iterates
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
@[simp]
theorem objectiveAmbient_of_mem
    {E S : Type*} (X : Set E) (F : {x : E // x ∈ X} → S → ℝ) (s : S)
    {x : E} (hx : x ∈ X) :
    objectiveAmbient X F s x = F ⟨x, hx⟩ s := by
  simp [objectiveAmbient, carrierTotalizeOn, hx]

end SOptLib

namespace SOptLib

/-- A value certified to be the Bochner expectation of a random variable.

`ExpectationValue μ Z` bundles a candidate value with the integrability boundary
needed for `SOptLib.expectation μ Z` and a proof that the candidate is exactly
that expectation. This keeps stochastic-optimization model files from exposing
totalized expectations before the well-definedness proof has been supplied.

Layer: Model | Concept: Objective
Proof: (definitional construction; certified expectation-value bundle over the
  SOptLib Bochner expectation and well-definedness predicate)
Source: Mathlib measure theory Bochner integration and integrability APIs
Used in: stochastic mirror descent and stochastic block mirror descent objective
  and oracle expectation boundaries
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/setup/problem
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
structure ExpectationValue
    {Ω R : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    (μ : Measure Ω) (Z : Ω → R) where
  val : R
  property : expectationWellDefined μ Z ∧ val = expectation μ Z

/-- A certified expectation value projects to the canonical expectation.

Any `ExpectationValue μ Z` carries both the well-definedness boundary for `Z`
and the equality of its stored value with `SOptLib.expectation μ Z`; this lemma
exposes the equality as a rewrite theorem for algorithm-facing objects.

Layer: Model | Gap: Level 0 (certified expectation value projection)
Proof: extract the equality component of the certified expectation bundle.
Source: Mathlib measure theory Bochner expectation and integrability APIs
Used in: stochastic block mirror descent final output expected suboptimality
  after constructing the certified expectation object
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/main_theorem
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
@[simp] theorem ExpectationValue.val_eq_expectation
    {Ω R : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    {μ : Measure Ω} {Z : Ω → R} (e : ExpectationValue μ Z) :
    e.val = expectation μ Z :=
  e.property.2

/-- An expectation is well-defined when the random variable is dominated by an
integrable real envelope almost everywhere.

This is the expectation-level form of the common final step after proving an
integrable stochastic envelope and an a.e. norm bound for the target random
variable.

Layer: Model | Gap: Level 0 (expectation well-definedness by integrable envelope)
Proof: apply Mathlib's Bochner integrability domination theorem
  `Integrable.mono'`, then unfold `expectationWellDefined` through its
  integrability characterization.
Source: Mathlib Bochner integrability and almost-everywhere domination APIs
Used in: stochastic block mirror descent expected suboptimality gap
  well-definedness from a finite-window stochastic envelope
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/main_theorem
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem expectationWellDefined_of_integrable_envelope
    {Ω R : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    {μ : Measure Ω} {Z : Ω → R} {envelope : Ω → ℝ}
    (henvelope : Integrable envelope μ)
    (hZ_meas : AEStronglyMeasurable Z μ)
    (hbound : ∀ᵐ ω ∂μ, ‖Z ω‖ ≤ envelope ω) :
    expectationWellDefined μ Z := by
  exact (expectationWellDefined_iff_integrable μ Z).2
    (Integrable.mono' henvelope hZ_meas hbound)

end SOptLib

namespace SOptLib

/-- Global minimizer predicate for a preorder-valued objective.

For an objective `Psi : P → R`, this names the condition that `xStar` has
objective value below every candidate value.

Layer: Model | Concept: Objective
Proof: (definitional construction; universal lower-bound predicate for a selected objective value)
Source: Mathlib order theory for preorder-valued objective minimization
Used in: randomized stochastic mirror descent feasible-carrier composite objective minimizer predicate
Book citation: book/FOML/StochasticMirrorDescent.json#/setup/problem/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, randomized stochastic mirror descent -/
def IsMinimizer
    {P R : Type*} [Preorder R] (Psi : P → R) (xStar : P) : Prop :=
  ∀ x : P, Psi xStar ≤ Psi x

/-- Composite objective obtained by adding two pointwise objective components.

For objectives `f` and `h` on the same feasible carrier, `compositeObjective f h`
names the paper objective `x ↦ f x + h x`.

Layer: Model | Concept: Objective
Proof: (definitional construction; pointwise additive wrapper for a composite
  objective on a feasible carrier)
Source: Mathlib function and additive algebra APIs for pointwise objective
  construction
Used in: nonconvex stochastic mirror descent feasible-carrier composite
  objective `Psi = f + h`
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
abbrev compositeObjective
    {P R : Type*} [Add R] (f h : P → R) (x : P) : R :=
  f x + h x

/-- Ambient composite objective obtained by adding two totalized objective components.

For ambient objective realizations `fAmbient` and `hAmbient` on the same space,
`compositeObjectiveAmbient fAmbient hAmbient` names the pointwise sum used to
totalize the composite feasible-carrier objective.

Layer: Model | Concept: Objective
Proof: (definitional construction; pointwise additive wrapper for ambient
  totalizations of two objective components)
Source: Mathlib function and additive algebra APIs for pointwise objective
  construction
Used in: nonconvex stochastic mirror descent ambient totalization of the
  composite objective `Psi = f + h`
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
abbrev compositeObjectiveAmbient
    {E R : Type*} [Add R] (fAmbient hAmbient : E → R) (x : E) : R :=
  fAmbient x + hAmbient x

/-- An ambient composite objective agrees with the carrier composite objective at feasible points.

If each ambient objective component agrees with its carrier objective component
at a feasible point `x ∈ X`, then the ambient pointwise composite objective
agrees with the carrier pointwise composite objective at the corresponding
subtype point.

Layer: Model | Gap: Level 0 (ambient composite objective feasible-point rewrite)
Proof: unfold the pointwise composite objective wrappers and rewrite the two
  component feasible-point equalities.
Source: Mathlib Set subtype coercions and additive function APIs
Used in: nonconvex stochastic mirror descent feasible-point bridge for the
  ambient composite objective `PsiAmbient` and carrier composite objective `Psi`
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic mirror descent -/
theorem compositeObjectiveAmbient_of_mem
    {E R : Type*} [Add R]
    (X : Set E) (f h : {x : E // x ∈ X} → R)
    (fAmbient hAmbient : E → R) {x : E} (hx : x ∈ X)
    (hf : fAmbient x = f ⟨x, hx⟩)
    (hh : hAmbient x = h ⟨x, hx⟩) :
    SOptLib.compositeObjectiveAmbient fAmbient hAmbient x =
      SOptLib.compositeObjective f h ⟨x, hx⟩ := by
  rw [SOptLib.compositeObjectiveAmbient, SOptLib.compositeObjective, hf, hh]

/-- The optimum value associated to a bundled global minimizer is the objective
value at the bundled minimizing point.

Layer: Model | Concept: Objective
Proof: (definitional construction; subtype projection from a certified global
  minimizer to the corresponding objective value)
Source: Mathlib order theory and subtype APIs for globally minimizing witnesses
Used in: randomized stochastic mirror descent realization of the paper optimum
  value `Ψ*` from an attained composite-objective minimum
Book citation: book/FOML/StochasticMirrorDescent.json#/setup/problem/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic mirror descent -/
noncomputable def optimizerValueOfMinimum
    {P R : Type*} [Preorder R]
    (Psi : P → R) (minimum : {x : P // ∀ y : P, Psi x ≤ Psi y}) : R :=
  Psi minimum.1

/-- An optimizer value obtained from an attained global minimum lower-bounds every objective value.

If `xStar` is a global minimizer of `Psi` on the whole feasible carrier and
`PsiStar` is the staged optimizer value associated to that attained minimum,
then every candidate has objective value at least `PsiStar`.

Layer: Model | Gap: Level 0 (attained optimizer value lower bound)
Proof: convert the `IsMinOn` certificate on `Set.univ` to a pointwise global
  lower-bound using `isMinOn_univ_iff`, then unfold the staged optimizer value.
Source: Mathlib order theory APIs for `IsMinOn` and global extrema on `Set.univ`
Used in: randomized stochastic mirror descent composite objective optimum `PsiStar`
  lower-bounding feasible terminal and initial objective values
Book citation: book/FOML/StochasticMirrorDescent.json#/setup/problem/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic mirror descent -/
theorem optimizerValue_le_of_attained_minimum
    {P R : Type*} [Preorder R]
    (Psi : P → R) (xStar : P) (PsiStar : R) (x : P)
    (hmin : IsMinOn Psi Set.univ xStar)
    (hPsiStar :
      PsiStar =
        optimizerValueOfMinimum Psi
          ⟨xStar, (isMinOn_univ_iff (f := Psi) (a := xStar)).1 hmin⟩) :
    PsiStar ≤ Psi x := by
  have hmin_all :
      ∀ y : P, Psi xStar ≤ Psi y :=
    (isMinOn_univ_iff (f := Psi) (a := xStar)).1 hmin
  simpa [hPsiStar, optimizerValueOfMinimum] using hmin_all x

/-- Bundled witness that an objective attains a global minimum.

An `ObjectiveMinimum f` stores a selected optimizer together with the proof
that its objective value is below every candidate value.

Layer: Model | Concept: Objective
Proof: (definitional construction; selected optimizer bundled with a global
  lower-bound certificate for a preorder-valued objective)
Source: Mathlib order theory for preorder-valued global minima and subtype APIs
Used in: stochastic mirror descent optimum-value and selected-optimizer bookkeeping
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
structure ObjectiveMinimum {P R : Type*} [Preorder R] (f : P → R) where
  val : P
  isMinimizer : SOptLib.IsMinimizer f val

namespace ObjectiveMinimum

/-- The objective value attained by a bundled objective minimum.

Layer: Model | Concept: Objective
Proof: (definitional construction; evaluate the objective at the bundled
  selected optimizer)
Source: Mathlib order theory and function evaluation APIs for objective values
Used in: stochastic mirror descent optimum value `fStar` associated to a selected optimizer
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
def value {P R : Type*} [Preorder R] {f : P → R}
    (minimum : ObjectiveMinimum f) : R :=
  f minimum.val

/-- The value of a bundled objective minimum unfolds to the objective at its optimizer.

Layer: Model | Gap: Level 0 (objective-minimum value projection)
Proof: by rfl after unfolding `ObjectiveMinimum.value`.
Source: Mathlib order theory and function evaluation APIs for objective values
Used in: stochastic mirror descent identification of `fStar` with `f x_*`
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
@[simp]
theorem value_eq {P R : Type*} [Preorder R] {f : P → R}
    (minimum : ObjectiveMinimum f) :
    minimum.value = f minimum.val := by
  rfl

/-- The value of a bundled objective minimum lower-bounds every objective value.

Layer: Model | Gap: Level 0 (attained objective-minimum lower bound)
Proof: unfold the bundled objective value and apply the stored global
  minimizer certificate to the comparison point.
Source: Mathlib order theory for preorder-valued global minima
Used in: stochastic mirror descent nonnegativity of output objective gaps
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem value_le {P R : Type*} [Preorder R] {f : P → R}
    (minimum : ObjectiveMinimum f) (x : P) :
    minimum.value ≤ f x := by
  simpa [value] using minimum.isMinimizer x

/-- Convert a bundled objective minimum to the existing minimizer subtype form.

Layer: Model | Concept: Objective
Proof: (definitional construction; subtype packaging of the bundled optimizer
  and its minimizer certificate)
Source: Mathlib subtype APIs for certified global minimizers
Used in: stochastic mirror descent compatibility with existing optimizer-value projections
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
def toSubtype {P R : Type*} [Preorder R] {f : P → R}
    (minimum : ObjectiveMinimum f) :
    {x : P // SOptLib.IsMinimizer f x} :=
  ⟨minimum.val, minimum.isMinimizer⟩

/-- Build a bundled objective minimum from the existing minimizer subtype form.

Layer: Model | Concept: Objective
Proof: (definitional construction; unpack the subtype optimizer and global
  minimizer certificate into the bundled objective-minimum structure)
Source: Mathlib subtype APIs for certified global minimizers
Used in: stochastic mirror descent migration from subtype minimizer witnesses to named objective minima
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
def ofSubtype {P R : Type*} [Preorder R] {f : P → R}
    (minimum : {x : P // SOptLib.IsMinimizer f x}) :
    ObjectiveMinimum f :=
  ⟨minimum.1, minimum.2⟩

/-- Build a bundled objective minimum from a source point and its global lower-bound proof.

Layer: Model | Concept: Objective
Proof: (definitional construction; store the selected source point with the
  supplied universal objective lower-bound certificate)
Source: Mathlib order theory for preorder-valued global minima
Used in: stochastic mirror descent source-backed optimizer bridge from theorem-local minimizer data
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
def ofSource {P R : Type*} [Preorder R] (f : P → R)
    (xStar : P) (hmin : ∀ x : P, f xStar ≤ f x) :
    ObjectiveMinimum f :=
  ⟨xStar, hmin⟩

/-- The source-backed bundled objective minimum has the supplied source as optimizer.

Layer: Model | Gap: Level 0 (source-backed objective-minimum optimizer projection)
Proof: by rfl after unfolding `ObjectiveMinimum.ofSource`.
Source: Mathlib structure projection APIs for certified global minimizers
Used in: stochastic mirror descent bridge from paper optimizer `x_*` to bundled objective minimum
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
@[simp]
theorem ofSource_val {P R : Type*} [Preorder R] (f : P → R)
    (xStar : P) (hmin : ∀ x : P, f xStar ≤ f x) :
    (ObjectiveMinimum.ofSource f xStar hmin).val = xStar := by
  rfl

end ObjectiveMinimum

/-- The objective value attached to a bundled attained objective minimum.

For a bundled minimizer `minimum : ObjectiveMinimum f`, this value is computed
through the existing subtype-based `optimizerValueOfMinimum` projection while
using the certificate stored in the bundled witness.

Layer: Model | Concept: Objective
Proof: (definitional construction; convert the bundled minimizer certificate
  to the subtype expected by `optimizerValueOfMinimum`)
Source: Mathlib order theory and subtype APIs for preorder-valued global minima
Used in: stochastic block mirror descent optimum value `fStar` associated with
  the selected feasible optimizer
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
noncomputable def objectiveMinimumValue
    {P R : Type*} [Preorder R] (f : P → R) (minimum : ObjectiveMinimum f) : R :=
  optimizerValueOfMinimum f
    ⟨minimum.val, by
      simpa [IsMinimizer] using minimum.isMinimizer⟩

/-- The value attached to a bundled attained objective minimum is the objective
at its selected optimizer.

Layer: Model | Gap: Level 0 (objective-minimum value projection)
Proof: unfold `objectiveMinimumValue`, `optimizerValueOfMinimum`, and the
  bundled objective-minimum projections.
Source: Mathlib order theory and subtype APIs for preorder-valued global minima
Used in: stochastic block mirror descent identification of `fStar` with
  `f x_*` for the selected optimizer
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
@[simp]
theorem objectiveMinimumValue_eq
    {P R : Type*} [Preorder R] (f : P → R) (minimum : ObjectiveMinimum f) :
    objectiveMinimumValue f minimum = f minimum.val := by
  rfl

/-- The value attached to a bundled attained objective minimum lower-bounds every objective value.

For a bundled minimizer `minimum : ObjectiveMinimum f`, the staged value
`objectiveMinimumValue f minimum` is below the objective value at any candidate.

Layer: Model | Gap: Level 0 (objective-minimum value lower bound)
Proof: unfold the staged compatibility value and apply the stored global
  minimizer certificate from the bundled objective minimum.
Source: Mathlib order theory and subtype APIs for preorder-valued global minima
Used in: stochastic block mirror descent nonnegativity of feasible objective gaps
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem objectiveMinimumValue_le
    {P R : Type*} [Preorder R] (f : P → R) (minimum : ObjectiveMinimum f) (x : P) :
    objectiveMinimumValue f minimum ≤ f x := by
  simpa [objectiveMinimumValue, optimizerValueOfMinimum, IsMinimizer] using
    minimum.isMinimizer x

/-- Build a feasible-carrier objective minimum from ambient optimizer data.

If an ambient point `xStar` is feasible and its objective value lower-bounds
the objective at every feasible ambient point, then `xStar` determines a
bundled attained minimum for the objective restricted to the feasible carrier.

Layer: Model | Concept: Objective
Proof: (definitional construction; package the feasible point as a subtype and
  transport the ambient feasible-set lower-bound certificate to all carrier
  candidates)
Source: Mathlib order theory and subtype APIs for preorder-valued constrained minima
Used in: stochastic block mirror descent construction of the feasible-carrier
  optimum witness from source optimizer data
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
noncomputable def objectiveMinimumOfFeasibleOptimizer
    {E R : Type*} [Preorder R] (X : Set E) (f : E → R)
    (xStar : E) (hxStar : xStar ∈ X)
    (h_opt : ∀ z, z ∈ X → f xStar ≤ f z) :
    ObjectiveMinimum (fun x : {x : E // x ∈ X} => f x.1) :=
  ObjectiveMinimum.ofSource (fun x : {x : E // x ∈ X} => f x.1)
    ⟨xStar, hxStar⟩ (by
      intro z
      exact h_opt z.1 z.2)

/-- The feasible-carrier minimum built from ambient optimizer data has value `f xStar`.

Layer: Model | Gap: Level 0 (feasible-carrier objective-minimum value projection)
Proof: unfold the feasible-carrier constructor and the bundled objective-minimum
  value, then reduce the subtype projection.
Source: Mathlib order theory and subtype APIs for preorder-valued constrained minima
Used in: stochastic block mirror descent identification of the staged optimum
  value with the source optimizer objective value
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
@[simp]
theorem objectiveMinimumOfFeasibleOptimizer_value
    {E R : Type*} [Preorder R] (X : Set E) (f : E → R)
    (xStar : E) (hxStar : xStar ∈ X)
    (h_opt : ∀ z, z ∈ X → f xStar ≤ f z) :
    (objectiveMinimumOfFeasibleOptimizer X f xStar hxStar h_opt).value = f xStar := by
  rfl

/-- A stream integral equals the canonical objective expectation when the
stream has the objective sample law.

For a fixed decision `x`, if the sample map `Y` pushes the source measure `P`
forward to the law `ν`, then the expected loss sampled through `Y` is the
objective expectation against `ν` and the identity sample map.

Layer: Model | Gap: Level 0 (objective expectation under pushforward law)
Proof: apply the Bochner integral map theorem to move the composed objective
  kernel to `Measure.map Y P`, rewrite this mapped measure by the supplied law,
  and fold the result into `objectiveExpectation`.
Source: Mathlib measure theory Bochner integral map API and SOptLib objective
  expectation definitions
Used in: stochastic block mirror descent objective expectation transport from
  generated sample streams to the canonical one-step objective law
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem objectiveExpectation_eq_integral_of_map_eq
    {Ω S X : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (ν : Measure S) (F : X → S → ℝ) (Y : Ω → S) (x : X)
    (hY : AEMeasurable Y P)
    (hF : AEStronglyMeasurable (fun s : S => F x s) ν)
    (hmap : Measure.map Y P = ν) :
    (∫ ω, F x (Y ω) ∂P) =
      objectiveExpectation ν F (fun s : S => s) x := by
  have hF_map : AEStronglyMeasurable (fun s : S => F x s) (Measure.map Y P) := by
    rwa [hmap]
  calc
    (∫ ω, F x (Y ω) ∂P) =
        ∫ s, F x s ∂Measure.map Y P :=
      (MeasureTheory.integral_map hY hF_map).symm
    _ = ∫ s, F x s ∂ν := by
      rw [hmap]
    _ = objectiveExpectation ν F (fun s : S => s) x := by
      exact (objectiveExpectation_def ν F (fun s : S => s) x).symm

/-- A stochastic objective well-defined on a carrier is well-defined at every
point of that carrier.

This packages the common model-layer step from a feasible-carrier
well-definedness assumption to the pointwise `objectiveWellDefined` fact used
by objective expectation proofs.

Layer: Model | Gap: Level 0 (carrier-indexed stochastic objective well-definedness)
Proof: specialize the carrier-indexed well-definedness hypothesis at the
  feasible point.
Source: Mathlib set membership and universal quantifier specialization APIs
Used in: stochastic block mirror descent objective expectation on feasible
  iterates and comparison points
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/assumptions/0/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem stochasticObjective_wellDefined_of_mem
    {Ω X S : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : X → S → ℝ) (ξ : Ω → S)
    (carrier : Set X)
    (h_wellDefined : ∀ y, y ∈ carrier → objectiveWellDefined μ F ξ y)
    {x : X} (hx : x ∈ carrier) :
    objectiveWellDefined μ F ξ x := by
  exact h_wellDefined x hx

/-- The gradient of a finite average objective is the finite average of the
component gradients.

If every component objective `F i` has gradient `gradF i x` at a point `x`,
then the normalized finite sum of the component objectives has gradient equal
to the normalized finite sum of those component gradients at `x`.

Layer: Model | Gap: Level 1 (finite-average objective gradient calculus)
Proof: sum the component Fréchet derivatives, scale the scalar-valued
  derivative by the averaging constant, and convert back through the
  Hilbert-space gradient/dual identification.
Source: Mathlib gradient calculus and finite Fréchet-derivative sum APIs
Used in: finite-sum stochastic nonconvex conditional gradient identification
  of the full finite-sum gradient used to center component-sampling estimators
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem finiteAverageObjective_hasGradientAt
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (F : ι → E → ℝ) (gradF : ι → E → E) (x : E)
    (hF : ∀ i : ι, HasGradientAt (F i) (gradF i x) x) :
    HasGradientAt
      (fun z : E => (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ (fun i : ι => F i z))
      ((Fintype.card ι : ℝ)⁻¹ •
        Finset.sum Finset.univ (fun i : ι => gradF i x)) x := by
  classical
  have hsum : HasFDerivAt
      (fun z : E => Finset.sum Finset.univ (fun i : ι => F i z))
      (Finset.sum Finset.univ
        (fun i : ι => InnerProductSpace.toDual ℝ E (gradF i x))) x := by
    refine HasFDerivAt.fun_sum ?_
    intro i _hi
    exact (hF i).hasFDerivAt
  have hscaled := hsum.const_smul ((Fintype.card ι : ℝ)⁻¹)
  convert hscaled.hasGradientAt using 1
  simp [map_smul, map_sum]

/-- A continuous objective on a nonempty compact feasible set attains its constrained minimum.

The witness is returned as a point of the feasible subtype, so downstream
objective code can consume it directly as an attained minimum over the carrier.

Layer: Model | Gap: Level 1 (compact constrained objective minimum existence)
Proof: apply Mathlib's compact extreme-value theorem to get an ambient
  `IsMinOn` witness, then rebuild it as a feasible-subtype minimizer.
Source: Mathlib compactness, closed-order topology, and extreme-value APIs
Used in: stochastic and finite-sum nonconvex conditional-gradient construction
  of the feasible objective optimum `f^*`
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem objectiveMinimum_exists_of_isCompact_continuousOn
    {E R : Type*} [TopologicalSpace E] [LinearOrder R] [TopologicalSpace R]
    [ClosedIicTopology R] {X : Set E} (f : E → R)
    (hX_compact : IsCompact X) (hX_nonempty : X.Nonempty)
    (hcont : ContinuousOn f X) :
    ∃ x : X, ∀ y : X, f x ≤ f y := by
  classical
  obtain ⟨x, hxX, hmin⟩ := hX_compact.exists_isMinOn hX_nonempty hcont
  refine ⟨⟨x, hxX⟩, ?_⟩
  intro y
  exact hmin y.property

/-- A carrier-restricted composite objective is measurable when both ambient
components are measurable after restriction to the carrier.

This packages the common optimization proof step where `f` and `h` are
established as measurable on feasible points, and the algorithm-facing goal is
the named composite objective `SOptLib.compositeObjective f h`.

Layer: Model | Gap: Level 0 (carrier composite-objective measurability)
Proof: unfold the named composite objective and close under Mathlib's
  measurable pointwise addition API.
Source: Mathlib measure theory APIs for measurable addition and subtype
  measurable spaces
Used in: stochastic accelerated gradient descent carrier composite-objective
  measurability before generated-output expected-gap integrability
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/setup/problem/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem carrierCompositeObjective_measurable
    {E R : Type*} {X : Set E}
    [MeasurableSpace {x : E // x ∈ X}]
    [MeasurableSpace R] [Add R] [MeasurableAdd₂ R]
    {f h : E → R}
    (hf : Measurable (fun x : {x : E // x ∈ X} => f x.1))
    (hh : Measurable (fun x : {x : E // x ∈ X} => h x.1)) :
    Measurable (fun x : {x : E // x ∈ X} =>
      compositeObjective f h x.1) := by
  simpa [compositeObjective] using hf.add hh


/-- Time-indexed objective-gap integrand for an output stochastic process.

`objectiveGapIntegrand objective optimumValue output k` is the random variable
`ω ↦ objective (output k ω) - optimumValue`, the pointwise suboptimality gap
before taking an expectation.

Layer: Model | Concept: Objective
Proof: (definitional construction; time-indexed output process evaluated through an objective and shifted by a reference value)
Source: Convex optimization suboptimality-gap notation and Mathlib function evaluation APIs
Used in: stochastic accelerated gradient descent expected suboptimality integrand before the Theorem 4.4 expectation bound
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/main_theorem/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic accelerated gradient descent -/
def objectiveGapIntegrand
    {Ω X R : Type*} [Sub R]
    (objective : X → R) (optimumValue : R) (output : ℕ → Ω → X)
    (k : ℕ) (ω : Ω) : R :=
  objective (output k ω) - optimumValue

/-- The time-indexed objective-gap integrand unfolds to objective value minus
the reference optimum value.

Layer: Model | Gap: Level 0 (objective-gap integrand formula)
Proof: by rfl after unfolding `objectiveGapIntegrand`.
Source: Convex optimization suboptimality-gap notation and Mathlib function evaluation APIs
Used in: stochastic accelerated gradient descent expected suboptimality integrand before the Theorem 4.4 expectation bound
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/main_theorem/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic accelerated gradient descent -/
@[simp]
theorem objectiveGapIntegrand_def
    {Ω X R : Type*} [Sub R]
    (objective : X → R) (optimumValue : R) (output : ℕ → Ω → X)
    (k : ℕ) (ω : Ω) :
    objectiveGapIntegrand objective optimumValue output k ω =
      objective (output k ω) - optimumValue := by
  rfl

/-- An objective-gap integrand is pointwise nonnegative whenever
the reference value lower-bounds all objective values.

Layer: Model | Gap: Level 0 (objective-gap integrand nonnegativity)
Proof: unfold `objectiveGapIntegrand` and use `sub_nonneg` with the supplied
objective lower bound.
Source: Convex optimization suboptimality-gap notation and Mathlib ordered
subtraction APIs
Used in: stochastic accelerated gradient descent expected suboptimality
integrand nonnegativity
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/main_theorem/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
Machine Learning, stochastic accelerated gradient descent -/
theorem objectiveGapIntegrand_nonneg
    {Ω X R : Type*} [AddGroup R] [LE R] [AddRightMono R]
    (objective : X → R) (optimumValue : R) (output : ℕ → Ω → X)
    (hoptimumValue_le : ∀ x : X, optimumValue ≤ objective x)
    (k : ℕ) (ω : Ω) :
    0 ≤ objectiveGapIntegrand objective optimumValue output k ω := by
  exact sub_nonneg.mpr (hoptimumValue_le (output k ω))


/-- An objective-gap integrand is a.e. strongly measurable when the objective
value along the output process is a.e. strongly measurable.

For a fixed time `k`, the random variable
`objectiveGapIntegrand objective optimumValue output k` is obtained from the
objective-value random variable by subtracting the constant reference value
`optimumValue`.

Layer: Model | Gap: Level 0 (objective-gap integrand measurability)
Proof: unfold the staged objective-gap integrand and apply Mathlib closure of
  `AEStronglyMeasurable` functions under subtraction, using the constant
  reference value as the second measurable function.
Source: Mathlib measure theory strongly measurable arithmetic APIs and convex
  optimization suboptimality-gap notation
Used in: stochastic accelerated gradient descent generated expected-gap
  integrand measurability before the Theorem 4.4 domination argument
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/main_theorem/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem objectiveGap_aestronglyMeasurable
    {Ω X : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (objective : X → ℝ) (optimumValue : ℝ)
    (output : ℕ → Ω → X) (k : ℕ)
    (hobjective :
      AEStronglyMeasurable (fun ω => objective (output k ω)) μ) :
    AEStronglyMeasurable
      (objectiveGapIntegrand objective optimumValue output k) μ := by
  simpa [objectiveGapIntegrand] using
    hobjective.sub
      (aestronglyMeasurable_const :
        AEStronglyMeasurable (fun _ : Ω => optimumValue) μ)

/-- Expected objective gap of a time-indexed stochastic output process. -/
noncomputable def expectedObjectiveGap
    {Ω X : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (objective : X → ℝ) (optimumValue : ℝ)
    (output : ℕ → Ω → X) (k : ℕ) : ℝ :=
  expectation μ (objectiveGapIntegrand objective optimumValue output k)

/-- The expected objective gap unfolds to the Bochner integral of the pointwise
objective gap. -/
@[simp]
theorem expectedObjectiveGap_def
    {Ω X : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (objective : X → ℝ) (optimumValue : ℝ)
    (output : ℕ → Ω → X) (k : ℕ) :
    expectedObjectiveGap μ objective optimumValue output k =
      ∫ ω, objective (output k ω) - optimumValue ∂μ := by
  rfl

/-- Composite first-order model with a simple term and Bregman-like
correction. -/
noncomputable def compositeLinearizedModel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (gradF : E → E) (h : E → ℝ) (mu : ℝ) (V : E → E → ℝ)
    (y x : E) : ℝ :=
  f y + ⟪gradF y, x - y⟫_ℝ + h x + mu * V y x

/-- The composite linearized model unfolds to its first-order formula. -/
@[simp]
theorem compositeLinearizedModel_def
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (gradF : E → E) (h : E → ℝ) (mu : ℝ) (V : E → E → ℝ)
    (y x : E) :
    compositeLinearizedModel f gradF h mu V y x =
      f y + ⟪gradF y, x - y⟫_ℝ + h x + mu * V y x := by
  rfl

/-- A constrained objective minimum lower-bounds every feasible ambient
objective value. -/
theorem objectiveMinimumValue_le_of_mem
    {E R : Type*} [Preorder R] {X : Set E} (f : E → R)
    (minimum : ObjectiveMinimum (fun x : {x : E // x ∈ X} => f x.1))
    {x : E} (hx : x ∈ X) :
    objectiveMinimumValue (fun x : {x : E // x ∈ X} => f x.1) minimum ≤ f x := by
  exact objectiveMinimumValue_le (fun x : {x : E // x ∈ X} => f x.1) minimum ⟨x, hx⟩

/-- Strong measurability of an ambient objective composed with a measurable
output known to remain in a feasible carrier. -/
theorem carrierObjective_comp_aestronglyMeasurable
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) {X : Set E}
    (objective : E → ℝ) (carrierObjective : {x : E // x ∈ X} → ℝ)
    (output : Ω → E)
    (hcarrier_measurable : Measurable carrierObjective)
    (houtput_measurable : Measurable output)
    (houtput_mem : ∀ ω, output ω ∈ X)
    (hobjective_eq : ∀ x hx, objective x = carrierObjective ⟨x, hx⟩) :
    AEStronglyMeasurable (fun ω => objective (output ω)) μ := by
  let outputCarrier : Ω → {x : E // x ∈ X} := fun ω => ⟨output ω, houtput_mem ω⟩
  have houtputCarrier_measurable : Measurable outputCarrier := by
    simpa [outputCarrier] using houtput_measurable.subtype_mk
  have hcomp : Measurable (fun ω => carrierObjective (outputCarrier ω)) :=
    hcarrier_measurable.comp houtputCarrier_measurable
  have hpointwise :
      (fun ω => objective (output ω)) =
        fun ω => carrierObjective (outputCarrier ω) := by
    funext ω
    exact hobjective_eq (output ω) (houtput_mem ω)
  rw [hpointwise]
  exact hcomp.aestronglyMeasurable

end SOptLib

namespace SOptLib

/-- Ambient feasible objective induced by certified stochastic objective expectations.

Given a stochastic objective kernel `F` and a certified expectation value at
each feasible point, this names the zero extension of the resulting feasible
objective from the carrier subtype to the ambient decision space.

Layer: Model | Concept: Objective
Proof: (definitional construction; totalize the certified feasible objective
  value from the carrier subtype to the ambient decision space)
Source: Mathlib subtype and set totalization APIs together with SOptLib
  certified expectation-value models
Used in: stochastic block mirror descent convexity and subgradient assumptions
  stated over an ambient objective built from feasible expected losses
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/setup/problem
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
noncomputable def feasibleObjectiveAmbient
    {Ω X : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : X → Ω → ℝ) (carrier : Set X)
    (objectiveExpectation :
      ∀ x, x ∈ carrier → ExpectationValue μ (fun ω => F x ω)) :
    X → ℝ :=
  totalizeOn carrier (fun x : {x : X // x ∈ carrier} =>
    (objectiveExpectation x.1 x.2).val)

/-- The ambient feasible objective is the certified carrier objective totalized to the
ambient space. -/
@[simp]
theorem feasibleObjectiveAmbient_def
    {Ω X : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : X → Ω → ℝ) (carrier : Set X)
    (objectiveExpectation :
      ∀ x, x ∈ carrier → ExpectationValue μ (fun ω => F x ω)) :
    feasibleObjectiveAmbient μ F carrier objectiveExpectation =
      totalizeOn carrier (fun x : {x : X // x ∈ carrier} =>
        (objectiveExpectation x.1 x.2).val) := rfl

/-- The ambient feasible objective agrees with the certified feasible objective on the carrier.

At a feasible point, the zero-extension branch is not used, so the ambient
objective reduces to the value stored in the corresponding expectation
certificate.

Layer: Model | Gap: Level 0 (ambient feasible objective carrier restriction)
Proof: unfold the ambient objective through `totalizeOn` and use the carrier
  membership witness to select the feasible subtype branch.
Source: Mathlib subtype coercions and SOptLib carrier totalization APIs
Used in: stochastic block mirror descent transport from ambient convexity and
  subgradient statements to feasible expected-loss values
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/setup/problem
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
@[simp]
theorem feasibleObjectiveAmbient_of_mem
    {Ω X : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : X → Ω → ℝ) (carrier : Set X)
    (objectiveExpectation :
      ∀ x, x ∈ carrier → ExpectationValue μ (fun ω => F x ω))
    {x : X} (hx : x ∈ carrier) :
    feasibleObjectiveAmbient μ F carrier objectiveExpectation x =
      (objectiveExpectation x hx).val := by
  exact totalizeOn_of_mem carrier
    (fun x : {x : X // x ∈ carrier} => (objectiveExpectation x.1 x.2).val) hx

/-- On the carrier, the ambient feasible objective is the certified stochastic
objective expectation.

Layer: Model | Gap: Level 0 (ambient feasible objective expectation value)
Proof: combine the carrier restriction of `feasibleObjectiveAmbient` with the
  expectation equality stored in the certified expectation value.
Source: Mathlib subtype coercions and SOptLib certified expectation-value APIs
Used in: stochastic block mirror descent transport from ambient objective values
  to expected stochastic losses
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/setup/problem
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem feasibleObjectiveAmbient_eq_expectation_of_mem
    {Ω X : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : X → Ω → ℝ) (carrier : Set X)
    (objectiveExpectation :
      ∀ x, x ∈ carrier → ExpectationValue μ (fun ω => F x ω))
    {x : X} (hx : x ∈ carrier) :
    feasibleObjectiveAmbient μ F carrier objectiveExpectation x =
      expectation μ (fun ω => F x ω) := by
  rw [feasibleObjectiveAmbient_of_mem μ F carrier objectiveExpectation hx]
  exact (objectiveExpectation x hx).property.2

/-- A proper convex lower-semicontinuous real-valued function on a carrier.

The bundle records an ambient objective together with the standard source
assumptions for a nonsmooth convex term on a feasible carrier: the carrier is
nonempty, the objective is convex on it, and it is lower-semicontinuous there.

Layer: Model | Concept: Objective
Proof: (definitional construction; bundled proper convex lower-semicontinuous
  carrier objective)
Source: Convex optimization objective models and Mathlib `ConvexOn` /
  `LowerSemicontinuousOn` APIs
Used in: stochastic accelerated primal-dual simple dual penalty setup and
  saddle-gap lower-semicontinuity
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
structure SimpleConvexFunctionOn
    (E : Type*) [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    (Y : Set E) where
  toFun : E → ℝ
  carrier_nonempty : ∃ y, y ∈ Y
  convexOn : ConvexOn ℝ Y toFun
  lowerSemicontinuousOn : LowerSemicontinuousOn toFun Y

instance SimpleConvexFunctionOn.instCoeFun
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    {Y : Set E} :
    CoeFun (SimpleConvexFunctionOn E Y) (fun _ => E → ℝ) where
  coe f := f.toFun

namespace SimpleConvexFunctionOn

variable {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
variable {Y : Set E}

/-- Properness/nonemptiness projection from a simple convex carrier objective.

Layer: Model | Gap: Level 0 (simple convex objective properness projection)
Proof: project the stored carrier nonemptiness witness from the bundled
  objective model.
Source: Mathlib set nonemptiness and convex objective APIs
Used in: stochastic accelerated primal-dual feasible dual carrier
  nonemptiness setup
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem proper (g : SimpleConvexFunctionOn E Y) : ∃ y, y ∈ Y :=
  g.carrier_nonempty

/-- Convexity projection from a simple convex carrier objective.

Layer: Model | Gap: Level 0 (simple convex objective convexity projection)
Proof: project the stored Mathlib `ConvexOn` field from the bundled objective
  model.
Source: Mathlib convex-analysis APIs for `ConvexOn`
Used in: stochastic accelerated primal-dual saddle-gap and prox-objective
  convexity steps for the simple dual penalty
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem convex (g : SimpleConvexFunctionOn E Y) : ConvexOn ℝ Y g :=
  g.convexOn

/-- Lower-semicontinuity projection from a simple convex carrier objective.

Layer: Model | Gap: Level 0 (simple convex objective lower-semicontinuity projection)
Proof: project the stored Mathlib `LowerSemicontinuousOn` field from the
  bundled objective model.
Source: Mathlib semicontinuity APIs for `LowerSemicontinuousOn`
Used in: stochastic accelerated primal-dual saddle-gap lower-semicontinuity and
  compact argmin setup for the simple dual penalty
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem lsc (g : SimpleConvexFunctionOn E Y) : LowerSemicontinuousOn g Y :=
  g.lowerSemicontinuousOn

end SimpleConvexFunctionOn

/-- A source-facing smooth convex objective with a selected gradient on a carrier.

The bundle records an ambient objective, a source gradient map, convexity on the
feasible carrier, pointwise gradient witnesses on that carrier, and the usual
quadratic smoothness upper bound.

Layer: Model | Concept: Objective
Proof: (definitional construction; bundled smooth convex objective with a
  source-selected gradient and quadratic upper-bound certificate)
Source: Mathlib convex analysis and `HasGradientAt` calculus APIs
Used in: stochastic accelerated primal-dual smooth primal-gradient oracle target
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/0/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
structure SmoothConvexFunction
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (X : Set E) (L : ℝ) where
  toFun : E → ℝ
  grad : E → E
  convexOn : ConvexOn ℝ X toFun
  gradient_at : ∀ x, x ∈ X → HasGradientAt toFun (grad x) x
  smooth_upper_bound :
    ∀ x, x ∈ X → ∀ u, u ∈ X →
      toFun u - toFun x - ⟪grad x, u - x⟫_ℝ ≤ (L / 2) * ‖u - x‖ ^ 2

/-- The selected gradient of a source-facing smooth convex objective.

`smoothConvexFunctionGradient f x` names the gradient map stored with the
smooth convex objective bundle, so stochastic-oracle targets can refer to the
mathematical source gradient rather than an unfolded structure field.

Layer: Model | Concept: Objective
Proof: (definitional construction; selected gradient projection from a bundled
  smooth convex objective)
Source: Mathlib gradient calculus naming conventions for selected gradients
Used in: stochastic accelerated primal-dual smooth primal-gradient oracle target
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/0/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
noncomputable def smoothConvexFunctionGradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {X : Set E} {L : ℝ} (f : SmoothConvexFunction E X L) (x : E) : E :=
  f.grad x

/-- The selected smooth-convex gradient unfolds to the stored gradient map.

Layer: Model | Gap: Level 0 (smooth convex gradient selector unfolding)
Proof: by rfl after unfolding `smoothConvexFunctionGradient`.
Source: Mathlib structure projection and simplification APIs
Used in: stochastic accelerated primal-dual smooth primal-gradient oracle target
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/0/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
@[simp]
theorem smoothConvexFunctionGradient_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {X : Set E} {L : ℝ} (f : SmoothConvexFunction E X L) (x : E) :
    smoothConvexFunctionGradient f x = f.grad x := by
  rfl

/-- The selected smooth-convex gradient is a genuine gradient on the carrier.

Layer: Model | Gap: Level 0 (smooth convex selected-gradient certificate)
Proof: specialize the pointwise gradient witness stored in the smooth convex
  objective bundle and normalize the selected-gradient name.
Source: Mathlib `HasGradientAt` calculus API
Used in: stochastic accelerated primal-dual source-gradient well-definedness
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/0/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem smoothConvexFunctionGradient_hasGradientAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {X : Set E} {L : ℝ} (f : SmoothConvexFunction E X L)
    (x : E) (hx : x ∈ X) :
    HasGradientAt f.toFun (smoothConvexFunctionGradient f x) x := by
  simpa [smoothConvexFunctionGradient] using f.gradient_at x hx

/-- The smooth convex objective satisfies its quadratic upper bound with the
selected gradient name.

Layer: Model | Gap: Level 0 (smooth convex quadratic upper-bound projection)
Proof: specialize the smoothness certificate stored in the smooth convex
  objective bundle and rewrite the selected-gradient name.
Source: Mathlib convex smooth-objective notation and inner-product APIs
Used in: stochastic accelerated primal-dual smoothness inequality before
  primal-dual descent algebra
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/0/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem smoothConvexFunctionGradient_smooth_upper_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {X : Set E} {L : ℝ} (f : SmoothConvexFunction E X L)
    (x : E) (hx : x ∈ X) (u : E) (hu : u ∈ X) :
    f.toFun u - f.toFun x - ⟪smoothConvexFunctionGradient f x, u - x⟫_ℝ ≤
      (L / 2) * ‖u - x‖ ^ 2 := by
  simpa [smoothConvexFunctionGradient] using f.smooth_upper_bound x hx u hu

namespace SmoothConvexFunction

/-- A smooth convex objective is differentiable at every carrier point.

For a source-facing `SmoothConvexFunction`, the stored selected-gradient
certificate gives ambient differentiability at each feasible carrier point.

Layer: Model | Gap: Level 0 (smooth convex pointwise differentiability)
Proof: specialize the selected-gradient certificate stored in the smooth convex
  objective bundle, then use Mathlib's `HasGradientAt` to `DifferentiableAt`
  conversion through the associated Frechet derivative.
Source: Mathlib `HasGradientAt`, Frechet derivative, and differentiability APIs
Used in: stochastic accelerated primal-dual continuity of the smooth primal
  objective on feasible carrier points
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/0/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem differentiableAt_on
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {X : Set E} {L : ℝ} (f : SmoothConvexFunction E X L)
    (x : E) (hx : x ∈ X) :
    DifferentiableAt ℝ f.toFun x := by
  exact (smoothConvexFunctionGradient_hasGradientAt f x hx).hasFDerivAt.differentiableAt

end SmoothConvexFunction

/-- Saddle/Lagrangian objective with a primal term, bilinear coupling, and dual penalty.

For a primal decision `x` and dual decision `y`, this names the standard
convex-concave value `hatf x + ⟪Aeval x, y⟫ - hatg y`.

Layer: Model | Concept: Objective
Proof: (definitional construction; primal objective plus Hilbert bilinear
  coupling minus dual objective)
Source: convex-concave saddle-point and Lagrangian objective models over real
  Hilbert spaces
Used in: stochastic accelerated primal-dual primal maximizer and saddle-gap
  definitions for the bilinear constrained model
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
noncomputable def saddleObjective
    {X Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (hatf : X → ℝ) (Aeval : X → Y) (hatg : Y → ℝ) (x : X) (y : Y) : ℝ :=
  hatf x + ⟪Aeval x, y⟫_ℝ - hatg y

/-- The saddle objective unfolds to primal value plus bilinear coupling minus dual penalty.

Layer: Model | Gap: Level 0 (saddle objective unfolding)
Proof: by rfl after unfolding `saddleObjective`.
Source: convex-concave saddle-point and Lagrangian objective models over real
  Hilbert spaces
Used in: stochastic accelerated primal-dual normalization of the Eq. (4.4.1)
  saddle objective at primal and dual feasible points
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
@[simp] theorem saddleObjective_def
    {X Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (hatf : X → ℝ) (Aeval : X → Y) (hatg : Y → ℝ) (x : X) (y : Y) :
    saddleObjective hatf Aeval hatg x y =
      hatf x + ⟪Aeval x, y⟫_ℝ - hatg y := by
  rfl

/-- Objective value obtained by evaluating a saddle kernel at a selected maximizer.

For a saddle or minimax kernel `L`, this names the profiled objective
`x ↦ L x (argmax x)` after a maximizer selector has been chosen.

Layer: Model | Concept: Objective
Proof: (definitional construction; selected-maximizer value of a two-argument
  real objective kernel)
Source: minimax and convex-concave saddle-point objective models over ordered
  real objective values
Used in: stochastic accelerated primal-dual primal objective definition after
  selecting a dual maximizer
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/setup/problem/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
def maximizedSaddleObjective
    {X Y : Type*} (L : X → Y → ℝ) (argmax : X → Y) (x : X) : ℝ :=
  L x (argmax x)

/-- The maximized saddle objective unfolds to the selected maximizer value.

Layer: Model | Gap: Level 0 (maximized saddle objective unfolding)
Proof: by rfl after unfolding `maximizedSaddleObjective`.
Source: minimax and convex-concave saddle-point objective value functions
Used in: stochastic accelerated primal-dual primal objective normalization
  after choosing a dual maximizer
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/setup/problem/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
@[simp] theorem maximizedSaddleObjective_def
    {X Y : Type*} (L : X → Y → ℝ) (argmax : X → Y) (x : X) :
    maximizedSaddleObjective L argmax x = L x (argmax x) := by
  rfl

/-- A pointwise maximizer certificate bounds every candidate by the maximized
saddle objective value.

Layer: Model | Gap: Level 0 (selected maximizer value upper-bound bridge)
Proof: fold the selected value through `maximizedSaddleObjective` and apply the
  supplied pointwise maximizer certificate.
Source: order-theoretic maximum certificates for real-valued minimax objectives
Used in: stochastic primal-dual saddle objective comparisons after replacing a
  raw selected maximizer value by the named primal/profile objective
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/setup/problem/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem le_maximizedSaddleObjective_of_forall_le_argmax
    {X Y : Type*} (L : X → Y → ℝ) (argmax : X → Y) {x : X}
    (hmax : ∀ y : Y, L x y ≤ L x (argmax x)) (y : Y) :
    L x y ≤ maximizedSaddleObjective L argmax x := by
  simpa [maximizedSaddleObjective] using hmax y

/-- An upper-semicontinuous objective attains a maximum on a carrier whose
Bregman radius is bounded at one base point.

The conclusion returns an ambient feasible point and a carrier-wide maximality
certificate, matching optimization proofs that later quantify over arbitrary
feasible comparison points.

Layer: Model | Gap: Level 1 (Bregman-bounded compact maximizer)
Proof: turn the closed Bregman-radius-bounded carrier into a compact set with
  the staged compactness lemma, then apply Mathlib's upper-semicontinuous
  extreme-value theorem and repackage its `IsMaxOn` certificate.
Source: Mathlib proper metric compactness and upper-semicontinuous
  extreme-value APIs
Used in: stochastic accelerated primal-dual saddle-section maximizer selection
  over a bounded Bregman feasible carrier
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/7
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem exists_isMaxOn_of_bregman_bounded_upperSemicontinuousOn
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (Y : Set E) (F : E → ℝ) (y0 : E) (D : ℝ) (V : E → E → ℝ)
    (hY_closed : IsClosed Y) (hY_nonempty : Y.Nonempty)
    (hV_lower : ∀ y, y ∈ Y → (1 / 2 : ℝ) * ‖y - y0‖ ^ 2 ≤ V y y0)
    (hV_upper : ∀ y, y ∈ Y → V y y0 ≤ D ^ 2)
    (husc : UpperSemicontinuousOn F Y) :
    ∃ y, y ∈ Y ∧ ∀ v, v ∈ Y → F v ≤ F y := by
  have hY_compact : IsCompact Y :=
    isCompact_of_closed_of_bregman_half_sq_le_bounded_at_base
      Y y0 V D hY_closed hV_lower hV_upper
  obtain ⟨y, hy, hmax⟩ :=
    UpperSemicontinuousOn.exists_isMaxOn hY_nonempty hY_compact husc
  exact ⟨y, hy, fun v hv => hmax hv⟩

/-- An upper-semicontinuous objective attains a maximum on a product carrier
whose two factors are Bregman-radius bounded.

The witness is returned as a point of the feasible-product subtype, matching
the usual optimization use where later arguments quantify over feasible
comparison points rather than ambient pairs with separate membership proofs.

Layer: Model | Gap: Level 1 (Bregman-bounded product compact maximizer)
Proof: turn each closed Bregman-radius-bounded carrier into a compact set,
  take the compact product, and apply Mathlib's upper-semicontinuous extreme
  value theorem before repackaging the witness as a subtype.
Source: Mathlib proper metric compactness, product compactness, and
  upper-semicontinuous extreme-value APIs
Used in: stochastic accelerated primal-dual saddle-gap maximizer selection over
  bounded Bregman product feasible sets
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/7
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem exists_isMaxOn_product_of_bregman_bounded_upperSemicontinuousOn
    {XSpace YSpace : Type*}
    [NormedAddCommGroup XSpace] [ProperSpace XSpace]
    [NormedAddCommGroup YSpace] [ProperSpace YSpace]
    (X : Set XSpace) (Y : Set YSpace) (q : XSpace × YSpace → ℝ)
    (x0 : XSpace) (y0 : YSpace) (DX DY : ℝ)
    (VX : XSpace → XSpace → ℝ) (VY : YSpace → YSpace → ℝ)
    (hX_closed : IsClosed X) (hY_closed : IsClosed Y)
    (hx0_mem : x0 ∈ X) (hy0_mem : y0 ∈ Y)
    (hVX_lower : ∀ x, x ∈ X → (1 / 2 : ℝ) * ‖x - x0‖ ^ 2 ≤ VX x x0)
    (hVX_upper : ∀ x, x ∈ X → VX x x0 ≤ DX ^ 2)
    (hVY_lower : ∀ y, y ∈ Y → (1 / 2 : ℝ) * ‖y - y0‖ ^ 2 ≤ VY y y0)
    (hVY_upper : ∀ y, y ∈ Y → VY y y0 ≤ DY ^ 2)
    (husc : UpperSemicontinuousOn q (X ×ˢ Y)) :
    ∃ z : {z : XSpace × YSpace // z ∈ X ×ˢ Y},
      ∀ u : {u : XSpace × YSpace // u ∈ X ×ˢ Y},
        q u.1 ≤ q z.1 := by
  classical
  have hX_compact : IsCompact X :=
    isCompact_of_closed_of_bregman_half_sq_le_bounded_at_base
      X x0 VX DX hX_closed hVX_lower hVX_upper
  have hY_compact : IsCompact Y :=
    isCompact_of_closed_of_bregman_half_sq_le_bounded_at_base
      Y y0 VY DY hY_closed hVY_lower hVY_upper
  have hZ_compact : IsCompact (X ×ˢ Y) :=
    hX_compact.prod hY_compact
  have hZ_nonempty : (X ×ˢ Y).Nonempty :=
    ⟨(x0, y0), ⟨hx0_mem, hy0_mem⟩⟩
  obtain ⟨z, hz, hmax⟩ :=
    UpperSemicontinuousOn.exists_isMaxOn hZ_nonempty hZ_compact husc
  refine ⟨⟨z, hz⟩, ?_⟩
  intro u
  exact hmax u.2

end SOptLib
