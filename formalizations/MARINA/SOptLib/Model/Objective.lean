import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Order.Filter.Extr
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic
import SOptLib.Model.Carrier
import SOptLib.Model.Selection
import Mathlib.Analysis.Calculus.FDeriv.Pi
import SOptLib.Model.Norms

open MeasureTheory
open ProbabilityTheory
open scoped InnerProductSpace
open scoped Gradient

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

/-- The total gradient of a finite-uniform average is the finite-uniform average
of component gradients.

If every component objective `F i` has gradient `gradF i x` at the point `x`,
then Mathlib's total gradient selector for the named finite-uniform average
objective returns the named finite-uniform average of those component
gradients.

Layer: Model | Gap: Level 1 (finite-uniform average gradient selector)
Proof: apply the existing finite-average `HasGradientAt` theorem, rewrite the
  normalized finite-sum formula through `finiteUniformAverage`, and use
  `HasGradientAt.gradient` to identify Mathlib's total gradient selector.
Source: SOptLib finite-average objective calculus and Mathlib Hilbert-space
  gradient selector uniqueness
Used in: random primal-dual gradient finite-sum objective gradient
  identification before constructing scaled component-gradient dual points
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem gradient_finiteUniformAverage_eq_finiteUniformAverage_gradient
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (F : ι → E → ℝ) (gradF : ι → E → E) (x : E)
    (hF : ∀ i : ι, HasGradientAt (F i) (gradF i x) x) :
    ∇ (finiteUniformAverage F) x =
      finiteUniformAverage (fun i : ι => gradF i x) := by
  classical
  have hAvgRaw := finiteAverageObjective_hasGradientAt F gradF x hF
  have hAvg :
      HasGradientAt (finiteUniformAverage F)
        (finiteUniformAverage (fun i : ι => gradF i x)) x := by
    rw [show finiteUniformAverage F =
        (fun z : E => (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ (fun i : ι => F i z)) by
      funext z
      simp [finiteUniformAverage]]
    simpa [finiteUniformAverage] using hAvgRaw
  exact hAvg.gradient

/-- Finite-family component smoothness with selected gradients and real constants.

This predicate records that every component objective has the selected gradient
at every point, that every component smoothness constant is nonnegative, and
that the selected component gradients satisfy the corresponding global
Lipschitz-gradient bound.

Layer: Model | Concept: Objective
Proof: (definitional construction; finite-family selected-gradient smoothness predicate)
Source: smooth finite-sum objective models and Mathlib Hilbert-space gradient APIs
Used in: random primal-dual gradient finite-sum component-gradient assumptions
  before finite-average gradient identification and scaled component-gradient
  dual constructions
Book citation: book/FOML/RandomPrimalDualGradient.json#/assumptions/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
def FiniteFamilyGradientSmoothness
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (F : ι → E → ℝ) (gradF : ι → E → E) (Lcomp : ι → ℝ) : Prop :=
  (∀ i : ι, ∀ x : E, HasGradientAt (F i) (gradF i x) x) ∧
    (∀ i : ι, 0 ≤ Lcomp i) ∧
      ∀ i : ι, ∀ x₁ x₂ : E,
        ‖gradF i x₁ - gradF i x₂‖ ≤ Lcomp i * ‖x₁ - x₂‖

@[simp] theorem FiniteFamilyGradientSmoothness_def
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (F : ι → E → ℝ) (gradF : ι → E → E) (Lcomp : ι → ℝ) :
    FiniteFamilyGradientSmoothness F gradF Lcomp ↔
      (∀ i : ι, ∀ x : E, HasGradientAt (F i) (gradF i x) x) ∧
        (∀ i : ι, 0 ≤ Lcomp i) ∧
          ∀ i : ι, ∀ x₁ x₂ : E,
            ‖gradF i x₁ - gradF i x₂‖ ≤ Lcomp i * ‖x₁ - x₂‖ :=
  Iff.rfl

namespace FiniteFamilyGradientSmoothness

/-- The selected component gradient realizes the component derivative.

Layer: Model | Gap: Level 0 (finite-family smoothness gradient projection)
Proof: unfold the finite-family smoothness predicate and take the first
  conjunct.
Source: Mathlib propositional conjunction APIs and Hilbert-space gradient
  predicates
Used in: finite-sum objective gradient identification from component
  differentiability assumptions
Book citation: book/FOML/RandomPrimalDualGradient.json#/assumptions/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem hasGradientAt
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {F : ι → E → ℝ} {gradF : ι → E → E} {Lcomp : ι → ℝ}
    (h : FiniteFamilyGradientSmoothness F gradF Lcomp) (i : ι) (x : E) :
    HasGradientAt (F i) (gradF i x) x :=
  h.1 i x

/-- Component smoothness constants in a finite-family smoothness predicate are
nonnegative.

Layer: Model | Gap: Level 0 (finite-family smoothness constant projection)
Proof: unfold the finite-family smoothness predicate and take the first part of
  the second conjunct.
Source: Mathlib propositional conjunction APIs for bundled assumptions
Used in: finite-sum smoothness constant normalization and importance-sampling
  probability construction
Book citation: book/FOML/RandomPrimalDualGradient.json#/assumptions/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem nonneg
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {F : ι → E → ℝ} {gradF : ι → E → E} {Lcomp : ι → ℝ}
    (h : FiniteFamilyGradientSmoothness F gradF Lcomp) (i : ι) :
    0 ≤ Lcomp i :=
  h.2.1 i

/-- The selected component gradients satisfy their component Lipschitz bounds.

Layer: Model | Gap: Level 0 (finite-family smoothness Lipschitz projection)
Proof: unfold the finite-family smoothness predicate and take the second part
  of the second conjunct.
Source: smooth finite-sum objective assumptions and Mathlib normed-group
  distance notation
Used in: finite-average gradient Lipschitz transfer and finite-sum smooth
  descent estimates
Book citation: book/FOML/RandomPrimalDualGradient.json#/assumptions/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem lipschitz
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {F : ι → E → ℝ} {gradF : ι → E → E} {Lcomp : ι → ℝ}
    (h : FiniteFamilyGradientSmoothness F gradF Lcomp)
    (i : ι) (x₁ x₂ : E) :
    ‖gradF i x₁ - gradF i x₂‖ ≤ Lcomp i * ‖x₁ - x₂‖ :=
  h.2.2 i x₁ x₂

end FiniteFamilyGradientSmoothness

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

/-- Gradient selector for an objective plus a squared-distance quadratic regularizer
on a feasible carrier.

For a carrier gradient selector `grad`, regularization weight `μ`, center `z`,
and feasible point `x`, this names the vector `grad x + (2 * μ) • (x - z)`.

Layer: Model | Concept: Objective gradient
Proof: (definitional construction; carrier gradient plus the squared-distance
  regularizer gradient)
Source: Mathlib real normed-module algebra and Hilbert-space squared-distance
  gradient calculus
Used in: randomized accelerated proximal-point component subproblem gradient
  evaluation and memory refresh
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
noncomputable def quadraticRegularizedGradientOn
    {E : Type*} [NormedAddCommGroup E] [Module ℝ E]
    {X : Set E} (grad : {x : E // x ∈ X} → E) (μ : ℝ) (z : E)
    (x : {x : E // x ∈ X}) : E :=
  grad x + (2 * μ) • (x.1 - z)

/-- The quadratic-regularized carrier gradient unfolds to the base carrier
gradient plus the squared-distance regularizer gradient.

Layer: Model | Gap: Level 0 (quadratic-regularized gradient unfolding)
Proof: by rfl after unfolding `quadraticRegularizedGradientOn`.
Source: Mathlib real normed-module algebra and Hilbert-space squared-distance
  gradient calculus
Used in: randomized accelerated proximal-point component subproblem gradient
  evaluation and memory refresh
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
@[simp] theorem quadraticRegularizedGradientOn_def
    {E : Type*} [NormedAddCommGroup E] [Module ℝ E]
    {X : Set E} (grad : {x : E // x ∈ X} → E) (μ : ℝ) (z : E)
    (x : {x : E // x ∈ X}) :
    quadraticRegularizedGradientOn grad μ z x =
      grad x + (2 * μ) • (x.1 - z) :=
  rfl

/-- Two-point difference formula for the quadratic-regularized carrier gradient.

This packages the algebraic cancellation of the shared center `z`, leaving the
base carrier-gradient difference plus the quadratic regularizer's linear
two-point contribution.

Layer: Model | Gap: Level 1 (quadratic-regularized gradient difference)
Proof: unfold the named gradient and normalize additive module algebra.
Source: Mathlib real normed-module algebra and Hilbert-space squared-distance
  gradient calculus
Used in: randomized accelerated proximal-point component-gradient Lipschitz
  estimates and source-domain gradient comparisons
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem quadraticRegularizedGradientOn_sub
    {E : Type*} [NormedAddCommGroup E] [Module ℝ E]
    {X : Set E} (grad : {x : E // x ∈ X} → E) (μ : ℝ) (z : E)
    (x y : {x : E // x ∈ X}) :
    quadraticRegularizedGradientOn grad μ z x -
      quadraticRegularizedGradientOn grad μ z y =
        (grad x - grad y) + (2 * μ) • (x.1 - y.1) := by
  simp only [quadraticRegularizedGradientOn_def]
  have hreg :
      (2 * μ) • (x.1 - z) - (2 * μ) • (y.1 - z) =
        (2 * μ) • (x.1 - y.1) := by
    rw [← smul_sub]
    congr 1
    abel
  calc
    grad x + (2 * μ) • (x.1 - z) - (grad y + (2 * μ) • (y.1 - z))
        =
      (grad x - grad y) +
        ((2 * μ) • (x.1 - z) - (2 * μ) • (y.1 - z)) := by
        abel
    _ = (grad x - grad y) + (2 * μ) • (x.1 - y.1) := by
        rw [hreg]

/-- Objective plus a squared-distance quadratic regularizer on a feasible carrier.

For a carrier objective `f`, regularization weight `μ`, center `z`, and feasible
point `x`, this names the value `f x + μ * ‖x - z‖ ^ 2`.

Layer: Model | Concept: Objective
Proof: (definitional construction; carrier objective plus centered
  squared-distance regularizer)
Source: Mathlib normed additive group norm algebra and proximal-point objective
  formulas
Used in: randomized accelerated proximal-point component subproblem objective
  construction
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
noncomputable def quadraticRegularizedObjectiveOn
    {E : Type*} [NormedAddCommGroup E]
    {X : Set E} (f : {x : E // x ∈ X} → ℝ) (μ : ℝ) (z : E)
    (x : {x : E // x ∈ X}) : ℝ :=
  f x + μ * ‖x.1 - z‖ ^ 2

/-- The quadratic-regularized carrier objective unfolds to the base objective
plus the squared-distance regularizer.

Layer: Model | Gap: Level 0 (quadratic-regularized objective unfolding)
Proof: by rfl after unfolding `quadraticRegularizedObjectiveOn`.
Source: Mathlib normed additive group norm algebra and proximal-point objective
  formulas
Used in: randomized accelerated proximal-point component subproblem objective
  construction
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
@[simp] theorem quadraticRegularizedObjectiveOn_def
    {E : Type*} [NormedAddCommGroup E]
    {X : Set E} (f : {x : E // x ∈ X} → ℝ) (μ : ℝ) (z : E)
    (x : {x : E // x ∈ X}) :
    quadraticRegularizedObjectiveOn f μ z x = f x + μ * ‖x.1 - z‖ ^ 2 :=
  rfl

/-- Difference formula for the quadratic-regularized carrier objective.

This separates the base-objective difference from the change in the centered
squared-distance regularizer.

Layer: Model | Gap: Level 0 (quadratic-regularized objective difference)
Proof: by unfolding `quadraticRegularizedObjectiveOn` and normalizing the ring
  expression.
Source: Mathlib normed additive group norm algebra and proximal-point objective
  formulas
Used in: randomized accelerated proximal-point component subproblem objective
  construction
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem quadraticRegularizedObjectiveOn_sub
    {E : Type*} [NormedAddCommGroup E]
    {X : Set E} (f : {x : E // x ∈ X} → ℝ) (μ : ℝ) (z : E)
    (x y : {x : E // x ∈ X}) :
    quadraticRegularizedObjectiveOn f μ z x -
        quadraticRegularizedObjectiveOn f μ z y =
      (f x - f y) + μ * (‖x.1 - z‖ ^ 2 - ‖y.1 - z‖ ^ 2) := by
  simp only [quadraticRegularizedObjectiveOn_def]
  ring

/-- Shifting the center of a quadratic-regularized carrier gradient adds the
corresponding affine correction.

For the regularizer gradient `x ↦ (2 * μ) • (x - z)`, moving the center from
`zOld` to `zNew` changes the gradient by `(2 * μ) • (zOld - zNew)`, independently
of the base carrier gradient.

Layer: Model | Gap: Level 1 (quadratic-regularized gradient center shift)
Proof: unfold `quadraticRegularizedGradientOn`; the base gradient cancels and
  real module algebra normalizes the old-center and new-center terms.
Source: Mathlib real normed-module algebra for affine translations of quadratic
  regularizer gradients
Used in: randomized accelerated proximal-point memory refresh between
  consecutive quadratic subproblem centers
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem quadraticRegularizedGradient_shift_center
    {E : Type*} [NormedAddCommGroup E] [Module ℝ E]
    {X : Set E} (grad : {x : E // x ∈ X} → E) (μ : ℝ)
    (zOld zNew : E) (x : {x : E // x ∈ X}) :
    quadraticRegularizedGradientOn grad μ zOld x +
        (2 * μ) • (zOld - zNew) =
      quadraticRegularizedGradientOn grad μ zNew x := by
  simp only [quadraticRegularizedGradientOn_def]
  module

/-- Normalized finite-sum objective with an additive regularizer.

For a finite component family `psi` and regularizer `regularizer`,
`finiteAverageRegularizedObjectiveOn psi regularizer x` is the value
`(card ι)⁻¹ * ∑ i, psi i x + regularizer x`.

Layer: Model | Concept: Objective
Proof: (definitional construction; inverse-cardinality scalar multiplying the
  component-objective sum plus a pointwise regularizer)
Source: Mathlib finite sums and real-valued objective arithmetic for finite-sum
  regularized optimization
Used in: randomized accelerated proximal-point exact finite-sum proximal
  subproblem objective construction
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
noncomputable def finiteAverageRegularizedObjectiveOn {ι X : Type*} [Fintype ι]
    (psi : ι → X → ℝ) (regularizer : X → ℝ) (x : X) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i : ι => psi i x) +
    regularizer x

/-- The finite-average regularized objective unfolds to the normalized component
sum plus the pointwise regularizer.

Layer: Model | Gap: Level 0 (finite average regularized objective unfolding)
Proof: by rfl after unfolding `finiteAverageRegularizedObjectiveOn`.
Source: Mathlib finite sums and real-valued objective arithmetic for finite-sum
  regularized optimization
Used in: randomized accelerated proximal-point exact finite-sum proximal
  subproblem objective construction
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
@[simp] theorem finiteAverageRegularizedObjectiveOn_def {ι X : Type*} [Fintype ι]
    (psi : ι → X → ℝ) (regularizer : X → ℝ) (x : X) :
    finiteAverageRegularizedObjectiveOn psi regularizer x =
      (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i : ι => psi i x) +
        regularizer x :=
  rfl

/-- The gradient of a finite-average regularized objective is the finite
average of the component gradients plus the regularizer gradient.

Layer: Model | Gap: Level 1 (finite average regularized objective gradient calculus)
Proof: combine `finiteAverageObjective_hasGradientAt` for the normalized
  finite sum with the regularizer gradient using Mathlib Fréchet derivative
  addition, then convert back to `HasGradientAt`.
Source: SOptLib finite-average objective calculus and Mathlib gradient APIs
Used in: finite-sum proximal and regularized optimization proofs that keep the
  regularized subproblem objective named while exposing its gradient -/
theorem finiteAverageRegularizedObjectiveOn_hasGradientAt
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (psi : ι → E → ℝ) (regularizer : E → ℝ)
    (gradPsi : ι → E → E) (gradRegularizer : E → E) (x : E)
    (hpsi : ∀ i : ι, HasGradientAt (psi i) (gradPsi i x) x)
    (hregularizer : HasGradientAt regularizer (gradRegularizer x) x) :
    HasGradientAt (finiteAverageRegularizedObjectiveOn psi regularizer)
      (((Fintype.card ι : ℝ)⁻¹ •
        Finset.sum Finset.univ (fun i : ι => gradPsi i x)) + gradRegularizer x) x := by
  have havg := finiteAverageObjective_hasGradientAt psi gradPsi x hpsi
  have hsum : HasFDerivAt
      (fun z : E =>
        (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i : ι => psi i z) +
          regularizer z)
      (InnerProductSpace.toDual ℝ E
        (((Fintype.card ι : ℝ)⁻¹ •
          Finset.sum Finset.univ (fun i : ι => gradPsi i x)) + gradRegularizer x)) x := by
    simpa [map_add] using havg.hasFDerivAt.add hregularizer.hasFDerivAt
  simpa [finiteAverageRegularizedObjectiveOn] using hsum.hasGradientAt

/-- First-order Taylor affine model of an objective at a base point.

`first_order_linear_model f g x y` is the value `f x + ⟪g, y - x⟫`,
the standard linearization of `f` at `x` evaluated at `y`.

Layer: Model | Concept: Objective first-order linear model
Proof: (definitional construction; objective value plus gradient inner product
  with the displacement from base point to evaluation point)
Source: first-order Taylor linearization over real inner-product spaces
Used in: stochastic conditional-gradient sliding smooth upper-model and
  convex lower-model comparisons before applying descent recurrences
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
def first_order_linear_model
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (g : E) (x y : E) : ℝ :=
  f x + ⟪g, y - x⟫_ℝ

/-- The first-order linear model unfolds to its Taylor affine formula.

Layer: Model | Gap: Level 0 (first-order linear-model formula)
Proof: by rfl after unfolding `first_order_linear_model`.
Source: first-order Taylor linearization over real inner-product spaces
Used in: stochastic conditional-gradient sliding smooth upper-model and
  convex lower-model comparisons before applying descent recurrences
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
@[simp]
theorem first_order_linear_model_def
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (g : E) (x y : E) :
    first_order_linear_model f g x y = f x + ⟪g, y - x⟫_ℝ := by
  rfl

/-- At the base point, the first-order linear model equals the objective value.

Layer: Model | Gap: Level 0 (base-point evaluation)
Proof: by simplifying the displacement `x - x`.
Source: first-order Taylor linearization over real inner-product spaces
Used in: stochastic conditional-gradient sliding model comparisons at the
  current iterate
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
@[simp]
theorem first_order_linear_model_self
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (g x : E) :
    first_order_linear_model f g x x = f x := by
  simp [first_order_linear_model]

/-- Difference of two first-order linear model evaluations with the same base.

Layer: Model | Gap: Level 0 (same-base affine difference)
Proof: expand the model and use linearity of the inner product in the second
  argument.
Source: first-order Taylor linearization over real inner-product spaces
Used in: stochastic conditional-gradient sliding comparisons between candidate
  points in the same local affine model
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem first_order_linear_model_sub
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (g x y z : E) :
    first_order_linear_model f g x y - first_order_linear_model f g x z =
      ⟪g, y - z⟫_ℝ := by
  have hsub : y - z = (y - x) - (z - x) := by
    abel
  rw [first_order_linear_model_def, first_order_linear_model_def, hsub]
  simp [inner_sub_right]

/-- A Bochner expectation is well-defined and equal to a prescribed target.

This predicate packages integrability with the displayed expectation value, so
source assumptions do not accidentally rely on the totalized fallback value of
the Bochner integral outside the integrable case.

Layer: Model | Concept: Objective
Proof: (definitional construction; paired expectation well-definedness and
  target-value equality)
Source: Mathlib measure theory Bochner integration and integrability APIs
Used in: stochastic conditional-gradient sliding stochastic-oracle unbiasedness
  and zero-mean batch-noise assumptions
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
def expectationEq
    {Ω R : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    (μ : Measure Ω) (Z : Ω → R) (target : R) : Prop :=
  expectationWellDefined μ Z ∧ expectation μ Z = target

/-- The paired expectation-equality predicate unfolds to integrability and a
Bochner-integral target equality.

Layer: Model | Gap: Level 0 (expectation equality as integrability plus integral value)
Proof: by rfl after unfolding `expectationEq`, `expectationWellDefined`, and
  `expectation`.
Source: Mathlib measure theory Bochner integral notation and integrability APIs
Used in: stochastic conditional-gradient sliding source expectation assumptions
  when extracting integrability and displayed expectation values
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
@[simp] theorem expectationEq_def
    {Ω R : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    (μ : Measure Ω) (Z : Ω → R) (target : R) :
    expectationEq μ Z target ↔ Integrable Z μ ∧ (∫ ω, Z ω ∂μ) = target := by
  rfl

/-- Build an expectation-equality predicate from integrability and the displayed
Bochner-integral value.

Layer: Model | Gap: Level 0 (constructor for expectation equality)
Proof: by the characterizing theorem for `expectationEq`.
Source: Mathlib measure theory Bochner integral notation and integrability APIs
Used in: stochastic oracle unbiasedness and zero-mean noise assumptions
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem expectationEq_of_integrable_integral_eq
    {Ω R : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    {μ : Measure Ω} {Z : Ω → R} {target : R}
    (hZ : Integrable Z μ) (h_eq : (∫ ω, Z ω ∂μ) = target) :
    expectationEq μ Z target := by
  exact (expectationEq_def μ Z target).2 ⟨hZ, h_eq⟩

/-- An expectation equality includes integrability of the random quantity.

Layer: Model | Gap: Level 0 (projection from expectation equality)
Proof: by the characterizing theorem for `expectationEq`.
Source: Mathlib measure theory Bochner integral notation and integrability APIs
Used in: stochastic oracle unbiasedness and zero-mean noise assumptions
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem expectationEq.integrable
    {Ω R : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    {μ : Measure Ω} {Z : Ω → R} {target : R}
    (h : expectationEq μ Z target) :
    Integrable Z μ :=
  ((expectationEq_def μ Z target).1 h).1

/-- An expectation equality gives the displayed Bochner-integral value.

Layer: Model | Gap: Level 0 (projection from expectation equality)
Proof: by the characterizing theorem for `expectationEq`.
Source: Mathlib measure theory Bochner integral notation and integrability APIs
Used in: stochastic oracle unbiasedness and zero-mean noise assumptions
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem expectationEq.integral_eq
    {Ω R : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    {μ : Measure Ω} {Z : Ω → R} {target : R}
    (h : expectationEq μ Z target) :
    (∫ ω, Z ω ∂μ) = target :=
  ((expectationEq_def μ Z target).1 h).2

/-- An expectation equality gives the corresponding `SOptLib.expectation`
value.

Layer: Model | Gap: Level 0 (projection from expectation equality)
Proof: by unfolding `expectation`.
Source: Mathlib measure theory Bochner integral notation and integrability APIs
Used in: stochastic oracle unbiasedness and zero-mean noise assumptions
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem expectationEq.expectation_eq
    {Ω R : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    {μ : Measure Ω} {Z : Ω → R} {target : R}
    (h : expectationEq μ Z target) :
    expectation μ Z = target := by
  simpa [expectation] using h.integral_eq

/-- A scalar Bochner expectation is well-defined and bounded above.

This predicate packages integrability with the displayed expectation inequality,
so source moment assumptions do not accidentally rely on the totalized fallback
value of the Bochner integral outside the integrable case.

Layer: Model | Concept: Objective
Proof: (definitional construction; paired expectation well-definedness and
  scalar upper-bound inequality)
Source: Mathlib measure theory Bochner integration, integrability, and ordered
  real APIs
Used in: stochastic conditional-gradient sliding oracle second-moment bounds
  and expected-gap source inequalities
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
def expectationLe
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → ℝ) (bound : ℝ) : Prop :=
  expectationWellDefined μ Z ∧ expectation μ Z ≤ bound

/-- The paired expectation-bound predicate unfolds to integrability and a
Bochner-integral upper bound.

Layer: Model | Gap: Level 0 (expectation upper bound as integrability plus integral inequality)
Proof: by rfl after unfolding `expectationLe`, `expectationWellDefined`, and
  `expectation`.
Source: Mathlib measure theory Bochner integral notation, integrability, and
  ordered real APIs
Used in: stochastic conditional-gradient sliding source variance and expected
  gap assumptions when extracting integrability and displayed expectation bounds
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
@[simp] theorem expectationLe_def
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → ℝ) (bound : ℝ) :
    expectationLe μ Z bound ↔ Integrable Z μ ∧ (∫ ω, Z ω ∂μ) ≤ bound := by
  rfl

/-- Build an expectation-bound predicate from integrability and the displayed
Bochner-integral upper bound.

Layer: Model | Gap: Level 0 (constructor for expectation upper bounds)
Proof: by the characterizing theorem for `expectationLe`.
Source: Mathlib measure theory Bochner integral notation, integrability, and
  ordered real APIs
Used in: stochastic oracle moment bounds and expected-gap source inequalities
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem expectationLe_of_integrable_integral_le
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Z : Ω → ℝ} {bound : ℝ}
    (hZ : Integrable Z μ) (h_le : (∫ ω, Z ω ∂μ) ≤ bound) :
    expectationLe μ Z bound := by
  exact (expectationLe_def μ Z bound).2 ⟨hZ, h_le⟩

/-- A finite-average objective with continuous components attains a constrained minimum on
a nonempty compact feasible set.

If every component objective is continuous on the feasible set, the normalized
finite average is continuous on the feasible set. The compact extreme-value
theorem then gives an ambient feasible minimizer.

Layer: Model | Gap: Level 1 (finite-average compact objective minimum existence)
Proof: derive `ContinuousOn` for the finite average from component continuity
  by finite sums and scaling, then apply the compact continuous-objective
  minimum theorem and unpack the feasible subtype witness.
Source: Mathlib finite-sum continuity, compactness, and extreme-value APIs
Used in: finite-sum stochastic conditional-gradient construction of the
  feasible objective optimum `fStar` from component continuity on a compact
  feasible set; algorithm callers can derive this continuity from component
  gradient assumptions when needed
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/setup/problem
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
theorem finiteAverageObjective_minimum_exists_of_isCompact_continuousOn
    {ι E : Type*} [Fintype ι] [TopologicalSpace E]
    (X : Set E) (F : ι → E → ℝ)
    (hX_compact : IsCompact X) (hX_nonempty : X.Nonempty)
    (hF_cont : ∀ i : ι, ContinuousOn (F i) X) :
    ∃ x : E, x ∈ X ∧ ∀ y : E, y ∈ X →
      finiteUniformAverage F x ≤ finiteUniformAverage F y := by
  have hcont : ContinuousOn (finiteUniformAverage F) X := by
    have hsum :
        ContinuousOn (fun x : E => Finset.sum Finset.univ (fun i : ι => F i x)) X := by
      exact continuousOn_finset_sum Finset.univ (fun i _hi => hF_cont i)
    rw [show finiteUniformAverage F =
        (fun x : E => (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ (fun i : ι => F i x)) by
      ext x
      simp [finiteUniformAverage]]
    exact hsum.const_smul ((Fintype.card ι : ℝ)⁻¹)
  rcases objectiveMinimum_exists_of_isCompact_continuousOn
      (finiteUniformAverage F)
      hX_compact hX_nonempty hcont with ⟨x, hx_min⟩
  refine ⟨x.1, x.2, ?_⟩
  intro y hy
  exact hx_min ⟨y, hy⟩

-- Generalization plan (G0):
-- concept/name: expected objective epsilon-solution at a fixed time; orig was
--   `FindsExpectedEpsilonSolutionAt`, renamed away from Algorithm 5.7 and setup fields.
-- generality used: arbitrary sample type with a measurable space, arbitrary sample
--   law, objective, reference value, output process, tolerance, and epoch; no
--   probability, convexity, smoothness, finite-dimensional, or oracle hypotheses
--   are needed to state the convergence conclusion.
-- portable call pattern: SGD, stochastic mirror descent, variance-reduced,
--   accelerated, proximal, and validation-output convergence theorems can change
--   the sample law, objective, optimum/reference value, output process, epoch, and
--   tolerance while keeping the same expected-gap epsilon-solution conclusion.
-- counterargument checked: this is a single-expression predicate over the existing
--   `SOptLib.expectedObjectiveGap`, so the wrapper risk is real; it still wins as a
--   Model concept because "expected objective epsilon-solution" is the reusable
--   convergence boundary called by corollaries and algorithm policies, not paper
--   source traceability or theorem-number bookkeeping.
-- coverage search: searched CATALOG/SOptLib for `expected objective gap`,
--   `epsilon solution`, and `FindsExpected`; SOptLib has `expectedObjectiveGap`,
--   `objectiveGapIntegrand`, and stationarity-oriented `IsEpsilonLambdaSolution`,
--   but no objective-gap epsilon-solution predicate. LeanSearch returned only
--   unrelated expectation/order and martingale facts, not this optimization concept.
-- minimal hypotheses: all already minimal; the statement only needs the measurable
--   space required by `SOptLib.expectedObjectiveGap`.

/-- A time-indexed stochastic output is an expected objective `epsilon`-solution.

The predicate records that the expected objective gap of `output s` against a
chosen reference value is at most the requested tolerance.

Layer: Model | Concept: Objective
Proof: (definitional construction; objective-gap convergence predicate over
  `SOptLib.expectedObjectiveGap`)
Source: Convex optimization expected suboptimality-gap notation and Mathlib
  measure-theory expectation primitives
Used in: variance-reduced accelerated gradient descent theorem-to-corollary
  handoff from an expected objective-gap bound to an epoch-selection policy
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
def IsExpectedObjectiveEpsilonSolutionAt
    {Ω X : Type*} [MeasurableSpace Ω]
    (sampleLaw : MeasureTheory.Measure Ω) (objective : X → ℝ)
    (referenceValue : ℝ) (output : ℕ → Ω → X)
    (epsilon : ℝ) (s : ℕ) : Prop :=
  SOptLib.expectedObjectiveGap sampleLaw objective referenceValue output s <= epsilon

/-- The expected objective epsilon-solution predicate unfolds to an expected
objective-gap upper bound.

Layer: Model | Gap: Level 0 (expected objective epsilon-solution formula)
Proof: by rfl after unfolding `IsExpectedObjectiveEpsilonSolutionAt`.
Source: Convex optimization expected suboptimality-gap notation and Mathlib
  order APIs for real-valued bounds
Used in: variance-reduced accelerated gradient descent theorem-to-corollary
  handoff from an expected objective-gap bound to an epoch-selection policy
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
@[simp]
theorem IsExpectedObjectiveEpsilonSolutionAt_def
    {Ω X : Type*} [MeasurableSpace Ω]
    (sampleLaw : MeasureTheory.Measure Ω) (objective : X → ℝ)
    (referenceValue : ℝ) (output : ℕ → Ω → X)
    (epsilon : ℝ) (s : ℕ) :
    IsExpectedObjectiveEpsilonSolutionAt sampleLaw objective referenceValue output
      epsilon s =
        (SOptLib.expectedObjectiveGap sampleLaw objective referenceValue output s <=
          epsilon) := rfl

/-- An expected objective `epsilon`-solution remains one after relaxing the
tolerance.

Layer: Model | Gap: Level 0 (expected objective epsilon-solution monotonicity)
Proof: transitivity of `≤` after unfolding the predicate.
Source: Mathlib order APIs for real-valued upper bounds
Used in: stochastic optimization corollaries that round, pad, or otherwise
  relax an expected objective-gap tolerance -/
theorem IsExpectedObjectiveEpsilonSolutionAt.mono_epsilon
    {Ω X : Type*} [MeasurableSpace Ω]
    {sampleLaw : MeasureTheory.Measure Ω} {objective : X → ℝ}
    {referenceValue : ℝ} {output : ℕ → Ω → X}
    {epsilon epsilon' : ℝ} {s : ℕ}
    (h :
      IsExpectedObjectiveEpsilonSolutionAt sampleLaw objective referenceValue output
        epsilon s)
    (hepsilon : epsilon <= epsilon') :
    IsExpectedObjectiveEpsilonSolutionAt sampleLaw objective referenceValue output
      epsilon' s := by
  exact h.trans hepsilon


-- Generalization plan (G0):
-- concept/name: expected objective-gap nonnegativity from a pointwise output
--   lower bound; orig was
--   `smooth_mu_zero_correctedCore_expected_objective_gap_nonneg`, renamed away
--   from the smooth, mu-zero, corrected-core, and setup-local process names.
-- generality used: arbitrary sample type with measurable space, arbitrary
--   measure, arbitrary decision/output type, real-valued objective, real
--   reference optimum value, output process, and time index; no probability,
--   convexity, smoothness, oracle, topology, norm, inner product, or finite
--   dimensionality is used.
-- portable call pattern: stochastic gradient, mirror descent, proximal,
--   accelerated, and variance-reduced proofs can call this after proving a
--   lower bound on the objective values reached by a random output path; the
--   measure, output process, epoch, objective, and reference value vary while
--   expected-gap nonnegativity stays the same.
-- counterargument checked: this is short after unfolding `SOptLib.expectedObjectiveGap`,
--   but it is not paper-local traceability: it packages the recurring
--   integral-nonnegativity proof step under the named expected suboptimality
--   API. SOptLib already has the pointwise `objectiveGapIntegrand_nonneg`, but
--   not the expected-gap integral consequence.
-- coverage search: searched CATALOG/SOptLib/Staging for `expectedObjectiveGap`,
--   `objectiveGapIntegrand`, `nonneg`, and `lower_bound`; relevant full hits
--   were `SOptLib.objectiveGapIntegrand`,
--   `SOptLib.objectiveGapIntegrand_nonneg`, `SOptLib.objectiveGap_aestronglyMeasurable`,
--   and `SOptLib.expectedObjectiveGap_def`. LeanSearch for integral
--   nonnegativity returned Mathlib `MeasureTheory.integral_nonneg`, which is
--   the proof primitive, not the optimization statement.
-- minimal hypotheses: algorithm-specific optimality and feasibility are
--   replaced by the pointwise scalar lower-bound hypothesis along the output
--   path, `forall omega, optimumValue <= objective (output k omega)`; no
--   integrability or probability assumption is needed for Mathlib's totalized
--   Bochner integral nonnegativity.

open MeasureTheory

/-- An expected objective gap is nonnegative when the reference value lower-bounds
the objective value along the output path.

This lifts the pointwise suboptimality inequality
`optimumValue <= objective (output k omega)` through
`SOptLib.expectedObjectiveGap` for any time-indexed stochastic output process
and any measure.

Layer: Model | Gap: Level 0 (expected objective-gap nonnegativity)
Proof: unfold `SOptLib.expectedObjectiveGap`, apply
  `MeasureTheory.integral_nonneg`, and discharge the integrand with
  `sub_nonneg` from the supplied pointwise lower bound.
Source: Mathlib Bochner integral nonnegativity and convex-optimization
  suboptimality-gap notation
Used in: variance-reduced accelerated gradient descent proof that a
  feasible stochastic output has nonnegative expected suboptimality gap
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem expectedObjectiveGap_nonneg_of_forall_lower_bound
    {Omega X : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (objective : X -> Real) (optimumValue : Real)
    (output : Nat -> Omega -> X) (k : Nat)
    (hoptimumValue_le : forall omega : Omega, optimumValue <= objective (output k omega)) :
    0 <= SOptLib.expectedObjectiveGap mu objective optimumValue output k := by
  rw [SOptLib.expectedObjectiveGap_def]
  exact
    MeasureTheory.integral_nonneg fun omega =>
      sub_nonneg.mpr (hoptimumValue_le omega)


-- Generalization plan (G0):
-- concept/name: expected objective-gap monotonicity in the reference value; orig
--   was `lemma520_correctedCore_expectedObjectiveGap_le_of_optimum_pre`, renamed
--   away from Lemma 5.20, corrected-core process, and setup-local optimizer words.
-- generality used: arbitrary sample type with measurable space, arbitrary measure,
--   objective, output process, time index, and two real reference values; no
--   probability, convexity, smoothness, oracle, topology on `X`, or finite
--   dimensionality is used.
-- portable call pattern: stochastic gradient, mirror descent, proximal, accelerated,
--   and variance-reduced proofs can call this when replacing a comparison-point
--   reference value by a lower optimum/reference value in an expected
--   suboptimality gap; the measure, objective, output process, epoch, and
--   reference constants vary while the conclusion shape is unchanged.
-- counterargument checked: this is short after unfolding `SOptLib.expectedObjectiveGap`,
--   but it is not a paper traceability wrapper: it packages the reusable
--   reference-value monotonicity proof step under the named expected-gap API.
--   Mathlib has `MeasureTheory.integral_mono`, and SOptLib has
--   `objectiveGapIntegrand_nonneg`, but neither states monotonicity of
--   `expectedObjectiveGap` under a lower reference constant.
-- coverage search: searched CATALOG/SOptLib/Staging/registry for
--   `expectedObjectiveGap`, `objectiveGapIntegrand`, `reference`, and `monotone`;
--   full hits were `SOptLib.objectiveGapIntegrand`,
--   `SOptLib.objectiveGapIntegrand_nonneg`, `SOptLib.expectedObjectiveGap`, and
--   `SOptLib.expectedObjectiveGap_def`. LeanSearch for integral monotonicity
--   returned Mathlib `MeasureTheory.integral_mono`, which is the proof primitive,
--   not the optimization statement.
-- minimal hypotheses: global optimizer structure is replaced by the pointwise
--   scalar assumption `vOpt <= v`; only integrability of the two gap integrands is
--   needed for Bochner integral monotonicity.

open MeasureTheory

/-- Expected objective gaps are monotone antitone in their reference value.

If `vOpt <= v`, then the gap measured from `v` is bounded above by the gap
measured from `vOpt`, provided both gap random variables are integrable.

Layer: Model | Gap: Level 0 (expected objective-gap reference monotonicity)
Proof: unfold `SOptLib.expectedObjectiveGap`, apply
  `MeasureTheory.integral_mono`, and use the scalar order hypothesis to compare
  the two pointwise objective-gap integrands.
Source: Mathlib Bochner integral monotonicity and convex-optimization
  suboptimality-gap notation
Used in: variance-reduced accelerated gradient descent replacement of a
  comparison-point reference objective value by the optimum objective value in
  the expected suboptimality gap
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/key_lemmas/23/proof
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem expectedObjectiveGap_le_expectedObjectiveGap_of_le_reference
    {Ω X : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (objective : X → ℝ) (output : ℕ → Ω → X) (k : ℕ)
    {v vOpt : ℝ}
    (hgap_v :
      Integrable (SOptLib.objectiveGapIntegrand objective v output k) μ)
    (hgap_vOpt :
      Integrable (SOptLib.objectiveGapIntegrand objective vOpt output k) μ)
    (hvOpt_le_v : vOpt <= v) :
    SOptLib.expectedObjectiveGap μ objective v output k <=
      SOptLib.expectedObjectiveGap μ objective vOpt output k := by
  rw [SOptLib.expectedObjectiveGap_def, SOptLib.expectedObjectiveGap_def]
  refine integral_mono ?_ ?_ ?_
  · simpa [SOptLib.objectiveGapIntegrand] using hgap_v
  · simpa [SOptLib.objectiveGapIntegrand] using hgap_vOpt
  · intro ω
    dsimp [SOptLib.objectiveGapIntegrand]
    linarith

/-- Feasible-set infimum value of a real-valued objective.

`objectiveInfimumValue X f` names the lower reference value `inf {f x | x in X}`
without asserting that the infimum is attained by an optimizer.

Layer: Model | Concept: Objective
Proof: (definitional construction; `sInf` of the objective image over the feasible set)
Source: Mathlib conditionally complete lattice infimum API for real-valued set images
Used in: nonconvex variance-reduced mirror descent objective-gap bounds with no attained optimizer
Book citation: book/FOML/NonconvexVarianceReducedMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, nonconvex variance-reduced mirror descent -/
noncomputable def objectiveInfimumValue {E : Type*} (X : Set E) (f : E → ℝ) : ℝ :=
  sInf (f '' X)

/-- The feasible objective infimum value unfolds to the infimum of the feasible
objective image.

Layer: Model | Gap: Level 0 (objective infimum value formula)
Proof: by rfl after unfolding `objectiveInfimumValue`.
Source: Mathlib conditionally complete lattice infimum API for real-valued set images
Used in: nonconvex variance-reduced mirror descent identification of the paper optimum value
Book citation: book/FOML/NonconvexVarianceReducedMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, nonconvex variance-reduced mirror descent -/
@[simp]
theorem objectiveInfimumValue_def {E : Type*} (X : Set E) (f : E → ℝ) :
    objectiveInfimumValue X f = sInf (f '' X) := by
  rfl

/-- The feasible objective infimum value lower-bounds every feasible objective
value when the feasible objective image is bounded below.

Layer: Model | Gap: Level 0 (bounded-below objective infimum lower bound)
Proof: unfold `objectiveInfimumValue` and apply Mathlib's `csInf_le` to the
  feasible objective image, using `x ∈ X` as the image-membership witness.
Source: Mathlib conditionally complete lattice infimum API for real-valued set images
Used in: nonconvex variance-reduced mirror descent nonnegativity of objective gaps along feasible iterates
Book citation: book/FOML/NonconvexVarianceReducedMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, nonconvex variance-reduced mirror descent -/
theorem objectiveInfimumValue_le {E : Type*} {X : Set E} {f : E → ℝ}
    (h_bddBelow : BddBelow (f '' X)) {x : E} (hx : x ∈ X) :
    objectiveInfimumValue X f ≤ f x := by
  rw [objectiveInfimumValue_def]
  exact csInf_le h_bddBelow ⟨x, hx, rfl⟩

end SOptLib

-- Merged from Staging/finiteAverageGradientRegularizerGap.lean
open scoped BigOperators InnerProductSpace

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: finite-average gradient regularizer gap; orig was `Q`, renamed
--   away from paper-local notation and equation numbering.
-- generality used: finite index type and real inner-product carrier; no measure,
--   convexity, smoothness, completeness, finite-dimensionality, or oracle
--   hypotheses are needed for the definitional comparison functional.
-- portable call pattern: finite-sum strongly-convex composite methods call this
--   at Jensen and objective-gap conversion steps while changing component
--   gradients, comparison points, the regularizer, and the scalar multiplier.
-- counterargument checked: the body is a formula, but it is a named two-point
--   linearized comparison gap rather than paper traceability; existing
--   `finiteAverageRegularizedObjectiveOn` and `first_order_linear_model` cover
--   objective values and affine models, not this regularizer-difference gap.
-- coverage search: searched `finite average gradient regularizer gap`, `first
--   order linear model`, `finiteAverageObjective`, and `regularizer difference`;
--   relevant hits were partial (`first_order_linear_model`,
--   `finiteAverageRegularizedObjectiveOn`, finite-average gradient calculus),
--   with no full SOptLib or Mathlib definition for this two-point gap.
-- minimal hypotheses: all already minimal; only `Fintype`, additive/normed
--   structure, and real inner product support the finite average and inner
--   product expression.

/-- Finite-average component-gradient comparison gap with a scaled regularizer difference.

For component gradient selectors `grad`, regularizer `nu`, and scalar `mu`, this
names the two-point quantity
`⟪card⁻¹ • ∑ᵢ grad i x, xUnder - x⟫ + mu * nu xUnder - mu * nu x`.

Layer: Model | Concept: Objective comparison gap
Proof: (definitional construction; normalized finite gradient sum paired with
  a comparison displacement plus a scaled regularizer value difference)
Source: finite-sum composite optimization first-order comparison models over
  real inner-product spaces
Used in: randomized gradient extrapolation Jensen step and objective-gap
  conversion for the finite-sum strongly-convex composite objective
Book citation: book/FOML/RandomGradientExtrapolation.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
noncomputable def finiteAverageGradientRegularizerGap
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (grad : ι → E → E) (nu : E → ℝ) (mu : ℝ) (xUnder x : E) : ℝ :=
  ⟪(Fintype.card ι : ℝ)⁻¹ •
      Finset.sum Finset.univ (fun i : ι => grad i x), xUnder - x⟫_ℝ +
    mu * nu xUnder - mu * nu x

/-- The finite-average gradient regularizer gap unfolds to its normalized
gradient-comparison formula.

Layer: Model | Gap: Level 0 (finite-average gradient regularizer gap formula)
Proof: by rfl after unfolding `finiteAverageGradientRegularizerGap`.
Source: finite-sum composite optimization first-order comparison models over
  real inner-product spaces
Used in: randomized gradient extrapolation Jensen step and objective-gap
  conversion for the finite-sum strongly-convex composite objective
Book citation: book/FOML/RandomGradientExtrapolation.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
@[simp]
theorem finiteAverageGradientRegularizerGap_def
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (grad : ι → E → E) (nu : E → ℝ) (mu : ℝ) (xUnder x : E) :
    finiteAverageGradientRegularizerGap grad nu mu xUnder x =
      ⟪(Fintype.card ι : ℝ)⁻¹ •
          Finset.sum Finset.univ (fun i : ι => grad i x), xUnder - x⟫_ℝ +
        mu * nu xUnder - mu * nu x := by
  rfl

/-- The finite-average gradient regularizer gap is convex in its first argument
on any carrier where the regularizer is convex and the regularizer multiplier is
nonnegative.

Layer: Model | Gap: Level 1 (convexity API for a finite-average gradient
  regularizer gap)
Proof: the gradient-comparison term is affine in `xUnder`, while nonnegative
  scaling preserves convexity of `nu`.
Source: finite-sum composite optimization first-order comparison models over
  real inner-product spaces
Used in: randomized gradient extrapolation Jensen step and objective-gap
  conversion for the finite-sum strongly-convex composite objective
Book citation: book/FOML/RandomGradientExtrapolation.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem finiteAverageGradientRegularizerGap_convexOn_left
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} {grad : ι → E → E} {nu : E → ℝ} {mu : ℝ} {x : E}
    (hnu : ConvexOn ℝ X nu) (hmu : 0 ≤ mu) :
    ConvexOn ℝ X (fun xUnder =>
      finiteAverageGradientRegularizerGap grad nu mu xUnder x) := by
  classical
  refine ⟨hnu.1, ?_⟩
  intro y hy z hz a b ha hb hab
  let w : E := a • y + b • z
  let g : E := (Fintype.card ι : ℝ)⁻¹ •
      Finset.sum Finset.univ (fun i : ι => grad i x)
  have hlin :
      ⟪g, w - x⟫_ℝ =
        a * ⟪g, y - x⟫_ℝ + b * ⟪g, z - x⟫_ℝ := by
    subst w
    have hvec : a • y + b • z - x =
        a • (y - x) + b • (z - x) := by
      have hb_eq : b = 1 - a := by
        linarith
      subst b
      module
    rw [hvec, inner_add_right, inner_smul_right, inner_smul_right]
  have hnu_conv : nu w ≤ a * nu y + b * nu z := by
    simpa [w, smul_eq_mul] using hnu.2 hy hz ha hb hab
  have hmu_nu : mu * nu w ≤ mu * (a * nu y + b * nu z) :=
    mul_le_mul_of_nonneg_left hnu_conv hmu
  change
    ⟪g, w - x⟫_ℝ + mu * nu w - mu * nu x ≤
      a * (⟪g, y - x⟫_ℝ + mu * nu y - mu * nu x) +
        b * (⟪g, z - x⟫_ℝ + mu * nu z - mu * nu x)
  calc
    ⟪g, w - x⟫_ℝ + mu * nu w - mu * nu x
        ≤ ⟪g, w - x⟫_ℝ + mu * (a * nu y + b * nu z) -
            mu * nu x := by
          nlinarith [hmu_nu]
    _ = a * (⟪g, y - x⟫_ℝ + mu * nu y - mu * nu x) +
        b * (⟪g, z - x⟫_ℝ + mu * nu z - mu * nu x) := by
          rw [hlin]
          have hb_eq : b = 1 - a := by
            linarith
          subst b
          ring

end SOptLib

-- Merged from Staging/expectationLe_of_ae_le_add.lean
open MeasureTheory

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: expectation upper bound under a.e. additive domination; orig was
--   `expectationLe_of_pointwise_le_add`, renamed to expose the measure-theoretic
--   a.e. hypothesis rather than paper-local pointwise phrasing.
-- generality used: arbitrary measurable space, arbitrary measure, real-valued
--   integrands, one integrability hypothesis for the dominated term, and two
--   `SOptLib.expectationLe` hypotheses; no probability, finite-dimensionality,
--   convexity, smoothness, oracle, filtration, or algorithm-state assumptions.
-- portable call pattern: expected-gap, expected-distance, and moment estimates
--   combine two previously bounded random terms after changing `μ`, `F`, `G`,
--   `H`, `bG`, `bH`, and the a.e. domination proof while preserving the same
--   `expectationLe μ F (bG + bH)` conclusion.
-- counterargument checked: not just paper traceability because it is a reusable
--   expectation-bound constructor; not a pure Mathlib duplicate because Mathlib
--   provides `integral_mono_ae` and `integral_add` but not this SOptLib
--   `expectationLe` packaging.
-- coverage search: searched CATALOG/SOptLib/Staging for `expectationLe`,
--   `integral_mono_ae`, `pointwise_le_add`, and `ae_le_add`; full hit
--   `SOptLib.expectationLe_of_integrable_integral_le` is only the one-integral
--   constructor, and LeanSearch returned lower-level integrability monotonicity
--   lemmas rather than a two-term expectation-bound constructor.
-- minimal hypotheses: all already minimal; the original global pointwise
--   domination is weakened to an a.e. domination over the supplied measure.

/-- Add two scalar expectation upper bounds under an a.e. additive domination.

If `F` is integrable, `G` and `H` have scalar expectation upper bounds, and
`F ≤ G + H` holds almost everywhere, then the expectation of `F` is bounded by
the sum of the two bounds.

Layer: Model | Gap: Level 0 (expectation upper bound under a.e. additive domination)
Proof: use `integral_mono_ae` to compare `∫ F` with `∫ (G + H)`, rewrite the
  latter by `integral_add`, and combine the two expectation bounds by
  `add_le_add`.
Source: Mathlib Bochner integral monotonicity, integrability, additive integral
  formulas, and ordered real APIs
Used in: randomized gradient extrapolation expected objective-gap bound from
  separate expected comparison-gap and expected distance-budget estimates
Book citation: book/FOML/RandomGradientExtrapolation.json#/main_theorem/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem expectationLe_of_ae_le_add
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {F G H : Ω → ℝ} {bG bH : ℝ}
    (hF : expectationWellDefined μ F)
    (hG : expectationLe μ G bG)
    (hH : expectationLe μ H bH)
    (h_le : ∀ᵐ ω ∂μ, F ω ≤ G ω + H ω) :
    expectationLe μ F (bG + bH) := by
  rcases (expectationLe_def μ G bG).1 hG with ⟨hG_int, hG_le⟩
  rcases (expectationLe_def μ H bH).1 hH with ⟨hH_int, hH_le⟩
  refine expectationLe_of_integrable_integral_le hF ?_
  have hsum_int : Integrable (fun ω => G ω + H ω) μ :=
    hG_int.add hH_int
  have hmono :
      (∫ ω, F ω ∂μ) ≤ ∫ ω, G ω + H ω ∂μ :=
    integral_mono_ae hF hsum_int h_le
  have hsum_eq :
      (∫ ω, G ω + H ω ∂μ) =
        (∫ ω, G ω ∂μ) + ∫ ω, H ω ∂μ := by
    exact integral_add hG_int hH_int
  calc
    (∫ ω, F ω ∂μ) ≤ ∫ ω, G ω + H ω ∂μ := hmono
    _ = (∫ ω, G ω ∂μ) + ∫ ω, H ω ∂μ := hsum_eq
    _ ≤ bG + bH := add_le_add hG_le hH_le

end SOptLib

-- Phase 4 batch 1 merge from Staging/hasGradientAt_coordinateSlice_exactBlockGradient.lean
namespace SOptLib

-- Generalization plan (G1):
-- concept/name: coordinate-slice gradient from ambient PiLp gradient; orig was block_coordinate_hasGradientAt
-- generality used: finite dependent product of real Hilbert blocks with complete block spaces; no measure, convexity, oracle, or algorithm setup assumptions
-- portable call pattern: stochastic block-coordinate and block mirror/prox proofs that restrict an ambient smooth objective to one updated coordinate and need the selected block of the product gradient as the slice gradient
-- counterargument checked: not paper-local because it packages a reusable PiLp chain-rule bridge; not a pure wrapper because callers avoid reproving the derivative of coordinate update plus PiLp inner-coordinate identification; no existing public SOptLib/Mathlib lemma had this exact coordinate-slice HasGradientAt conclusion
-- coverage search: queried "HasGradientAt coordinate slice product gradient PiLp replaceBlock", "gradient coordinate slice ambient finite product chain rule", and "coordinate slice HasGradientAt Function.update PiLp gradient"; hits covered local private proof, Mathlib hasFDerivAt_update, and SOptLib piLp_inner_coord_single but no full packaged theorem
-- minimal hypotheses: pointwise HasGradientAt of the transported PiLp objective at an arbitrary supplied ambient gradient is enough; global ContDiff smoothness and algorithm setup fields are intentionally left to callers

/-- The selected block of an ambient finite-product gradient is the gradient of
the corresponding one-coordinate slice.

For a real objective on raw dependent block coordinates, transport it to
`PiLp 2`, assume an ambient `HasGradientAt` certificate at the point where the
selected coordinate has value `u`, and project that gradient back to raw
coordinates.  The selected coordinate is the `HasGradientAt` gradient of
`z ↦ f (Function.update x i z)`.

Layer: Model | Gap: Level 1 (coordinate-slice product gradient chain rule)
Proof: compose the supplied ambient `HasGradientAt` certificate with the
  Fréchet derivative of `Function.update`, then identify the resulting dual
  functional using the finite `PiLp` single-coordinate inner-product lemma.
Source: Mathlib `HasGradientAt`/Fréchet chain rule, `Function.update`
  derivative, finite `PiLp` coordinate insertion, and Hilbert-space Riesz APIs
Used in: stochastic block mirror descent smooth upper-model proofs where a
  one-block objective slice must use the selected coordinate of the ambient
  product-space gradient
Book citation: book/FOML/NonconvexStochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic block mirror descent -/
theorem hasGradientAt_coordinate_slice_of_piLp_hasGradientAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Block : ι → Type*}
    [∀ i, NormedAddCommGroup (Block i)] [∀ i, InnerProductSpace ℝ (Block i)]
    [∀ i, CompleteSpace (Block i)]
    (f : (∀ i, Block i) → ℝ) (x : ∀ i, Block i) (i : ι) (u : Block i)
    (g : PiLp 2 Block)
    (hgrad :
      HasGradientAt (fun y : PiLp 2 Block => f (WithLp.ofLp y))
        g
        (WithLp.toLp 2 (Function.update x i u))) :
    HasGradientAt (fun z : Block i => f (Function.update x i z))
      (WithLp.ofLp g i) u := by
  let F : PiLp 2 Block → ℝ := fun y => f (WithLp.ofLp y)
  let xu : ∀ j, Block j := Function.update x i u
  have hraw :
      HasFDerivAt (fun z : Block i => Function.update x i z)
        (ContinuousLinearMap.pi (Pi.single i (.id ℝ (Block i)))) u := by
    simpa using
      (hasFDerivAt_update (𝕜 := ℝ) x (i := i) (y := u))
  have hmap :
      HasFDerivAt
        (fun z : Block i => WithLp.toLp 2 (Function.update x i z))
        (((PiLp.continuousLinearEquiv 2 ℝ Block).symm :
            (∀ j, Block j) →L[ℝ] PiLp 2 Block).comp
          (ContinuousLinearMap.pi (Pi.single i (.id ℝ (Block i))))) u := by
    simpa [PiLp.coe_symm_continuousLinearEquiv] using
      (((PiLp.continuousLinearEquiv 2 ℝ Block).symm :
          (∀ j, Block j) →L[ℝ] PiLp 2 Block).hasFDerivAt.comp u hraw)
  have hcomp := hgrad.hasFDerivAt.comp u hmap
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hcomp using 1
  · ext z
    simp [PiLp.coe_symm_continuousLinearEquiv,
      InnerProductSpace.toDual_apply_apply, SOptLib.piLp_inner_coord_single,
      Pi.single]
    congr 1
    ext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [Function.update_of_ne hji, Pi.single_eq_of_ne hji]

end SOptLib

-- Phase 4 batch 1 merge from Staging/piLpBlockGradient.lean
namespace SOptLib

-- Generalization plan (G0):
-- concept/name: finite dependent PiLp block gradient; orig was exactBlockGradient
-- generality used: finite dependent product of real Hilbert blocks with complete block spaces; no measure, convexity, smoothness, oracle, or algorithm setup assumptions
-- portable call pattern: finite block-gradient and block-coordinate methods that represent an objective on raw dependent coordinates but use Mathlib's gradient on the associated PiLp Hilbert product
-- counterargument checked: not paper-local because the object is the canonical PiLp-gradient-to-coordinate bridge for any finite block objective; not a pure wrapper because downstream proofs can name the exact gradient in block coordinates and share its coordinate formula; not covered by existing SOptLib/Mathlib entries, which provide PiLp projections, inner-coordinate pairing, and coordinate-slice derivative facts but not this block-gradient definition
-- coverage search: queried "finite product PiLp gradient block coordinates", "gradient PiLp ofLp toLp coordinate finite product", and Mathlib semantic search "gradient on finite PiLp product returned as dependent function coordinates"; hits were Mathlib gradient, PiLp differentiability/projection APIs, SOptLib piLp_inner_coord_single, PiLp.proj_toLp, and the existing coordinate-slice HasGradientAt theorem, with no full duplicate definition
-- minimal hypotheses: all already minimal for Mathlib's Hilbert-space gradient on PiLp 2: Fintype index, real inner-product block spaces, and completeness of each block

/-- The finite dependent-product gradient transported through `PiLp 2` and
returned in raw block coordinates.

For an objective written on dependent block coordinates, `piLpBlockGradient`
assembles the point as a `PiLp 2` Hilbert product, applies Mathlib's `gradient`,
and projects the resulting ambient gradient back to the raw coordinate family.

Layer: Model | Concept: finite PiLp block gradient
Proof: (definitional construction; transported Mathlib gradient on a finite dependent `PiLp 2` Hilbert product followed by `WithLp.ofLp`)
Source: Mathlib inner-product-space gradient and finite dependent `PiLp` Hilbert product APIs
Used in: stochastic block mirror descent exact-gradient modeling where the paper's block gradient `g(x)` is represented by raw block coordinates while calculus is performed on the product Hilbert space
Book citation: book/FOML/NonconvexStochasticBlockMirrorDescent.json#/setup/variable_space
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, nonconvex stochastic block mirror descent -/
noncomputable def piLpBlockGradient
    {ι : Type*} [Fintype ι]
    {Block : ι → Type*}
    [∀ i, NormedAddCommGroup (Block i)] [∀ i, InnerProductSpace ℝ (Block i)]
    [∀ i, CompleteSpace (Block i)]
    (f : (∀ i, Block i) → ℝ) (x : ∀ i, Block i) : ∀ i, Block i :=
  WithLp.ofLp
    (gradient (fun y : PiLp 2 Block => f (WithLp.ofLp y)) (WithLp.toLp 2 x))

/-- The finite dependent-product block gradient unfolds to the transported
Mathlib gradient on `PiLp 2`.

Layer: Model | Gap: Level 0 (finite PiLp block-gradient definition)
Proof: by rfl after unfolding `piLpBlockGradient`.
Source: Mathlib inner-product-space gradient and finite dependent `PiLp` APIs
Used in: stochastic block mirror descent proofs that move between the named
block-gradient object and the ambient product-space gradient -/
@[simp]
theorem piLpBlockGradient_def
    {ι : Type*} [Fintype ι]
    {Block : ι → Type*}
    [∀ i, NormedAddCommGroup (Block i)] [∀ i, InnerProductSpace ℝ (Block i)]
    [∀ i, CompleteSpace (Block i)]
    (f : (∀ i, Block i) → ℝ) (x : ∀ i, Block i) :
    piLpBlockGradient f x =
      WithLp.ofLp
        (gradient (fun y : PiLp 2 Block => f (WithLp.ofLp y)) (WithLp.toLp 2 x)) := by
  rfl

/-- The transported finite-product block gradient is the coordinate projection
of the Mathlib gradient on `PiLp 2`.

Layer: Model | Gap: Level 0 (finite PiLp block-gradient coordinate formula)
Proof: by rfl after unfolding `piLpBlockGradient`.
Source: Mathlib inner-product-space gradient and finite dependent `PiLp` coordinate APIs
Used in: stochastic block mirror descent proofs that select the sampled block of the exact product gradient before comparing it with a stochastic block oracle
Book citation: book/FOML/NonconvexStochasticBlockMirrorDescent.json#/algorithm_spec/steps/1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, nonconvex stochastic block mirror descent -/
@[simp]
theorem piLpBlockGradient_apply
    {ι : Type*} [Fintype ι]
    {Block : ι → Type*}
    [∀ i, NormedAddCommGroup (Block i)] [∀ i, InnerProductSpace ℝ (Block i)]
    [∀ i, CompleteSpace (Block i)]
    (f : (∀ i, Block i) → ℝ) (x : ∀ i, Block i) (i : ι) :
    piLpBlockGradient f x i =
      WithLp.ofLp
        (gradient (fun y : PiLp 2 Block => f (WithLp.ofLp y)) (WithLp.toLp 2 x)) i := by
  rfl

/-- The transported finite-product block gradient gives the gradient of a
one-coordinate slice when the ambient transported objective has its Mathlib
gradient at the corresponding `PiLp 2` point.

Layer: Model | Gap: Level 1 (PiLp block-gradient coordinate-slice API)
Proof: specialize the ambient coordinate-slice `HasGradientAt` bridge to the
Mathlib gradient used by `piLpBlockGradient`, then fold the named block-gradient
definition.
Source: Mathlib `HasGradientAt`/gradient APIs and SOptLib coordinate-slice
PiLp gradient bridge
Used in: stochastic block mirror descent proofs that replace the selected block
of the exact product gradient with the gradient of the one-block objective
slice -/
theorem hasGradientAt_coordinate_slice_piLpBlockGradient_of_piLp_hasGradientAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Block : ι → Type*}
    [∀ i, NormedAddCommGroup (Block i)] [∀ i, InnerProductSpace ℝ (Block i)]
    [∀ i, CompleteSpace (Block i)]
    (f : (∀ i, Block i) → ℝ) (x : ∀ i, Block i) (i : ι) (u : Block i)
    (hgrad :
      HasGradientAt (fun y : PiLp 2 Block => f (WithLp.ofLp y))
        (gradient (fun y : PiLp 2 Block => f (WithLp.ofLp y))
          (WithLp.toLp 2 (Function.update x i u)))
        (WithLp.toLp 2 (Function.update x i u))) :
    HasGradientAt (fun z : Block i => f (Function.update x i z))
      (piLpBlockGradient f (Function.update x i u) i) u := by
  simpa [piLpBlockGradient] using
    hasGradientAt_coordinate_slice_of_piLp_hasGradientAt
      (f := f) (x := x) (i := i) (u := u)
      (g := gradient (fun y : PiLp 2 Block => f (WithLp.ofLp y))
        (WithLp.toLp 2 (Function.update x i u)))
      hgrad

-- Generalization plan (G0):
-- concept/name: finite-component smoothness and initial objective-gap assumption; orig was SmoothnessAssumption.
-- generality used: arbitrary component index type and real Hilbert carrier with complete-space gradient calculus; no measure, independence, integrability, convexity, oracle, filtration, or finite-dimensional hypotheses are used.
-- portable call pattern: finite-sum smooth distributed and variance-reduced algorithms call the same component-gradient Lipschitz and initial component-gap projections while changing the component family, selected gradients, initial point, smoothness scale, and gap scale.
-- counterargument checked: not paper-local because finite-component smoothness together with bounded initial gaps is a standard finite-sum optimization assumption; not a pure duplicate because SOptLib.FiniteFamilyGradientSmoothness covers only gradient realization and Lipschitzness, while this predicate adds the objective-infimum lower-boundedness and initial-gap clauses.
-- coverage search: lean_search_symbols "finite component smoothness assumption HasGradientAt Lipschitz initial gap bounded below" found SOptLib.FiniteFamilyGradientSmoothness as a partial smoothness bundle and finite-average smooth-descent theorems, but no assumption carrying the objective-infimum gap; lean_search_symbols "objective infimum initial gap finite component lower bounded smoothness assumption" found only the local SmoothnessAssumption plus objectiveInfimumValue APIs; lean_leansearch "finite family component smoothness assumption gradients Lipschitz initial objective gap bounded below" found Mathlib Lipschitz/mean-value lemmas but no finite-sum optimization assumption bundle.
-- minimal hypotheses: the algorithm setup object, node finiteness, decidable equality, nonempty node assumption, and finite-dimensionality were removed; the complete-space assumption is retained because the bundled gradient predicate is Mathlib/SOptLib's Hilbert gradient API.

/-- Finite-family gradient smoothness with bounded component initial gaps.

The predicate extends `FiniteFamilyGradientSmoothness` by recording that each
component objective is bounded below on a carrier `X`, and that a common budget
`Delta` bounds every component's initial gap to the corresponding carrier
infimum value.

Layer: Model | Concept: finite-component smoothness and initial objective-gap assumption
Proof: (definitional construction; conjunction of selected-gradient smoothness, objective lower-boundedness, and initial component-gap bounds)
Source: finite-sum smooth optimization assumptions, Mathlib Hilbert-space gradient predicates, and SOptLib objective-infimum values
Used in: pull-with-memory decentralized gradient descent extraction of component smoothness, finite-average gradient identification, and initial objective-gap bounds
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/assumptions/4
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
noncomputable def FiniteComponentSmoothnessAssumption
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (X : Set E) (F : ι → E → ℝ) (gradF : ι → E → E) (x0 : E)
    (Lcomp : ι → ℝ) (Delta : ℝ) : Prop :=
  FiniteFamilyGradientSmoothness F gradF Lcomp ∧
    0 ≤ Delta ∧
      (∀ i, BddBelow ((F i) '' X)) ∧
        ∀ i, F i x0 - objectiveInfimumValue X (F i) ≤ Delta

/-- The finite-component smoothness and initial-gap assumption unfolds to
finite-family gradient smoothness, nonnegativity of the initial-gap budget,
component lower-boundedness on the carrier, and component initial-gap bounds.

Layer: Model | Gap: Level 0 (finite-component smoothness assumption unfolding)
Proof: by rfl after unfolding `FiniteComponentSmoothnessAssumption`.
Source: finite-sum smooth optimization assumptions, Mathlib conjunction APIs, and SOptLib objective-infimum values
Used in: rewriting a finite-component smoothness assumption into smoothness, lower-bound, and initial-gap clauses for finite-average descent proofs
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/assumptions/4
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
@[simp] theorem FiniteComponentSmoothnessAssumption_def
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (X : Set E) (F : ι → E → ℝ) (gradF : ι → E → E) (x0 : E)
    (Lcomp : ι → ℝ) (Delta : ℝ) :
    FiniteComponentSmoothnessAssumption X F gradF x0 Lcomp Delta ↔
      FiniteFamilyGradientSmoothness F gradF Lcomp ∧
        0 ≤ Delta ∧
          (∀ i, BddBelow ((F i) '' X)) ∧
            ∀ i, F i x0 - objectiveInfimumValue X (F i) ≤ Delta := by
  rfl

namespace FiniteComponentSmoothnessAssumption

/-- A finite-component smoothness and initial-gap assumption exposes the
underlying finite-family gradient smoothness bundle.

Layer: Model | Gap: Level 0 (finite-component smoothness bridge to selected-gradient smoothness)
Proof: project the finite-family smoothness conjunct from the assumption.
Source: SOptLib finite-family gradient smoothness API and Mathlib conjunction projections
Used in: finite-sum proofs that first consume the broader initial-gap assumption and then call SOptLib finite-family gradient-smoothness lemmas
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/assumptions/4
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
theorem finiteFamilyGradientSmoothness
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {X : Set E} {F : ι → E → ℝ} {gradF : ι → E → E} {x0 : E}
    {Lcomp : ι → ℝ} {Delta : ℝ}
    (h : FiniteComponentSmoothnessAssumption X F gradF x0 Lcomp Delta) :
    FiniteFamilyGradientSmoothness F gradF Lcomp :=
  h.1

/-- Component smoothness constants are nonnegative.

Layer: Model | Gap: Level 0 (finite-component smoothness nonnegative scale projection)
Proof: project nonnegativity from the underlying finite-family smoothness bundle.
Source: ordered real smoothness constants and Mathlib conjunction projections
Used in: finite-sum stepsize and smooth descent side-condition extraction from component smoothness assumptions
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/assumptions/4
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
theorem smoothness_nonneg
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {X : Set E} {F : ι → E → ℝ} {gradF : ι → E → E} {x0 : E}
    {Lcomp : ι → ℝ} {Delta : ℝ}
    (h : FiniteComponentSmoothnessAssumption X F gradF x0 Lcomp Delta) (i : ι) :
    0 ≤ Lcomp i :=
  h.1.2.1 i

/-- The common initial component-gap scale is nonnegative.

Layer: Model | Gap: Level 0 (finite-component initial-gap nonnegative scale projection)
Proof: project the initial-gap budget conjunct of `FiniteComponentSmoothnessAssumption`.
Source: ordered real objective-gap scales and Mathlib conjunction projections
Used in: finite-sum descent proofs that extract nonnegativity of the initial objective-gap budget
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/assumptions/4
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
theorem initial_gap_nonneg
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {X : Set E} {F : ι → E → ℝ} {gradF : ι → E → E} {x0 : E}
    {Lcomp : ι → ℝ} {Delta : ℝ}
    (h : FiniteComponentSmoothnessAssumption X F gradF x0 Lcomp Delta) :
    0 ≤ Delta :=
  h.2.1

/-- The selected component gradient realizes the derivative of each component.

Layer: Model | Gap: Level 0 (finite-component gradient realization projection)
Proof: project gradient realization from the underlying finite-family smoothness bundle.
Source: Mathlib Hilbert-space gradient predicates and conjunction projections
Used in: finite-average gradient identification from component differentiability in finite-sum smooth algorithms
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/assumptions/4
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
theorem hasGradientAt
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {X : Set E} {F : ι → E → ℝ} {gradF : ι → E → E} {x0 : E}
    {Lcomp : ι → ℝ} {Delta : ℝ}
    (h : FiniteComponentSmoothnessAssumption X F gradF x0 Lcomp Delta)
    (i : ι) (x : E) :
    HasGradientAt (F i) (gradF i x) x :=
  h.1.1 i x

/-- Selected component gradients satisfy their componentwise Lipschitz bounds.

Layer: Model | Gap: Level 0 (finite-component gradient Lipschitz projection)
Proof: project the component Lipschitz conjunct from the underlying finite-family smoothness bundle.
Source: normed-space Lipschitz-gradient assumptions and Mathlib conjunction projections
Used in: finite-average smooth quadratic upper bounds and disagreement-gradient estimates in finite-sum algorithms
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/assumptions/4
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
theorem lipschitz
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {X : Set E} {F : ι → E → ℝ} {gradF : ι → E → E} {x0 : E}
    {Lcomp : ι → ℝ} {Delta : ℝ}
    (h : FiniteComponentSmoothnessAssumption X F gradF x0 Lcomp Delta)
    (i : ι) (x y : E) :
    ‖gradF i x - gradF i y‖ ≤ Lcomp i * ‖x - y‖ :=
  h.1.2.2 i x y

/-- Each component objective image over the carrier is bounded below.

Layer: Model | Gap: Level 0 (finite-component objective lower-boundedness projection)
Proof: project the bounded-below objective-image conjunct of `FiniteComponentSmoothnessAssumption`.
Source: Mathlib order-theoretic boundedness and SOptLib objective-infimum values
Used in: justifying component infimum values before converting initial component gaps into finite-average objective gaps
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/assumptions/4
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
theorem bddBelow
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {X : Set E} {F : ι → E → ℝ} {gradF : ι → E → E} {x0 : E}
    {Lcomp : ι → ℝ} {Delta : ℝ}
    (h : FiniteComponentSmoothnessAssumption X F gradF x0 Lcomp Delta) (i : ι) :
    BddBelow ((F i) '' X) :=
  h.2.2.1 i

/-- Each component's initial objective gap to its carrier infimum value is
bounded by the common gap scale.

Layer: Model | Gap: Level 0 (finite-component initial objective-gap projection)
Proof: project the initial objective-gap conjunct of `FiniteComponentSmoothnessAssumption`.
Source: SOptLib objective-infimum values, ordered real objective gaps, and Mathlib conjunction projections
Used in: bounding the initial finite-average objective gap in distributed finite-sum smooth descent arguments
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/assumptions/4
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
theorem initial_gap_le
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {X : Set E} {F : ι → E → ℝ} {gradF : ι → E → E} {x0 : E}
    {Lcomp : ι → ℝ} {Delta : ℝ}
    (h : FiniteComponentSmoothnessAssumption X F gradF x0 Lcomp Delta) (i : ι) :
    F i x0 - objectiveInfimumValue X (F i) ≤ Delta :=
  h.2.2.2 i

/-- Specialization of the carrier/componentwise predicate to a common
component smoothness constant on the full ambient space.

Layer: Model | Gap: Level 0 (finite-component smoothness full-space constant specialization)
Proof: by rfl after unfolding `FiniteComponentSmoothnessAssumption`.
Source: finite-sum smooth optimization assumptions and SOptLib objective-infimum values
Used in: source-facing smooth finite-sum algorithms whose component assumptions are stated on the full ambient carrier with one common smoothness scale
Book citation: book/LiangSongYuan2025/PullWithMemoryDGD.json#/assumptions/4
Origin algorithm: Liang, Song, and Yuan, Decentralized Optimization over Time-Varying Row-Stochastic Digraphs, PULM-based Decentralized Gradient Descent -/
theorem univ_const_iff
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (F : ι → E → ℝ) (gradF : ι → E → E) (x0 : E) (L Delta : ℝ) :
    FiniteComponentSmoothnessAssumption (Set.univ : Set E) F gradF x0
        (fun _ : ι => L) Delta ↔
      FiniteFamilyGradientSmoothness F gradF (fun _ : ι => L) ∧
        0 ≤ Delta ∧
          (∀ i, BddBelow ((F i) '' (Set.univ : Set E))) ∧
            ∀ i, F i x0 - objectiveInfimumValue (Set.univ : Set E) (F i) ≤ Delta := by
  rfl

end FiniteComponentSmoothnessAssumption

end SOptLib

namespace SOptLib


-- Generalization plan (G0):
-- concept/name: Lipschitz-gradient objective regularity; orig was CL11.
-- generality used: arbitrary complete real inner-product normed additive group
--   E and objective f : E -> Real with a real smoothness constant L; no measure,
--   convexity, oracle, or finite-dimensional assumptions are needed to state
--   the predicate.
-- portable call pattern: smooth first-order, finite-sum, stochastic-gradient,
--   and zeroth-order proofs can instantiate E, f, and L when they need the
--   reusable assumption that f is differentiable and its Mathlib gradient has a
--   global L-Lipschitz bound.
-- counterargument checked: not just paper-local traceability because the same
--   regularity class is the entry assumption for smooth descent, Gaussian
--   smoothing, and gradient-gap steps; it is not a pure duplicate of the
--   existing finite-family or carrier-gradient predicates, which require
--   selected gradients, carriers, or component families.
-- coverage search: searched "differentiable Lipschitz gradient predicate",
--   "Lipschitz gradient objective differentiable", and "Smooth objective
--   differentiable gradient Lipschitz definition"; top hits were
--   FiniteFamilyGradientSmoothness, carrierGradient_lipschitz_of_assumption,
--   and smooth-descent consequence theorems, all partial rather than this
--   global Mathlib-gradient objective predicate.
-- minimal hypotheses: all already minimal for the proposition; positivity of L
--   and finite-dimensional Euclidean structure are caller-side assumptions, not
--   needed by the definition.

/-- A real objective is differentiable and has a globally Lipschitz Mathlib gradient.

Layer: Model | Concept: Lipschitz-gradient objective regularity
Proof: (definitional construction; conjunction of differentiability and a
  global norm bound for gradient differences)
Source: Mathlib Hilbert-space gradient and differentiability predicates
Used in: randomized stochastic gradient-free smoothness assumptions before
  smooth descent, Gaussian smoothing, finite-difference moment, and gradient-gap
  estimates
Book citation: book/FOML/StochasticZerothOrder.json#/assumptions/3/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic gradient-free method -/
def LipschitzGradientObjective
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (L : ℝ) : Prop :=
  Differentiable ℝ f ∧
    ∀ x y : E, ‖∇ f y - ∇ f x‖ ≤ L * ‖y - x‖

/-- The Lipschitz-gradient objective predicate unfolds to differentiability and
the global gradient-difference bound.

Layer: Model | Gap: Level 0 (Lipschitz-gradient objective unfolding)
Proof: by rfl after unfolding `LipschitzGradientObjective`.
Source: Mathlib Hilbert-space gradient and differentiability predicates
Used in: randomized stochastic gradient-free smoothness assumptions when
  replacing the source `C_L^{1,1}` notation by its Lean proposition
Book citation: book/FOML/StochasticZerothOrder.json#/assumptions/3/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic gradient-free method -/
@[simp] theorem LipschitzGradientObjective_def
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (L : ℝ) :
    LipschitzGradientObjective f L ↔
      Differentiable ℝ f ∧
        ∀ x y : E, ‖∇ f y - ∇ f x‖ ≤ L * ‖y - x‖ :=
  Iff.rfl

namespace LipschitzGradientObjective

/-- A Lipschitz-gradient objective is differentiable.

Layer: Model | Gap: Level 0 (Lipschitz-gradient objective differentiability projection)
Proof: unfold the Lipschitz-gradient objective predicate and take the first
  conjunct.
Source: Mathlib Hilbert-space differentiability predicates and propositional
  conjunction APIs
Used in: smooth first-order and zeroth-order objective proofs before converting
  differentiability into pointwise gradient certificates
Book citation: book/FOML/StochasticZerothOrder.json#/assumptions/3/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic gradient-free method -/
theorem differentiable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {L : ℝ} (h : LipschitzGradientObjective f L) :
    Differentiable ℝ f :=
  h.1

/-- A Lipschitz-gradient objective satisfies its global gradient-difference bound.

Layer: Model | Gap: Level 0 (Lipschitz-gradient objective bound projection)
Proof: unfold the Lipschitz-gradient objective predicate and specialize the
  second conjunct at the two points.
Source: Mathlib Hilbert-space gradient and norm APIs
Used in: smooth descent, Gaussian smoothing, and stochastic finite-difference
  estimates that consume the Lipschitz gradient inequality pointwise
Book citation: book/FOML/StochasticZerothOrder.json#/assumptions/3/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic gradient-free method -/
theorem gradient_lipschitz
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {L : ℝ} (h : LipschitzGradientObjective f L)
    (x y : E) :
    ‖∇ f y - ∇ f x‖ ≤ L * ‖y - x‖ :=
  h.2 x y

end LipschitzGradientObjective




-- Generalization plan (G0):
-- concept/name: stochastic objective realization by sample losses; orig was
--   SZOAssumption15.
-- generality used: arbitrary decision type X, sample type S with a measurable
--   space, sample law P, real-valued sample loss F, and deterministic objective
--   f; no Euclidean, smoothness, convexity, probability, oracle, or
--   finite-dimensional assumptions are needed.
-- portable call pattern: zeroth-order, stochastic-objective, and sampled-loss
--   proofs can instantiate the decision type, sample law, loss kernel, and
--   objective while keeping the conclusion that every fixed query has a
--   measurable integrable function-value realization whose expectation is the
--   objective value.
-- counterargument checked: not paper-local traceability because the same
--   all-query function-value realization contract is used before converting
--   finite differences or sampled objectives into deterministic objectives;
--   not a duplicate of objectiveExpectation or expectationEq, which name a
--   single expectation expression/equality but do not bundle all fixed
--   decisions with measurability.
-- coverage search: searched "sample function values measurable integrable
--   expectation equals objective" and "stochastic objective realization
--   integrable measurable integral equals objective"; top hits were
--   SOptLib.objectiveExpectation_eq_integral_kernel,
--   SOptLib.objectiveExpectation_eq_integral_of_map_eq, and
--   SOptLib.expectationEq, all partial rather than this all-query sampled-loss
--   realization predicate.
-- minimal hypotheses: all already minimal; measurability of S is required for
--   measurable fibers, and real-valued Bochner integrability/equality supplies
--   the expectation contract without further typeclasses.

/-- Sample losses realize a deterministic stochastic objective at every query.

For each decision `x`, the sample function `s ↦ F x s` is measurable and
integrable under `P`, and its Bochner integral is the deterministic objective
value `f x`.

Layer: Model | Concept: Stochastic objective realization
Proof: (definitional construction; all-query conjunction of measurable
  fibers, Bochner integrability, and objective expectation equality)
Source: Mathlib measure theory Bochner integral notation and stochastic
  objective expectation predicates
Used in: randomized stochastic gradient-free proofs when Assumption 15 turns
  sampled zeroth-order function values at fixed queries into deterministic
  objective values before finite-difference and smoothing estimates
Book citation: book/FOML/StochasticZerothOrder.json#/assumptions/4
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic gradient-free method -/
def StochasticObjectiveRealization
    {X S : Type*} [MeasurableSpace S]
    (P : Measure S) (F : X → S → ℝ) (f : X → ℝ) : Prop :=
  (∀ x : X, Measurable (fun s => F x s)) ∧
    (∀ x : X, Integrable (fun s => F x s) P) ∧
    (∀ x : X, (∫ s, F x s ∂P) = f x)

/-- The stochastic objective realization predicate unfolds to fixed-query
measurability, integrability, and expectation equality.

Layer: Model | Gap: Level 0 (stochastic objective realization formula)
Proof: by rfl after unfolding `StochasticObjectiveRealization`.
Source: Mathlib measure theory Bochner integral notation and measurability APIs
Used in: randomized stochastic gradient-free proofs when extracting the three
  fixed-query obligations supplied by the function-value realization assumption
Book citation: book/FOML/StochasticZerothOrder.json#/assumptions/4
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic gradient-free method -/
@[simp]
theorem StochasticObjectiveRealization_def
    {X S : Type*} [MeasurableSpace S]
    (P : Measure S) (F : X → S → ℝ) (f : X → ℝ) :
    StochasticObjectiveRealization P F f ↔
      (∀ x : X, Measurable (fun s => F x s)) ∧
        (∀ x : X, Integrable (fun s => F x s) P) ∧
        (∀ x : X, (∫ s, F x s ∂P) = f x) := by
  rfl

/-- A stochastic objective realization gives measurability of each sample-loss
fiber.

Layer: Model | Gap: Level 0 (sample-loss fiber measurability projection)
Proof: project the first conjunct of `StochasticObjectiveRealization`.
Source: Mathlib measure theory measurable function predicates
Used in: randomized stochastic gradient-free proofs when fixed-query
  zeroth-order function values must be measurable before integration
Book citation: book/FOML/StochasticZerothOrder.json#/assumptions/4
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic gradient-free method -/
theorem StochasticObjectiveRealization.measurable
    {X S : Type*} [MeasurableSpace S]
    {P : Measure S} {F : X → S → ℝ} {f : X → ℝ}
    (h : StochasticObjectiveRealization P F f) (x : X) :
    Measurable (fun s => F x s) :=
  h.1 x

/-- A stochastic objective realization gives integrability of each sample-loss
fiber.

Layer: Model | Gap: Level 0 (sample-loss fiber integrability projection)
Proof: project the second conjunct of `StochasticObjectiveRealization`.
Source: Mathlib measure theory Bochner integrability predicates
Used in: randomized stochastic gradient-free proofs when fixed-query
  zeroth-order function values must be integrable before expectation rewrites
Book citation: book/FOML/StochasticZerothOrder.json#/assumptions/4
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic gradient-free method -/
theorem StochasticObjectiveRealization.integrable
    {X S : Type*} [MeasurableSpace S]
    {P : Measure S} {F : X → S → ℝ} {f : X → ℝ}
    (h : StochasticObjectiveRealization P F f) (x : X) :
    Integrable (fun s => F x s) P :=
  h.2.1 x

/-- A stochastic objective realization identifies each sample-loss expectation
with the deterministic objective value.

Layer: Model | Gap: Level 0 (sample-loss expectation equality projection)
Proof: project the final conjunct of `StochasticObjectiveRealization`.
Source: Mathlib measure theory Bochner integral notation and equality APIs
Used in: randomized stochastic gradient-free proofs when integrating the
  two function values in a zeroth-order finite difference and rewriting them
  as deterministic objective values
Book citation: book/FOML/StochasticZerothOrder.json#/assumptions/4
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic gradient-free method -/
theorem StochasticObjectiveRealization.integral_eq
    {X S : Type*} [MeasurableSpace S]
    {P : Measure S} {F : X → S → ℝ} {f : X → ℝ}
    (h : StochasticObjectiveRealization P F f) (x : X) :
    (∫ s, F x s ∂P) = f x :=
  h.2.2 x




-- Generalization plan (G0):
-- concept/name: attained feasible objective infimum; orig was
--   `fStar_eq_objective_of_global_optimal`, renamed away from paper-local
--   optimum notation and algorithm-specific global-optimal wording.
-- generality used: arbitrary carrier type, feasible set, real-valued objective,
--   and feasible optimizer; no measure, convexity, smoothness, oracle, topology,
--   Hilbert, or finite-dimensional assumptions are used.
-- portable call pattern: convex or nonconvex stochastic-optimization proofs
--   that replace a named infimum value by the objective value at an attained
--   globally optimal feasible comparison point; the feasible set, objective,
--   and optimizer witness vary while the equality statement stays fixed.
-- counterargument checked: this is not only paper traceability because it closes
--   a recurring attained-optimum-to-infimum bridge for the named SOptLib
--   `objectiveInfimumValue`; it is not a pure wrapper around Mathlib because
--   the statement preserves the SOptLib objective model and discharges the
--   bounded-below side condition from pointwise optimality.
-- coverage search: lean_search_symbols "objective infimum value equals attained
--   minimum forall lower bound feasible set" found `objectiveInfimumValue`,
--   `objectiveInfimumValue_le`, and bundled `objectiveMinimum...` projections
--   as partial hits but no equality for `objectiveInfimumValue`; lean_search_symbols
--   "sInf image equals value minimizer lower bound member" and LeanSearch
--   "infimum of a set equals an attained lower bound" found Mathlib `csInf` and
--   `IsGLB` facts as proof ingredients, not the SOptLib objective bridge.
-- minimal hypotheses: explicit bounded-below hypothesis removed; it follows
--   from feasibility of `xStar` and the pointwise feasible-set lower bound.

/-- The feasible objective infimum equals the objective value at any feasible
point whose value lower-bounds all feasible objective values.

Layer: Model | Gap: Level 0 (attained feasible objective infimum equality)
Proof: unfold `objectiveInfimumValue`, use pointwise optimality to build the
  lower-bound certificate for the feasible objective image, and combine
  `csInf_le` with `le_csInf` by antisymmetry.
Source: Mathlib conditionally complete linear order API for real `sInf` over
  set images
Used in: randomized stochastic gradient-free convex branch where the paper
  optimum value `f*` is replaced by the objective value at an attained global
  optimizer
Book citation: book/FOML/StochasticZerothOrder.json#/assumptions/11
Origin algorithm: G. Lan, First-Order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic gradient free method -/
theorem objectiveInfimumValue_eq_of_forall_le {E : Type*} {X : Set E}
    {f : E → ℝ} {xStar : E}
    (hxStar : xStar ∈ X) (h_le : ∀ x, x ∈ X → f xStar ≤ f x) :
    objectiveInfimumValue X f = f xStar := by
  have h_bddBelow : BddBelow (f '' X) := by
    exact ⟨f xStar, by
      rintro y ⟨x, hx, rfl⟩
      exact h_le x hx⟩
  refine le_antisymm ?_ ?_
  · exact objectiveInfimumValue_le h_bddBelow hxStar
  · rw [objectiveInfimumValue_def]
    refine le_csInf ?_ ?_
    · exact ⟨f xStar, ⟨xStar, hxStar, rfl⟩⟩
    · rintro y ⟨x, hx, rfl⟩
      exact h_le x hx




-- Generalization plan (G0):
-- concept/name: Gaussian smoothing of a real objective by standard-Gaussian
--   additive perturbations; orig was gaussianSmoothing.
-- generality used: arbitrary finite-dimensional real inner-product normed
--   additive group E with a measurable space; no smoothness, convexity, oracle,
--   integrability, or positivity hypotheses are needed to name the total
--   Bochner integral expression.
-- portable call pattern: randomized zeroth-order and Gaussian random-search
--   algorithms can instantiate E, f, and mu when replacing a raw expectation
--   expression by the named smoothed objective f_mu.
-- counterargument checked: not paper-local traceability because the same
--   standard-Gaussian smoothing object appears in RSGF, random gradient-free,
--   accelerated random-search, and nonconvex random-search proofs; not covered
--   by Mathlib, whose Gaussian API provides stdGaussian and moments but no
--   smoothing objective definition.
-- coverage search: searched "Gaussian smoothing maps function integral shifted
--   gaussian measure", "gaussianSmoothing standard Gaussian integral shift",
--   "stdGaussianSmoothing", and "standard Gaussian smoothing definition
--   integral shifted function"; top hits were only this algorithm declaration,
--   reference-example wrappers around a missing stdGaussianSmoothing name, and
--   Mathlib/SOptLib Gaussian moment facts, all partial rather than this
--   Model-level definition with an apply theorem.
-- minimal hypotheses: finite-dimensional inner-product structure is required
--   by Mathlib's stdGaussian; Borel, second-countability, positivity of mu, and
--   regularity assumptions are caller-side facts not needed by the definition.

/-- Gaussian smoothing sends `f` to `x ↦ ∫ u, f (x + mu • u) d(stdGaussian E)`.

Layer: Model | Concept: Gaussian smoothing
Proof: (definitional construction; Bochner integral of a shifted objective
  along the finite-dimensional standard Gaussian law)
Source: Mathlib multivariate standard Gaussian measure and Bochner integral
  notation
Used in: randomized stochastic gradient-free smoothing when the raw Gaussian
  expectation defining the smoothed objective is replaced by a named model
  object before differentiating, comparing gradients, and applying descent
Book citation: book/FOML/StochasticZerothOrder.json#/algorithm_spec/parameters/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic gradient-free method -/
noncomputable def gaussianSmoothing
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E]
    (f : E → ℝ) (mu : ℝ) (x : E) : ℝ :=
  ∫ u, f (x + mu • u) ∂(stdGaussian E)

/-- The value of Gaussian smoothing is the standard-Gaussian integral of the
shifted objective.

Layer: Model | Gap: Level 0 (Gaussian smoothing definitional formula)
Proof: by rfl after unfolding `gaussianSmoothing`.
Source: Mathlib multivariate standard Gaussian measure and Bochner integral
  notation
Used in: randomized stochastic gradient-free proofs when rewriting the named
  smoothed objective back to its Gaussian expectation for integrability,
  differentiation, and finite-difference estimates
Book citation: book/FOML/StochasticZerothOrder.json#/algorithm_spec/parameters/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic gradient-free method -/
@[simp]
theorem gaussianSmoothing_def
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E]
    (f : E → ℝ) (mu : ℝ) (x : E) :
    gaussianSmoothing f mu x = ∫ u, f (x + mu • u) ∂(stdGaussian E) := by
  rfl

/-- Compatibility name for rewriting a Gaussian smoothing value to its
standard-Gaussian integral formula. -/
theorem gaussianSmoothing_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E]
    (f : E → ℝ) (mu : ℝ) (x : E) :
    gaussianSmoothing f mu x = ∫ u, f (x + mu • u) ∂(stdGaussian E) := by
  rfl

/-- Gaussian smoothing preserves constant objectives. -/
@[simp]
theorem gaussianSmoothing_const
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (c mu : ℝ) (x : E) :
    gaussianSmoothing (fun _ : E => c) mu x = c := by
  simp [gaussianSmoothing, integral_const, probReal_univ]

/-- Gaussian smoothing with zero radius returns the original objective value. -/
@[simp]
theorem gaussianSmoothing_zero_mu
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (x : E) :
    gaussianSmoothing f 0 x = f x := by
  simp [gaussianSmoothing, integral_const, probReal_univ]




-- Generalization plan (G0):
-- concept/name: nonnegative objective gap to an attained feasible infimum; orig was
--   `objective_gap_nonneg_of_global_optimal`, renamed away from paper-local `fStar`.
-- generality used: arbitrary carrier type, feasible set, real-valued objective,
--   feasible optimizer and comparison point; no measure, topology, convexity,
--   smoothness, oracle, Hilbert, or finite-dimensional assumptions are needed.
-- portable call pattern: stochastic optimization convergence proofs establish a
--   global lower-bound witness and use this theorem to discard a feasible
--   objective gap; the objective, feasible set, optimizer, and iterate vary.
-- counterargument checked: this is not paper-only traceability or a caller-side
--   expression because it packages the attained-infimum bridge with the final
--   ordered subtraction step; it is not duplicated by `objectiveGapIntegrand_nonneg`,
--   whose conclusion is an indexed integrand and whose lower-bound hypothesis is
--   already stated directly against a reference value.
-- coverage search: searched `objective infimum gap nonnegative lower bound` and
--   `sub objectiveInfimumValue nonnegative forall lower bound`; hits were the
--   partial `objectiveInfimumValue_le`, `objectiveInfimumValue_eq_of_forall_le`,
--   and `objectiveGapIntegrand_nonneg`, with no theorem for this feasible scalar gap.
-- minimal hypotheses: explicit bounded-below assumptions are avoided because the
--   optimizer lower-bound certificate supplies them through the equality bridge.

/-- Every feasible objective value lies above an attained feasible infimum.

Layer: Model | Gap: Level 0 (nonnegative objective gap to an attained infimum)
Proof: rewrite the feasible infimum using the attained-optimizer equality bridge,
then apply `sub_nonneg` to the pointwise optimality inequality.
Source: Mathlib conditionally complete linear-order `sInf` API and ordered real subtraction
Used in: convergence bounds that replace a feasible objective gap by a nonnegative
remainder after selecting a globally optimal comparison point
Book citation: book/FOML/StochasticZerothOrder.json#/assumptions/11
Origin algorithm: G. Lan, First-Order and Stochastic Optimization Methods for Machine Learning, randomized stochastic gradient-free method -/
theorem sub_objectiveInfimumValue_nonneg_of_forall_le
    {E : Type*} {X : Set E} {f : E → ℝ} {xStar x : E}
    (hxStar : xStar ∈ X) (hx : x ∈ X)
    (h_le : ∀ y : E, y ∈ X → f xStar ≤ f y) :
    0 ≤ f x - objectiveInfimumValue X f := by
  rw [objectiveInfimumValue_eq_of_forall_le hxStar h_le]
  exact sub_nonneg.mpr (h_le x hx)




-- Generalization plan (G0):
-- concept/name: AbsTaylorRemainderBound exposes the global absolute first-order
--   Taylor remainder bound for a smooth real objective; orig was
--   SmoothDescentBound.
-- generality used: arbitrary complete real inner-product normed additive group
--   E, objective f : E -> Real, and real smoothness scale L; no measure,
--   convexity, oracle, filtration, probability, bounded-below, or
--   finite-dimensional assumptions are needed to state the predicate.
-- portable call pattern: zeroth-order, stochastic-gradient, variance-reduced,
--   and proximal-descent proofs can instantiate E, f, and L when they need the
--   same two-sided Taylor-remainder estimate before pathwise descent or
--   finite-difference error algebra.
-- counterargument checked: existing SOptLib has
--   abs_taylor_remainder_le_of_hasGradientAt_lipschitzOn_convex, which derives
--   the pointwise inequality from selected-gradient hypotheses on a convex set;
--   this staging entry differs by naming the global property used as an
--   objective assumption and supplies the LipschitzGradientObjective bridge.
-- coverage search: searched "absolute Taylor remainder bound Lipschitz
--   gradient squared displacement", "taylor remainder le HasGradientAt
--   lipschitzOn convex", and Mathlib semantic search for an absolute
--   first-order Taylor remainder from Lipschitz derivative. Top hits were
--   SOptLib.abs_taylor_remainder_le_of_hasGradientAt_lipschitzOn_convex,
--   SOptLib.smooth_quadratic_upper_bound_of_hasGradientAt_lipschitzOn_convex,
--   and Mathlib one-dimensional Taylor remainder bounds; these are constructor
--   or proof components, not the named global predicate.
-- minimal hypotheses: all already minimal for the predicate; CompleteSpace is
--   retained because Mathlib's Hilbert-space gradient API and the staged
--   LipschitzGradientObjective API use it, while positivity of L is caller-side.

/-- A real objective satisfies the global absolute first-order Taylor remainder bound.

For every pair of points, the error between `f y` and the affine Taylor model
of `f` at `x` is bounded by `L / 2` times the squared displacement norm.

Layer: Model | Concept: absolute Taylor-remainder objective regularity
Proof: (definitional construction; universal absolute first-order Taylor
  remainder inequality using the Mathlib gradient)
Source: Mathlib Hilbert-space gradient notation and smooth first-order Taylor
  remainder calculus
Used in: randomized stochastic gradient-free smoothness assumptions before
  pathwise descent and finite-difference Taylor-remainder estimates
Book citation: book/FOML/StochasticZerothOrder.json#/assumptions/0/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic gradient-free method -/
def AbsTaylorRemainderBound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (L : ℝ) : Prop :=
  ∀ x y : E,
    |f y - f x - ⟪∇ f x, y - x⟫_ℝ| ≤ (L / 2) * ‖y - x‖ ^ (2 : ℕ)

/-- The absolute Taylor-remainder predicate unfolds to its pointwise inequality.

Layer: Model | Gap: Level 0 (absolute Taylor-remainder predicate unfolding)
Proof: by rfl after unfolding `AbsTaylorRemainderBound`.
Source: Mathlib Hilbert-space gradient notation and ordered real inequalities
Used in: randomized stochastic gradient-free proofs when replacing the source
  smooth-descent display by the Lean objective-regularity predicate
Book citation: book/FOML/StochasticZerothOrder.json#/assumptions/0/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic gradient-free method -/
@[simp] theorem AbsTaylorRemainderBound_def
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (L : ℝ) :
    AbsTaylorRemainderBound f L ↔
      ∀ x y : E,
        |f y - f x - ⟪∇ f x, y - x⟫_ℝ| ≤ (L / 2) * ‖y - x‖ ^ (2 : ℕ) :=
  Iff.rfl


end SOptLib
