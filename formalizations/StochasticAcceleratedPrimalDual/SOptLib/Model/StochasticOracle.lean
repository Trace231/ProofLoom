import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic
import SOptLib.Model.Carrier
import SOptLib.Model.Filtration
import SOptLib.Model.Iterates
import SOptLib.Model.Objective
import SOptLib.Model.Subdifferential
import Mathlib.Analysis.InnerProductSpace.Basic

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal InnerProductSpace

namespace SOptLib

open MeasureTheory ProbabilityTheory


/-- Oracle kernel obtained by composing a fixed decision parameter with a sampled
random variable.
Layer: Model | Concept: Oracle
Proof: (definitional construction; sample-indexed stochastic oracle map)
Source: Mathlib Bochner integral primitives for stochastic kernels
Used in: stochastic mirror descent oracle mean/variance definitions
Book citation: book/FOML/StochasticMirrorDescent.json#/assumptions/2/math
Origin algorithm: FOML stochastic mirror descent -/
def oracleKernel
    {Ω X S E : Type*} [MeasurableSpace Ω]
    (G : X → S → E) (ξ : Ω → S) (x : X) : Ω → E :=
  fun ω => G x (ξ ω)

/-- Paper-level well-definedness predicate for an oracle mean expectation.
Layer: Model | Gap: Level 0 (oracle mean integrability predicate)
Proof: definitional expansion
Source: Mathlib Bochner integral primitives for stochastic kernels
Used in: stochastic mirror descent oracle well-definedness
Book citation: book/FOML/StochasticMirrorDescent.json#/assumptions/2/math
Origin algorithm: FOML stochastic mirror descent -/
def oracleWellDefined
    {Ω X S E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (G : X → S → E) (ξ : Ω → S) (x : X) : Prop :=
  Integrable (oracleKernel G ξ x) μ

/-- Mean oracle `x ↦ ∫ ω, G x (ξ ω) ∂μ` for an abstract stochastic kernel.
Layer: Model | Concept: Oracle
Proof: (definitional construction; expectation of the stochastic oracle against its sample distribution)
Source: Mathlib Bochner integral primitives for stochastic kernels
Used in: stochastic mirror descent oracle mean/variance/random-iterate bridges
Book citation: book/FOML/StochasticMirrorDescent.json#/assumptions/2/math
Origin algorithm: FOML stochastic mirror descent -/
noncomputable def oracleMean
    {Ω X S E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (G : X → S → E) (ξ : Ω → S) (x : X) : E :=
  ∫ ω, oracleKernel G ξ x ω ∂μ

/-- Definitional formula for the oracle kernel.
Layer: Model | Gap: Level 0 (oracle kernel formula)
Proof: projection reduction
Source: Mathlib Bochner integral primitives for stochastic kernels
Used in: stochastic mirror descent oracle kernel bridges
Book citation: book/FOML/StochasticMirrorDescent.json#/assumptions/2/math
Origin algorithm: FOML stochastic mirror descent -/
@[simp]
theorem oracleKernel_apply
    {Ω X S E : Type*} [MeasurableSpace Ω]
    (G : X → S → E) (ξ : Ω → S) (x : X) (ω : Ω) :
    oracleKernel G ξ x ω = G x (ξ ω) := by
  rfl

/-- Definitional formula for the oracle mean as a Bochner integral.
Layer: Model | Gap: Level 0 (oracle mean formula)
Proof: expand the canonical oracle mean definition
Source: Mathlib Bochner integral primitives for stochastic kernels
Used in: stochastic mirror descent oracle mean bridge
Book citation: book/FOML/StochasticMirrorDescent.json#/assumptions/2/math
Origin algorithm: FOML stochastic mirror descent -/
theorem oracleMean_def
    {Ω X S E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (G : X → S → E) (ξ : Ω → S) (x : X) :
    oracleMean μ G ξ x = ∫ ω, G x (ξ ω) ∂μ := by
  rfl

/-- The oracle mean is the integral of the staged oracle kernel.
Layer: Model | Gap: Level 0 (oracle mean/kernel bridge)
Proof: definitional expansion
Source: Mathlib Bochner integral primitives for stochastic kernels
Used in: stochastic mirror descent oracle mean bridge
Book citation: book/FOML/StochasticMirrorDescent.json#/assumptions/2/math
Origin algorithm: FOML stochastic mirror descent -/
theorem oracleMean_eq_integral_kernel
    {Ω X S E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (G : X → S → E) (ξ : Ω → S) (x : X) :
    oracleMean μ G ξ x = ∫ ω, oracleKernel G ξ x ω ∂μ := by
  rfl

/-- A sampled oracle process is the oracle evaluated at the current random iterate and sample.

This bridge records that the time-indexed process `G t` agrees with
`oracle (x t ω) (ξ t ω)` whenever the oracle-process specification gives that
identity for every time.

Layer: Model | Gap: Level 0 (sampled oracle process identity)
Proof: specialize the oracle-process hypothesis `hG` at the requested time `t`;
  the resulting function equality is exactly the claim.
Source: Mathlib core logic and equality APIs
Used in: stochastic mirror descent oracle process tied to iterates and samples
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem sampledOracleProcess
    {Ω T P S E : Type*}
    (oracle : P → S → E)
    (x : T → Ω → P)
    (ξ : T → Ω → S)
    (G : T → Ω → E)
    (hG : ∀ t, G t = fun ω => oracle (x t ω) (ξ t ω))
    (t : T) :
    G t = fun ω => oracle (x t ω) (ξ t ω) := by
  exact hG t

/-- Definitional formula for a sampled stochastic oracle process along random iterates.

The process obtained at time `t` by evaluating `oracle` on the iterate `x t ω`
and sample `ξ t ω` is definitionally the corresponding function of `ω`.

Layer: Model | Gap: Level 0 (sampled stochastic oracle process formula)
Proof: by rfl after unfolding sampledOracleProcess_def.
Source: Mathlib logic and function definitional equality APIs
Used in: stochastic mirror descent oracle-gradient process construction
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem sampledOracleProcess_def
    {Ω X S E T : Type*}
    (oracle : X → S → E)
    (x : T → Ω → X)
    (ξ : T → Ω → S)
    (t : T) :
    (fun ω => oracle (x t ω) (ξ t ω)) =
      fun ω => oracle (x t ω) (ξ t ω) := by
  rfl

/-- A jointly measurable stochastic oracle is measurable when sampled along measurable
iterate and noise processes.

If an oracle kernel is measurable as a function on the product `X × S`, and
the iterate process `x` and sample process `ξ` are measurable, then
`ω ↦ oracle (x ω) (ξ ω)` is measurable.

Layer: Model | Gap: Level 0 (jointly measurable oracle sampling composition)
Proof: compose the joint oracle measurability with the measurable product map
  `ω ↦ (x ω, ξ ω)` built by `Measurable.prodMk`, then simplify the resulting
  function composition.
Source: Mathlib MeasureTheory measurability, product measurable spaces, and
  composition APIs
Used in: stochastic mirror descent sampled oracle response measurability for
  measurable iterates and stochastic gradients
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem sampledOracle_measurable
    {Ω X S E : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace S]
    [MeasurableSpace E]
    {oracle : X → S → E} {x : Ω → X} {ξ : Ω → S}
    (horacle : Measurable (fun p : X × S => oracle p.1 p.2))
    (hx : Measurable x) (hξ : Measurable ξ) :
    Measurable (fun ω => oracle (x ω) (ξ ω)) := by
  simpa [Function.comp_def] using horacle.comp (hx.prodMk hξ)

/-- Ambient totalization of a sampled stochastic oracle kernel from a feasible carrier.

Given a carrier-valued stochastic oracle `G` on feasible decisions `X`, `oracleAmbient`
extends the sampled kernel at scenario `s` to the ambient decision space by `totalizeOn`.

Layer: Model | Concept: Oracle
Proof: (definitional construction; `totalizeOn` wrapper sending feasible ambient
  points through the subtype carrier oracle and using the ambient zero value off `X`)
Source: Mathlib set/subtype function extension APIs
Used in: stochastic mirror descent sampled oracle evaluation after moving between
  feasible carrier points and ambient decision vectors
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
noncomputable def oracleAmbient
    {E S : Type*} [Zero E] (X : Set E) (G : {x : E // x ∈ X} → S → E) (s : S) :
    E → E :=
  totalizeOn X (fun x => G x s)

/-- The ambient sampled oracle agrees with the carrier oracle on feasible points.

For any feasible `x ∈ X`, evaluating the totalized ambient oracle at `x`
returns the original stochastic oracle value on the subtype carrier.

Layer: Model | Gap: Level 0 (ambient oracle feasibility agreement)
Proof: unfold `oracleAmbient` and apply `totalizeOn_of_mem` to the feasible
  point; the result is discharged by simplification.
Source: Mathlib set subtypes and totalized partial-function wrappers
Used in: stochastic mirror descent oracle evaluation on feasible iterates
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
@[simp]
theorem oracleAmbient_of_mem
    {E S : Type*} [Zero E] (X : Set E) (G : {x : E // x ∈ X} → S → E) (s : S)
    {x : E} (hx : x ∈ X) :
    oracleAmbient X G s x = G ⟨x, hx⟩ s := by
  simpa [oracleAmbient] using totalizeOn_of_mem X (fun x => G x s) hx

/-- Paper mean oracle `x ↦ E[G(x, ξ)]` for a stochastic kernel.

Layer: Model | Concept: Oracle
Proof: (definitional construction; paper stochastic-gradient mean oracle wrapper
  around `oracleMean`)
Source: Mathlib measure theory and Bochner integration APIs
Used in: stochastic mirror descent setup of the unbiased mean oracle for
  gradient samples `g` drawn through `proc.ξ`
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
noncomputable def paperMeanOracle
    {Ω X S E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (G : X → S → E) (ξ : Ω → S) : X → E :=
  oracleMean μ G ξ

/-- The paper mean oracle is definitionally the Bochner integral of the sampled oracle kernel.

For an oracle kernel `G` and sampling map `ξ`, `paperMeanOracle μ G ξ x`
unfolds to the expectation `∫ ω, G x (ξ ω) ∂μ`.

Layer: Model | Gap: Level 0 (paper mean oracle Bochner-integral unfolding)
Proof: by rfl after unfolding paperMeanOracle.
Source: Mathlib measure theory Bochner integral notation and definitional equality
Used in: stochastic mirror descent oracle mean expectation bridge
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem paperMeanOracle_def
    {Ω X S E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (G : X → S → E) (ξ : Ω → S) (x : X) :
    paperMeanOracle μ G ξ x = ∫ ω, G x (ξ ω) ∂μ := by
  rfl

/-- Paper mean-oracle well-definedness is exactly the required integrability hypothesis.

If the paper oracle sample map `ω ↦ G x (ξ ω)` is integrable under `μ`, then the
abstract `oracleWellDefined` predicate holds for the same oracle kernel at `x`.

Layer: Model | Gap: Level 0 (oracle well-definedness from integrability)
Proof: unfold `oracleWellDefined` and `oracleKernel`; `simpa` identifies the
  predicate with the supplied `Integrable` assumption.
Source: Mathlib measure theory integrability APIs
Used in: stochastic mirror descent paper mean-oracle well-definedness bridge
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem paperMeanOracle_wellDefined
    {Ω X S E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (G : X → S → E) (ξ : Ω → S) (x : X)
    (h_wellDefined : Integrable (fun ω => G x (ξ ω)) μ) :
    oracleWellDefined μ G ξ x := by
  simpa [oracleWellDefined, oracleKernel] using h_wellDefined

/-- Fixed-iterate squared stochastic oracle deviation kernel.

For an oracle sample map `G`, randomness `ξ`, dual norm `dualNorm`, and iterate `x`,
this is the measurable-kernel-shaped function
`ω ↦ dualNorm (G x (ξ ω) - oracleMean μ G ξ x) ^ 2` used to state oracle
variance assumptions.

Layer: Model | Concept: Oracle
Proof: (definitional construction; fixed-iterate oracle variance kernel built
  from the oracle mean and squared dual-norm deviation)
Source: Mathlib measure theory, Bochner integration, and normed-space APIs
Used in: stochastic mirror descent oracle variance control at a fixed iterate
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
noncomputable def oracleVarianceKernel
    {Ω X S E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (G : X → S → E) (ξ : Ω → S)
    (dualNorm : E → ℝ) (x : X) : Ω → ℝ :=
  fun ω => dualNorm (G x (ξ ω) - oracleMean μ G ξ x) ^ 2

/-- Paper-level well-definedness predicate for the fixed-iterate oracle variance.

`oracleVarianceWellDefined μ G ξ dualNorm x` records that the oracle variance
kernel at iterate `x` is integrable under the sampling law `μ`.

Layer: Model | Concept: Oracle
Proof: (definitional construction; fixed-iterate variance integrability predicate
  wrapping `Integrable (oracleVarianceKernel μ G ξ dualNorm x) μ`)
Source: Mathlib measure-theory Bochner integrability APIs
Used in: stochastic mirror descent oracle variance setup at a fixed iterate
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
def oracleVarianceWellDefined
    {Ω X S E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (G : X → S → E) (ξ : Ω → S)
    (dualNorm : E → ℝ) (x : X) : Prop :=
  Integrable (oracleVarianceKernel μ G ξ dualNorm x) μ

/-- Fixed-iterate oracle variance well-definedness is exactly integrability of its
variance kernel.

Layer: Model | Gap: Level 0 (oracle variance integrability specification)
Proof: by rfl after unfolding oracleVarianceWellDefined.
Source: Mathlib measure theory integrability APIs
Used in: stochastic mirror descent oracle variance well-definedness checks
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem oracleVarianceWellDefined_iff_integrable
    {Ω X S E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (G : X → S → E) (ξ : Ω → S)
    (dualNorm : E → ℝ) (x : X) :
    oracleVarianceWellDefined μ G ξ dualNorm x ↔
      Integrable (oracleVarianceKernel μ G ξ dualNorm x) μ := by
  rfl

/-- Fixed-iterate oracle variance expectation for stochastic mirror descent.

`oracleVariance μ G ξ dualNorm x` integrates the sampled squared deviation kernel
`oracleVarianceKernel μ G ξ dualNorm x` over the oracle noise law `μ`, modeling
`E[‖G x ξ - E[G x ξ]‖_*²]`.

Layer: Model | Concept: Oracle
Proof: (definitional construction; oracle variance as the measure integral of
  the fixed-iterate squared deviation kernel)
Source: Mathlib measure-theoretic integration APIs for real-valued kernels
Used in: stochastic mirror descent oracle variance bound at a fixed iterate
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
noncomputable def oracleVariance
    {Ω X S E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (G : X → S → E) (ξ : Ω → S)
    (dualNorm : E → ℝ) (x : X) : ℝ :=
  ∫ ω, oracleVarianceKernel μ G ξ dualNorm x ω ∂μ

/-- Fixed-iterate sampled squared oracle deviation kernel.

For an abstract stochastic oracle `G`, base sampling law `μ`, base sample map
`ξBase`, and time-indexed sample map `ξSample`, this kernel is
`ω ↦ dualNorm (G x (ξSample t ω) - oracleMean μ G ξBase x)^2`.

Layer: Model | Concept: Oracle
Proof: (definitional construction; pointwise sampled squared deviation from the
  oracle mean in the dual norm)
Source: Mathlib measure-theory kernels and normed-space algebra APIs
Used in: stochastic mirror descent oracle sample variance bounds
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
noncomputable def oracleSampleVarianceKernel
    {T Ω X S E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (G : X → S → E) (ξBase : Ω → S)
    (ξSample : T → Ω → S) (dualNorm : E → ℝ) (x : X) (t : T) : Ω → ℝ :=
  fun ω => dualNorm (G x (ξSample t ω) - oracleMean μ G ξBase x) ^ 2

/-- Paper-level well-definedness predicate for the fixed-iterate sampled oracle variance.

This predicate records that the oracle sample-variance kernel at iterate `x` and
time `t` is integrable with respect to the sampling measure.

Layer: Model | Concept: Oracle
Proof: (definitional construction; integrability wrapper for the sampled oracle
  variance kernel)
Source: Mathlib measure-theoretic integration and `Integrable` APIs
Used in: stochastic mirror descent oracle sample-variance well-definedness at a
  fixed iterate and time index
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
def oracleSampleVarianceWellDefined
    {T Ω X S E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (G : X → S → E) (ξBase : Ω → S)
    (ξSample : T → Ω → S) (dualNorm : E → ℝ) (x : X) (t : T) : Prop :=
  Integrable (oracleSampleVarianceKernel μ G ξBase ξSample dualNorm x t) μ

/-- Sampled oracle variance well-definedness is exactly integrability of its kernel.

For a fixed iterate `x` and time `t`, the abstract oracle variance
well-definedness predicate unfolds to integrability of the sampled squared
dual-norm deviation kernel.

Layer: Model | Gap: Level 0 (sampled oracle variance integrability predicate)
Proof: by rfl after unfolding oracleSampleVarianceWellDefined
Source: Mathlib measure theory integrability APIs
Used in: stochastic mirror descent oracle variance assumptions for sampled
  gradient noise
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem oracleSampleVarianceWellDefined_iff_integrable
    {T Ω X S E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (G : X → S → E) (ξBase : Ω → S)
    (ξSample : T → Ω → S) (dualNorm : E → ℝ) (x : X) (t : T) :
    oracleSampleVarianceWellDefined μ G ξBase ξSample dualNorm x t ↔
      Integrable (oracleSampleVarianceKernel μ G ξBase ξSample dualNorm x t) μ := by
  rfl

/-- Fixed-iterate sampled oracle variance expectation for stochastic mirror descent.

This is the expectation of the squared dual-norm deviation between the sampled
oracle value `G x (ξ_t ω)` and the base-sample oracle mean at the same iterate.

Layer: Model | Concept: Oracle
Proof: (definitional construction; Bochner-style scalar integral of the
  oracle sample variance kernel over the sampling measure)
Source: Mathlib measure integration APIs and stochastic-oracle variance model
Used in: stochastic mirror descent oracle sample-variance expectation setup
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
noncomputable def oracleSampleVariance
    {T Ω X S E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (G : X → S → E) (ξBase : Ω → S)
    (ξSample : T → Ω → S) (dualNorm : E → ℝ) (x : X) (t : T) : ℝ :=
  ∫ ω, oracleSampleVarianceKernel μ G ξBase ξSample dualNorm x t ω ∂μ

/-- Random-iterate squared oracle deviation kernel for an abstract stochastic oracle.

This kernel maps each outcome `ω` to the squared dual norm of the difference
between the sampled oracle vector at the random iterate `xProcess t ω` and the
oracle mean computed from the base noise law.

Layer: Model | Concept: Oracle
Proof: (definitional construction; pointwise random-iterate variance kernel
  built from `oracleMean`, oracle samples, and a squared dual norm)
Source: Mathlib measure-theory function kernels and normed additive group APIs
Used in: stochastic mirror descent random-iterate oracle variance control
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
noncomputable def oracleRandomIterateVarianceKernel
    {T Ω X S E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (G : X → S → E) (ξBase : Ω → S)
    (ξSample : T → Ω → S) (xProcess : T → Ω → X)
    (dualNorm : E → ℝ) (t : T) : Ω → ℝ :=
  fun ω =>
    dualNorm (G (xProcess t ω) (ξSample t ω) -
      oracleMean μ G ξBase (xProcess t ω)) ^ 2

/-- Well-definedness predicate for random-iterate stochastic oracle variance.

This records integrability of the squared oracle-deviation kernel obtained by
comparing sampled stochastic oracle values along a random iterate process.

Layer: Model | Concept: Oracle
Proof: (definitional construction; integrability wrapper for the random-iterate
  squared oracle deviation kernel).
Source: Mathlib measure theory integrability APIs
Used in: stochastic mirror descent random-iterate oracle variance control
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
def oracleRandomIterateVarianceWellDefined
    {T Ω X S E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (G : X → S → E) (ξBase : Ω → S)
    (ξSample : T → Ω → S) (xProcess : T → Ω → X)
    (dualNorm : E → ℝ) (t : T) : Prop :=
  Integrable (oracleRandomIterateVarianceKernel μ G ξBase ξSample xProcess dualNorm t) μ

/-- Random-iterate oracle variance well-definedness is exactly integrability of its kernel.

Layer: Model | Gap: Level 0 (random-iterate oracle variance well-definedness)
Proof: by rfl after unfolding oracleRandomIterateVarianceWellDefined.
Source: Mathlib MeasureTheory integrability APIs
Used in: stochastic mirror descent oracle variance assumption discharge for sampled random iterates
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem oracleRandomIterateVarianceWellDefined_iff_integrable
    {T Ω X S E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (G : X → S → E) (ξBase : Ω → S)
    (ξSample : T → Ω → S) (xProcess : T → Ω → X)
    (dualNorm : E → ℝ) (t : T) :
    oracleRandomIterateVarianceWellDefined μ G ξBase ξSample xProcess dualNorm t ↔
      Integrable
        (oracleRandomIterateVarianceKernel μ G ξBase ξSample xProcess dualNorm t) μ := by
  rfl

/-- Random-iterate oracle variance bound for an abstract stochastic oracle noise kernel.

This proposition packages integrability of the squared oracle deviation at a
selected iterate together with the bound of its expectation by `σ2`.

Layer: Model | Concept: Oracle
Proof: (definitional construction; conjunction of squared-deviation
  integrability and Bochner-integral variance bound)
Source: Mathlib measure theory integrability and Bochner integral APIs
Used in: stochastic mirror descent random-iterate oracle noise variance control
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
noncomputable def oracleRandomIterateVarianceBound
    {T Ω X S E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E]
    (μ : Measure Ω) (G : X → S → E) (g : X → E)
    (x : T → Ω → X) (Y : T → Ω → S)
    (normDual : E → ℝ) (σ2 : ℝ) (t : T) : Prop :=
  Integrable (fun ω => normDual (G (x t ω) (Y t ω) - g (x t ω)) ^ 2) μ ∧
    ∫ ω, normDual (G (x t ω) (Y t ω) - g (x t ω)) ^ 2 ∂μ ≤ σ2

/-- The random-iterate oracle variance predicate unfolds to integrability plus a second-moment bound.

For a fixed iterate index `t`, `oracleRandomIterateVarianceBound` is equivalent to
integrability of the squared oracle error and an integral bound by `σ2`.

Layer: Model | Gap: Level 0 (random-iterate oracle variance predicate unfolding)
Proof: by rfl after unfolding oracleRandomIterateVarianceBound.
Source: Mathlib measure theory integration APIs for `Integrable`, interval
  integrals over measures, and ordered real inequalities
Used in: stochastic mirror descent random-iterate stochastic-gradient variance
  assumption
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
@[simp]
theorem oracleRandomIterateVarianceBound_iff
    {T Ω X S E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E]
    (μ : Measure Ω) (G : X → S → E) (g : X → E)
    (x : T → Ω → X) (Y : T → Ω → S)
    (normDual : E → ℝ) (σ2 : ℝ) (t : T) :
    oracleRandomIterateVarianceBound μ G g x Y normDual σ2 t ↔
      Integrable (fun ω => normDual (G (x t ω) (Y t ω) - g (x t ω)) ^ 2) μ ∧
        ∫ ω, normDual (G (x t ω) (Y t ω) - g (x t ω)) ^ 2 ∂μ ≤ σ2 := by
  rfl

end SOptLib

namespace SOptLib

open MeasureTheory
open scoped BigOperators InnerProductSpace

/-- Time-indexed sampled oracle value as an oracle kernel evaluated at one sample coordinate.

`stagedOracleValue G ξ n x` is the stochastic process
`ω ↦ G x (ξ n ω)`, routed through the reusable oracle-kernel model definition.

Layer: Model | Concept: Oracle
Proof: (definitional construction; time-indexed sampled oracle wrapper around `oracleKernel`)
Source: Mathlib function evaluation APIs and SOptLib stochastic oracle kernel definitions
Used in: randomized stochastic mirror descent mini-batch oracle evaluation from a global sample stream
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic mirror descent -/
def stagedOracleValue
    {Ω X S E : Type*} [MeasurableSpace Ω]
    (G : X → S → E) (ξ : ℕ → Ω → S) (n : ℕ) (x : X) : Ω → E :=
  oracleKernel G (ξ n) x

/-- The staged oracle value unfolds to the sampled stochastic oracle at the chosen coordinate.

This pointwise identity preserves the paper notation `G(x, ξ_n)` after routing
the sampled value through the reusable oracle-kernel definition.

Layer: Model | Gap: Level 0 (time-indexed sampled oracle unfolding)
Proof: by rfl after unfolding `stagedOracleValue` and `oracleKernel`.
Source: Mathlib function evaluation APIs and SOptLib stochastic oracle kernel definitions
Used in: randomized stochastic mirror descent mini-batch oracle evaluation from a global sample stream
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic mirror descent -/
@[simp]
theorem stagedOracleValue_apply
    {Ω X S E : Type*} [MeasurableSpace Ω]
    (G : X → S → E) (ξ : ℕ → Ω → S) (n : ℕ) (x : X) (ω : Ω) :
    stagedOracleValue G ξ n x ω = G x (ξ n ω) := by
  rfl

/-- A time-indexed displayed oracle-call stream is measurable on every positive
index up to a finite horizon.

This is the reusable regularity predicate for displayed oracle responses that
are consumed by finite-prefix stochastic-process measurability inductions.

Layer: Model | Concept: Oracle
Proof: (definitional construction; positive finite-prefix measurability predicate for a time-indexed random stream)
Source: Mathlib MeasureTheory measurable-function APIs for stochastic processes
Used in: stochastic accelerated primal-dual source-boundary displayed oracle-call measurability
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/source_scope_notes
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic accelerated primal-dual method -/
def displayedOracleCallMeasurableUpTo
    {Ω F : Type*} [MeasurableSpace Ω] [MeasurableSpace F]
    (call : ℕ → Ω → F) (T : ℕ) : Prop :=
  ∀ i, 1 ≤ i → i ≤ T → Measurable (call i)

/-- Characterization of positive finite-prefix measurability for a displayed
oracle-call stream.

Layer: Model | Gap: Level 0 (displayed oracle-call prefix measurability formula)
Proof: by rfl after unfolding `displayedOracleCallMeasurableUpTo`.
Source: Mathlib MeasureTheory measurable-function APIs for stochastic processes
Used in: stochastic accelerated primal-dual source-boundary displayed oracle-call measurability
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/source_scope_notes
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic accelerated primal-dual method -/
theorem displayedOracleCallMeasurableUpTo_iff
    {Ω F : Type*} [MeasurableSpace Ω] [MeasurableSpace F]
    (call : ℕ → Ω → F) (T : ℕ) :
    displayedOracleCallMeasurableUpTo call T ↔
      ∀ i, 1 ≤ i → i ≤ T → Measurable (call i) := by
  rfl

/-- A displayed oracle-call prefix predicate gives measurability at each
positive index inside the horizon.

Layer: Model | Gap: Level 0 (displayed oracle-call prefix point access)
Proof: specialize the finite-prefix predicate at the requested index and bounds.
Source: Mathlib MeasureTheory measurable-function APIs for stochastic processes
Used in: stochastic accelerated primal-dual source-boundary displayed oracle-call measurability
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/source_scope_notes
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic accelerated primal-dual method -/
theorem displayedOracleCallMeasurableUpTo.measurable
    {Ω F : Type*} [MeasurableSpace Ω] [MeasurableSpace F]
    {call : ℕ → Ω → F} {T i : ℕ}
    (hcall : displayedOracleCallMeasurableUpTo call T)
    (hi_pos : 1 ≤ i) (hi_le : i ≤ T) :
    Measurable (call i) :=
  hcall i hi_pos hi_le

/-- Finite-prefix displayed oracle-call measurability is monotone when the
horizon is shortened.

Layer: Model | Gap: Level 0 (displayed oracle-call prefix horizon monotonicity)
Proof: compose the requested index bound with the horizon comparison, then use
  the longer-prefix predicate.
Source: Mathlib order transitivity and MeasureTheory measurable-function APIs
Used in: stochastic accelerated primal-dual source-boundary displayed oracle-call measurability
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/source_scope_notes
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic accelerated primal-dual method -/
theorem displayedOracleCallMeasurableUpTo_mono
    {Ω F : Type*} [MeasurableSpace Ω] [MeasurableSpace F]
    {call : ℕ → Ω → F} {T U : ℕ}
    (hcall : displayedOracleCallMeasurableUpTo call U) (hTU : T ≤ U) :
    displayedOracleCallMeasurableUpTo call T := by
  intro i hi_pos hi_le
  exact hcall i hi_pos (le_trans hi_le hTU)

@[deprecated displayedOracleCallMeasurableUpTo (since := "2026-06-14")]
abbrev DisplayedOracleCallMeasurableUpTo
    {Ω F : Type*} [MeasurableSpace Ω] [MeasurableSpace F]
    (call : ℕ → Ω → F) (T : ℕ) : Prop :=
  displayedOracleCallMeasurableUpTo call T

/-- Component semantics for a two-block stochastic-oracle residual stream.

At every active time, the first component is the sum of the centered
gradient-like and adjoint-like oracle residuals, while the second component is
the signed forward-oracle residual.

Layer: Model | Concept: Oracle
Proof: (definitional construction; active-index component predicate for a
  two-block oracle residual stream)
Source: stochastic saddle-point oracle notation with Mathlib additive-group
  operations and product types
Used in: stochastic accelerated primal-dual descent proofs when a guarded noise
  stream is unfolded into its sampled-oracle and deterministic-target terms
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
def twoBlockOracleResidualPairComponentSemantics
    {Ω State XG Y XF EX EY : Type*} [Sub EX] [Add EX] [Neg EY] [Add EY]
    (active : ℕ → Prop)
    (delta : ℕ → Ω → EX × EY)
    (state : ℕ → Ω → State)
    (primalQuery : State → XG) (nextDualQuery : State → Y)
    (forwardQuery : State → XF)
    (gradientSample : ℕ → XG → Ω → EX) (gradientTarget : ∀ i, active i → Ω → EX)
    (adjointSample : ℕ → Y → Ω → EX) (adjointTarget : Y → EX)
    (forwardSample : ℕ → Ω → EY) (forwardTarget : XF → EY) : Prop :=
  ∀ i, (hi : active i) → ∀ ω,
    (delta i ω).1 =
        gradientSample i (primalQuery (state i ω)) ω - gradientTarget i hi ω +
          (adjointSample i (nextDualQuery (state (i + 1) ω)) ω -
            adjointTarget (nextDualQuery (state (i + 1) ω))) ∧
      (delta i ω).2 =
        -forwardSample i ω + forwardTarget (forwardQuery (state i ω))

/-- Characterization of `twoBlockOracleResidualPairComponentSemantics` by its
guarded component equations.

Layer: Model | Gap: Level 0 (guarded two-block residual stream semantics)
Proof: by rfl after unfolding `twoBlockOracleResidualPairComponentSemantics`.
Source: stochastic saddle-point oracle notation with Mathlib additive-group
  operations and product types
Used in: stochastic accelerated primal-dual descent proofs when a guarded noise
  stream is unfolded into its sampled-oracle and deterministic-target terms
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
@[simp] theorem twoBlockOracleResidualPairComponentSemantics_def
    {Ω State XG Y XF EX EY : Type*} [Sub EX] [Add EX] [Neg EY] [Add EY]
    (active : ℕ → Prop)
    (delta : ℕ → Ω → EX × EY)
    (state : ℕ → Ω → State)
    (primalQuery : State → XG) (nextDualQuery : State → Y)
    (forwardQuery : State → XF)
    (gradientSample : ℕ → XG → Ω → EX) (gradientTarget : ∀ i, active i → Ω → EX)
    (adjointSample : ℕ → Y → Ω → EX) (adjointTarget : Y → EX)
    (forwardSample : ℕ → Ω → EY) (forwardTarget : XF → EY) :
    twoBlockOracleResidualPairComponentSemantics active delta state primalQuery
      nextDualQuery forwardQuery gradientSample gradientTarget adjointSample
      adjointTarget forwardSample forwardTarget ↔
      ∀ i, (hi : active i) → ∀ ω,
        (delta i ω).1 =
            gradientSample i (primalQuery (state i ω)) ω - gradientTarget i hi ω +
              (adjointSample i (nextDualQuery (state (i + 1) ω)) ω -
                adjointTarget (nextDualQuery (state (i + 1) ω))) ∧
          (delta i ω).2 =
            -forwardSample i ω + forwardTarget (forwardQuery (state i ω)) :=
  Iff.rfl

@[deprecated twoBlockOracleResidualPairComponentSemantics (since := "2026-06-14")]
abbrev Algorithm43SourceBoundaryDeltaSemantics
    {Ω State XG Y XF EX EY : Type*} [Sub EX] [Add EX] [Neg EY] [Add EY]
    (active : ℕ → Prop)
    (delta : ℕ → Ω → EX × EY)
    (state : ℕ → Ω → State)
    (primalQuery : State → XG) (nextDualQuery : State → Y)
    (forwardQuery : State → XF)
    (gradientSample : ℕ → XG → Ω → EX) (gradientTarget : ∀ i, active i → Ω → EX)
    (adjointSample : ℕ → Y → Ω → EX) (adjointTarget : Y → EX)
    (forwardSample : ℕ → Ω → EY) (forwardTarget : XF → EY) : Prop :=
  twoBlockOracleResidualPairComponentSemantics active delta state primalQuery nextDualQuery
    forwardQuery gradientSample gradientTarget adjointSample adjointTarget forwardSample
    forwardTarget

/-- Finite-horizon feasibility coverage for one-based generated oracle queries.

For every one-based time index in `Finset.Icc 1 T` and every outcome, the
generated query value lies in the feasible set `X`.

Layer: Model | Concept: Oracle
Proof: (definitional construction; one-based finite-horizon membership
  predicate for generated stochastic-oracle queries)
Source: stochastic approximation oracle-domain assumptions and Mathlib finite
  interval indexing APIs
Used in: stochastic accelerated primal-dual generated oracle query feasibility
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
def finiteHorizonOracleQueryCoverage
    {Ω E : Type*}
    (query : ∀ i, 1 ≤ i → Ω → E) (X : Set E) (T : ℕ) : Prop :=
  ∀ i, ∀ hi : i ∈ Finset.Icc 1 T, ∀ ω : Ω,
    query i (Finset.mem_Icc.mp hi).1 ω ∈ X

/-- The finite-horizon oracle-query coverage predicate unfolds to pointwise
membership on `Finset.Icc 1 T`.

Layer: Model | Gap: Level 0 (finite-horizon oracle-query coverage unfolding)
Proof: by rfl after unfolding `finiteHorizonOracleQueryCoverage`.
Source: stochastic approximation oracle-domain assumptions and Mathlib finite
  interval indexing APIs
Used in: stochastic accelerated primal-dual generated oracle query feasibility
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
@[simp]
theorem finiteHorizonOracleQueryCoverage_def
    {Ω E : Type*}
    (query : ∀ i, 1 ≤ i → Ω → E) (X : Set E) (T : ℕ) :
    finiteHorizonOracleQueryCoverage query X T =
      (∀ i, ∀ hi : i ∈ Finset.Icc 1 T, ∀ ω : Ω,
        query i (Finset.mem_Icc.mp hi).1 ω ∈ X) := by
  rfl

/-- Finite-horizon oracle-query coverage gives feasibility of any covered
query point.

Layer: Model | Gap: Level 0 (finite-horizon oracle-query coverage projection)
Proof: specialize the pointwise coverage predicate at the requested time,
  interval-membership proof, and outcome.
Source: stochastic approximation oracle-domain assumptions and Mathlib finite
  interval indexing APIs
Used in: stochastic accelerated primal-dual generated oracle query feasibility
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem finiteHorizonOracleQueryCoverage.mem
    {Ω E : Type*} {query : ∀ i, 1 ≤ i → Ω → E} {X : Set E} {T i : ℕ}
    (h : finiteHorizonOracleQueryCoverage query X T)
    (hi : i ∈ Finset.Icc 1 T) (ω : Ω) :
    query i (Finset.mem_Icc.mp hi).1 ω ∈ X := by
  exact h i hi ω

@[deprecated finiteHorizonOracleQueryCoverage (since := "2026-06-14")]
abbrev GeneratedOracleQueryCoverage
    {Ω E : Type*}
    (query : ∀ i, 1 ≤ i → Ω → E) (X : Set E) (T : ℕ) : Prop :=
  finiteHorizonOracleQueryCoverage query X T

@[deprecated finiteHorizonOracleQueryCoverage (since := "2026-06-14")]
abbrev GeneratedAxQueryCoverage
    {Ω E : Type*}
    (query : ∀ i, 1 ≤ i → Ω → E) (X : Set E) (T : ℕ) : Prop :=
  finiteHorizonOracleQueryCoverage query X T

/-- Finite-horizon realization of a generated stream by a fixed-domain oracle.

For every one-based time in the horizon and every outcome, the generated query
is feasible and the supplied sample stream equals the carrier-domain oracle
sample evaluated at that feasible query.

Layer: Model | Concept: Oracle
Proof: (definitional construction; dependent finite-horizon realization
  contract combining feasible generated queries with fixed-domain oracle
  equality)
Source: stochastic approximation oracle-domain assumptions and Mathlib set
  subtype APIs
Used in: stochastic accelerated primal-dual generated `A_x` oracle realization
  before measurability and martingale-noise arguments
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/3/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
def generatedOracleRealization
    {Ω E Y : Type*} (X : Set E)
    (sample : ℕ → Ω → Y)
    (query : ∀ i, 1 ≤ i → Ω → E)
    (oracleSample : ℕ → {x : E // x ∈ X} → Ω → Y)
    (T : ℕ) : Prop :=
  ∀ i, ∀ hi : i ∈ Finset.Icc 1 T, ∀ ω : Ω,
    ∃ hmem : query i (Finset.mem_Icc.mp hi).1 ω ∈ X,
      sample i ω =
        oracleSample i ⟨query i (Finset.mem_Icc.mp hi).1 ω, hmem⟩ ω

/-- The generated-oracle realization predicate unfolds to feasibility plus
fixed-domain oracle equality at every covered positive time.

Layer: Model | Gap: Level 0 (generated oracle realization unfolding)
Proof: by rfl after unfolding `generatedOracleRealization`.
Source: stochastic approximation oracle-domain assumptions and Mathlib set
  subtype APIs
Used in: stochastic accelerated primal-dual generated fixed-domain oracle
  realization at extrapolated feasible queries
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/3/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
@[simp]
theorem generatedOracleRealization_def
    {Ω E Y : Type*} (X : Set E)
    (sample : ℕ → Ω → Y)
    (query : ∀ i, 1 ≤ i → Ω → E)
    (oracleSample : ℕ → {x : E // x ∈ X} → Ω → Y)
    (T : ℕ) :
    generatedOracleRealization X sample query oracleSample T =
      (∀ i, ∀ hi : i ∈ Finset.Icc 1 T, ∀ ω : Ω,
        ∃ hmem : query i (Finset.mem_Icc.mp hi).1 ω ∈ X,
          sample i ω =
            oracleSample i ⟨query i (Finset.mem_Icc.mp hi).1 ω, hmem⟩ ω) := by
  rfl

/-- A generated-oracle realization supplies finite-horizon feasible-query
coverage.

Layer: Model | Gap: Level 0 (generated oracle realization feasibility projection)
Proof: specialize the realization contract and project the membership witness
  from the dependent existential.
Source: stochastic approximation oracle-domain assumptions and Mathlib set
  subtype APIs
Used in: stochastic accelerated primal-dual generated oracle query coverage
  extracted from explicit fixed-domain oracle realization
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/3/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem generatedOracleRealization_coverage
    {Ω E Y : Type*} {X : Set E}
    {sample : ℕ → Ω → Y}
    {query : ∀ i, 1 ≤ i → Ω → E}
    {oracleSample : ℕ → {x : E // x ∈ X} → Ω → Y}
    {T : ℕ}
    (h : generatedOracleRealization X sample query oracleSample T) :
    finiteHorizonOracleQueryCoverage query X T := by
  intro i hi ω
  exact (h i hi ω).1

/-- A generated-oracle realization identifies the generated sample with the
fixed-domain oracle sample at any supplied feasibility proof.

Layer: Model | Gap: Level 0 (generated oracle realization sample equality)
Proof: specialize the realization contract, then use proof irrelevance for the
  subtype membership proof to rewrite the carrier argument.
Source: stochastic approximation oracle-domain assumptions and Mathlib subtype
  proof-irrelevance APIs
Used in: stochastic accelerated primal-dual replacement of generated `A_x`
  samples by fixed-domain oracle evaluations
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/3/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem generatedOracleRealization_sample_eq
    {Ω E Y : Type*} {X : Set E}
    {sample : ℕ → Ω → Y}
    {query : ∀ i, 1 ≤ i → Ω → E}
    {oracleSample : ℕ → {x : E // x ∈ X} → Ω → Y}
    {T i : ℕ} {hi : i ∈ Finset.Icc 1 T} {ω : Ω}
    (h : generatedOracleRealization X sample query oracleSample T)
    (hmem : query i (Finset.mem_Icc.mp hi).1 ω ∈ X) :
    sample i ω =
      oracleSample i ⟨query i (Finset.mem_Icc.mp hi).1 ω, hmem⟩ ω := by
  rcases h i hi ω with ⟨hmem', heq⟩
  simpa using heq

@[deprecated generatedOracleRealization (since := "2026-06-14")]
abbrev GeneratedOracleRealization
    {Ω E Y : Type*} (X : Set E)
    (sample : ℕ → Ω → Y)
    (query : ∀ i, 1 ≤ i → Ω → E)
    (oracleSample : ℕ → {x : E // x ∈ X} → Ω → Y)
    (T : ℕ) : Prop :=
  generatedOracleRealization X sample query oracleSample T

@[deprecated generatedOracleRealization (since := "2026-06-14")]
abbrev GeneratedAxOracleRealization
    {Ω E Y : Type*} (X : Set E)
    (sample : ℕ → Ω → Y)
    (query : ∀ i, 1 ≤ i → Ω → E)
    (oracleSample : ℕ → {x : E // x ∈ X} → Ω → Y)
    (T : ℕ) : Prop :=
  generatedOracleRealization X sample query oracleSample T

namespace GeneratedOracleStreamMeasurableUpTo

/-- A realized generated oracle stream is measurable on a finite positive prefix.

If each generated query is measurable and a supplied stream agrees pointwise
with a jointly measurable fixed-domain stochastic oracle evaluated at that
query and a measurable sample coordinate, then the stream is measurable at
every positive index up to the horizon.

Layer: Model | Gap: Level 1 (generated oracle realization stream measurability)
Proof: for each covered index, package the random query with the feasibility
  witness supplied by the realization contract, compose the jointly measurable
  oracle with the measurable query/sample pair, then transport measurability
  across the realization equality.
Source: Mathlib MeasureTheory product/subtype measurable-function APIs and
  SOptLib sampled stochastic-oracle composition
Used in: stochastic accelerated primal-dual generated fixed-domain `A_x` oracle
  stream measurability before recursive extension-process induction
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/3/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem of_realization
    {Ω X S Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace S]
    [MeasurableSpace Y]
    {C : Set X}
    {sample : ℕ → Ω → Y}
    {query : ∀ i, 1 ≤ i → Ω → X}
    {oracle : {x : X // x ∈ C} → S → Y}
    {ξ : ℕ → Ω → S}
    {T : ℕ}
    (horacle : Measurable (fun p : {x : X // x ∈ C} × S => oracle p.1 p.2))
    (hξ : ∀ i, Measurable (ξ i))
    (hrealize :
      generatedOracleRealization C sample
        query
        (fun i x ω => oracle x (ξ i ω))
        T)
    (hquery : ∀ i, (hi : 1 ≤ i) → i ≤ T → Measurable (query i hi)) :
    displayedOracleCallMeasurableUpTo sample T := by
  intro i hi_pos hi_le
  let hi : i ∈ Finset.Icc 1 T := Finset.mem_Icc.mpr ⟨hi_pos, hi_le⟩
  let q : Ω → {x : X // x ∈ C} := fun ω =>
    ⟨query i hi_pos ω, (hrealize i hi ω).1⟩
  have hq : Measurable q := by
    simpa [q] using (hquery i hi_pos hi_le).subtype_mk
  have hsample : Measurable (fun ω => oracle (q ω) (ξ i ω)) := by
    simpa using
      SOptLib.sampledOracle_measurable
        (oracle := oracle)
        (x := q)
        (ξ := ξ i)
        horacle
        hq
        (hξ i)
  have hEq : sample i = fun ω => oracle (q ω) (ξ i ω) := by
    funext ω
    simpa [q] using (hrealize i hi ω).2
  simpa [hEq] using hsample

end GeneratedOracleStreamMeasurableUpTo

@[deprecated GeneratedOracleStreamMeasurableUpTo.of_realization (since := "2026-06-14")]
theorem GeneratedAxStreamMeasurableUpTo_of_realization
    {Ω X S Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace S]
    [MeasurableSpace Y]
    {C : Set X}
    {sample : ℕ → Ω → Y}
    {query : ∀ i, 1 ≤ i → Ω → X}
    {oracle : {x : X // x ∈ C} → S → Y}
    {ξ : ℕ → Ω → S}
    {T : ℕ}
    (horacle : Measurable (fun p : {x : X // x ∈ C} × S => oracle p.1 p.2))
    (hξ : ∀ i, Measurable (ξ i))
    (hrealize :
      generatedOracleRealization C sample
        query
        (fun i x ω => oracle x (ξ i ω))
        T)
    (hquery : ∀ i, (hi : 1 ≤ i) → i ≤ T → Measurable (query i hi)) :
    displayedOracleCallMeasurableUpTo sample T :=
  GeneratedOracleStreamMeasurableUpTo.of_realization horacle hξ hrealize hquery

@[deprecated GeneratedOracleStreamMeasurableUpTo.of_realization (since := "2026-06-14")]
theorem GeneratedOracleStreamMeasurableUpTo_of_realization
    {Ω X S Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace S]
    [MeasurableSpace Y]
    {C : Set X}
    {sample : ℕ → Ω → Y}
    {query : ∀ i, 1 ≤ i → Ω → X}
    {oracle : {x : X // x ∈ C} → S → Y}
    {ξ : ℕ → Ω → S}
    {T : ℕ}
    (horacle : Measurable (fun p : {x : X // x ∈ C} × S => oracle p.1 p.2))
    (hξ : ∀ i, Measurable (ξ i))
    (hrealize :
      generatedOracleRealization C sample
        query
        (fun i x ω => oracle x (ξ i ω))
        T)
    (hquery : ∀ i, (hi : 1 ≤ i) → i ≤ T → Measurable (query i hi)) :
    displayedOracleCallMeasurableUpTo sample T :=
  GeneratedOracleStreamMeasurableUpTo.of_realization horacle hξ hrealize hquery

/-- Per-index square-moment bounds aggregate to a finite-window moment bound.

For a finite family of oracle-noise vectors, if every squared norm is
integrable and its expectation is bounded by the corresponding deterministic
budget, then the finite sum of squared norms is integrable and its expectation
is bounded by the finite sum of the budgets.

Layer: Model | Gap: Level 1 (finite oracle-noise square-moment aggregation)
Proof: build the membership-dependent summand, apply Mathlib finite-sum
  integrability, commute the Bochner integral through the finite sum, and
  compare the resulting scalar finite sums pointwise.
Source: Mathlib Bochner integrability, finite-sum integral linearity, and
  ordered real finite-sum APIs
Used in: stochastic accelerated primal-dual same-sample adjoint-noise finite
  moment guard before primal square-noise aggregation
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem finite_oracle_noise_sq_moment_sum_integrable_and_integral_le
    {ι Ω E : Type*} [DecidableEq ι] [MeasurableSpace Ω] [NormedAddCommGroup E]
    {P : Measure Ω} {I : Finset ι} {delta : ∀ i, i ∈ I → Ω → E}
    {bound : ι → ℝ}
    (hdelta_int :
      ∀ i, ∀ hi : i ∈ I, Integrable (fun ω => ‖delta i hi ω‖ ^ 2) P)
    (hdelta_bound :
      ∀ i, ∀ hi : i ∈ I, ∫ ω, ‖delta i hi ω‖ ^ 2 ∂P ≤ bound i) :
    Integrable
        (fun ω =>
          Finset.sum I (fun i =>
            if hi : i ∈ I then ‖delta i hi ω‖ ^ 2 else 0)) P ∧
      ∫ ω,
          Finset.sum I (fun i =>
            if hi : i ∈ I then ‖delta i hi ω‖ ^ 2 else 0) ∂P ≤
        Finset.sum I bound := by
  classical
  let term : ι → Ω → ℝ := fun i ω =>
    if hi : i ∈ I then ‖delta i hi ω‖ ^ 2 else 0
  have hterm_int : ∀ i ∈ I, Integrable (term i) P := by
    intro i hi
    have hterm_eq :
        term i = (fun ω => ‖delta i hi ω‖ ^ 2) := by
      funext ω
      simp [term, hi]
    simpa [hterm_eq] using hdelta_int i hi
  have hterm_bound : ∀ i ∈ I, ∫ ω, term i ω ∂P ≤ bound i := by
    intro i hi
    have hterm_eq :
        term i = (fun ω => ‖delta i hi ω‖ ^ 2) := by
      funext ω
      simp [term, hi]
    simpa [hterm_eq] using hdelta_bound i hi
  constructor
  · simpa [term] using
      (integrable_finset_sum (s := I) (f := term) hterm_int)
  · calc
      ∫ ω, Finset.sum I (fun i => term i ω) ∂P
          = Finset.sum I (fun i => ∫ ω, term i ω ∂P) := by
            rw [integral_finset_sum I hterm_int]
      _ ≤ Finset.sum I bound := by
            exact Finset.sum_le_sum hterm_bound

/-- Per-index same-sample oracle-noise regularity and second-moment control.

For every index in a finite window, the oracle-noise vector is a.e. strongly
measurable, its squared norm is integrable, and its second moment is bounded by
the common variance budget `sigma2`.

Layer: Model | Concept: Oracle
Proof: (definitional construction; finite-index package of oracle-noise
  measurability, squared-norm integrability, and a uniform second-moment budget)
Source: Mathlib Bochner integrability and a.e. strong-measurability APIs
Used in: stochastic accelerated primal-dual same-sample adjoint-noise
  component bounds before primal square-noise aggregation
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
def sameSampleOracleNoisePerIndexMomentBound
    {ι Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) (I : Finset ι) (delta : ∀ i, i ∈ I → Ω → E)
    (sigma2 : ℝ) : Prop :=
  (∀ i, ∀ hi : i ∈ I, AEStronglyMeasurable (delta i hi) P) ∧
    (∀ i, ∀ hi : i ∈ I,
      Integrable (fun ω => ‖delta i hi ω‖ ^ 2) P) ∧
    (∀ i, ∀ hi : i ∈ I,
      ∫ ω, ‖delta i hi ω‖ ^ 2 ∂P ≤ sigma2)

@[deprecated finite_oracle_noise_sq_moment_sum_integrable_and_integral_le (since := "2026-06-14")]
theorem GeneratedDeltaXASameSampleMomentBound
    {ι Ω E : Type*} [DecidableEq ι] [MeasurableSpace Ω] [NormedAddCommGroup E]
    {P : Measure Ω} {I : Finset ι} {delta : ∀ i, i ∈ I → Ω → E}
    {bound : ι → ℝ}
    (hdelta_int :
      ∀ i, ∀ hi : i ∈ I, Integrable (fun ω => ‖delta i hi ω‖ ^ 2) P)
    (hdelta_bound :
      ∀ i, ∀ hi : i ∈ I, ∫ ω, ‖delta i hi ω‖ ^ 2 ∂P ≤ bound i) :
    Integrable
        (fun ω =>
          Finset.sum I (fun i =>
            if hi : i ∈ I then ‖delta i hi ω‖ ^ 2 else 0)) P ∧
      ∫ ω,
          Finset.sum I (fun i =>
            if hi : i ∈ I then ‖delta i hi ω‖ ^ 2 else 0) ∂P ≤
        Finset.sum I bound :=
  finite_oracle_noise_sq_moment_sum_integrable_and_integral_le hdelta_int hdelta_bound

@[deprecated sameSampleOracleNoisePerIndexMomentBound (since := "2026-06-14")]
abbrev SameSampleOracleNoisePerIndexMomentBound
    {ι Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) (I : Finset ι) (delta : ∀ i, i ∈ I → Ω → E)
    (sigma2 : ℝ) : Prop :=
  sameSampleOracleNoisePerIndexMomentBound P I delta sigma2

@[deprecated sameSampleOracleNoisePerIndexMomentBound (since := "2026-06-14")]
abbrev GeneratedDeltaXASameSamplePerIndexMomentBound
    {ι Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) (I : Finset ι) (delta : ∀ i, i ∈ I → Ω → E)
    (sigma2 : ℝ) : Prop :=
  sameSampleOracleNoisePerIndexMomentBound P I delta sigma2

/-- A finite window of residuals has an integrable squared-norm sum bounded by
a deterministic budget.

For a residual family indexed by membership in a finite set `I`, this predicate
records exactly the aggregate finite-horizon second-moment condition used in
stochastic-optimization noise estimates: integrability of the sum of squared
norms and an upper bound by the corresponding deterministic budget sum.

Layer: Model | Concept: Oracle
Proof: (definitional construction; finite-window residual square-moment
  predicate with a deterministic aggregate budget)
Source: stochastic approximation finite-horizon second-moment estimates and
  Mathlib Bochner integrability APIs for finite sums
Used in: stochastic accelerated primal-dual mixed-center gradient residual
  moment condition before generated descent aggregation
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
def finiteWindowResidualSqMomentBound
    {Ω E ι : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [DecidableEq ι]
    (P : Measure Ω) (I : Finset ι) (residual : ∀ i, i ∈ I → Ω → E)
    (budget : ι → ℝ) : Prop :=
  Integrable
      (fun ω =>
        Finset.sum I (fun i =>
          if hi : i ∈ I then ‖residual i hi ω‖ ^ 2 else 0))
      P ∧
    ∫ ω,
        Finset.sum I (fun i =>
          if hi : i ∈ I then ‖residual i hi ω‖ ^ 2 else 0)
        ∂P ≤
      Finset.sum I budget

/-- The finite-window residual square-moment predicate unfolds to aggregate
integrability and a deterministic budget bound.

Layer: Model | Gap: Level 0 (finite-window residual moment unfolding)
Proof: by rfl after unfolding `finiteWindowResidualSqMomentBound`.
Source: stochastic approximation finite-horizon second-moment estimates and
  Mathlib Bochner integrability APIs for finite sums
Used in: stochastic accelerated primal-dual mixed-center gradient residual
  moment condition unfolding
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
@[simp]
theorem finiteWindowResidualSqMomentBound_def
    {Ω E ι : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [DecidableEq ι]
    (P : Measure Ω) (I : Finset ι) (residual : ∀ i, i ∈ I → Ω → E)
    (budget : ι → ℝ) :
    finiteWindowResidualSqMomentBound P I residual budget =
      (Integrable
          (fun ω =>
            Finset.sum I (fun i =>
              if hi : i ∈ I then ‖residual i hi ω‖ ^ 2 else 0))
          P ∧
        ∫ ω,
            Finset.sum I (fun i =>
              if hi : i ∈ I then ‖residual i hi ω‖ ^ 2 else 0)
            ∂P ≤
          Finset.sum I budget) := by
  rfl

@[deprecated finiteWindowResidualSqMomentBound (since := "2026-06-14")]
abbrev MixedCenterResidualFiniteMomentBound
    {Ω E ι : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [DecidableEq ι]
    (P : Measure Ω) (I : Finset ι) (residual : ∀ i, i ∈ I → Ω → E)
    (budget : ι → ℝ) : Prop :=
  finiteWindowResidualSqMomentBound P I residual budget

@[deprecated finiteWindowResidualSqMomentBound (since := "2026-06-14")]
abbrev GeneratedDeltaXHatfMixedCenterMomentBound
    {Ω E ι : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [DecidableEq ι]
    (P : Measure Ω) (I : Finset ι) (residual : ∀ i, i ∈ I → Ω → E)
    (budget : ι → ℝ) : Prop :=
  finiteWindowResidualSqMomentBound P I residual budget

/-- A finite residual process has per-index square moments and an aggregate
finite-window bound under a deterministic mismatch budget.

For a membership-dependent residual family `delta` on a finite window `I`, the
package records a budget witness `M`, vector and squared-norm measurability,
per-index square integrability and expectation bounds, and the resulting
finite-window integrability and expectation bound.  The scalar `sigma2` is the
base oracle second-moment budget before the residual-specific mismatch
contribution.

Layer: Model | Concept: Oracle
Proof: (definitional construction; finite residual square-moment package with
  explicit deterministic mismatch budget)
Source: stochastic approximation finite-horizon second-moment estimates and
  Mathlib Bochner integrability APIs for finite sums
Used in: stochastic accelerated primal-dual mixed-center gradient residual
  moment package before primal square-noise aggregation
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
def mixedCenterResidualFiniteMomentStep
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) (I : Finset ℕ) (delta : ∀ i, i ∈ I → Ω → E)
    (mismatchBudget : (ℕ → ℝ) → Prop) (sigma2 : ℝ) : Prop :=
  ∃ M : ℕ → ℝ,
    mismatchBudget M ∧
    (∀ i, ∀ _hi : i ∈ I,
      AEStronglyMeasurable (fun ω => delta i _hi ω) P) ∧
    (∀ i, ∀ _hi : i ∈ I,
      AEStronglyMeasurable (fun ω => ‖delta i _hi ω‖ ^ 2) P) ∧
    (∀ i, ∀ _hi : i ∈ I,
      Integrable (fun ω => ‖delta i _hi ω‖ ^ 2) P) ∧
    (∀ i, ∀ _hi : i ∈ I,
      ∫ ω, ‖delta i _hi ω‖ ^ 2 ∂P ≤ 2 * sigma2 + 2 * M i) ∧
    Integrable
      (fun ω =>
        Finset.sum I (fun i =>
          if hi : i ∈ I then ‖delta i hi ω‖ ^ 2 else 0)) P ∧
    ∫ ω,
        Finset.sum I (fun i =>
          if hi : i ∈ I then ‖delta i hi ω‖ ^ 2 else 0) ∂P ≤
      Finset.sum I (fun i => 2 * sigma2 + 2 * M i)

@[deprecated mixedCenterResidualFiniteMomentStep (since := "2026-06-14")]
abbrev MixedCenterResidualFiniteMomentStep
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) (I : Finset ℕ) (delta : ∀ i, i ∈ I → Ω → E)
    (mismatchBudget : (ℕ → ℝ) → Prop) (sigma2 : ℝ) : Prop :=
  mixedCenterResidualFiniteMomentStep P I delta mismatchBudget sigma2

@[deprecated mixedCenterResidualFiniteMomentStep (since := "2026-06-14")]
abbrev GeneratedDeltaXHatfSourceMomentStep
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) (I : Finset ℕ) (delta : ∀ i, i ∈ I → Ω → E)
    (mismatchBudget : (ℕ → ℝ) → Prop) (sigma2 : ℝ) : Prop :=
  mixedCenterResidualFiniteMomentStep P I delta mismatchBudget sigma2

/-- Finite-index oracle-noise cross moments are nonpositive.

For each index in a finite window, the expected scaled inner product between
two Hilbert-valued oracle-noise components is bounded above by zero.

Layer: Model | Concept: Oracle
Proof: (definitional construction; finite-index package of nonpositive
  Hilbert-space oracle-noise cross moments)
Source: Mathlib Bochner integral notation and real Hilbert-space inner-product
  APIs
Used in: stochastic accelerated primal-dual same-sample primal-noise square
  aggregation before Eq. (4.4.73)
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
def oracleNoiseCrossMomentNonpos
    {ι Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (P : Measure Ω) (I : Finset ι)
    (delta1 delta2 : ∀ i, i ∈ I → Ω → E) : Prop :=
  ∀ i, ∀ hi : i ∈ I,
    ∫ ω, 2 * ⟪delta1 i hi ω, delta2 i hi ω⟫_ℝ ∂P ≤ 0

@[deprecated oracleNoiseCrossMomentNonpos (since := "2026-06-14")]
abbrev OracleNoiseCrossMomentNonpos
    {ι Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (P : Measure Ω) (I : Finset ι)
    (delta1 delta2 : ∀ i, i ∈ I → Ω → E) : Prop :=
  oracleNoiseCrossMomentNonpos P I delta1 delta2

@[deprecated oracleNoiseCrossMomentNonpos (since := "2026-06-14")]
abbrev GeneratedDeltaXHatfXACrossMomentNonpos
    {ι Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (P : Measure Ω) (I : Finset ι)
    (delta1 delta2 : ∀ i, i ∈ I → Ω → E) : Prop :=
  oracleNoiseCrossMomentNonpos P I delta1 delta2

/-- A finite window of gradient mismatches has per-index square moments bounded
by a deterministic budget.

For a membership-dependent mismatch family on a finite window `I`, this
predicate records the pointwise-in-time second-moment obligations used when a
deterministic model-drift term is kept separate from stochastic oracle noise.

Layer: Model | Concept: Oracle
Proof: (definitional construction; finite-window gradient-mismatch
  square-moment predicate with deterministic per-index budgets)
Source: stochastic approximation finite-horizon second-moment estimates and
  Mathlib Bochner integrability APIs
Used in: stochastic accelerated primal-dual deterministic gradient-mismatch
  budget before residual-plus-mismatch moment aggregation
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
def gradientMismatchFiniteMomentBudget
    {Ω E ι : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) (I : Finset ι) (mismatch : ∀ i, i ∈ I → Ω → E)
    (budget : ι → ℝ) : Prop :=
  (∀ i, ∀ hi : i ∈ I,
    Integrable (fun ω => ‖mismatch i hi ω‖ ^ 2) P) ∧
  (∀ i, ∀ hi : i ∈ I,
    ∫ ω, ‖mismatch i hi ω‖ ^ 2 ∂P ≤ budget i)

/-- The integrability component of a finite-window gradient-mismatch budget.

Layer: Model | Gap: Level 0 (finite-window gradient-mismatch budget projection)
Proof: first projection of `gradientMismatchFiniteMomentBudget`.
Source: stochastic approximation finite-horizon second-moment estimates and
  Mathlib Bochner integrability APIs
Used in: stochastic accelerated primal-dual deterministic gradient-mismatch
  budget projection
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem gradientMismatchFiniteMomentBudget.integrable
    {Ω E ι : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {P : Measure Ω} {I : Finset ι} {mismatch : ∀ i, i ∈ I → Ω → E}
    {budget : ι → ℝ}
    (h : gradientMismatchFiniteMomentBudget P I mismatch budget) :
    ∀ i, ∀ hi : i ∈ I,
      Integrable (fun ω => ‖mismatch i hi ω‖ ^ 2) P :=
  h.1

/-- The deterministic integral-bound component of a finite-window
gradient-mismatch budget.

Layer: Model | Gap: Level 0 (finite-window gradient-mismatch budget projection)
Proof: second projection of `gradientMismatchFiniteMomentBudget`.
Source: stochastic approximation finite-horizon second-moment estimates and
  Mathlib Bochner integrability APIs
Used in: stochastic accelerated primal-dual deterministic gradient-mismatch
  budget projection
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem gradientMismatchFiniteMomentBudget.integral_le
    {Ω E ι : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {P : Measure Ω} {I : Finset ι} {mismatch : ∀ i, i ∈ I → Ω → E}
    {budget : ι → ℝ}
    (h : gradientMismatchFiniteMomentBudget P I mismatch budget) :
    ∀ i, ∀ hi : i ∈ I,
      ∫ ω, ‖mismatch i hi ω‖ ^ 2 ∂P ≤ budget i :=
  h.2

/-- A finite residual process has per-index square moments and an aggregate
finite-window bound under a deterministic mismatch budget.

For a membership-dependent residual family `delta` on a finite window `I`, the
package records a budget witness `M`, vector and squared-norm measurability,
per-index square integrability and expectation bounds, and the resulting
finite-window integrability and expectation bound. The scalar `sigma2` is the
base oracle second-moment budget before the residual-specific mismatch
contribution.

Layer: Model | Concept: Oracle
Proof: (definitional construction; finite residual square-moment package with
  explicit deterministic mismatch budget)
Source: stochastic approximation finite-horizon second-moment estimates and
  Mathlib Bochner integrability APIs for finite sums
Used in: stochastic accelerated primal-dual mixed-center gradient residual
  moment package before primal square-noise aggregation
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
abbrev finiteResidualMomentBudget
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) (I : Finset ℕ) (delta : ∀ i, i ∈ I → Ω → E)
    (mismatchBudget : (ℕ → ℝ) → Prop) (sigma2 : ℝ) : Prop :=
  mixedCenterResidualFiniteMomentStep P I delta mismatchBudget sigma2

@[deprecated gradientMismatchFiniteMomentBudget (since := "2026-06-14")]
abbrev GradientMismatchFiniteMomentBudget
    {Ω E ι : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) (I : Finset ι) (mismatch : ∀ i, i ∈ I → Ω → E)
    (budget : ι → ℝ) : Prop :=
  gradientMismatchFiniteMomentBudget P I mismatch budget

@[deprecated gradientMismatchFiniteMomentBudget (since := "2026-06-14")]
abbrev GeneratedHatfGradientMismatchBudget
    {Ω E ι : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) (I : Finset ι) (mismatch : ∀ i, i ∈ I → Ω → E)
    (budget : ι → ℝ) : Prop :=
  gradientMismatchFiniteMomentBudget P I mismatch budget

/-- Second moment of a normed-valued stochastic error process.

For an error process `error : Ω → E`, this is the Bochner expectation of the
squared norm `‖error‖²` with respect to an arbitrary measure.

Layer: Model | Concept: Oracle
Proof: (definitional construction; squared-norm second moment of a fixed-query
  stochastic-oracle residual)
Source: Mathlib Bochner integral notation and normed additive group APIs for
  real-valued moments of stochastic processes
Used in: stochastic accelerated primal-dual fixed-query oracle variance
  assumptions for gradient, linear-map, and adjoint-linear-map residuals
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
noncomputable def secondMoment
    {Ω E : Type*} [MeasurableSpace Ω] [SeminormedAddCommGroup E]
    (P : Measure Ω) (error : Ω → E) : ℝ :=
  ∫ ω, ‖error ω‖ ^ 2 ∂P

/-- The second moment unfolds to the Bochner integral of the squared norm.

Layer: Model | Gap: Level 0 (second-moment unfolding)
Proof: by rfl after unfolding `secondMoment`.
Source: Mathlib Bochner integral notation and normed additive group APIs for
  real-valued moments of stochastic processes
Used in: stochastic accelerated primal-dual fixed-query variance assumptions
  where a named residual second moment must expose its source integral
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
@[simp]
theorem secondMoment_def
    {Ω E : Type*} [MeasurableSpace Ω] [SeminormedAddCommGroup E]
    (P : Measure Ω) (error : Ω → E) :
    secondMoment P error = ∫ ω, ‖error ω‖ ^ 2 ∂P := by
  rfl

/-- The second moment over the zero measure is zero.

Layer: Model | Gap: Level 0 (second-moment zero-measure API)
Proof: unfold `secondMoment` and simplify the Bochner integral over the zero
  measure.
Source: Mathlib Bochner integral simplification over the zero measure
Used in: degenerate-measure simplifications for stochastic-oracle
  second-moment assumptions
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
@[simp]
theorem secondMoment_zero_measure
    {Ω E : Type*} [MeasurableSpace Ω] [SeminormedAddCommGroup E]
    (error : Ω → E) :
    secondMoment (0 : Measure Ω) error = 0 := by
  simp [secondMoment]

/-- Well-definedness of the squared-norm second moment of an error process.

For an error process `error : Ω → E`, this predicate records integrability of
the real-valued squared norm `ω ↦ ‖error ω‖ ^ 2` under an arbitrary measure.

Layer: Model | Concept: Oracle
Proof: (definitional construction; squared-norm second-moment integrability
  predicate for a fixed error process)
Source: Mathlib Bochner integrability and normed-space APIs for real-valued
  random variables
Used in: stochastic accelerated primal-dual fixed-query oracle residual
  second-moment assumptions
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/8
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
def secondMomentWellDefined
    {Ω E : Type*} [MeasurableSpace Ω] [SeminormedAddCommGroup E]
    (P : Measure Ω) (error : Ω → E) : Prop :=
  Integrable (fun ω => ‖error ω‖ ^ 2) P

/-- The second-moment well-definedness predicate unfolds to squared-norm
integrability.

Layer: Model | Gap: Level 0 (second-moment integrability unfolding)
Proof: by rfl after unfolding `secondMomentWellDefined`.
Source: Mathlib Bochner integrability and normed-space APIs for real-valued
  random variables
Used in: stochastic accelerated primal-dual fixed-query oracle residual
  second-moment assumptions
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/8
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem secondMomentWellDefined_iff_integrable
    {Ω E : Type*} [MeasurableSpace Ω] [SeminormedAddCommGroup E]
    (P : Measure Ω) (error : Ω → E) :
    secondMomentWellDefined P error ↔ Integrable (fun ω => ‖error ω‖ ^ 2) P := by
  rfl

/-- Fixed-query squared-norm exponential moment under an explicit nonzero scale.

For an error process `error : Ω → E`, this is the Bochner expectation of
`exp (‖error‖² / sigma²)` with respect to an arbitrary measure. The nonzero
scale argument records the denominator regime used by light-tail assumptions.

Layer: Model | Concept: Oracle
Proof: (definitional construction; scaled squared-norm exponential moment of a
  fixed-query stochastic-oracle residual)
Source: stochastic first-order oracle light-tail assumptions and Mathlib
  Bochner integral notation for real-valued random variables
Used in: stochastic accelerated primal-dual fixed-query oracle light-tail
  bridges for gradient, linear-map, and adjoint-linear-map residuals
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/7
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
noncomputable def fixedQueryExponentialMoment
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) (error : Ω → E) (sigma : ℝ) (_hSigma : sigma ≠ 0) : ℝ :=
  ∫ ω, Real.exp (‖error ω‖ ^ 2 / sigma ^ 2) ∂P

/-- The fixed-query exponential moment unfolds to the corresponding Bochner
integral of the scaled squared-norm exponential.

Layer: Model | Gap: Level 0 (fixed-query exponential-moment unfolding)
Proof: by rfl after unfolding `fixedQueryExponentialMoment`.
Source: Mathlib Bochner integral notation and real exponential APIs
Used in: stochastic accelerated primal-dual Assumption 9 projections where a
  fixed-query light-tail moment must expose its source integral
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/7
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
@[simp]
theorem fixedQueryExponentialMoment_def
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) (error : Ω → E) (sigma : ℝ) (hSigma : sigma ≠ 0) :
    fixedQueryExponentialMoment P error sigma hSigma =
      ∫ ω, Real.exp (‖error ω‖ ^ 2 / sigma ^ 2) ∂P := by
  rfl

@[deprecated fixedQueryExponentialMoment (since := "2026-06-14")]
noncomputable abbrev SapdExponentialMoment
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) (error : Ω → E) (sigma : ℝ) (hSigma : sigma ≠ 0) : ℝ :=
  fixedQueryExponentialMoment P error sigma hSigma

/-- Fixed-query light-tail predicate for a staged stochastic oracle residual.

For a deterministic query `x`, sample stream `xi`, oracle kernel `oracle`, and
target field `target`, the residual
`ω ↦ target x - stagedOracleValue oracle xi t x ω` has measurable squared norm
and a bounded scaled squared-norm exponential moment for every nonzero scale.

Layer: Model | Concept: Oracle
Proof: (definitional construction; fixed-query staged stochastic-oracle
  residual light-tail predicate using the named exponential-moment integral)
Source: stochastic first-order oracle light-tail assumptions, Mathlib
  measurability predicates, and Bochner integrability for real random variables
Used in: stochastic accelerated primal-dual high-probability oracle
  assumptions for gradient, linear-map, and adjoint-linear-map channels
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/7
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
noncomputable def fixedQueryStagedOracleLightTailBound
    {Ω X S E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) (oracle : X → S → E) (xi : ℕ → Ω → S)
    (target : X → E) (sigma : ℝ) (x : X) (t : ℕ) : Prop :=
  Measurable
      (fun ω => ‖target x - SOptLib.stagedOracleValue oracle xi t x ω‖ ^ 2) ∧
    ∀ hSigma : sigma ≠ 0,
      Integrable
          (fun ω => Real.exp
            (‖target x - SOptLib.stagedOracleValue oracle xi t x ω‖ ^ 2 / sigma ^ 2))
          P ∧
        fixedQueryExponentialMoment P
            (fun ω => target x - SOptLib.stagedOracleValue oracle xi t x ω) sigma hSigma ≤
          Real.exp 1

@[deprecated fixedQueryStagedOracleLightTailBound (since := "2026-06-14")]
abbrev SapdOracleLightTailBoundExtension
    {Ω X S E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) (oracle : X → S → E) (xi : ℕ → Ω → S)
    (target : X → E) (sigma : ℝ) (x : X) (t : ℕ) : Prop :=
  fixedQueryStagedOracleLightTailBound P oracle xi target sigma x t

/-- Fixed-query variance predicate for a staged stochastic oracle residual.

For a deterministic query `x`, sample stream `xi`, oracle kernel `oracle`, and
target field `target`, the residual
`ω ↦ stagedOracleValue oracle xi t x ω - target x` has a well-defined
squared-norm second moment bounded by `sigma ^ 2`.

Layer: Model | Concept: Oracle
Proof: (definitional construction; fixed-query staged stochastic-oracle
  residual second-moment predicate using the named second-moment
  well-definedness condition)
Source: stochastic first-order oracle variance assumptions and Mathlib
  Bochner integration APIs for real random variables
Used in: stochastic accelerated primal-dual fixed-query oracle variance
  assumptions for gradient, linear-map, and adjoint-linear-map channels
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/8
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
noncomputable def fixedQueryStagedOracleVarianceBound
    {Ω X S E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) (oracle : X → S → E) (xi : ℕ → Ω → S)
    (target : X → E) (sigma : ℝ) (x : X) (t : ℕ) : Prop :=
  secondMomentWellDefined P
    (fun ω => SOptLib.stagedOracleValue oracle xi t x ω - target x) ∧
    ∫ ω, ‖SOptLib.stagedOracleValue oracle xi t x ω - target x‖ ^ 2 ∂P ≤
      sigma ^ 2

/-- Build a fixed-query staged-oracle variance bound from second-moment
well-definedness and the numerical second-moment bound.

Layer: Model | Gap: Level 0 (fixed-query staged-oracle variance constructor)
Proof: pair the supplied second-moment well-definedness and bound components.
Source: Mathlib conjunction APIs and Bochner second-moment notation
Used in: stochastic accelerated primal-dual source-oracle assumptions when the
  paper supplies well-definedness and variance bounds separately
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/8
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem fixedQueryStagedOracleVarianceBound_intro
    {Ω X S E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {P : Measure Ω} {oracle : X → S → E} {xi : ℕ → Ω → S}
    {target : X → E} {sigma : ℝ} {x : X} {t : ℕ}
    (hWellDefined :
      secondMomentWellDefined P
        (fun ω => SOptLib.stagedOracleValue oracle xi t x ω - target x))
    (hBound :
      ∫ ω, ‖SOptLib.stagedOracleValue oracle xi t x ω - target x‖ ^ 2 ∂P ≤
        sigma ^ 2) :
    fixedQueryStagedOracleVarianceBound P oracle xi target sigma x t :=
  ⟨hWellDefined, hBound⟩

/-- The squared residual in a fixed-query staged-oracle variance bound is
well-defined as a second moment.

Layer: Model | Gap: Level 0 (fixed-query staged-oracle variance integrability)
Proof: project the first component of the fixed-query variance predicate.
Source: Mathlib conjunction APIs and second-moment integrability predicates
Used in: stochastic accelerated primal-dual oracle variance projections where
  the squared residual integrability side condition is needed separately
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/8
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem fixedQueryStagedOracleVarianceBound.secondMomentWellDefined
    {Ω X S E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {P : Measure Ω} {oracle : X → S → E} {xi : ℕ → Ω → S}
    {target : X → E} {sigma : ℝ} {x : X} {t : ℕ}
    (h : fixedQueryStagedOracleVarianceBound P oracle xi target sigma x t) :
    secondMomentWellDefined P
      (fun ω => SOptLib.stagedOracleValue oracle xi t x ω - target x) :=
  h.1

/-- A fixed-query staged-oracle variance bound controls the residual second
moment by `sigma ^ 2`.

Layer: Model | Gap: Level 0 (fixed-query staged-oracle variance bound)
Proof: project the second component of the fixed-query variance predicate.
Source: Mathlib conjunction APIs and Bochner second-moment notation
Used in: stochastic accelerated primal-dual oracle variance projections where
  the numerical squared-residual moment bound is needed separately
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/8
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem fixedQueryStagedOracleVarianceBound.secondMoment_le
    {Ω X S E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {P : Measure Ω} {oracle : X → S → E} {xi : ℕ → Ω → S}
    {target : X → E} {sigma : ℝ} {x : X} {t : ℕ}
    (h : fixedQueryStagedOracleVarianceBound P oracle xi target sigma x t) :
    ∫ ω, ‖SOptLib.stagedOracleValue oracle xi t x ω - target x‖ ^ 2 ∂P ≤
      sigma ^ 2 :=
  h.2

/-- A fixed-query staged-oracle variance bound supplies squared residual
integrability and the unfolded second-moment estimate.

For a deterministic query `x`, the target-centered residual of the staged
oracle has an integrable squared norm, and its Bochner integral is bounded by
`sigma ^ 2`.

Layer: Model | Gap: Level 0 (fixed-query staged-oracle variance accessor)
Proof: project the named second-moment well-definedness and bound from the
  variance predicate, then unfold `secondMomentWellDefined` and `secondMoment`
  to the raw squared-residual obligations.
Source: stochastic first-order oracle variance assumptions and Mathlib Bochner
  integrability/integral notation for real-valued moments
Used in: stochastic accelerated primal-dual fixed-query oracle variance
  projections for gradient, linear-map, and adjoint-linear-map channels
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/8
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem fixedQueryStagedOracleVarianceBound.integrable_and_bound
    {Ω X S E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {P : Measure Ω} {oracle : X → S → E} {xi : ℕ → Ω → S}
    {target : X → E} {sigma : ℝ} {x : X} {t : ℕ}
    (h : fixedQueryStagedOracleVarianceBound P oracle xi target sigma x t) :
    Integrable
        (fun ω => ‖SOptLib.stagedOracleValue oracle xi t x ω - target x‖ ^ 2)
        P ∧
      ∫ ω, ‖SOptLib.stagedOracleValue oracle xi t x ω - target x‖ ^ 2 ∂P ≤
        sigma ^ 2 := by
  constructor
  · simpa [secondMomentWellDefined] using
      fixedQueryStagedOracleVarianceBound.secondMomentWellDefined h
  · exact fixedQueryStagedOracleVarianceBound.secondMoment_le h

@[deprecated fixedQueryStagedOracleVarianceBound (since := "2026-06-14")]
abbrev SapdOracleVarianceBound
    {Ω X S E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) (oracle : X → S → E) (xi : ℕ → Ω → S)
    (target : X → E) (sigma : ℝ) (x : X) (t : ℕ) : Prop :=
  fixedQueryStagedOracleVarianceBound P oracle xi target sigma x t

/-- Three fixed-query light-tail channels for staged stochastic oracle values.

For three oracle kernels sharing one sample stream, this predicate records that
each fixed query at every admissible time has the supplied light-tail property
for its target-centered staged residual.

Layer: Model | Concept: Oracle
Proof: (definitional construction; three target-centered staged stochastic
  oracle residual channels passed to caller-supplied light-tail predicates)
Source: stochastic first-order oracle light-tail assumptions and time-indexed
  sampled-oracle kernels
Used in: stochastic accelerated primal-dual high-probability assumptions for
  gradient, linear-map, and adjoint-linear-map oracle channels
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/7
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
noncomputable def threeStagedOracleLightTailBounds
    {Ω S X₁ X₂ X₃ E₁ E₂ E₃ : Type*}
    [MeasurableSpace Ω]
    [MeasurableSpace E₁] [NormedAddCommGroup E₁]
    [MeasurableSpace E₂] [NormedAddCommGroup E₂]
    [MeasurableSpace E₃] [NormedAddCommGroup E₃]
    (P : Measure Ω)
    (lightTail₁ : Measure Ω → (Ω → E₁) → ℝ → Prop)
    (lightTail₂ : Measure Ω → (Ω → E₂) → ℝ → Prop)
    (lightTail₃ : Measure Ω → (Ω → E₃) → ℝ → Prop)
    (oracle₁ : X₁ → S → E₁) (oracle₂ : X₂ → S → E₂)
    (oracle₃ : X₃ → S → E₃)
    (xi : ℕ → Ω → S)
    (target₁ : X₁ → E₁) (target₂ : X₂ → E₂) (target₃ : X₃ → E₃)
    (sigma₁ sigma₂ sigma₃ : ℝ) (start : ℕ) : Prop :=
  (∀ x : X₁, ∀ t, start ≤ t →
      lightTail₁ P
        (fun ω => target₁ x - SOptLib.stagedOracleValue oracle₁ xi t x ω)
        sigma₁) ∧
    (∀ x : X₂, ∀ t, start ≤ t →
      lightTail₂ P
        (fun ω => target₂ x - SOptLib.stagedOracleValue oracle₂ xi t x ω)
        sigma₂) ∧
    (∀ x : X₃, ∀ t, start ≤ t →
      lightTail₃ P
        (fun ω => target₃ x - SOptLib.stagedOracleValue oracle₃ xi t x ω)
        sigma₃)

/-- The three-channel staged-oracle light-tail package unfolds to the three
fixed-query channel predicates.

Layer: Model | Gap: Level 0 (three-channel staged oracle light-tail unfolding)
Proof: by rfl after unfolding `threeStagedOracleLightTailBounds`.
Source: stochastic first-order oracle light-tail assumptions and SOptLib
  staged-oracle kernel notation
Used in: stochastic accelerated primal-dual assumption setup where the
  displayed source predicates are exposed for three fixed-query oracle channels
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/7
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
@[simp]
theorem threeStagedOracleLightTailBounds_def
    {Ω S X₁ X₂ X₃ E₁ E₂ E₃ : Type*}
    [MeasurableSpace Ω]
    [MeasurableSpace E₁] [NormedAddCommGroup E₁]
    [MeasurableSpace E₂] [NormedAddCommGroup E₂]
    [MeasurableSpace E₃] [NormedAddCommGroup E₃]
    (P : Measure Ω)
    (lightTail₁ : Measure Ω → (Ω → E₁) → ℝ → Prop)
    (lightTail₂ : Measure Ω → (Ω → E₂) → ℝ → Prop)
    (lightTail₃ : Measure Ω → (Ω → E₃) → ℝ → Prop)
    (oracle₁ : X₁ → S → E₁) (oracle₂ : X₂ → S → E₂)
    (oracle₃ : X₃ → S → E₃)
    (xi : ℕ → Ω → S)
    (target₁ : X₁ → E₁) (target₂ : X₂ → E₂) (target₃ : X₃ → E₃)
    (sigma₁ sigma₂ sigma₃ : ℝ) (start : ℕ) :
    threeStagedOracleLightTailBounds P lightTail₁ lightTail₂ lightTail₃
        oracle₁ oracle₂ oracle₃ xi target₁ target₂ target₃
        sigma₁ sigma₂ sigma₃ start =
      ((∀ x : X₁, ∀ t, start ≤ t →
          lightTail₁ P
            (fun ω => target₁ x - SOptLib.stagedOracleValue oracle₁ xi t x ω)
            sigma₁) ∧
        (∀ x : X₂, ∀ t, start ≤ t →
          lightTail₂ P
            (fun ω => target₂ x - SOptLib.stagedOracleValue oracle₂ xi t x ω)
            sigma₂) ∧
        (∀ x : X₃, ∀ t, start ≤ t →
          lightTail₃ P
            (fun ω => target₃ x - SOptLib.stagedOracleValue oracle₃ xi t x ω)
            sigma₃)) := by
  rfl

/-- Ambient totalization of a time-indexed sampled oracle from a feasible carrier.

For a stochastic oracle `G` defined on feasible decisions `{x // x in X}`,
`oracleAmbientOn X G xi t` is the pointwise process that evaluates the sample
coordinate `xi t omega` on carrier points and returns zero off the carrier.
The input carrier type and output oracle-value type are independent, covering
block and saddle-point oracles whose values live in a different space.

Layer: Model | Concept: Oracle
Proof: (definitional construction; time-indexed sampled oracle wrapped by
  carrier totalization with a heterogeneous output type)
Source: Mathlib set subtype APIs and stochastic first-order oracle notation
Used in: stochastic accelerated primal-dual dual prox update where the sampled
  primal-side operator is displayed at an ambient extrapolated primal point
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
noncomputable def oracleAmbientOn
    {E F Ω S : Type*} [Zero F] (X : Set E)
    (G : {x : E // x ∈ X} → S → F) (xi : ℕ → Ω → S) (t : ℕ) :
    E → Ω → F :=
  fun x ω => totalizeOn X (fun z => G z (xi t ω)) x

/-- The ambient sampled oracle unfolds to carrier totalization at the selected sample.

Layer: Model | Gap: Level 0 (ambient sampled oracle formula)
Proof: by rfl after unfolding `oracleAmbientOn`.
Source: Mathlib function evaluation and set subtype APIs
Used in: stochastic accelerated primal-dual displayed sampled operator
  normalization before totalization reasoning
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
@[simp]
theorem oracleAmbientOn_apply
    {E F Ω S : Type*} [Zero F] (X : Set E)
    (G : {x : E // x ∈ X} → S → F) (xi : ℕ → Ω → S) (t : ℕ)
    (x : E) (ω : Ω) :
    oracleAmbientOn X G xi t x ω = totalizeOn X (fun z => G z (xi t ω)) x := by
  rfl

/-- The ambient sampled oracle agrees with the carrier oracle on feasible points.

For any `x in X`, the heterogeneous ambient totalization recovers the original
sampled carrier oracle at `x` and sample coordinate `xi t omega`.

Layer: Model | Gap: Level 0 (ambient sampled oracle feasibility agreement)
Proof: unfold `oracleAmbientOn` and apply `totalizeOn_of_mem` to select the
  carrier branch of the totalized function.
Source: Mathlib set subtype APIs and SOptLib carrier totalization
Used in: stochastic accelerated primal-dual replacement of a displayed
  ambient `A_x(tilde x_t)` call by the fixed-domain oracle when coverage is known
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
@[simp]
theorem oracleAmbientOn_of_mem
    {E F Ω S : Type*} [Zero F] (X : Set E)
    (G : {x : E // x ∈ X} → S → F) (xi : ℕ → Ω → S) (t : ℕ)
    {x : E} (hx : x ∈ X) (ω : Ω) :
    oracleAmbientOn X G xi t x ω = G ⟨x, hx⟩ (xi t ω) := by
  simpa [oracleAmbientOn] using
    (totalizeOn_of_mem X (fun z : {x : E // x ∈ X} => G z (xi t ω)) hx)

/-- A displayed ambient oracle call equals the sampled fixed-domain oracle under
finite-horizon realization coverage.

If a displayed time-indexed call is represented by the ambient totalization of
a carrier-domain sampled oracle along a generated query, then any finite-horizon
coverage witness for that query identifies the displayed call with the sampled
oracle evaluated at the feasible subtype query.

Layer: Model | Gap: Level 0 (displayed oracle realization identity)
Proof: rewrite the displayed call by its ambient-oracle representation, then
  apply `oracleAmbientOn_of_mem` with the finite-horizon coverage witness.
Source: stochastic approximation fixed-domain oracle semantics and Mathlib
  set/subtype equality APIs
Used in: stochastic accelerated primal-dual source-boundary replacement of the
  displayed `A_x(tilde x_t)` call by the fixed-domain sampled oracle
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/3/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem displayedOracleCall_eq_sampledOracle_of_realization
    {Ω E F S : Type*} [Zero F] (X : Set E)
    (G : {x : E // x ∈ X} → S → F) (ξ : ℕ → Ω → S)
    (query : ℕ → Ω → E) (call : ℕ → Ω → F)
    (hcall : ∀ i ω, call i ω = oracleAmbientOn X G ξ i (query i ω) ω)
    {T i : ℕ}
    (hrealize : ∀ j, j ∈ Finset.Icc 1 T → ∀ ω : Ω, query j ω ∈ X)
    (hi : i ∈ Finset.Icc 1 T) (ω : Ω) :
    call i ω = G ⟨query i ω, hrealize i hi ω⟩ (ξ i ω) := by
  rw [hcall]
  simpa using
    (oracleAmbientOn_of_mem X G ξ i (hrealize i hi ω) ω)

/-- Pointwise displayed ambient oracle call equality on a feasible query.

Layer: Model | Gap: Level 0 (displayed oracle feasible identity)
Proof: rewrite the displayed call by its ambient-oracle representation and
  simplify the feasible carrier branch.
Source: stochastic approximation fixed-domain oracle semantics and Mathlib
  set/subtype equality APIs
Used in: stochastic accelerated primal-dual source-boundary fixed-domain oracle
  identities at a single covered index
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/3/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem displayedOracleCall_eq_sampledOracle_of_mem
    {Ω E F S : Type*} [Zero F] (X : Set E)
    (G : {x : E // x ∈ X} → S → F) (ξ : ℕ → Ω → S)
    (query : ℕ → Ω → E) (call : ℕ → Ω → F)
    (hcall : ∀ i ω, call i ω = oracleAmbientOn X G ξ i (query i ω) ω)
    (i : ℕ) (ω : Ω) (hmem : query i ω ∈ X) :
    call i ω = G ⟨query i ω, hmem⟩ (ξ i ω) := by
  rw [hcall]
  simpa using oracleAmbientOn_of_mem X G ξ i hmem ω

/-- A completed state-query realization induces a generated fixed-domain oracle
realization.

If every completed state query is feasible, the generated query agrees with
that completed state query, and the generated sample agrees with the fixed-
domain oracle at the completed state query, then the generated stream satisfies
the finite-horizon generated-oracle realization contract.

Layer: Model | Gap: Level 1 (state-query generated oracle realization)
Proof: at each covered positive time, transport feasibility across the query
  equality and transport the sample equality across the same dependent subtype
  argument using proof irrelevance.
Source: stochastic approximation fixed-domain oracle semantics and Mathlib
  set/subtype equality APIs
Used in: stochastic accelerated primal-dual conversion from completed
  fixed-domain partial states to a generated `A_x` oracle realization
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/3/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem generatedOracleRealization_of_state_query_sample_eq
    {Ω State X Y : Type*} {C : Set X}
    {sample : ℕ → Ω → Y}
    {generatedQuery : ∀ i, 1 ≤ i → Ω → X}
    {oracleSample : ℕ → {x : X // x ∈ C} → Ω → Y}
    {T : ℕ}
    (completedState : ∀ i, i ∈ Finset.Icc 1 T → Ω → State)
    (stateQuery : State → X)
    (hmem :
      ∀ i, ∀ hi : i ∈ Finset.Icc 1 T, ∀ ω : Ω,
        stateQuery (completedState i hi ω) ∈ C)
    (hquery :
      ∀ i, ∀ hi : i ∈ Finset.Icc 1 T, ∀ ω : Ω,
        generatedQuery i (Finset.mem_Icc.mp hi).1 ω =
          stateQuery (completedState i hi ω))
    (hsample :
      ∀ i, ∀ hi : i ∈ Finset.Icc 1 T, ∀ ω : Ω,
        sample i ω =
          oracleSample i
            ⟨stateQuery (completedState i hi ω), hmem i hi ω⟩ ω) :
    generatedOracleRealization C sample generatedQuery oracleSample T := by
  intro i hi ω
  refine ⟨?_, ?_⟩
  · simpa [hquery i hi ω] using hmem i hi ω
  · simpa [hquery i hi ω] using hsample i hi ω

/-- Combined primal-noise process obtained as the pointwise sum of two components.

The optional dependent witness `H t` lets the components be indexed only on
admissible times, such as iterations with `1 ≤ t`, while still exposing the
combined process as a single named stochastic-optimization object.

Layer: Model | Concept: Oracle
Proof: (definitional construction; pointwise sum of two admissible-index
  stochastic primal-noise processes)
Source: Mathlib function evaluation and addition APIs for stochastic process
  notation
Used in: stochastic accelerated primal-dual combined primal-noise construction
  before componentwise second-moment and cross-term estimates
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
def combinedPrimalNoiseProcess
    {T Ω E : Type*} {H : T → Sort*} [Add E]
    (firstNoise secondNoise : (t : T) → H t → Ω → E)
    (t : T) (h : H t) (ω : Ω) : E :=
  firstNoise t h ω + secondNoise t h ω

/-- The combined primal-noise process unfolds to the sum of its two components.

Layer: Model | Gap: Level 0 (combined primal-noise process unfolding)
Proof: by rfl after unfolding `combinedPrimalNoiseProcess`.
Source: Mathlib function evaluation and addition APIs for stochastic process
  notation
Used in: stochastic accelerated primal-dual replacement of raw component sums
  by a named combined primal-noise process
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
@[simp]
theorem combinedPrimalNoiseProcess_apply
    {T Ω E : Type*} {H : T → Sort*} [Add E]
    (firstNoise secondNoise : (t : T) → H t → Ω → E)
    (t : T) (h : H t) (ω : Ω) :
    combinedPrimalNoiseProcess firstNoise secondNoise t h ω =
      firstNoise t h ω + secondNoise t h ω := by
  rfl

/-- The sum of measurable primal-noise components is measurable.

At a fixed admissible time, measurability of each component gives
measurability of the combined primal-noise process by measurable addition.

Layer: Model | Gap: Level 0 (combined primal-noise measurability)
Proof: unfold the combined process and apply Mathlib's measurable addition API
  to the selected component time slices.
Source: Mathlib measurable addition APIs for functions into measurable additive
  spaces
Used in: stochastic accelerated primal-dual combined primal-noise integrability
  setup before square-moment estimates
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem combinedPrimalNoiseProcess_measurable
    {T Ω E : Type*} {H : T → Sort*}
    [MeasurableSpace Ω] [MeasurableSpace E] [Add E] [MeasurableAdd₂ E]
    {firstNoise secondNoise : (t : T) → H t → Ω → E} {t : T} {h : H t}
    (hfirst : Measurable (firstNoise t h))
    (hsecond : Measurable (secondNoise t h)) :
    Measurable (fun ω => combinedPrimalNoiseProcess firstNoise secondNoise t h ω) := by
  simpa [combinedPrimalNoiseProcess] using hfirst.add hsecond

/-- Residual process of a sampled adjoint oracle against its realized target process.

For a time-indexed sampled adjoint response and a time-indexed target adjoint
process, this names the centered process
`ω ↦ sampledAdjoint t ω - targetAdjoint t ω`.

Layer: Model | Concept: Oracle
Proof: (definitional construction; pointwise residual of two indexed stochastic
  adjoint processes)
Source: Mathlib function evaluation and subtraction APIs for stochastic process
  notation
Used in: stochastic accelerated primal-dual primal update adjoint-oracle noise
  before the descent-envelope residual split
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
def adjointOracleResidualProcess
    {T Ω E : Type*} [Sub E]
    (sampledAdjoint targetAdjoint : T → Ω → E) (t : T) (ω : Ω) : E :=
  sampledAdjoint t ω - targetAdjoint t ω

/-- The adjoint-oracle residual process unfolds to sampled adjoint minus target adjoint.

Layer: Model | Gap: Level 0 (adjoint-oracle residual unfolding)
Proof: by rfl after unfolding `adjointOracleResidualProcess`.
Source: Mathlib function evaluation and subtraction APIs for stochastic process
  notation
Used in: stochastic accelerated primal-dual primal update adjoint-oracle noise
  before the descent-envelope residual split
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
@[simp]
theorem adjointOracleResidualProcess_apply
    {T Ω E : Type*} [Sub E]
    (sampledAdjoint targetAdjoint : T → Ω → E) (t : T) (ω : Ω) :
    adjointOracleResidualProcess sampledAdjoint targetAdjoint t ω =
      sampledAdjoint t ω - targetAdjoint t ω := by
  rfl

/-- A residual of measurable sampled and target adjoint processes is measurable.

At a fixed time index, measurability of each realized adjoint process gives
measurability of their centered residual by measurable subtraction.

Layer: Model | Gap: Level 0 (adjoint-oracle residual measurability)
Proof: unfold the residual process and apply Mathlib's measurable subtraction
  API to the selected sampled and target time slices.
Source: Mathlib measurable subtraction APIs for functions into measurable
  additive spaces
Used in: stochastic accelerated primal-dual adjoint-oracle residual
  integrability and conditional-expectation setup
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem adjointOracleResidualProcess_measurable
    {T Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [Sub E] [MeasurableSub₂ E]
    {sampledAdjoint targetAdjoint : T → Ω → E} {t : T}
    (hsampled : Measurable (sampledAdjoint t))
    (htarget : Measurable (targetAdjoint t)) :
    Measurable (fun ω => adjointOracleResidualProcess sampledAdjoint targetAdjoint t ω) := by
  simpa [adjointOracleResidualProcess] using hsampled.sub htarget

/-- Two-block stochastic-oracle residual pair along a state process.

The primal component is the sum of a centered gradient-like oracle call and a
centered adjoint-like oracle call at the next block state. The dual component is
the signed residual between a sampled forward call and its deterministic target.

Layer: Model | Concept: Oracle
Proof: (definitional construction; two-block oracle residual pair assembled
  from current-state, next-state, and forward-query targets)
Source: stochastic saddle-point oracle notation with Mathlib additive-group
  operations and product types
Used in: stochastic accelerated primal-dual one-step noise pair inside the
  displayed saddle residual decomposition
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
noncomputable def twoBlockOracleResidualPair
    {Ω State XG Y XF EX EY : Type*} [AddGroup EX] [AddGroup EY]
    (state : ℕ → Ω → State)
    (primalQuery : State → XG) (nextDualQuery : State → Y)
    (forwardQuery : State → XF)
    (gradientSample : ℕ → XG → Ω → EX) (gradientTarget : ℕ → Ω → EX)
    (adjointSample : ℕ → Y → Ω → EX) (adjointTarget : Y → EX)
    (forwardSample : ℕ → Ω → EY) (forwardTarget : XF → EY)
    (i : ℕ) (ω : Ω) : EX × EY :=
  (gradientSample i (primalQuery (state i ω)) ω - gradientTarget i ω +
      (adjointSample i (nextDualQuery (state (i + 1) ω)) ω -
        adjointTarget (nextDualQuery (state (i + 1) ω))),
    -forwardSample i ω + forwardTarget (forwardQuery (state i ω)))

/-- The two-block stochastic-oracle residual pair unfolds to its component formula.

Layer: Model | Gap: Level 0 (two-block oracle residual pair unfolding)
Proof: by rfl after unfolding `twoBlockOracleResidualPair`.
Source: stochastic saddle-point oracle notation with Mathlib additive-group
  operations and product types
Used in: stochastic accelerated primal-dual one-step noise pair inside the
  displayed saddle residual decomposition
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
@[simp]
theorem twoBlockOracleResidualPair_apply
    {Ω State XG Y XF EX EY : Type*} [AddGroup EX] [AddGroup EY]
    (state : ℕ → Ω → State)
    (primalQuery : State → XG) (nextDualQuery : State → Y)
    (forwardQuery : State → XF)
    (gradientSample : ℕ → XG → Ω → EX) (gradientTarget : ℕ → Ω → EX)
    (adjointSample : ℕ → Y → Ω → EX) (adjointTarget : Y → EX)
    (forwardSample : ℕ → Ω → EY) (forwardTarget : XF → EY)
    (i : ℕ) (ω : Ω) :
    twoBlockOracleResidualPair state primalQuery nextDualQuery forwardQuery
        gradientSample gradientTarget adjointSample adjointTarget forwardSample
        forwardTarget i ω =
      (gradientSample i (primalQuery (state i ω)) ω - gradientTarget i ω +
          (adjointSample i (nextDualQuery (state (i + 1) ω)) ω -
            adjointTarget (nextDualQuery (state (i + 1) ω))),
        -forwardSample i ω + forwardTarget (forwardQuery (state i ω))) := by
  rfl

/-- Active-index totalization of a two-block stochastic-oracle residual pair.

On active indices this is the two-block residual pair formed from sampled
gradient, adjoint, and forward oracle streams and their deterministic targets.
Outside the active set it is zero.

Layer: Model | Concept: Oracle
Proof: (definitional construction; active-index totalization of the reusable
  two-block oracle residual pair)
Source: stochastic saddle-point oracle residual notation with Mathlib
  dependent `if`, product, and additive-operation APIs
Used in: stochastic accelerated primal-dual positive-index noise-pair
  construction before component-semantics and moment arguments
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
noncomputable def activeTwoBlockOracleResidualPair
    {Ω State XG Y XF EX EY : Type*} [AddGroup EX] [AddGroup EY]
    (active : ℕ → Prop) [DecidablePred active]
    (state : ℕ → Ω → State)
    (primalQuery : State → XG) (nextDualQuery : State → Y)
    (forwardQuery : State → XF)
    (gradientSample : ℕ → XG → Ω → EX)
    (gradientTarget : ∀ i, active i → Ω → EX)
    (adjointSample : ℕ → Y → Ω → EX) (adjointTarget : Y → EX)
    (forwardSample : ℕ → Ω → EY) (forwardTarget : XF → EY) :
    ℕ → Ω → EX × EY :=
  fun i ω =>
    if _ : active i then
      twoBlockOracleResidualPair state primalQuery nextDualQuery forwardQuery
        gradientSample
        (fun j ω => if hj : active j then gradientTarget j hj ω else 0)
        adjointSample adjointTarget forwardSample forwardTarget i ω
    else
      0

/-- The active two-block residual process unfolds to its guarded definition.

Layer: Model | Gap: Level 0 (active two-block residual pair definition)
Proof: by rfl after unfolding `activeTwoBlockOracleResidualPair`.
Source: stochastic saddle-point oracle residual notation with Mathlib
  dependent `if`, product, and additive-operation APIs
Used in: stochastic accelerated primal-dual positive-index noise-pair
  construction before component-semantics and moment arguments
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
@[simp]
theorem activeTwoBlockOracleResidualPair_def
    {Ω State XG Y XF EX EY : Type*} [AddGroup EX] [AddGroup EY]
    (active : ℕ → Prop) [DecidablePred active]
    (state : ℕ → Ω → State)
    (primalQuery : State → XG) (nextDualQuery : State → Y)
    (forwardQuery : State → XF)
    (gradientSample : ℕ → XG → Ω → EX)
    (gradientTarget : ∀ i, active i → Ω → EX)
    (adjointSample : ℕ → Y → Ω → EX) (adjointTarget : Y → EX)
    (forwardSample : ℕ → Ω → EY) (forwardTarget : XF → EY) :
    activeTwoBlockOracleResidualPair active state primalQuery nextDualQuery
        forwardQuery gradientSample gradientTarget adjointSample adjointTarget
        forwardSample forwardTarget =
      fun i ω =>
        if _ : active i then
          twoBlockOracleResidualPair state primalQuery nextDualQuery forwardQuery
            gradientSample
            (fun j ω => if hj : active j then gradientTarget j hj ω else 0)
            adjointSample adjointTarget forwardSample forwardTarget i ω
        else
          0 := by
  rfl

/-- On an active index, the active two-block residual process is the centered
two-block oracle residual pair.

Layer: Model | Gap: Level 0 (active two-block residual pair active branch)
Proof: unfold the active residual process and select the active branch by the
  supplied proof.
Source: stochastic saddle-point oracle residual notation with Mathlib
  dependent `if` simplification APIs
Used in: stochastic accelerated primal-dual positive-index noise-pair
  component unfolding
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
@[simp]
theorem activeTwoBlockOracleResidualPair_of_active
    {Ω State XG Y XF EX EY : Type*} [AddGroup EX] [AddGroup EY]
    (active : ℕ → Prop) [DecidablePred active]
    (state : ℕ → Ω → State)
    (primalQuery : State → XG) (nextDualQuery : State → Y)
    (forwardQuery : State → XF)
    (gradientSample : ℕ → XG → Ω → EX)
    (gradientTarget : ∀ i, active i → Ω → EX)
    (adjointSample : ℕ → Y → Ω → EX) (adjointTarget : Y → EX)
    (forwardSample : ℕ → Ω → EY) (forwardTarget : XF → EY)
    {i : ℕ} (hi : active i) (ω : Ω) :
    activeTwoBlockOracleResidualPair active state primalQuery nextDualQuery
        forwardQuery gradientSample gradientTarget adjointSample adjointTarget
        forwardSample forwardTarget i ω =
      (gradientSample i (primalQuery (state i ω)) ω - gradientTarget i hi ω +
          (adjointSample i (nextDualQuery (state (i + 1) ω)) ω -
            adjointTarget (nextDualQuery (state (i + 1) ω))),
        -forwardSample i ω + forwardTarget (forwardQuery (state i ω))) := by
  simp [activeTwoBlockOracleResidualPair, hi, twoBlockOracleResidualPair]

/-- Off the active set, the active two-block residual process is zero.

Layer: Model | Gap: Level 0 (active two-block residual pair inactive branch)
Proof: unfold the active residual process and select the inactive branch by
  `if_neg`.
Source: Mathlib dependent `if` simplification APIs for zero-totalized
  stochastic processes
Used in: stochastic accelerated primal-dual residual processes outside the
  positive iteration range
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
@[simp]
theorem activeTwoBlockOracleResidualPair_of_not_active
    {Ω State XG Y XF EX EY : Type*} [AddGroup EX] [AddGroup EY]
    (active : ℕ → Prop) [DecidablePred active]
    (state : ℕ → Ω → State)
    (primalQuery : State → XG) (nextDualQuery : State → Y)
    (forwardQuery : State → XF)
    (gradientSample : ℕ → XG → Ω → EX)
    (gradientTarget : ∀ i, active i → Ω → EX)
    (adjointSample : ℕ → Y → Ω → EX) (adjointTarget : Y → EX)
    (forwardSample : ℕ → Ω → EY) (forwardTarget : XF → EY)
    {i : ℕ} (hi : ¬ active i) (ω : Ω) :
    activeTwoBlockOracleResidualPair active state primalQuery nextDualQuery
        forwardQuery gradientSample gradientTarget adjointSample adjointTarget
        forwardSample forwardTarget i ω = 0 := by
  simp [activeTwoBlockOracleResidualPair, hi]

/-- The active two-block residual process satisfies the active component
semantics predicate.

Layer: Model | Gap: Level 0 (active two-block residual pair component semantics)
Proof: unfold the active residual process at an active index and simplify the
  two-block residual formula.
Source: SOptLib two-block oracle residual semantics and Mathlib dependent
  `if` simplification APIs
Used in: stochastic accelerated primal-dual positive-index noise-pair
  construction before descent and moment estimates
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem activeTwoBlockOracleResidualPair_componentSemantics
    {Ω State XG Y XF EX EY : Type*} [AddGroup EX] [AddGroup EY]
    (active : ℕ → Prop) [DecidablePred active]
    (state : ℕ → Ω → State)
    (primalQuery : State → XG) (nextDualQuery : State → Y)
    (forwardQuery : State → XF)
    (gradientSample : ℕ → XG → Ω → EX)
    (gradientTarget : ∀ i, active i → Ω → EX)
    (adjointSample : ℕ → Y → Ω → EX) (adjointTarget : Y → EX)
    (forwardSample : ℕ → Ω → EY) (forwardTarget : XF → EY) :
    twoBlockOracleResidualPairComponentSemantics active
      (activeTwoBlockOracleResidualPair active state primalQuery nextDualQuery
        forwardQuery gradientSample gradientTarget adjointSample adjointTarget
        forwardSample forwardTarget)
      state primalQuery nextDualQuery forwardQuery gradientSample gradientTarget
      adjointSample adjointTarget forwardSample forwardTarget := by
  intro i hi ω
  simp [activeTwoBlockOracleResidualPair, hi, twoBlockOracleResidualPair]

/-- Option-valued sample of a fixed-domain stochastic oracle at an ambient query.

For an oracle whose decision argument lives on the feasible carrier subtype
`{x // x ∈ C}`, this samples at `query st` when that ambient query is feasible
and returns `none` otherwise.

Layer: Model | Concept: Oracle
Proof: (definitional construction; dependent feasibility guard turning a
  carrier-domain stochastic oracle sample into an Option-valued ambient query
  sample)
Source: Mathlib set subtype and `Option` APIs for partial functions
Used in: stochastic accelerated primal-dual fixed-domain oracle realization at
  the extrapolated primal query before the dual prox update
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/3/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
noncomputable def fixedDomainOracleSample?
    {Ω X A State : Type*} (C : Set X)
    (oracleSample : {x : X // x ∈ C} → Ω → A)
    (query : State → X) (st : State) (ω : Ω) : Option A :=
  by
    classical
    exact
      if hmem : query st ∈ C then
        some (oracleSample ⟨query st, hmem⟩ ω)
      else
        none

/-- A fixed-domain oracle sample agrees with the carrier oracle on feasible
ambient queries.

Layer: Model | Gap: Level 0 (fixed-domain oracle feasible branch)
Proof: unfold the Option-valued sample and simplify the dependent `if` with
  the supplied membership proof.
Source: Mathlib set subtype and `Option` APIs for partial functions
Used in: stochastic accelerated primal-dual replacement of a partial
  fixed-domain oracle call by the literal carrier oracle sample
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/3/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
@[simp]
theorem fixedDomainOracleSample?_of_mem
    {Ω X A State : Type*} (C : Set X)
    (oracleSample : {x : X // x ∈ C} → Ω → A)
    (query : State → X) (st : State) (ω : Ω)
    (hmem : query st ∈ C) :
    fixedDomainOracleSample? C oracleSample query st ω =
      some (oracleSample ⟨query st, hmem⟩ ω) := by
  classical
  simp [fixedDomainOracleSample?, hmem]

/-- A fixed-domain oracle sample is undefined off the feasible carrier.

Layer: Model | Gap: Level 0 (fixed-domain oracle infeasible branch)
Proof: unfold the Option-valued sample and simplify the dependent `if` with
  the supplied nonmembership proof.
Source: Mathlib set subtype and `Option` APIs for partial functions
Used in: stochastic accelerated primal-dual domain-boundary proofs where the
  generated ambient oracle query has not been proved feasible
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/3/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
@[simp]
theorem fixedDomainOracleSample?_of_not_mem
    {Ω X A State : Type*} (C : Set X)
    (oracleSample : {x : X // x ∈ C} → Ω → A)
    (query : State → X) (st : State) (ω : Ω)
    (hnot : query st ∉ C) :
    fixedDomainOracleSample? C oracleSample query st ω = none := by
  classical
  simp [fixedDomainOracleSample?, hnot]

/-- Generated adjoint-oracle value obtained by projecting a query from a state process.

For a time-indexed stochastic oracle response, a generated state process, and a
state-to-query projection, this names the process that evaluates the oracle at
the projected query stored in the generated state at the same time.

Layer: Model | Concept: Oracle
Proof: (definitional construction; state-projected time-indexed stochastic
  oracle value process)
Source: stochastic approximation oracle-process notation and Mathlib function
  evaluation APIs
Used in: stochastic accelerated primal-dual primal-prox step where the
  generated dual state component feeds the sampled adjoint-linear oracle
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
noncomputable def generatedAdjointOracleValueAtState
    {Ω Query State E : Type*}
    (oracleValue : ℕ → Query → Ω → E)
    (process : ℕ → Ω → State)
    (queryOfState : State → Query)
    (t : ℕ) : Ω → E :=
  fun ω => oracleValue t (queryOfState (process t ω)) ω

/-- The generated state-projected adjoint-oracle value unfolds to pointwise
oracle evaluation at the projected query.

Layer: Model | Gap: Level 0 (state-projected oracle-value unfolding)
Proof: by rfl after unfolding `generatedAdjointOracleValueAtState`.
Source: stochastic approximation oracle-process notation and Mathlib function
  evaluation APIs
Used in: stochastic accelerated primal-dual replacement of the raw
  `A_y(y_{t+1})` sample by a named generated-state oracle value
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
@[simp]
theorem generatedAdjointOracleValueAtState_apply
    {Ω Query State E : Type*}
    (oracleValue : ℕ → Query → Ω → E)
    (process : ℕ → Ω → State)
    (queryOfState : State → Query)
    (t : ℕ) (ω : Ω) :
    generatedAdjointOracleValueAtState oracleValue process queryOfState t ω =
      oracleValue t (queryOfState (process t ω)) ω := by
  rfl

/-- A generated oracle query obtained as a state projection is prefix-measurable.

If the previous state slice is adapted at `filt.seq (i - 1)` and the
adaptedness interface exposes measurability of the selected query projection,
then the same generated query is measurable at the current prefix `filt.seq i`.

Layer: Model | Gap: Level 1 (generated state-projection query prefix measurability)
Proof: extract projection measurability from the adapted-state interface, then
  lift it along filtration monotonicity using `i - 1 ≤ i`.
Source: Mathlib MeasureTheory measurable-function monotonicity, process
  filtrations, and natural-number predecessor arithmetic
Used in: stochastic accelerated primal-dual generated oracle query
  measurability before fresh-sample independence and variance bounds
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem generated_oracle_query_prefix_measurable_of_state_projection
    {Ω Query : Type*} [MeasurableSpace Ω] [MeasurableSpace Query]
    (filt : Filtration ℕ (by infer_instance : MeasurableSpace Ω))
    {query : Ω → Query} (i : ℕ)
    (hquery : Measurable[filt.seq (i - 1)] query) :
    Measurable[filt.seq i] query := by
  exact hquery.mono (filt.mono (Nat.sub_le i 1)) le_rfl

/-- A finite-horizon adapted process supplies generated-query prefix measurability.

If each process slice up to `T` is adapted at its own filtration cutoff and the
adaptedness interface exposes measurability of a query projection, then every
generated query built from the predecessor state `process (i - 1)` is
measurable at the current prefix `filt.seq i`.

Layer: Model | Gap: Level 1 (finite-horizon generated adapted-query prefix measurability)
Proof: specialize the adapted-process hypothesis at the predecessor index
  `i - 1` using the bounds from `i ∈ Icc 1 T`; then lift the query
  measurability along filtration monotonicity from `i - 1` to `i`.
Source: Mathlib MeasureTheory measurable-function monotonicity, process
  filtrations, finite interval indexing, and natural-number predecessor
  arithmetic
Used in: stochastic accelerated primal-dual generated primal-query
  measurability before fresh oracle-sample independence and variance bounds
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem generated_oracle_query_prefix_measurable_of_adapted_process
    {Ω State Query : Type*} [MeasurableSpace Ω] [MeasurableSpace Query]
    (filt : Filtration ℕ (by infer_instance : MeasurableSpace Ω))
    (process : ℕ → Ω → State)
    (queryOfState : State → Query)
    (AdaptedAt : MeasurableSpace Ω → (Ω → State) → Prop)
    (T : ℕ)
    (hquery :
      ∀ {mΩ : MeasurableSpace Ω} {x : Ω → State},
        AdaptedAt mΩ x → Measurable[mΩ] (fun ω => queryOfState (x ω)))
    (hadapted : ∀ j, j ≤ T → AdaptedAt (filt.seq j) (process j)) :
    ∀ i, ∀ hi : i ∈ Finset.Icc 1 T,
      Measurable[filt.seq i] (fun ω => queryOfState (process (i - 1) ω)) := by
  intro i hi
  have hi_pair : 1 ≤ i ∧ i ≤ T := Finset.mem_Icc.mp hi
  have hquery_prev :
      Measurable[filt.seq (i - 1)]
        (fun ω => queryOfState (process (i - 1) ω)) :=
    hquery (hadapted (i - 1) (by omega))
  exact hquery_prev.mono (filt.mono (by omega)) le_rfl

/-- Generated oracle queries are prefix-measurable from successor-adapted realized states.

If a zero-based generated process is adapted at `filt.seq (j + 1)` and the
state-query selector is measurable whenever the state process is adapted, then
the positive-time generated query at every `i ∈ Icc 1 T` is measurable at
`filt.seq i`.

Layer: Model | Gap: Level 1 (generated query prefix measurability)
Proof: specialize the successor-adapted process hypothesis at the shifted
  state index `i - 1`, apply the state-query measurability accessor, normalize
  `(i - 1) + 1` to `i`, and unfold the generated query point view.
Source: Mathlib MeasureTheory measurability APIs, filtrations, and natural-number
  successor/subtraction arithmetic
Used in: stochastic accelerated primal-dual generated oracle query measurability
  before fresh-sample variance and independence bounds
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem generated_oracle_query_prefix_measurable_of_realization
    {Ω State Query : Type*} [MeasurableSpace Ω] [MeasurableSpace Query]
    (filt : Filtration ℕ (by infer_instance : MeasurableSpace Ω))
    (process : ℕ → Ω → State)
    (queryOfState : State → Query)
    (AdaptedAt : MeasurableSpace Ω → (Ω → State) → Prop)
    (T : ℕ)
    (hquery :
      ∀ {mΩ : MeasurableSpace Ω} {x : Ω → State},
        AdaptedAt mΩ x → Measurable[mΩ] (fun ω => queryOfState (x ω)))
    (hadapted :
      ∀ j, j ≤ T → AdaptedAt (filt.seq (j + 1)) (process j)) :
    ∀ i, ∀ hi : i ∈ Finset.Icc 1 T,
      Measurable[filt.seq i]
        (fun ω => queryOfState (process (i - 1) ω)) := by
  intro i hi
  have hi_pair : 1 ≤ i ∧ i ≤ T := Finset.mem_Icc.mp hi
  have hstate :
      AdaptedAt (filt.seq ((i - 1) + 1)) (process (i - 1)) :=
    hadapted (i - 1) (by omega)
  have hquery_i :
      Measurable[filt.seq ((i - 1) + 1)]
        (fun ω => queryOfState (process (i - 1) ω)) :=
    hquery hstate
  have hidx : (i - 1) + 1 = i := Nat.sub_add_cancel hi_pair.1
  rwa [hidx] at hquery_i

/-- A realized fixed-domain oracle sample is measurable at a measurable random
query.

If a stream agrees pointwise with a jointly measurable stochastic oracle
evaluated at a feasible random query and a measurable sample coordinate, then
the stream is measurable with respect to the same source sigma-algebra.

Layer: Model | Gap: Level 0 (realized random-query oracle-sample measurability)
Proof: package the feasible query as a subtype-valued measurable map, compose
  the jointly measurable oracle with the query/sample pair, then transport
  measurability across the pointwise realization equality.
Source: Mathlib MeasureTheory product/subtype measurable-function APIs and
  SOptLib sampled stochastic-oracle composition
Used in: stochastic accelerated primal-dual generated fixed-domain `A_x` oracle
  sample measurability before extension-process adaptedness
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/3/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem measurable_realizedOracleSample_of_measurable_query
    {Ω X S E : Type*} [MeasurableSpace X] [MeasurableSpace S]
    [MeasurableSpace E]
    (m : MeasurableSpace Ω) {C : Set X}
    {oracle : {x : X // x ∈ C} → S → E}
    {query : Ω → X} {ξ : Ω → S} {stream : Ω → E}
    (horacle : Measurable (fun p : {x : X // x ∈ C} × S => oracle p.1 p.2))
    (hquery : Measurable[m] query) (hξ : Measurable[m] ξ)
    (hmem : ∀ ω, query ω ∈ C)
    (hstream : ∀ ω, stream ω = oracle ⟨query ω, hmem ω⟩ (ξ ω)) :
    Measurable[m] stream := by
  let q : Ω → {x : X // x ∈ C} := fun ω => ⟨query ω, hmem ω⟩
  have hq : Measurable[m] q := by
    simpa [q] using hquery.subtype_mk
  have hsample : Measurable[m] (fun ω => oracle (q ω) (ξ ω)) := by
    simpa [q] using
      (@SOptLib.sampledOracle_measurable
        Ω {x : X // x ∈ C} S E
        m (by infer_instance) (by infer_instance) (by infer_instance)
        (oracle := oracle)
        (x := q)
        (ξ := ξ)
        horacle
        hq
        hξ)
  have hEq : stream = fun ω => oracle (q ω) (ξ ω) := by
    funext ω
    simpa [q] using hstream ω
  simpa [hEq] using hsample

/-- A realized sampled-oracle stream is measurable at a later filtration when
its query is measurable at an earlier prefix.

Layer: Model | Gap: Level 0 (filtration-realized oracle-sample measurability)
Proof: lift the query along filtration monotonicity, compose the jointly
  measurable oracle with the query and sample maps, then transport across the
  realization equality.
Source: Mathlib Probability filtration and MeasureTheory product measurable
  composition APIs with SOptLib sampled stochastic-oracle composition
Used in: stochastic accelerated primal-dual generated fixed-domain `A_x` oracle
  sample adaptedness from a predictable query and a later sample coordinate
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/3/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem measurableAt_realizedOracleSample_of_query_le
    {Ω X S E : Type*} [MeasurableSpace X] [MeasurableSpace S]
    [MeasurableSpace E]
    (mΩ : MeasurableSpace Ω) (filt : Filtration ℕ mΩ)
    {oracle : X → S → E} {query : Ω → X} {ξ : Ω → S} {stream : Ω → E}
    {i j : ℕ}
    (hij : i ≤ j)
    (horacle : Measurable (fun p : X × S => oracle p.1 p.2))
    (hquery_prefix : Measurable[filt.seq i] query)
    (hξ_j : Measurable[filt.seq j] ξ)
    (hstream : ∀ ω, stream ω = oracle (query ω) (ξ ω)) :
    Measurable[filt.seq j] stream := by
  have hquery_j : Measurable[filt.seq j] query :=
    hquery_prefix.mono (filt.mono hij) le_rfl
  have hsample : Measurable[filt.seq j] (fun ω => oracle (query ω) (ξ ω)) :=
    @SOptLib.sampledOracle_measurable
      Ω X S E
      (filt.seq j) (by infer_instance) (by infer_instance) (by infer_instance)
      (oracle := oracle)
      (x := query)
      (ξ := ξ)
      horacle
      hquery_j
      hξ_j
  have hEq : stream = fun ω => oracle (query ω) (ξ ω) := by
    funext ω
    exact hstream ω
  simpa [hEq] using hsample

/-- A realized sampled-oracle stream is measurable at the successor filtration
when its query is predictable at the previous prefix.

If the random query is measurable with respect to `filt.seq i`, the sample
coordinate is measurable with respect to `filt.seq (i+1)`, and a stream agrees
pointwise with a jointly measurable oracle evaluated at those inputs, then the
stream is measurable with respect to the successor sigma-algebra.

Layer: Model | Gap: Level 0 (successor-filtration realized oracle-sample measurability)
Proof: lift the predictable query from `filt.seq i` to `filt.seq (i+1)` by
  filtration monotonicity, compose the jointly measurable oracle with the
  query/sample pair, then transport measurability across the realization
  equality.
Source: Mathlib Probability filtration and MeasureTheory product measurable
  composition APIs with SOptLib sampled stochastic-oracle composition
Used in: stochastic accelerated primal-dual generated fixed-domain `A_x` oracle
  sample adaptedness from a predictable query and the next sample coordinate
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/3/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem measurableAt_succ_realizedOracleSample_of_prefix_query
    {Ω X S E : Type*} [MeasurableSpace X] [MeasurableSpace S]
    [MeasurableSpace E]
    (mΩ : MeasurableSpace Ω) (filt : Filtration ℕ mΩ)
    {oracle : X → S → E} {query : Ω → X} {ξ : Ω → S} {stream : Ω → E}
    (i : ℕ)
    (horacle : Measurable (fun p : X × S => oracle p.1 p.2))
    (hquery_prefix : Measurable[filt.seq i] query)
    (hξ_succ : Measurable[filt.seq (i + 1)] ξ)
    (hstream : ∀ ω, stream ω = oracle (query ω) (ξ ω)) :
    Measurable[filt.seq (i + 1)] stream :=
  measurableAt_realizedOracleSample_of_query_le mΩ filt (Nat.le_succ i)
    horacle hquery_prefix hξ_succ hstream

/-- A state query adapted at an earlier filtration slice is measurable at a
stage-separated later cutoff.

If an adaptedness predicate exposes measurability of a query projection from a
state process at `filt.seq i`, then the same query is measurable at the later
stage-separated prefix `filt.seq (T + i)`.

Layer: Model | Gap: Level 1 (stage-separated adapted-query prefix measurability)
Proof: extract projection measurability from the adapted-state interface, then
  lift it along filtration monotonicity using `i ≤ T + i`.
Source: Mathlib MeasureTheory measurable-function monotonicity, process
  filtrations, and natural-number order arithmetic
Used in: stochastic accelerated primal-dual stage-separated dual-query
  measurability before fresh adjoint-oracle variance and independence bounds
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem stageSeparatedQuery_prefixMeasurable_of_adapted_state
    {Ω State Query : Type*} [MeasurableSpace Ω] [MeasurableSpace Query]
    (filt : Filtration ℕ (by infer_instance : MeasurableSpace Ω))
    (state : Ω → State)
    (queryOfState : State → Query)
    (AdaptedAt : MeasurableSpace Ω → (Ω → State) → Prop)
    (T i : ℕ)
    (hquery :
      ∀ {mΩ : MeasurableSpace Ω} {x : Ω → State},
        AdaptedAt mΩ x → Measurable[mΩ] (fun ω => queryOfState (x ω)))
    (hstate : AdaptedAt (filt.seq i) state) :
    Measurable[filt.seq (T + i)] (fun ω => queryOfState (state ω)) := by
  have hquery_i :
      Measurable[filt.seq i] (fun ω => queryOfState (state ω)) :=
    hquery hstate
  exact hquery_i.mono (filt.mono (by omega)) le_rfl

/-- A finite-horizon adapted process supplies stage-separated prefix measurability
for every query in the horizon interval.

If each process slice up to `T` is adapted at its own filtration cutoff and the
adaptedness interface exposes measurability of a query projection, then every
stage-separated query slice is measurable at the later prefix `filt.seq (T+i)`.

Layer: Model | Gap: Level 1 (finite-horizon stage-separated adapted-query prefix measurability)
Proof: specialize the adapted-process hypothesis at the queried index using
  the upper bound from `i ∈ Icc 1 T`, then apply the single-state
  stage-separated prefix measurability theorem.
Source: Mathlib MeasureTheory measurable-function monotonicity, process
  filtrations, finite interval indexing, and natural-number order arithmetic
Used in: stochastic accelerated primal-dual stage-separated dual-query
  measurability before fresh adjoint-oracle variance and independence bounds
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem stageSeparatedQuery_prefixMeasurable_of_adapted_process
    {Ω State Query : Type*} [MeasurableSpace Ω] [MeasurableSpace Query]
    (filt : Filtration ℕ (by infer_instance : MeasurableSpace Ω))
    (state : ℕ → Ω → State)
    (queryOfState : State → Query)
    (AdaptedAt : MeasurableSpace Ω → (Ω → State) → Prop)
    (T : ℕ)
    (hquery :
      ∀ {mΩ : MeasurableSpace Ω} {x : Ω → State},
        AdaptedAt mΩ x → Measurable[mΩ] (fun ω => queryOfState (x ω)))
    (hadapted : ∀ j, j ≤ T → AdaptedAt (filt.seq j) (state j)) :
    ∀ i, ∀ hi : i ∈ Finset.Icc 1 T,
      Measurable[filt.seq (T + i)] (fun ω => queryOfState (state i ω)) := by
  intro i hi
  exact
    stageSeparatedQuery_prefixMeasurable_of_adapted_state
      (filt := filt)
      (state := state i)
      (queryOfState := queryOfState)
      (AdaptedAt := AdaptedAt)
      (T := T)
      (i := i)
      (hquery := hquery)
      (hstate := hadapted i (Finset.mem_Icc.mp hi).2)

/-- A successor-adapted process supplies stage-separated prefix measurability
for every positive-horizon query.

If each process slice `i` is adapted after the successor cutoff `filt.seq
(i+1)` and the adaptedness interface exposes measurability of a query
projection, then every positive-index stage-separated query is measurable at
the later prefix `filt.seq (T+i)`.

Layer: Model | Gap: Level 1 (successor-adapted stage-separated query prefix measurability)
Proof: specialize the successor-adapted process hypothesis at the queried
  index, obtain query measurability from the adaptedness accessor, and lift
  along filtration monotonicity using `i + 1 ≤ T + i`.
Source: Mathlib MeasureTheory measurable-function monotonicity, process
  filtrations, finite interval indexing, and natural-number order arithmetic
Used in: stochastic accelerated primal-dual stage-separated dual-query
  measurability before fresh adjoint-oracle variance and independence bounds
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem stageSeparatedQuery_prefixMeasurable_of_succ_adapted_process
    {Ω State Query : Type*} [MeasurableSpace Ω] [MeasurableSpace Query]
    (filt : Filtration ℕ (by infer_instance : MeasurableSpace Ω))
    (state : ℕ → Ω → State)
    (queryOfState : State → Query)
    (AdaptedAt : MeasurableSpace Ω → (Ω → State) → Prop)
    (T : ℕ)
    (hquery :
      ∀ {mΩ : MeasurableSpace Ω} {x : Ω → State},
        AdaptedAt mΩ x → Measurable[mΩ] (fun ω => queryOfState (x ω)))
    (hadapted :
      ∀ j, j ≤ T → AdaptedAt (filt.seq (j + 1)) (state j)) :
    ∀ i, ∀ hi : i ∈ Finset.Icc 1 T,
      Measurable[filt.seq (T + i)] (fun ω => queryOfState (state i ω)) := by
  intro i hi
  have hi_pair : 1 ≤ i ∧ i ≤ T := Finset.mem_Icc.mp hi
  have hstate :
      AdaptedAt (filt.seq (i + 1)) (state i) :=
    hadapted i hi_pair.2
  have hquery_i :
      Measurable[filt.seq (i + 1)] (fun ω => queryOfState (state i ω)) :=
    hquery hstate
  exact hquery_i.mono (filt.mono (by omega)) le_rfl

end SOptLib

namespace SOptLib

/-- A product-measurable stochastic oracle kernel has measurable fixed decision fibers.

If a curried oracle `G : X → S → E` is measurable through its product
presentation `fun p : X × S => G p.1 p.2`, then fixing the decision variable
leaves a measurable function of the sample variable.

Layer: Model | Gap: Level 0 (fixed-decision oracle fiber measurability)
Proof: compose the product-measurable oracle with the measurable map
  `s ↦ (x, s)`, whose first coordinate is constant and second coordinate is
  the identity.
Source: Mathlib MeasureTheory product measurable-space and composition APIs
Used in: randomized stochastic mirror descent fixed-query stochastic oracle measurability
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic mirror descent -/
theorem measurable_fiber_of_prod_measurable
    {X S E : Type*} [MeasurableSpace X] [MeasurableSpace S] [MeasurableSpace E]
    {G : X → S → E}
    (hG : Measurable (fun p : X × S => G p.1 p.2)) (x : X) :
    Measurable (fun s => G x s) := by
  have hx : Measurable (fun _ : S => x) := measurable_const
  simpa [Function.comp_def] using hG.comp (hx.prodMk measurable_id)

/-- A product-measurable stochastic oracle kernel remains measurable in uncurried notation.

If a curried oracle `G : X → S → E` is known to be measurable through its
product presentation `fun p : X × S => G p.1 p.2`, then Lean's
`Function.uncurry` presentation of the same kernel is measurable.

Layer: Model | Gap: Level 0 (product-measurable oracle uncurrying bridge)
Proof: unfold `Function.uncurry`; the product presentation and uncurried
  curried presentation are definitionally the same measurable function.
Source: Mathlib MeasureTheory product measurable-space and function uncurrying APIs
Used in: randomized stochastic mirror descent stochastic oracle kernel measurability bridge
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic mirror descent -/
theorem measurable_uncurry_of_prod_measurable
    {X S E : Type*} [MeasurableSpace X] [MeasurableSpace S] [MeasurableSpace E]
    {G : X → S → E}
    (hG : Measurable (fun p : X × S => G p.1 p.2)) :
    Measurable (Function.uncurry fun x s => G x s) := by
  simpa [Function.uncurry] using hG

/-- Empirical average of a staged oracle process over post-optimization sample coordinates.

For an oracle response indexed by a global sample coordinate, a post-sampling
index map selects the validation samples for one run and averages the resulting
oracle values over `i = 1, ..., T`.

Layer: Model | Concept: Oracle
Proof: (definitional construction; scaled finite sum of a staged oracle process over a post-sample index map)
Source: Mathlib finite sums over natural intervals and normed-space scalar multiplication APIs
Used in: nonconvex stochastic mirror descent post-optimization validation oracle average
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
noncomputable def empiricalOracleAverage
    {Ω X E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (oracle : ℕ → X → Ω → E) (postIndex : ℕ → ℕ → ℕ) (T : ℕ)
    (s : ℕ) (x : X) (ω : Ω) : E :=
  ((T : ℝ)⁻¹) •
    Finset.sum (Finset.Icc 1 T)
      (fun i => oracle (postIndex s i) x ω)

/-- The empirical oracle average unfolds to its scaled finite-sum formula.

Layer: Model | Gap: Level 0 (empirical oracle average unfolding)
Proof: by rfl after unfolding `empiricalOracleAverage`.
Source: Mathlib finite sums over natural intervals and normed-space scalar multiplication APIs
Used in: nonconvex stochastic mirror descent post-optimization validation oracle average
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
@[simp]
theorem empiricalOracleAverage_eq_sum
    {Ω X E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (oracle : ℕ → X → Ω → E) (postIndex : ℕ → ℕ → ℕ) (T : ℕ)
    (s : ℕ) (x : X) (ω : Ω) :
    empiricalOracleAverage oracle postIndex T s x ω =
      ((T : ℝ)⁻¹) •
        Finset.sum (Finset.Icc 1 T)
          (fun i => oracle (postIndex s i) x ω) := by
  rfl

/-- Mini-batch oracle average over the natural interval `1, ..., m k`.

For an abstract batch-size schedule, sample-index map, and staged oracle
response, this packages the paper expression `(m k)⁻¹ • ∑ᵢ oracleValue ...`
without committing to a particular sample stream or stochastic process.

Layer: Model | Concept: Oracle
Proof: (definitional construction; scaled finite sum of staged oracle values over a mini-batch index map)
Source: Mathlib finite sums over natural intervals and normed-space scalar multiplication APIs
Used in: nonconvex stochastic mirror descent RSMD inner mini-batch oracle average
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/steps/1/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
noncomputable def miniBatchOracleAverage
    {Ω I X E K SRun : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : K → ℕ) (oracleValue : I → X → Ω → E)
    (sampleIndex : SRun → K → ℕ → I) (s : SRun) (k : K) (x : X) (ω : Ω) : E :=
  ((m k : ℝ)⁻¹) •
    Finset.sum (Finset.Icc 1 (m k))
      (fun i => oracleValue (sampleIndex s k i) x ω)

/-- A finite mini-batch oracle average is measurable along a measurable random query.

If every oracle response in a finite mini-batch is measurable after evaluating
at the same random query `x`, then the scaled finite sum defining the
mini-batch average is measurable.

Layer: Model | Gap: Level 0 (finite mini-batch oracle average measurability)
Proof: apply Mathlib's finite-sum measurability theorem and close the scaled
  average with measurability of constant scalar multiplication.
Source: Mathlib MeasureTheory measurability APIs for finite sums and normed
  vector-space scalar multiplication
Used in: nonconvex stochastic mirror descent mini-batch oracle measurability at
  random iterates
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic mirror descent -/
theorem miniBatchOracle_measurable
    {Ω P E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace P] [MeasurableSpace E]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableAdd₂ E] [MeasurableSMul ℝ E]
    (I : Finset ι) (c : ℝ) (oracle : ι → P → Ω → E) (x : Ω → P)
    (_hx : Measurable x)
    (horacle : ∀ i ∈ I, Measurable (fun ω => oracle i (x ω) ω)) :
    Measurable (fun ω => c • Finset.sum I (fun i => oracle i (x ω) ω)) := by
  exact (Finset.measurable_sum I (fun i hi => horacle i hi)).const_smul c

/-- Time-indexed oracle mean as a Bochner integral at one sample-stream coordinate.

`stagedOracleMean μ G ξ n x` is the mean oracle at decision `x` for the
coordinate process `ξ n`, routed through the reusable `oracleMean` model.

Layer: Model | Concept: Oracle
Proof: (definitional construction; time-indexed sampled oracle mean wrapper around `oracleMean`)
Source: Mathlib Bochner integral primitives and SOptLib stochastic oracle mean definitions
Used in: randomized stochastic mirror descent oracle mean at a global sample-stream coordinate
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic mirror descent -/
noncomputable def stagedOracleMean
    {Ω X S E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (G : X → S → E) (ξ : ℕ → Ω → S) (n : ℕ) (x : X) : E :=
  oracleMean μ G (ξ n) x

/-- The staged oracle mean unfolds to the Bochner integral at the chosen coordinate.

This identity preserves the paper notation for `E[G(x, ξ_n)]` after routing the
coordinate-specific sampled mean through the reusable oracle-mean definition.

Layer: Model | Gap: Level 0 (time-indexed oracle mean unfolding)
Proof: by rfl after unfolding `stagedOracleMean`, `oracleMean`, and `oracleKernel`.
Source: Mathlib Bochner integral primitives and SOptLib stochastic oracle mean definitions
Used in: randomized stochastic mirror descent oracle mean at a global sample-stream coordinate
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic mirror descent -/
theorem stagedOracleMean_def
    {Ω X S E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (G : X → S → E) (ξ : ℕ → Ω → S) (n : ℕ) (x : X) :
    stagedOracleMean μ G ξ n x = ∫ ω, G x (ξ n ω) ∂μ := by
  rfl

/-- Oracle noise residual evaluated at a random query point and a fixed sample coordinate.

For a time-indexed oracle response `oracleValue`, target field `target`, sample
coordinate `n`, and random query `x`, this is the centered process
`ω ↦ oracleValue n (x ω) ω - target (x ω)`.

Layer: Model | Concept: Oracle
Proof: (definitional construction; time-indexed oracle response centered at the
  target field along a random query)
Source: Mathlib function evaluation APIs and subtraction in additive groups
Used in: randomized stochastic mirror descent Assumption 13 residuals along
  algorithm iterates and post-optimization validation queries
Book citation: book/FOML/StochasticMirrorDescent.json#/assumptions/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic mirror descent -/
noncomputable def oracleResidualAtRandomQuery
    {Ω X E : Type*} [Sub E]
    (oracleValue : ℕ → X → Ω → E) (target : X → E)
    (n : ℕ) (x : Ω → X) : Ω → E :=
  fun ω => oracleValue n (x ω) ω - target (x ω)

/-- The random-query oracle residual unfolds to the sampled oracle minus its target.

This pointwise identity exposes the definition used when translating paper
residual notation into integrability, zero-mean, and second-moment hypotheses.

Layer: Model | Gap: Level 0 (random-query oracle residual unfolding)
Proof: by rfl after unfolding `oracleResidualAtRandomQuery`.
Source: Mathlib function evaluation APIs and subtraction in additive groups
Used in: randomized stochastic mirror descent Assumption 13 residuals along
  algorithm iterates and post-optimization validation queries
Book citation: book/FOML/StochasticMirrorDescent.json#/assumptions/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic mirror descent -/
@[simp]
theorem oracleResidualAtRandomQuery_apply
    {Ω X E : Type*} [Sub E]
    (oracleValue : ℕ → X → Ω → E) (target : X → E)
    (n : ℕ) (x : Ω → X) (ω : Ω) :
    oracleResidualAtRandomQuery oracleValue target n x ω =
      oracleValue n (x ω) ω - target (x ω) := by
  rfl

/-- Validation residual obtained by evaluating a time-indexed oracle at a selected output.

For a validation selector `postIndex`, stochastic output process `output`, and
target field `target`, this names the pointwise process
`ω ↦ oracleValue (postIndex t) (output t ω) ω - target (output t ω)`.

Layer: Model | Concept: Oracle
Proof: (definitional construction; selector-indexed oracle residual wrapper
  along a randomized output process)
Source: Mathlib function evaluation APIs and subtraction in additive groups for
  stochastic oracle processes
Used in: nonconvex stochastic mirror descent post-optimization validation residual
  at a randomized run output
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic mirror descent -/
noncomputable def validationResidual
    {Ω X E T I : Type*} [Sub E]
    (oracleValue : I → X → Ω → E)
    (output : T → Ω → X) (target : X → E)
    (postIndex : T → I) (t : T) (ω : Ω) : E :=
  oracleValue (postIndex t) (output t ω) ω - target (output t ω)

/-- The validation residual unfolds to the selected oracle value minus its target.

This pointwise identity preserves the paper notation for fresh validation
oracle calls after routing the randomized output and validation sample index
through the staged model definition.

Layer: Model | Gap: Level 0 (validation residual unfolding)
Proof: by rfl after unfolding `validationResidual`.
Source: Mathlib function evaluation APIs and subtraction in additive groups for
  stochastic oracle processes
Used in: nonconvex stochastic mirror descent post-optimization validation residual
  at a randomized run output
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic mirror descent -/
@[simp]
theorem validationResidual_apply
    {Ω X E T I : Type*} [Sub E]
    (oracleValue : I → X → Ω → E)
    (output : T → Ω → X) (target : X → E)
    (postIndex : T → I) (t : T) (ω : Ω) :
    validationResidual oracleValue output target postIndex t ω =
      oracleValue (postIndex t) (output t ω) ω - target (output t ω) := by
  rfl

/-- Empirical average of validation residuals over the finite window `1, ..., T`.

The index map separates the finite validation coordinate from the residual
process, so the same definition applies to flattened sample streams, tagged
sample families, or direct natural validation indices.

Layer: Model | Concept: Oracle
Proof: (definitional construction; scaled finite sum of indexed validation residual vectors)
Source: Mathlib finite sums over natural intervals and normed-space scalar multiplication APIs
Used in: nonconvex stochastic mirror descent post-optimization validation residual average
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
noncomputable def validationAverageResidual
    {Ω E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℕ) (index : ℕ → I) (residual : I → Ω → E) (ω : Ω) : E :=
  ((T : ℝ)⁻¹) •
    Finset.sum (Finset.Icc 1 T)
      (fun i => residual (index i) ω)

/-- Residual process formed by subtracting a deterministic target from a mini-batch oracle at an iterate.

For a time-indexed mini-batch oracle, target map, and stochastic iterate process,
this names the pointwise centered oracle average used in variance-transfer
arguments.

Layer: Model | Concept: Oracle
Proof: (definitional construction; pointwise mini-batch oracle residual wrapper at a stochastic iterate)
Source: Mathlib normed additive group and function evaluation APIs for stochastic oracle processes
Used in: randomized stochastic mirror descent mini-batch residual variance transfer at a fixed iterate
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic mirror descent -/
def miniBatchResidualAtIterate
    {Ω P E T : Type*} [NormedAddCommGroup E]
    (miniBatch : T → P → Ω → E) (target : P → E)
    (x : T → Ω → P) (t : T) (ω : Ω) : E :=
  miniBatch t (x t ω) ω - target (x t ω)

/-- The staged mini-batch residual unfolds to the oracle average minus its target at the iterate.

This simp lemma preserves the local rewriting pattern used in stochastic mirror
descent proofs after the residual process is routed through the staged model
definition.

Layer: Model | Gap: Level 0 (mini-batch residual unfolding)
Proof: by rfl after unfolding `miniBatchResidualAtIterate`.
Source: Mathlib normed additive group and function evaluation APIs for stochastic oracle processes
Used in: randomized stochastic mirror descent mini-batch residual variance transfer at a fixed iterate
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic mirror descent -/
@[simp]
theorem miniBatchResidualAtIterate_apply
    {Ω P E T : Type*} [NormedAddCommGroup E]
    (miniBatch : T → P → Ω → E) (target : P → E)
    (x : T → Ω → P) (t : T) (ω : Ω) :
    miniBatchResidualAtIterate miniBatch target x t ω =
      miniBatch t (x t ω) ω - target (x t ω) := by
  rfl

/-- A mini-batch residual evaluated along a measurable random iterate is measurable.

For a time-indexed mini-batch oracle, if the mini-batch response is measurable
after plugging in the random iterate and the deterministic target is measurable,
then the centered residual process is measurable.

Layer: Model | Gap: Level 0 (mini-batch residual measurability at random iterate)
Proof: compose target measurability with iterate measurability, then apply
  Mathlib's measurable subtraction API after unfolding the residual wrapper.
Source: Mathlib MeasureTheory measurability APIs for composition and subtraction
Used in: randomized stochastic mirror descent mini-batch residual variance
  transfer at a fixed iterate
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic mirror descent -/
theorem miniBatchResidualAtIterate_measurable
    {Ω P E T : Type*} [MeasurableSpace Ω] [MeasurableSpace P] [MeasurableSpace E]
    [NormedAddCommGroup E] [MeasurableSub₂ E]
    (miniBatch : T → P → Ω → E) (target : P → E)
    (x : T → Ω → P) (t : T)
    (hminiBatch : Measurable (fun ω => miniBatch t (x t ω) ω))
    (htarget : Measurable target) (hx : Measurable (x t)) :
    Measurable (fun ω => miniBatchResidualAtIterate miniBatch target x t ω) := by
  simpa [miniBatchResidualAtIterate] using hminiBatch.sub (htarget.comp hx)

/-- The canonical iid stream law with one-time marginal `mu`.

For a measurable sample space `A`, this is the infinite product measure on
`Nat`-indexed streams whose coordinate law is the same measure `mu` at every
time.

Layer: Model | Concept: Probability
Proof: (definitional construction; constant-family specialization of Mathlib's infinite product measure)
Source: Mathlib probability product measures and infinite product construction
Used in: stochastic block mirror descent iid oracle/block sample-pair stream
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic block mirror descent -/
noncomputable def iidStreamLaw
    {A : Type*} [MeasurableSpace A] (mu : Measure A) : Measure (ℕ → A) :=
  Measure.infinitePi (fun _ : ℕ => mu)

/-- The iid stream law of a probability measure is a probability measure.

Layer: Model | Gap: Level 0 (iid product-stream probability measure)
Proof: unfold `iidStreamLaw` and use Mathlib's probability-measure instance for
  infinite products of probability measures.
Source: Mathlib probability product measures and `IsProbabilityMeasure` instances
Used in: stochastic block mirror descent probability instance for the canonical sample-pair stream
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic block mirror descent -/
@[instance]
theorem iidStreamLaw_isProbabilityMeasure
    {A : Type*} [MeasurableSpace A] (mu : Measure A) [IsProbabilityMeasure mu] :
    IsProbabilityMeasure (iidStreamLaw mu) := by
  unfold iidStreamLaw
  infer_instance

/-- Coordinate projections are independent under the iid stream law.

Layer: Model | Gap: Level 0 (iid coordinate independence)
Proof: unfold `iidStreamLaw` and apply Mathlib's `iIndepFun_infinitePi` theorem
  to the measurable coordinate projections.
Source: Mathlib probability independence API for infinite product measures
Used in: stochastic block mirror descent independence of fresh oracle/block sample pairs across iteration time
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic block mirror descent -/
theorem iidStreamLaw_iIndepFun_eval
    {A : Type*} [MeasurableSpace A] (mu : Measure A) [IsProbabilityMeasure mu] :
    iIndepFun (fun t (omega : ℕ → A) => omega t) (iidStreamLaw mu) := by
  unfold iidStreamLaw
  exact ProbabilityTheory.iIndepFun_infinitePi (fun _ : ℕ => measurable_id)

/-- Every coordinate projection of the iid stream law has marginal law `mu`.

Layer: Model | Gap: Level 0 (iid coordinate marginal law)
Proof: unfold `iidStreamLaw` and specialize Mathlib's marginal theorem
  `Measure.infinitePi_map_eval` to the constant family.
Source: Mathlib probability product measures and coordinate marginal API
Used in: stochastic block mirror descent transport from stream samples to one-step oracle/block laws
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic block mirror descent -/
theorem iidStreamLaw_map_eval
    {A : Type*} [MeasurableSpace A] (mu : Measure A) [IsProbabilityMeasure mu] (t : ℕ) :
    Measure.map (fun omega : ℕ → A => omega t) (iidStreamLaw mu) = mu := by
  unfold iidStreamLaw
  simpa using (MeasureTheory.Measure.infinitePi_map_eval (μ := fun _ : ℕ => mu) t)

/-- Finite discrete sampling law induced by nonnegative real weights summing to one.

For a finite measurable space, real weights `p a ≥ 0` with total mass one define
the canonical measure whose atom at `a` has mass `ENNReal.ofReal (p a)`.

Layer: Model | Concept: Probability
Proof: (definitional construction; finite PMF from normalized real weights followed by `PMF.toMeasure`)
Source: Mathlib probability mass functions, finite sums, and measure construction from discrete laws
Used in: stochastic block mirror descent block-index sampling and coordinate-selection expectations
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic block mirror descent -/
noncomputable def finiteBlockIndexLaw
    {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (p : ι → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1) : Measure ι :=
  (PMF.ofFintypeOfReal p hp_nonneg hp_sum).toMeasure

/-- The finite discrete sampling law assigns singleton mass `ENNReal.ofReal (p i)`.

Layer: Model | Gap: Level 0 (finite real-weight law singleton mass)
Proof: unfold the measure-level law, apply `PMF.toMeasure_apply_singleton`, and
  simplify the PMF mass with `PMF.ofFintypeOfReal_apply`.
Source: Mathlib probability mass functions, singleton measurable sets, and finite discrete measures
Used in: stochastic block mirror descent replacement of sampled block probabilities by real weights
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic block mirror descent -/
@[simp]
theorem finiteBlockIndexLaw_singleton
    {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (p : ι → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1) (i : ι) :
    finiteBlockIndexLaw p hp_nonneg hp_sum ({i} : Set ι) = ENNReal.ofReal (p i) := by
  simpa [finiteBlockIndexLaw] using
    (PMF.toMeasure_apply_singleton
      (PMF.ofFintypeOfReal p hp_nonneg hp_sum) i (measurableSet_singleton i))

/-- The finite discrete sampling law from normalized real weights is a probability measure.

Layer: Model | Gap: Level 0 (finite real-weight law probability measure)
Proof: unfold the law and use the probability-measure instance for a PMF's
  associated measure.
Source: Mathlib probability mass functions and probability-measure instances
Used in: stochastic block mirror descent product sampling law and block-coordinate expectation integrals
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic block mirror descent -/
theorem finiteBlockIndexLaw_isProbabilityMeasure
    {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (p : ι → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1) :
    IsProbabilityMeasure (finiteBlockIndexLaw p hp_nonneg hp_sum) := by
  unfold finiteBlockIndexLaw
  infer_instance

/-- Scalarized residual of a sampled block oracle after inverse-probability lifting.

At time `k`, the sampled block `block k ω` selects the lifted stochastic block
oracle value at the random iterate `xIter k ω`; after scaling by the inverse
sampling probability and centering by `meanGrad`, the residual is paired with
the comparison displacement `target - xIter k ω`.

Layer: Model | Concept: Oracle
Proof: (definitional construction; inverse-probability lifted block oracle residual paired with a comparison displacement)
Source: Mathlib real inner-product spaces, scalar multiplication, and additive-group operations
Used in: stochastic block mirror descent one-step descent noise term and martingale residual scalarization
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic block mirror descent -/
noncomputable def blockOracleResidualInner
    {Ω S ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (block : ℕ → Ω → ι) (sample : ℕ → Ω → S) (xIter : ℕ → Ω → E)
    (sampleGradLift : ι → E → S → E) (meanGrad : E → E) (p : ι → ℝ)
    (target : E) (k : ℕ) (ω : Ω) : ℝ :=
  let i_k := block k ω
  let x_k := xIter k ω
  ⟪(p i_k)⁻¹ • sampleGradLift i_k x_k (sample k ω) - meanGrad x_k, target - x_k⟫_ℝ

/-- The scalarized sampled block oracle residual unfolds to its inner-product formula.

Layer: Model | Gap: Level 0 (sampled block oracle residual unfolding)
Proof: by rfl after unfolding `blockOracleResidualInner`.
Source: Mathlib real inner-product spaces, scalar multiplication, and additive-group operations
Used in: stochastic block mirror descent one-step descent noise term and martingale residual scalarization
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic block mirror descent -/
@[simp]
theorem blockOracleResidualInner_apply
    {Ω S ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (block : ℕ → Ω → ι) (sample : ℕ → Ω → S) (xIter : ℕ → Ω → E)
    (sampleGradLift : ι → E → S → E) (meanGrad : E → E) (p : ι → ℝ)
    (target : E) (k : ℕ) (ω : Ω) :
    blockOracleResidualInner block sample xIter sampleGradLift meanGrad p target k ω =
      (let i_k := block k ω
       let x_k := xIter k ω
       ⟪(p i_k)⁻¹ • sampleGradLift i_k x_k (sample k ω) - meanGrad x_k,
         target - x_k⟫_ℝ) := by
  rfl

/-- Importance-weighted squared dual norm of a sampled block oracle.

At time `k`, the sampled block `block k ω` selects both the oracle codomain and
the block dual norm. The selected squared dual norm is weighted by the inverse
sampling probability for that block.

Layer: Model | Concept: Oracle
Proof: (definitional construction; selected-block oracle norm square scaled by inverse sampling probability)
Source: Stochastic block-coordinate mirror descent second-moment notation and Mathlib real arithmetic primitives
Used in: stochastic block mirror descent one-step descent quadratic term and random-iterate second-moment transport
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec/steps/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic block mirror descent -/
noncomputable def blockOracleQuadraticTerm
    {Ω S ι X : Type*} {B : ι → Type*}
    (block : ℕ → Ω → ι) (sample : ℕ → Ω → S) (xIter : ℕ → Ω → X)
    (sampleGrad : (i : ι) → X → S → B i) (dualNorm : (i : ι) → B i → ℝ)
    (p : ι → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  let i_k := block k ω
  let x_k := xIter k ω
  (p i_k)⁻¹ * dualNorm i_k (sampleGrad i_k x_k (sample k ω)) ^ 2

/-- The sampled block oracle quadratic term unfolds to its inverse-probability
weighted squared-dual-norm formula.

Layer: Model | Gap: Level 0 (sampled block oracle quadratic unfolding)
Proof: by rfl after unfolding `blockOracleQuadraticTerm`.
Source: Stochastic block-coordinate mirror descent second-moment notation and Mathlib real arithmetic primitives
Used in: stochastic block mirror descent one-step descent quadratic term and random-iterate second-moment transport
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec/steps/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic block mirror descent -/
@[simp]
theorem blockOracleQuadraticTerm_def
    {Ω S ι X : Type*} {B : ι → Type*}
    (block : ℕ → Ω → ι) (sample : ℕ → Ω → S) (xIter : ℕ → Ω → X)
    (sampleGrad : (i : ι) → X → S → B i) (dualNorm : (i : ι) → B i → ℝ)
    (p : ι → ℝ) (k : ℕ) (ω : Ω) :
    blockOracleQuadraticTerm block sample xIter sampleGrad dualNorm p k ω =
      (let i_k := block k ω
       let x_k := xIter k ω
       (p i_k)⁻¹ * dualNorm i_k (sampleGrad i_k x_k (sample k ω)) ^ 2) := by
  rfl

/-- A projected stochastic oracle is measurable under jointly measurable oracle data.

If an oracle kernel is jointly measurable in query and sample, the query and
sample are measurable from a source sigma-algebra, and the block-coordinate
projection is measurable, then the projected sampled oracle value is measurable
from the same source.

Layer: Model | Gap: Level 0 (projected sampled oracle measurability)
Proof: build the product map `ω ↦ (x ω, ξ ω)`, compose the jointly measurable
  oracle with it, and post-compose with the measurable block projection.
Source: Mathlib MeasureTheory product measurable-space and measurable
  composition APIs
Used in: stochastic block mirror descent fixed-block sampled gradient
  coordinate measurability before the block prox selector
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem blockOracle_measurable_of_joint_measurable
    {Ω X S E B : Type*} [MeasurableSpace X] [MeasurableSpace S]
    [MeasurableSpace E] [MeasurableSpace B]
    (m : MeasurableSpace Ω)
    {oracle : X → S → E} {coord : E → B} {x : Ω → X} {ξ : Ω → S}
    (horacle : Measurable (fun p : X × S => oracle p.1 p.2))
    (hcoord : Measurable coord)
    (hx : Measurable[m] x) (hξ : Measurable[m] ξ) :
    Measurable[m] (fun ω => coord (oracle (x ω) (ξ ω))) := by
  have horacle_sampled : Measurable[m] (fun ω => oracle (x ω) (ξ ω)) := by
    simpa [Function.comp_def] using horacle.comp (hx.prodMk hξ)
  exact hcoord.comp horacle_sampled

/-- Backward-compatible name for projected sampled-oracle measurability.

Layer: Model | Gap: Level 0 (projected sampled oracle measurability)
Proof: direct alias of `blockOracle_measurable_of_joint_measurable`.
Source: Mathlib MeasureTheory product measurable-space and measurable composition APIs
Used in: stochastic block mirror descent fixed-block sampled gradient coordinate measurability
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic block mirror descent -/
theorem oracle_postcomp_measurable_of_joint_measurable
    {Ω X S E B : Type*} [MeasurableSpace X] [MeasurableSpace S]
    [MeasurableSpace E] [MeasurableSpace B]
    (m : MeasurableSpace Ω)
    {oracle : X → S → E} {coord : E → B} {x : Ω → X} {ξ : Ω → S}
    (horacle : Measurable (fun p : X × S => oracle p.1 p.2))
    (hcoord : Measurable coord)
    (hx : Measurable[m] x) (hξ : Measurable[m] ξ) :
    Measurable[m] (fun ω => coord (oracle (x ω) (ξ ω))) := by
  exact blockOracle_measurable_of_joint_measurable m horacle hcoord hx hξ

/-- Pointwise estimator error obtained by subtracting the target field at a query.

For an estimator value `G` at a point `x`, `oracleEstimatorError target G x`
names the centered quantity `G - target x`. This is the non-process version of
the estimator residual used in one-step oracle and Wolfe-gap algebra.

Layer: Model | Concept: Oracle
Proof: (definitional construction; pointwise estimator value centered at a target field)
Source: Mathlib function evaluation and subtraction APIs for stochastic oracle notation
Used in: stochastic nonconvex conditional gradient Wolfe-gap estimator-error term
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/parameters/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic nonconvex conditional gradient -/
def oracleEstimatorError
    {X E : Type*} [Sub E] (target : X → E) (G : E) (x : X) : E :=
  G - target x

/-- The pointwise estimator error unfolds to estimator minus target.

Layer: Model | Gap: Level 0 (pointwise estimator-error unfolding)
Proof: by rfl after unfolding `oracleEstimatorError`.
Source: Mathlib function evaluation and subtraction APIs for stochastic oracle notation
Used in: stochastic nonconvex conditional gradient Wolfe-gap estimator-error term
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/parameters/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic nonconvex conditional gradient -/
@[simp]
theorem oracleEstimatorError_def
    {X E : Type*} [Sub E] (target : X → E) (G : E) (x : X) :
    oracleEstimatorError target G x = G - target x := by
  rfl

/-- The pointwise estimator error is measurable along measurable estimator and query processes.

For a random estimator value `G` and random query `x`, measurability of the target field
transfers through the centered error `ω ↦ oracleEstimatorError target (G ω) (x ω)`.

Layer: Model | Gap: Level 0 (pointwise estimator-error measurability)
Proof: compose target measurability with query measurability, then apply Mathlib's
  measurable subtraction API after unfolding `oracleEstimatorError`.
Source: Mathlib MeasureTheory measurability APIs for composition and subtraction
Used in: stochastic nonconvex conditional gradient Wolfe-gap estimator-error term
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/parameters/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic nonconvex conditional gradient -/
theorem oracleEstimatorError_measurable
    {Ω X E : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace E]
    [Sub E] [MeasurableSub₂ E]
    (target : X → E) (G : Ω → E) (x : Ω → X)
    (hG : Measurable G) (hx : Measurable x) (htarget : Measurable target) :
    Measurable (fun ω => oracleEstimatorError target (G ω) (x ω)) := by
  simpa [oracleEstimatorError] using hG.sub (htarget.comp hx)

/-- Smoothness-proportional finite-component importance weight.

For a component smoothness family `Lcomp`, component-count normalizer `n`, and
average/global smoothness scale `L`, this names the sampling weight
`Lcomp i / (n * L)` used by finite-sum stochastic oracle models.

Layer: Model | Concept: Oracle
Proof: (definitional construction; finite-component smoothness-proportional sampling weight)
Source: finite-sum stochastic gradient importance sampling conventions
Used in: stochastic nonconvex conditional gradient component sampling probabilities
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic nonconvex conditional gradient -/
noncomputable def smoothnessImportanceWeight
    {ι : Type*} (Lcomp : ι → ℝ) (n L : ℝ) (i : ι) : ℝ :=
  Lcomp i / (n * L)

/-- A smoothness-proportional importance weight is nonnegative under
nonnegative component, count, and smoothness scales.

Layer: Model | Gap: Level 0 (finite smoothness-importance weight nonnegativity)
Proof: numerator and denominator are nonnegative, so the quotient is nonnegative.
Source: Mathlib ordered-field division and finite-sum importance-sampling weights
Used in: stochastic nonconvex conditional gradient component sampling probabilities
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem smoothnessImportanceWeight_nonneg
    {ι : Type*} {Lcomp : ι → ℝ} {n L : ℝ}
    (hcomp : ∀ i, 0 ≤ Lcomp i) (hn : 0 ≤ n) (hL : 0 ≤ L) (i : ι) :
    0 ≤ smoothnessImportanceWeight Lcomp n L i := by
  unfold smoothnessImportanceWeight
  exact div_nonneg (hcomp i) (mul_nonneg hn hL)

/-- Residual process formed by subtracting a target field at the current random iterate.

For an already-realized estimator process `estimator`, iterate process `iterate`,
and deterministic target field `target`, this names the centered process
`ω ↦ estimator k ω - target (iterate k ω)` at time `k`.

Layer: Model | Concept: Oracle
Proof: (definitional construction; pointwise estimator-process residual along a stochastic iterate)
Source: Mathlib function evaluation and subtraction APIs for stochastic process notation
Used in: stochastic nonconvex conditional gradient recursive gradient-estimator residual
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/parameters/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic nonconvex conditional gradient -/
def estimatorResidualProcess
    {Ω T X E : Type*} [Sub E]
    (estimator : T → Ω → E) (iterate : T → Ω → X) (target : X → E)
    (k : T) (ω : Ω) : E :=
  estimator k ω - target (iterate k ω)

/-- The estimator residual process unfolds to estimator minus target at the iterate.

This pointwise identity exposes the centered estimator-error formula used when
transporting recursive gradient-estimator notation into measurability,
conditional-expectation, and second-moment goals.

Layer: Model | Gap: Level 0 (estimator-process residual unfolding)
Proof: by rfl after unfolding `estimatorResidualProcess`.
Source: Mathlib function evaluation and subtraction APIs for stochastic process notation
Used in: stochastic nonconvex conditional gradient recursive gradient-estimator residual
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/parameters/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic nonconvex conditional gradient -/
@[simp]
theorem estimatorResidualProcess_apply
    {Ω T X E : Type*} [Sub E]
    (estimator : T → Ω → E) (iterate : T → Ω → X) (target : X → E)
    (k : T) (ω : Ω) :
    estimatorResidualProcess estimator iterate target k ω =
      estimator k ω - target (iterate k ω) := by
  rfl

/-- An exact-refresh estimator residual is zero at an epoch-start index.

If an estimator process agrees with its deterministic target field evaluated
at the current random iterate at an epoch boundary, then the corresponding
estimator residual process vanishes at that boundary.

Layer: Model | Gap: Level 0 (exact-refresh estimator residual epoch-start base case)
Proof: apply function extensionality, unfold `estimatorResidualProcess`, rewrite
  by the refresh equality at the selected epoch start, and cancel `x - x`.
Source: Mathlib additive-group cancellation and stochastic-optimization residual-process notation
Used in: finite-sum stochastic nonconvex conditional gradient epoch-refresh residual base case
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic nonconvex conditional gradient -/
theorem estimatorResidualProcess_epochStart_eq_zero
    {Ω T X E : Type*} [AddGroup E]
    (estimator : T → Ω → E) (iterate : T → Ω → X) (target : X → E)
    (epochStart : T)
    (hrefresh : estimator epochStart = fun ω => target (iterate epochStart ω)) :
    (fun ω => estimatorResidualProcess estimator iterate target epochStart ω) = fun _ => 0 := by
  funext ω
  have hω := congrArg (fun f => f ω) hrefresh
  simp [estimatorResidualProcess, hω]

/-- A successor-time process recursion transports to one-based global epoch coordinates.

If a process satisfies a two-time recursion from `k + 1` to `k + 2` whenever
`k + 1` is not an epoch-refresh boundary, then for every within-epoch
coordinate `2 ≤ j ≤ T` the same recursion holds between
`global_index T s (j - 1)` and `global_index T s j`.

Layer: Model | Gap: Level 1 (fixed-length epoch recursion transport)
Proof: choose `k = global_index T s (j - 1) - 1`, prove the predecessor and
  successor equalities by natural-number arithmetic, and use `j - 1 < T` to
  discharge the non-refresh modulo side condition.
Source: Mathlib natural-number modulo arithmetic and additive process recursions
Used in: stochastic nonconvex conditional-gradient finite-sum estimator-error
  recursion inside non-refresh epoch steps
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem global_index_recursive_of_succ
    {Ω E : Type*} [Add E] [Sub E]
    (T : ℕ) (process : ℕ → Ω → E) (increment correction : ℕ → ℕ → Ω → E)
    (hrec : ∀ k, (k + 1) % T ≠ 0 → ∀ ω,
      process (k + 2) ω =
        process (k + 1) ω + increment (k + 1) (k + 2) ω -
          correction (k + 1) (k + 2) ω)
    (s j : ℕ) (hj2 : 2 ≤ j) (hjT : j ≤ T) :
    ∀ ω,
      process (global_index T s j) ω =
        process (global_index T s (j - 1)) ω +
          increment (global_index T s (j - 1)) (global_index T s j) ω -
        correction (global_index T s (j - 1)) (global_index T s j) ω := by
  let k := global_index T s (j - 1) - 1
  have hprev_pos : 1 ≤ global_index T s (j - 1) := by
    rw [global_index_def]
    omega
  have hk1 : k + 1 = global_index T s (j - 1) := by
    dsimp [k]
    exact Nat.sub_add_cancel hprev_pos
  have hk2 : k + 2 = global_index T s j := by
    dsimp [k]
    rw [show global_index T s (j - 1) - 1 + 2 =
        global_index T s (j - 1) + 1 by omega]
    simp [global_index_def]
    omega
  have hmod : (k + 1) % T ≠ 0 := by
    have hj1_lt : j - 1 < T := by
      omega
    have hmod_eq : global_index T s (j - 1) % T = j - 1 := by
      rw [global_index_def]
      rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj1_lt]
    rw [hk1, hmod_eq]
    omega
  intro ω
  simpa [hk1, hk2] using hrec k hmod ω

/-- A recursive process increment written as an average minus a target can be
rewritten as an average of centered residuals.

Given a pathwise recursion whose fresh increment is
`m⁻¹ • ∑ i ∈ I, a i ω - target ω`, a nonempty batch with cardinality `m`
lets the same recursion be stated with increment
`m⁻¹ • ∑ i ∈ I, (a i ω - target ω)`.

Layer: Model | Gap: Level 1 (recursive mini-batch residual centering)
Proof: specialize the pathwise recursion, apply the finite mini-batch
  centering identity, and regroup the additive previous-state term.
Source: Mathlib finite sums, real scalar actions, and additive-group algebra
Used in: stochastic nonconvex conditional-gradient finite-sum estimator-error
  recursion before mini-batch variance reduction
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem process_recursive_average_sub_target_eq_average_residual
    {Ω ι E : Type*} [AddCommGroup E] [Module ℝ E]
    (I : Finset ι) (m : ℕ) (hmcard : I.card = m) (hmpos : 0 < m)
    (process : ℕ → Ω → E) (prev curr : ℕ)
    (a : ι → Ω → E) (target : Ω → E)
    (hrec : ∀ ω,
      process curr ω =
        process prev ω + ((m : ℝ)⁻¹) • Finset.sum I (fun i => a i ω) -
          target ω) :
    ∀ ω,
      process curr ω =
        process prev ω +
          ((m : ℝ)⁻¹) • Finset.sum I (fun i => a i ω - target ω) := by
  intro ω
  have hcenter :
      ((m : ℝ)⁻¹) • Finset.sum I (fun i => a i ω) - target ω =
        ((m : ℝ)⁻¹) • Finset.sum I (fun i => a i ω - target ω) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, smul_sub]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ, ← hmcard, smul_smul]
    have hcard_ne : (I.card : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (by simpa [hmcard] using hmpos))
    have hmul : (I.card : ℝ)⁻¹ * (I.card : ℝ) = 1 := by
      field_simp [hcard_ne]
    rw [hmul, one_smul]
  calc
    process curr ω =
        process prev ω +
          (((m : ℝ)⁻¹) • Finset.sum I (fun i => a i ω) - target ω) := by
      simpa [sub_eq_add_neg, add_assoc] using hrec ω
    _ =
        process prev ω +
          ((m : ℝ)⁻¹) • Finset.sum I (fun i => a i ω - target ω) := by
      rw [hcenter]

/-- A one-step estimator update induces the corresponding residual-process update.

If an estimator process advances from time `t` to `t + 1` by adding the
average of mini-batch component increments, then its residual relative to a
target field advances by the same estimator increment minus the target-field
difference between the two iterates.

Layer: Model | Gap: Level 1 (estimator-residual recursive update algebra)
Proof: unfold the named residual process, rewrite by the pointwise estimator
  update, and use additive-module algebra to collect the target difference.
Source: Mathlib finite sums, real scalar multiplication, and additive-group
  cancellation APIs
Used in: stochastic nonconvex conditional gradient finite-sum recursive
  estimator residual inside an epoch
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem estimatorResidualProcess_succ_eq_of_estimator_update
    {Ω X E : Type*} [AddCommGroup E] [Module ℝ E]
    (estimator : ℕ → Ω → E) (iterate : ℕ → Ω → X) (target : X → E)
    (componentIncrement : ℕ → ℕ → Ω → E) (b t : ℕ)
    (hupdate : ∀ ω,
      estimator (t + 1) ω =
        estimator t ω +
          (b : ℝ)⁻¹ •
            Finset.sum (Finset.range b) (fun i => componentIncrement t i ω)) :
    ∀ ω,
      estimatorResidualProcess estimator iterate target (t + 1) ω =
        estimatorResidualProcess estimator iterate target t ω +
          (b : ℝ)⁻¹ •
            Finset.sum (Finset.range b) (fun i => componentIncrement t i ω) -
          (target (iterate (t + 1) ω) - target (iterate t ω)) := by
  intro ω
  simp [estimatorResidualProcess, hupdate ω]
  abel

/-- An exact-refresh estimator process equals its target field at every epoch start.

For the finite-sum exact-refresh state process, the estimator component at
index `s*T+1` is the deterministic target evaluated at the state component at
that same index. This packages the arithmetic branch identification for all
epochs, including the initial epoch.

Layer: Model | Gap: Level 0 (exact-refresh estimator epoch-start identity)
Proof: split the initial epoch from positive epochs. Positive epochs rewrite
`s*T+1` as a successor-after-successor index, identify the modulo refresh
branch with `Nat.mul_mod_right`, and simplify the state constructor accessors.
Source: Mathlib natural-number arithmetic and finite-sum variance-reduction process recursions
Used in: finite-sum stochastic nonconvex conditional gradient estimator-error base case
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic nonconvex conditional gradient -/
theorem estimatorProcess_epochStart_eq_target
    {Ω State E : Type*} [Zero E]
    (mkState : E → E → ℕ → State)
    (stateX : State → E) (stateEstimator : State → E) (stateEpoch : State → ℕ)
    (hstateX_mk : ∀ x G s, stateX (mkState x G s) = x)
    (hstateEstimator_mk : ∀ x G s, stateEstimator (mkState x G s) = G)
    (x0 : E)
    (target : E → E)
    (recursiveEstimator : E → E → E → ℕ → ℕ → Ω → E)
    (iterUpdate : E → E → ℕ → E)
    (T b : ℕ)
    (hT_pos : 1 ≤ T)
    (s : ℕ) :
    (fun ω =>
        stateEstimator
          (finiteSumConditionalGradientProcess mkState stateX stateEstimator stateEpoch
            x0 target recursiveEstimator iterUpdate T b (s * T + 1) ω)) =
      fun ω =>
        target
          (stateX
            (finiteSumConditionalGradientProcess mkState stateX stateEstimator stateEpoch
              x0 target recursiveEstimator iterUpdate T b (s * T + 1) ω)) := by
  funext ω
  cases s with
  | zero =>
      simp [hstateX_mk, hstateEstimator_mk]
  | succ r =>
      have hprod_pos : 0 < (r + 1) * T := by
        exact Nat.mul_pos (Nat.succ_pos r) (Nat.lt_of_lt_of_le Nat.zero_lt_one hT_pos)
      have hpred_add : ((r + 1) * T - 1) + 1 = (r + 1) * T := by
        exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr hprod_pos)
      have hidx : (r + 1) * T + 1 = ((r + 1) * T - 1) + 2 := by
        omega
      have hmod : (((((r + 1) * T - 1) + 1) % T == 0) = true) := by
        have hzero : ((r + 1) * T) % T = 0 := by
          rw [Nat.mul_comm]
          exact Nat.mul_mod_right T (r + 1)
        simp [hpred_add, hzero]
      rw [hidx]
      simp [finiteSumConditionalGradientProcess, hmod, hstateX_mk, hstateEstimator_mk]

/-- A finite sum of paired stochastic-oracle value differences is measurable
when the queries and selected sample coordinates are block-measurable.

For a jointly measurable oracle kernel `G`, two measurable random queries `x`
and `y`, and a finite family of sample indices all lying in the same generated
sample block, the sum of `G (x omega)` minus `G (y omega)` evaluated at each
selected sample coordinate is measurable for that block sigma-algebra.

Layer: Model | Gap: Level 0 (finite oracle-gradient difference sum measurability)
Proof: each selected coordinate is measurable by the finite sample-block
  generator lemma; compose the joint oracle with the two query/sample product
  maps, close each summand under subtraction, and then apply finite-sum
  measurability.
Source: Mathlib MeasureTheory product measurable-space, measurable algebra,
  and finite-sum APIs
Used in: stochastic nonconvex conditional-gradient recursive mini-batch
  gradient-difference adaptedness over the optimization sample block
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem oracle_value_sub_sum_measurable_of_coordinate_measurable
    {Ω X Ξ E I J : Type*} [MeasurableSpace X] [MeasurableSpace Ξ]
    [MeasurableSpace E] [AddCommMonoid E] [Sub E] [MeasurableAdd₂ E]
    [MeasurableSub₂ E]
    (G : X → Ξ → E) (hG : Measurable (fun p : X × Ξ => G p.1 p.2))
    (ξ : I → Ω → Ξ) {block : Finset I} (terms : Finset J)
    {x y : Ω → X} {idx : J → I}
    (hx : Measurable[sampleBlockMeasurableSpace ξ block] x)
    (hy : Measurable[sampleBlockMeasurableSpace ξ block] y)
    (hidx : ∀ j, j ∈ terms → idx j ∈ block) :
    Measurable[sampleBlockMeasurableSpace ξ block]
      (fun ω =>
        Finset.sum terms
          (fun j => G (x ω) (ξ (idx j) ω) - G (y ω) (ξ (idx j) ω))) := by
  refine Finset.measurable_sum terms ?_
  intro j hj
  have hξj :
      Measurable[sampleBlockMeasurableSpace ξ block] (ξ (idx j)) := by
    exact measurable_iff_comap_le.mpr (by
      rw [sampleBlockMeasurableSpace]
      exact le_iSup
        (fun q : {q // q ∈ block} =>
          MeasurableSpace.comap (fun ω => ξ q.1 ω)
            (by infer_instance : MeasurableSpace Ξ))
        ⟨idx j, hidx j hj⟩)
  exact (hG.comp (hx.prodMk hξj)).sub (hG.comp (hy.prodMk hξj))

/-- Recursive gradient-difference average added to a previous estimator.

For a finite mini-batch of samples, this is the standard pathwise
variance-reduced update `G_prev + |I|⁻¹ ∑ᵢ (gradF x_curr sampleᵢ -
gradF x_prev sampleᵢ)` used inside SARAH/SPIDER-style epochs.

Layer: Model | Concept: Oracle
Proof: (definitional construction; finite mini-batch paired-gradient
  difference update with a previous estimator)
Source: stochastic variance-reduction estimator recursions and Mathlib finite-sum APIs
Used in: stochastic nonconvex conditional gradient within-epoch recursive estimator update
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic nonconvex conditional gradient -/
noncomputable def recursiveGradientDifferenceAverage
    {ι X S E : Type*} [Fintype ι] [AddCommMonoid E] [Sub E] [SMul ℝ E]
    (gradF : X → S → E) (G_prev : E) (x_prev x_curr : X) (samples : ι → S) : E :=
  (Fintype.card ι : ℝ)⁻¹ •
      Finset.sum Finset.univ
        (fun i => gradF x_curr (samples i) - gradF x_prev (samples i)) +
    G_prev

/-- The recursive gradient-difference average unfolds to its mini-batch formula.

This is the controlled simp theorem for exposing the raw estimator update when
downstream proofs need finite-sum or scalar algebra.

Layer: Model | Gap: Level 0 (recursive gradient-difference average unfolding)
Proof: by rfl after unfolding `recursiveGradientDifferenceAverage`.
Source: stochastic variance-reduction estimator recursions and Mathlib finite-sum APIs
Used in: stochastic nonconvex conditional gradient recursive estimator algebra
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic nonconvex conditional gradient -/
@[simp]
theorem recursiveGradientDifferenceAverage_def
    {ι X S E : Type*} [Fintype ι] [AddCommMonoid E] [Sub E] [SMul ℝ E]
    (gradF : X → S → E) (G_prev : E) (x_prev x_curr : X) (samples : ι → S) :
    recursiveGradientDifferenceAverage gradF G_prev x_prev x_curr samples =
      (Fintype.card ι : ℝ)⁻¹ •
          Finset.sum Finset.univ
            (fun i => gradF x_curr (samples i) - gradF x_prev (samples i)) +
        G_prev := by
  rfl

/-- A sampled finite-index stream is identically distributed with the identity
map on its PMF law when each coordinate has that pushforward law.

This is the PMF-facing bridge from a stochastic-optimization sampling assumption
stated as `Measure.map (sample k) P = qpmf.toMeasure` to the `IdentDistrib`
object used by expectation and integrability transport lemmas.

Layer: Model | Gap: Level 0 (PMF sample-law IdentDistrib bridge)
Proof: build the three fields of `IdentDistrib`: coordinate a.e.
  measurability, identity a.e. measurability on the PMF law, and the supplied
  pushforward-law equality.
Source: Mathlib probability `IdentDistrib`, `Measure.map`, and PMF
  associated-measure APIs
Used in: finite-sum stochastic conditional-gradient component-index law
  transport before finite-PMF expectation and variance bounds
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/key_lemmas/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem sample_identDistrib_finiteImportancePMF
    {Ω ι : Type*} [MeasurableSpace Ω] [MeasurableSpace ι]
    (sample : ℕ → Ω → ι) (P : Measure Ω) (qpmf : PMF ι)
    (k : ℕ)
    (hsample_aemeas : AEMeasurable (sample k) P)
    (hsample_law : Measure.map (sample k) P = qpmf.toMeasure) :
    IdentDistrib (sample k) (fun i : ι => i) P qpmf.toMeasure := by
  refine ⟨hsample_aemeas, measurable_id.aemeasurable, ?_⟩
  simpa using hsample_law


/-- Accelerated stochastic approximation error integrand from a quadratic noise
penalty plus a linear martingale-noise comparison term.

For a time-indexed accelerated schedule, this names the pointwise error term
formed from the denominator `1 + μ γ_t - L α_t γ_t`, the dual norm of the
oracle residual, and the inner product against `x - xPlus_t`.

Layer: Model | Concept: Oracle
Proof: (definitional construction; accelerated stochastic error model combining
  denominator-weighted oracle-noise square with a scalarized residual)
Source: accelerated stochastic approximation one-step descent notation and
  Mathlib real inner-product arithmetic
Used in: accelerated stochastic gradient descent one-step descent error term
  before martingale cancellation and quadratic-noise expectation bounds
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/main_theorem/proof/1/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
noncomputable def acceleratedStochasticError
    {T I Ω E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (time : T → I) (alpha gamma : I → ℝ) (M mu L : ℝ) (dualNorm : E → ℝ)
    (delta xPlus : T → Ω → E) (t : T) (ω : Ω) (x : E) : ℝ :=
  (alpha (time t) * gamma (time t) * (M + dualNorm (delta t ω)) ^ 2) /
      (2 * (1 + mu * gamma (time t) - L * alpha (time t) * gamma (time t))) +
    alpha (time t) * ⟪delta t ω, x - xPlus t ω⟫_ℝ

/-- The accelerated stochastic error unfolds to its quadratic-noise and
inner-product formula.

Layer: Model | Gap: Level 0 (accelerated stochastic error unfolding)
Proof: by rfl after unfolding `acceleratedStochasticError`.
Source: accelerated stochastic approximation one-step descent notation and
  Mathlib real inner-product arithmetic
Used in: accelerated stochastic gradient descent one-step descent error term
  before martingale cancellation and quadratic-noise expectation bounds
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/main_theorem/proof/1/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
@[simp]
theorem acceleratedStochasticError_def
    {T I Ω E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (time : T → I) (alpha gamma : I → ℝ) (M mu L : ℝ) (dualNorm : E → ℝ)
    (delta xPlus : T → Ω → E) (t : T) (ω : Ω) (x : E) :
    acceleratedStochasticError time alpha gamma M mu L dualNorm delta xPlus t ω x =
      (alpha (time t) * gamma (time t) * (M + dualNorm (delta t ω)) ^ 2) /
          (2 * (1 + mu * gamma (time t) -
            L * alpha (time t) * gamma (time t))) +
        alpha (time t) * ⟪delta t ω, x - xPlus t ω⟫_ℝ := by
  rfl

/-- Changing the comparison point in `acceleratedStochasticError` only changes
the linear residual term.

Layer: Model | Gap: Level 0 (accelerated stochastic error comparison)
Proof: unfold `acceleratedStochasticError`, cancel the common quadratic term,
  and use linearity of the real inner product in the second argument.
Source: accelerated stochastic approximation one-step descent notation and
  Mathlib real inner-product arithmetic
Used in: accelerated stochastic gradient descent comparison-point rewrites
  before martingale cancellation and quadratic-noise expectation bounds
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/main_theorem/proof/1/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem acceleratedStochasticError_sub
    {T I Ω E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (time : T → I) (alpha gamma : I → ℝ) (M mu L : ℝ) (dualNorm : E → ℝ)
    (delta xPlus : T → Ω → E) (t : T) (ω : Ω) (x y : E) :
    acceleratedStochasticError time alpha gamma M mu L dualNorm delta xPlus t ω x -
        acceleratedStochasticError time alpha gamma M mu L dualNorm delta xPlus t ω y =
      alpha (time t) * ⟪delta t ω, x - y⟫_ℝ := by
  simp [acceleratedStochasticError, inner_sub_right]
  ring

/-- Fixed-query unbiased and bounded-variance stochastic oracle interface on a set.

For every feasible query, the oracle fiber has a well-defined Bochner mean equal
to the target field, its squared centered residual is integrable and uniformly
bounded by `sigma ^ 2`, and the centered residual kernel is jointly measurable
on feasible queries and samples.

Layer: Model | Concept: Oracle
Proof: (definitional construction; bundled fixed-query stochastic first-order
  oracle assumptions with a carrier-indexed residual measurability invariant)
Source: Stochastic first-order oracle assumptions, Bochner expectation, and
  second-moment variance bounds
Used in: stochastic accelerated gradient descent source SFO assumptions before
  random-query unbiasedness and variance transfer at search points
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/assumptions
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
structure BoundedVarianceUnbiasedOracleOn
    {E S : Type*} [MeasurableSpace S] [MeasurableSpace E]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (μ : Measure S) (G : E → S → E) (target : E → E)
    (normDual : E → ℝ) (sigma : ℝ) where
  unbiased :
    ∀ x, x ∈ X →
      oracleWellDefined μ G id x ∧
        oracleMean μ G id x = target x
  variance :
    ∀ x, x ∈ X →
      Integrable (fun ξ => normDual (G x ξ - target x) ^ 2) μ ∧
        ∫ ξ, normDual (G x ξ - target x) ^ 2 ∂μ ≤ sigma ^ 2
  residual_joint_measurable :
    Measurable
      (fun p : {x : E // x ∈ X} × S =>
        G p.1.1 p.2 - target p.1.1)

/-- Oracle noise evaluated at a time-indexed adapted random query and sample coordinate.

For an already-centered oracle-noise kernel `oracleNoise`, a random query
process `query`, a sample stream `sample`, and an index selector `sampleIndex`,
this names the process `ω ↦ oracleNoise (query t ω) (sample (sampleIndex t) ω)`.

Layer: Model | Concept: Oracle
Proof: (definitional construction; indexed random-query evaluation of a centered
  stochastic oracle-noise kernel)
Source: Mathlib function evaluation APIs and SOptLib stochastic-oracle process notation
Used in: stochastic accelerated gradient descent martingale-noise process at the
  adapted search point before conditional-expectation cancellation
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/parameters[1]/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
def oracleNoiseAtAdaptedQuery
    {T I Ω X S E : Type*}
    (oracleNoise : X → S → E) (query : T → Ω → X) (sample : I → Ω → S)
    (sampleIndex : T → I) (t : T) (ω : Ω) : E :=
  oracleNoise (query t ω) (sample (sampleIndex t) ω)

/-- The adapted-query oracle-noise process unfolds to evaluation of the centered
oracle-noise kernel at the query and selected sample.

Layer: Model | Gap: Level 0 (adapted-query oracle-noise unfolding)
Proof: by rfl after unfolding `oracleNoiseAtAdaptedQuery`.
Source: Mathlib function evaluation APIs and SOptLib stochastic-oracle process notation
Used in: stochastic accelerated gradient descent martingale-noise process at the
  adapted search point before conditional-expectation cancellation
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/parameters[1]/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
@[simp]
theorem oracleNoiseAtAdaptedQuery_apply
    {T I Ω X S E : Type*}
    (oracleNoise : X → S → E) (query : T → Ω → X) (sample : I → Ω → S)
    (sampleIndex : T → I) (t : T) (ω : Ω) :
    oracleNoiseAtAdaptedQuery oracleNoise query sample sampleIndex t ω =
      oracleNoise (query t ω) (sample (sampleIndex t) ω) := by
  rfl

/-- A feasible stochastic-oracle residual is jointly measurable from measurable
oracle and target fields.

For an oracle kernel jointly measurable on feasible queries and samples, and a
deterministic target field measurable on the feasible carrier, the centered
residual kernel `(x, s) ↦ oracle x s - target x` is jointly measurable.

Layer: Model | Gap: Level 0 (feasible oracle residual joint measurability)
Proof: compose the target-field measurability with the first projection from
  the feasible query/sample product, then close the oracle-minus-target kernel
  under Mathlib's measurable subtraction API.
Source: Mathlib MeasureTheory product measurable-space, subtype projection,
  composition, and measurable subtraction APIs
Used in: stochastic accelerated gradient descent random-query oracle residual
  measurability at feasible search points
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/assumptions/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem oracleResidual_feasible_joint_measurable
    {E S : Type*} [MeasurableSpace E] [MeasurableSpace S]
    [Sub E] [MeasurableSub₂ E]
    {X : Set E} {oracle : E → S → E} {target : E → E}
    (horacle :
      Measurable
        (fun p : {x : E // x ∈ X} × S =>
          oracle p.1.1 p.2))
    (htarget :
      Measurable
        (fun x : {x : E // x ∈ X} =>
          target x.1)) :
    Measurable
      (fun p : {x : E // x ∈ X} × S =>
        oracle p.1.1 p.2 - target p.1.1) := by
  exact horacle.sub (htarget.comp measurable_fst)

end SOptLib

namespace SOptLib

open MeasureTheory
open scoped BigOperators InnerProductSpace

/-- The uncentered block-oracle second moment as a certified expectation value.

For a stochastic oracle block `Gblock x ξ` and scalar dual-norm functional
`dualNorm`, this packages the expectation of
`ξ ↦ dualNorm (Gblock x ξ) ^ 2` together with the integrability boundary needed
to use it as a named expectation object.

Layer: Model | Concept: Oracle
Proof: (definitional construction; certified expectation-value wrapper around
  the uncentered squared block-oracle dual-norm integrand)
Source: Mathlib measure theory Bochner integration and stochastic oracle
  second-moment notation
Used in: stochastic block mirror descent fixed block-oracle second-moment
  expectation before applying the moment bound
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/assumptions/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
noncomputable def blockOracleSecondMomentExpectationValue
    {X S B : Type*} [MeasurableSpace S]
    (μ : Measure S) (Gblock : X → S → B) (dualNorm : B → ℝ) (x : X)
    (h_wellDefined :
      expectationWellDefined μ (fun s => dualNorm (Gblock x s) ^ 2)) :
    ExpectationValue μ (fun s => dualNorm (Gblock x s) ^ 2) :=
  ⟨expectation μ (fun s => dualNorm (Gblock x s) ^ 2), h_wellDefined, rfl⟩

/-- Block-indexed mean oracle extracted from certified stochastic-oracle
expectation values.

Given a dependent family of block oracle random variables and certified
expectation values for each block, `blockMeanOracle` is the deterministic
block-indexed oracle whose coordinate is the corresponding certified mean.

Layer: Model | Concept: Oracle
Proof: (definitional construction; dependent block-coordinate selector from
  certified expectation values)
Source: Mathlib measure theory Bochner integration and SOptLib certified
  expectation-value APIs
Used in: stochastic block mirror descent formation of the deterministic mean
  subgradient from blockwise oracle expectation objects
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/assumptions/1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
noncomputable def blockMeanOracle
    {Xi ι : Type*} {B : ι → Type*} [MeasurableSpace Xi]
    [∀ i, NormedAddCommGroup (B i)] [∀ i, NormedSpace ℝ (B i)]
    (μ : Measure Xi) (Gblock : ∀ i : ι, Xi → B i)
    (meanExp : ∀ i : ι, ExpectationValue μ (Gblock i)) : ∀ i : ι, B i :=
  fun i => (meanExp i).val

/-- The block mean oracle coordinate is the value field of its certified
expectation object.

Layer: Model | Gap: Level 0 (block mean-oracle coordinate unfolding)
Proof: by rfl after unfolding `blockMeanOracle`.
Source: Mathlib dependent function reduction and SOptLib certified
  expectation-value APIs
Used in: stochastic block mirror descent coordinate-level mean-subgradient
  unfolding
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/assumptions/1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
@[simp] theorem blockMeanOracle_apply
    {Xi ι : Type*} {B : ι → Type*} [MeasurableSpace Xi]
    [∀ i, NormedAddCommGroup (B i)] [∀ i, NormedSpace ℝ (B i)]
    (μ : Measure Xi) (Gblock : ∀ i : ι, Xi → B i)
    (meanExp : ∀ i : ι, ExpectationValue μ (Gblock i)) (i : ι) :
    blockMeanOracle μ Gblock meanExp i = (meanExp i).val := by
  rfl

/-- The block mean oracle coordinate is the canonical expectation of the
corresponding block oracle random variable.

Layer: Model | Gap: Level 0 (block mean-oracle expectation unfolding)
Proof: unfold `blockMeanOracle` at the selected coordinate and use the
  equality certificate stored in the corresponding `ExpectationValue`.
Source: Mathlib measure theory Bochner integration and SOptLib certified
  expectation-value APIs
Used in: stochastic block mirror descent identification of each mean
  subgradient block with its sample expectation
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/assumptions/1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem blockMeanOracle_eq_expectation
    {Xi ι : Type*} {B : ι → Type*} [MeasurableSpace Xi]
    [∀ i, NormedAddCommGroup (B i)] [∀ i, NormedSpace ℝ (B i)]
    (μ : Measure Xi) (Gblock : ∀ i : ι, Xi → B i)
    (meanExp : ∀ i : ι, ExpectationValue μ (Gblock i)) (i : ι) :
    blockMeanOracle μ Gblock meanExp i = expectation μ (Gblock i) := by
  exact (meanExp i).property.2

/-- A fixed feasible query inherits block mean-oracle expectation well-definedness.

If every feasible query has a well-defined vector-valued block oracle expectation
under the sample law, then the sampled block oracle at a selected feasible query
has a well-defined expectation.

Layer: Model | Gap: Level 0 (fixed-query block mean-oracle integrability)
Proof: specialize the feasible-family expectation well-definedness hypothesis
  to the selected query and its feasibility proof.
Source: Mathlib measure theory Bochner integrability APIs for vector-valued
  random variables
Used in: stochastic block mirror descent fixed block mean-subgradient expectation
  boundary before forming the deterministic mean oracle
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/assumptions/1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem blockMeanOracle_wellDefined
    {Xi X B : Type*} [MeasurableSpace Xi]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (μ : Measure Xi) (Gblock : X → Xi → B) (feasible : Set X)
    (x : X) (hx : x ∈ feasible)
    (h_wellDefined :
      ∀ z : X, z ∈ feasible →
        expectationWellDefined μ (fun xi => Gblock z xi)) :
    expectationWellDefined μ (fun xi => Gblock x xi) := by
  exact h_wellDefined x hx

/-- A block stochastic oracle has bounded uncentered second moments on a carrier.

For every feasible query and every block, the certified expectation of the
squared block gauge of the oracle response is bounded by the corresponding
block budget `M i ^ 2`.

Layer: Model | Concept: Oracle
Proof: (definitional construction; block-indexed bounded uncentered
  second-moment oracle predicate over certified expectation values)
Source: Stochastic approximation and stochastic mirror-descent bounded
  second-moment oracle assumptions
Used in: stochastic block mirror descent oracle second-moment assumption and
  randomized coordinate stochastic-gradient moment budgets
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/assumptions/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
def blockOracleSecondMomentBound
    {Ω ι X : Type*} {B : ι → Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (oracle : X → Ω → ∀ i, B i)
    (carrier : Set X)
    (dualNorm : ∀ i, B i → ℝ)
    (M : ι → ℝ)
    (secondMomentExpectation :
      ∀ i (x : X), x ∈ carrier →
        ExpectationValue μ (fun ω => dualNorm i (oracle x ω i) ^ 2)) : Prop :=
  ∀ i (x : X), ∀ hx : x ∈ carrier,
    (secondMomentExpectation i x hx).val ≤ M i ^ 2

/-- A bounded block stochastic oracle supplies the fixed block/query
second-moment bound.

Layer: Model | Gap: Level 0 (block oracle second-moment predicate elimination)
Proof: unfold the bounded block-oracle second-moment predicate and specialize it
  to the requested block, query, and carrier proof.
Source: Stochastic approximation bounded second-moment oracle assumptions
Used in: stochastic block mirror descent fixed block oracle second-moment
  control
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/assumptions/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem blockOracleSecondMomentBound_apply
    {Ω ι X : Type*} {B : ι → Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (oracle : X → Ω → ∀ i, B i)
    (carrier : Set X)
    (dualNorm : ∀ i, B i → ℝ)
    (M : ι → ℝ)
    (secondMomentExpectation :
      ∀ i (x : X), x ∈ carrier →
        ExpectationValue μ (fun ω => dualNorm i (oracle x ω i) ^ 2))
    (hbound :
      blockOracleSecondMomentBound μ oracle carrier dualNorm M
        secondMomentExpectation)
    (i : ι) (x : X) (hx : x ∈ carrier) :
    (secondMomentExpectation i x hx).val ≤ M i ^ 2 := by
  exact hbound i x hx

/-- A block stochastic oracle is unbiased as a product subgradient.

For every feasible product query, certified blockwise expectation values form a
deterministic block mean oracle, and that mean oracle belongs to the finite
product subdifferential of the objective at the query.

Layer: Model | Concept: Oracle
Proof: (definitional construction; blockwise certified mean-oracle product-subgradient predicate)
Source: Stochastic first-order oracle assumptions and convex-analysis subgradient support inequalities
Used in: stochastic block mirror descent formation of the mean stochastic subgradient assumption
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/assumptions/1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic block mirror descent -/
noncomputable def blockOracleUnbiasedSubgradient
    {Xi ι : Type*} {Block : ι → Type*} [Fintype ι] [MeasurableSpace Xi]
    [∀ i, NormedAddCommGroup (Block i)] [∀ i, InnerProductSpace ℝ (Block i)]
    (μ : Measure Xi)
    (G : (∀ i, Block i) → Xi → ∀ i, Block i)
    (X : ∀ i, Set (Block i)) (f : (∀ i, Block i) → ℝ)
    (meanExp :
      ∀ x, (∀ i, x i ∈ X i) → ∀ i,
        ExpectationValue μ (fun ξ => G x ξ i)) : Prop :=
  ∀ x, ∀ hx : ∀ i, x i ∈ X i,
    blockMeanOracle μ (fun i ξ => G x ξ i) (meanExp x hx) ∈
      productSubdifferential X f x

/-- Unfolding of block oracle unbiased product-subgradient membership.

Layer: Model | Gap: Level 0 (block oracle unbiased-subgradient unfolding)
Proof: by rfl after unfolding `blockOracleUnbiasedSubgradient`.
Source: Stochastic first-order oracle assumptions and convex-analysis subgradient support inequalities
Used in: stochastic block mirror descent bridge from the source unbiased oracle assumption to the canonical mean subgradient
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/assumptions/1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic block mirror descent -/
theorem blockOracleUnbiasedSubgradient_iff
    {Xi ι : Type*} {Block : ι → Type*} [Fintype ι] [MeasurableSpace Xi]
    [∀ i, NormedAddCommGroup (Block i)] [∀ i, InnerProductSpace ℝ (Block i)]
    (μ : Measure Xi)
    (G : (∀ i, Block i) → Xi → ∀ i, Block i)
    (X : ∀ i, Set (Block i)) (f : (∀ i, Block i) → ℝ)
    (meanExp :
      ∀ x, (∀ i, x i ∈ X i) → ∀ i,
        ExpectationValue μ (fun ξ => G x ξ i)) :
    blockOracleUnbiasedSubgradient μ G X f meanExp ↔
      ∀ x, ∀ hx : ∀ i, x i ∈ X i,
        blockMeanOracle μ (fun i ξ => G x ξ i) (meanExp x hx) ∈
          productSubdifferential X f x := by
  rfl

/-- Scalar pairing of a selected inverse-probability block oracle residual.

At time `k` and path `omega`, the sampled block contributes the
inverse-probability weighted oracle pairing against the comparison displacement,
while the deterministic mean side subtracts the full finite sum of blockwise
mean-oracle pairings.

Layer: Model | Concept: Oracle
Proof: (definitional construction; selected block-coordinate oracle residual
  paired with a comparison displacement)
Source: Stochastic block-coordinate mirror descent oracle-noise notation and
  Mathlib finite sums over dependent real Hilbert blocks
Used in: stochastic block mirror descent one-step descent scalar martingale
  residual and randomized coordinate oracle-noise scalarization
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
noncomputable def selectedBlockOracleResidualPairing
    {Omega Xi ι X : Type*} [Fintype ι]
    {Block : ι → Type*}
    [∀ i, NormedAddCommGroup (Block i)] [∀ i, InnerProductSpace ℝ (Block i)]
    (p : ι → ℝ)
    (coord : X → ∀ i, Block i)
    (x : ℕ → Omega → X)
    (sample : ℕ → Omega → Xi)
    (block : ℕ → Omega → ι)
    (oracle : (i : ι) → X → Xi → Block i)
    (meanOracle : X → (i : ι) → Block i)
    (xRef : X) (k : ℕ) (omega : Omega) : ℝ :=
  let xk := x k omega
  let ik := block k omega
  (p ik)⁻¹ * ⟪oracle ik xk (sample k omega), coord xRef ik - coord xk ik⟫_ℝ -
    Finset.sum Finset.univ (fun i =>
      ⟪meanOracle xk i, coord xRef i - coord xk i⟫_ℝ)

/-- The selected block oracle residual pairing unfolds to its finite block formula.

Layer: Model | Gap: Level 0 (selected block oracle residual unfolding)
Proof: by rfl after unfolding `selectedBlockOracleResidualPairing`.
Source: Stochastic block-coordinate mirror descent oracle-noise notation and
  Mathlib finite sums over dependent real Hilbert blocks
Used in: stochastic block mirror descent one-step descent scalar martingale
  residual and randomized coordinate oracle-noise scalarization
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
@[simp]
theorem selectedBlockOracleResidualPairing_apply
    {Omega Xi ι X : Type*} [Fintype ι]
    {Block : ι → Type*}
    [∀ i, NormedAddCommGroup (Block i)] [∀ i, InnerProductSpace ℝ (Block i)]
    (p : ι → ℝ)
    (coord : X → ∀ i, Block i)
    (x : ℕ → Omega → X)
    (sample : ℕ → Omega → Xi)
    (block : ℕ → Omega → ι)
    (oracle : (i : ι) → X → Xi → Block i)
    (meanOracle : X → (i : ι) → Block i)
    (xRef : X) (k : ℕ) (omega : Omega) :
    selectedBlockOracleResidualPairing p coord x sample block oracle meanOracle xRef k omega =
      (let xk := x k omega
       let ik := block k omega
      (p ik)⁻¹ * ⟪oracle ik xk (sample k omega), coord xRef ik - coord xk ik⟫_ℝ -
        Finset.sum Finset.univ (fun i =>
          ⟪meanOracle xk i, coord xRef i - coord xk i⟫_ℝ)) := by
  rfl

/-- Stage-separated adjoint-oracle value at a random query.

For a time-indexed adjoint oracle response `sampledAdjoint`, horizon `T`, and
random query process `query`, this names the process obtained at local index
`i` by evaluating the query from `i` on the fresh sample coordinate `T + i`.

Layer: Model | Concept: Oracle
Proof: (definitional construction; horizon-shifted random-query stochastic adjoint-oracle value)
Source: Mathlib function evaluation APIs and stochastic primal-dual fresh-sample oracle notation
Used in: stochastic accelerated primal-dual martingale arguments for adjoint-oracle noise at generated dual iterates
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic accelerated primal-dual method -/
def stageSeparatedAdjointOracleValue
    {Ω Query E : Type*}
    (sampledAdjoint : ℕ → Query → Ω → E)
    (query : ℕ → Ω → Query) (T i : ℕ) : Ω → E :=
  fun ω => sampledAdjoint (T + i) (query i ω) ω

/-- The stage-separated adjoint-oracle value unfolds to the sampled adjoint call
at coordinate `T + i`.

Layer: Model | Gap: Level 0 (stage-separated adjoint-oracle unfolding)
Proof: by rfl after unfolding `stageSeparatedAdjointOracleValue`.
Source: Mathlib function evaluation APIs and stochastic primal-dual fresh-sample oracle notation
Used in: stochastic accelerated primal-dual martingale arguments for adjoint-oracle noise at generated dual iterates
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic accelerated primal-dual method -/
@[simp]
theorem stageSeparatedAdjointOracleValue_apply
    {Ω Query E : Type*}
    (sampledAdjoint : ℕ → Query → Ω → E)
    (query : ℕ → Ω → Query) (T i : ℕ) (ω : Ω) :
    stageSeparatedAdjointOracleValue sampledAdjoint query T i ω =
      sampledAdjoint (T + i) (query i ω) ω := by
  rfl

/-- A realized sampled-oracle stream is measurable at a measurable random query.

If a stream agrees pointwise with a jointly measurable stochastic oracle
evaluated at a measurable query and a measurable sample coordinate, then the
stream is measurable with respect to the same source sigma-algebra.

Layer: Model | Gap: Level 0 (realized sampled-oracle stream measurability)
Proof: compose the jointly measurable oracle with the query/sample pair using
  `sampledOracle_measurable`, then transport measurability across the pointwise
  realization equality by function extensionality.
Source: Mathlib MeasureTheory product measurable-space and measurable
  composition APIs, plus SOptLib sampled stochastic-oracle composition
Used in: stochastic accelerated primal-dual generated fixed-domain `A_x` oracle
  sample measurability before extension-process adaptedness
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/3/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem measurable_realizedSampledOracle
    {Ω X S E : Type*} [MeasurableSpace X] [MeasurableSpace S]
    [MeasurableSpace E]
    (m : MeasurableSpace Ω)
    {oracle : X → S → E} {query : Ω → X} {ξ : Ω → S} {stream : Ω → E}
    (horacle : Measurable (fun p : X × S => oracle p.1 p.2))
    (hquery : Measurable[m] query) (hξ : Measurable[m] ξ)
    (hstream : ∀ ω, stream ω = oracle (query ω) (ξ ω)) :
    Measurable[m] stream := by
  have hsample : Measurable[m] (fun ω => oracle (query ω) (ξ ω)) :=
    SOptLib.sampledOracle_measurable
      (oracle := oracle)
      (x := query)
      (ξ := ξ)
      horacle
      hquery
      hξ
  have hEq : stream = fun ω => oracle (query ω) (ξ ω) := by
    funext ω
    exact hstream ω
  simpa [hEq] using hsample

/-- Signed residual process of a sampled forward oracle against its realized target process.

For a time-indexed sampled forward response and a time-indexed target forward
process, this names the signed process `ω ↦ -sampledForward t ω + targetForward t ω`.

Layer: Model | Concept: Oracle
Proof: (definitional construction; pointwise signed residual of two indexed
  stochastic forward-oracle processes)
Source: Mathlib function evaluation, negation, and addition APIs for stochastic
  process notation
Used in: stochastic accelerated primal-dual dual update forward-oracle noise
  before second-moment and martingale residual estimates
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
def signedForwardOracleResidualProcess
    {T Ω E : Type*} [Neg E] [Add E]
    (sampledForward targetForward : T → Ω → E) (t : T) (ω : Ω) : E :=
  -sampledForward t ω + targetForward t ω

/-- The signed forward-oracle residual unfolds to negative sampled forward plus target.

Layer: Model | Gap: Level 0 (signed forward-oracle residual unfolding)
Proof: by rfl after unfolding `signedForwardOracleResidualProcess`.
Source: Mathlib function evaluation, negation, and addition APIs for stochastic
  process notation
Used in: stochastic accelerated primal-dual replacement of raw signed
  forward-oracle noise by a named residual process
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
@[simp]
theorem signedForwardOracleResidualProcess_apply
    {T Ω E : Type*} [Neg E] [Add E]
    (sampledForward targetForward : T → Ω → E) (t : T) (ω : Ω) :
    signedForwardOracleResidualProcess sampledForward targetForward t ω =
      -sampledForward t ω + targetForward t ω := by
  rfl

/-- A signed residual of measurable sampled and target forward processes is measurable.

At a fixed time index, measurability of each realized forward process gives
measurability of the signed residual by measurable negation and addition.

Layer: Model | Gap: Level 0 (signed forward-oracle residual measurability)
Proof: unfold the residual process, negate the selected sampled time slice, and
  apply Mathlib's measurable addition API with the target slice.
Source: Mathlib measurable negation and addition APIs for functions into
  measurable additive spaces
Used in: stochastic accelerated primal-dual forward-oracle residual
  integrability and conditional-expectation setup
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem signedForwardOracleResidualProcess_measurable
    {T Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [Neg E] [Add E] [MeasurableNeg E] [MeasurableAdd₂ E]
    {sampledForward targetForward : T → Ω → E} {t : T}
    (hsampled : Measurable (sampledForward t))
    (htarget : Measurable (targetForward t)) :
    Measurable (fun ω => signedForwardOracleResidualProcess sampledForward targetForward t ω) := by
  simpa [signedForwardOracleResidualProcess] using hsampled.neg.add htarget

/-- Combined primal-noise scale from two variance-scale components.

For two scalar standard-deviation or variance-proxy components, this names the
root-sum-square scale whose square is the sum of the component squares.

Layer: Model | Concept: Oracle
Proof: (definitional construction; root-sum-square scalar noise scale)
Source: Mathlib real square-root and ordered-field APIs for variance-scale
  aggregation
Used in: stochastic accelerated primal-dual combined primal noise scale before
  replacing component variance constants by a single scalar budget
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/8/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
noncomputable def combinedPrimalNoiseScale
    (sigmaHatf sigmaA : ℝ) : ℝ :=
  Real.sqrt (sigmaHatf ^ 2 + sigmaA ^ 2)

/-- The combined primal-noise scale unfolds to its root-sum-square formula.

Layer: Model | Gap: Level 0 (combined primal-noise scale formula)
Proof: by rfl after unfolding `combinedPrimalNoiseScale`.
Source: Mathlib real square-root APIs for scalar root-sum-square expressions
Used in: stochastic accelerated primal-dual replacement of paper-local
  `sigmaX` notation by a named combined primal-noise scale
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/8/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
@[simp]
theorem combinedPrimalNoiseScale_def
    (sigmaHatf sigmaA : ℝ) :
    combinedPrimalNoiseScale sigmaHatf sigmaA =
      Real.sqrt (sigmaHatf ^ 2 + sigmaA ^ 2) := by
  rfl

/-- The square of the combined primal-noise scale is the sum of component squares.

Layer: Model | Gap: Level 0 (combined primal-noise square identity)
Proof: unfold the root-sum-square scale, use `Real.sq_sqrt`, and discharge
  nonnegativity of the radicand from nonnegativity of squares.
Source: Mathlib real square-root and ordered-ring square nonnegativity APIs
Used in: stochastic accelerated primal-dual conversion from the named
  primal-noise scale back to the two component variance budgets
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/8/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem combinedPrimalNoiseScale_sq
    (sigmaHatf sigmaA : ℝ) :
    combinedPrimalNoiseScale sigmaHatf sigmaA ^ 2 =
      sigmaHatf ^ 2 + sigmaA ^ 2 := by
  unfold combinedPrimalNoiseScale
  rw [Real.sq_sqrt]
  nlinarith [sq_nonneg sigmaHatf, sq_nonneg sigmaA]

/-- The combined primal-noise scale is nonnegative.

Layer: Model | Gap: Level 0 (combined primal-noise scale nonnegativity)
Proof: unfold the root-sum-square scale and apply nonnegativity of real square
  roots.
Source: Mathlib real square-root nonnegativity API
Used in: stochastic accelerated primal-dual scalar budget estimates requiring
  a nonnegative combined primal-noise standard-deviation scale
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/8/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem combinedPrimalNoiseScale_nonneg
    (sigmaHatf sigmaA : ℝ) :
    0 ≤ combinedPrimalNoiseScale sigmaHatf sigmaA := by
  unfold combinedPrimalNoiseScale
  exact Real.sqrt_nonneg _

/-- A carrier-totalized stochastic oracle is measurable along a measurable ambient query.

If the feasible carrier `X` is measurable, a fallback feasible point is
available, the carrier oracle is jointly measurable in its feasible query and
sample arguments, and both the sample and ambient query maps are measurable,
then the totalized oracle value is measurable. The proof turns the ambient
query into a subtype-valued feasible query on the measurable event
`{ω | query ω ∈ X}` and uses the zero branch off that event.

Layer: Model | Gap: Level 1 (carrier-totalized oracle measurability at ambient query)
Proof: build a measurable feasible-subtype query by piecewise replacement with
  a fixed feasible point, compose the jointly measurable oracle with the
  query/sample pair, and rewrite the carrier totalization as a measurable
  piecewise function.
Source: Mathlib MeasureTheory measurable preimage, subtype, product, and
  piecewise APIs with SOptLib carrier totalization
Used in: stochastic accelerated primal-dual displayed carrier oracle evaluation
  at an ambient extrapolated primal query
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem oracleAmbientOn_measurable_of_measurable_query
    {Ω E F S : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSpace S] [MeasurableSpace F] [Zero F]
    {X : Set E} {x0 : E} {oracle : {x : E // x ∈ X} → S → F}
    {xi : Ω → S} {query : Ω → E}
    (hX : MeasurableSet X) (hx0 : x0 ∈ X)
    (horacle : Measurable (fun p : {x : E // x ∈ X} × S => oracle p.1 p.2))
    (hxi : Measurable xi) (hquery : Measurable query) :
    Measurable (fun ω => totalizeOn X (fun z => oracle z (xi ω)) (query ω)) := by
  classical
  let s : Set Ω := {ω | query ω ∈ X}
  have hs : MeasurableSet s := hX.preimage hquery
  let qAmb : Ω → E := s.piecewise query (fun _ => x0)
  have hqAmb : Measurable qAmb := hquery.piecewise hs measurable_const
  have hqMem : ∀ ω, qAmb ω ∈ X := by
    intro ω
    by_cases hω : ω ∈ s
    · have hx : query ω ∈ X := by simpa [s] using hω
      simpa [qAmb, hω] using hx
    · simpa [qAmb, hω] using hx0
  let q : Ω → {x : E // x ∈ X} := fun ω => ⟨qAmb ω, hqMem ω⟩
  have hq : Measurable q := hqAmb.subtype_mk
  have hsample : Measurable (fun ω => oracle (q ω) (xi ω)) := by
    simpa [Function.comp_def] using horacle.comp (hq.prodMk hxi)
  have hpiece :
      Measurable (s.piecewise (fun ω => oracle (q ω) (xi ω)) (fun _ω => (0 : F))) :=
    hsample.piecewise hs measurable_const
  have hEq :
      (fun ω => totalizeOn X (fun z => oracle z (xi ω)) (query ω)) =
        s.piecewise (fun ω => oracle (q ω) (xi ω)) (fun _ω => (0 : F)) := by
    funext ω
    by_cases hω : ω ∈ s
    · have hx : query ω ∈ X := by simpa [s] using hω
      simp [totalizeOn, carrierTotalizeOn, q, qAmb, s, hω, hx]
    · have hx : query ω ∉ X := by simpa [s] using hω
      simp [totalizeOn, carrierTotalizeOn, q, qAmb, s, hω, hx]
  simpa [hEq] using hpiece

end SOptLib
