import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import SOptLib.Model.Carrier
import SOptLib.Model.Filtration
import SOptLib.Model.Iterates
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
