import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic
import SOptLib.Model.Carrier
import SOptLib.Model.Filtration
import SOptLib.Model.Iterates
import SOptLib.Model.Selection
import Mathlib.Analysis.InnerProductSpace.Basic
import SOptLib.Model.ConditionalExpectation
import SOptLib.Model.Objective
import SOptLib.Model.BlockSampling

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

/-- Uniform finite-sum control-variate estimator after replacing one component value.

For a finite population of size `card ι`, `old` is the stored component value and
`new` is the freshly evaluated component value.  The estimator scales the single
component difference by the population size and adds back the old memory value.

Layer: Model | Concept: Oracle
Proof: (definitional construction; finite-population control-variate update from
  old and refreshed component values)
Source: finite-sum variance-reduction estimators in stochastic optimization
Used in: randomized accelerated proximal-point refreshed gradient-memory estimator
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/7
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
noncomputable def uniformFiniteSumControlVariateEstimator
    {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E] (old new : E) : E :=
  (Fintype.card ι : ℝ) • (new - old) + old

/-- The uniform finite-sum control-variate estimator unfolds to
`card • (new - old) + old`.

Layer: Model | Gap: Level 0 (finite-sum control-variate estimator unfolding)
Proof: by rfl after unfolding `uniformFiniteSumControlVariateEstimator`.
Source: finite-sum variance-reduction estimators in stochastic optimization
Used in: randomized accelerated proximal-point refreshed gradient-memory estimator
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/7
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
@[simp] theorem uniformFiniteSumControlVariateEstimator_def
    {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E] (old new : E) :
    uniformFiniteSumControlVariateEstimator (ι := ι) old new =
      (Fintype.card ι : ℝ) • (new - old) + old :=
  rfl

/-- The estimator's displacement from the stored value is the population size
times the refreshed residual.

Layer: Model | Gap: Level 0 (finite-sum control-variate residual identity)
Proof: unfold the estimator and cancel the old value.
Source: finite-sum variance-reduction estimators in stochastic optimization
Used in: randomized accelerated proximal-point refreshed gradient-memory estimator
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/7
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
@[simp] theorem uniformFiniteSumControlVariateEstimator_sub_old
    {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E] (old new : E) :
    uniformFiniteSumControlVariateEstimator (ι := ι) old new - old =
      (Fintype.card ι : ℝ) • (new - old) := by
  simp [uniformFiniteSumControlVariateEstimator]

/-- A mini-batch oracle residual is the average of its centered oracle residual atoms.

The mini-batch oracle is evaluated at `point (query k omega)`, while the
residual target is attached to the query object itself. This covers carrier
queries whose oracle input is a projection to an ambient space.

Layer: Model | Gap: Level 1 (mini-batch oracle residual centering)
Proof: unfold the staged mini-batch average and random-query residual objects,
  then apply finite-average centering over the interval `1, ..., m k`.
Source: SOptLib stochastic oracle model definitions and Mathlib finite-sum
  module algebra over real scalars
Used in: stochastic conditional-gradient sliding mini-batch variance bridge and
  martingale residual cancellation
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem miniBatchOracleResidual_eq_average_oracleResidualAt
    {Ω ι Q X E K SRun : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : K → ℕ) (oracleValue : ι → X → Ω → E)
    (sampleIndex : SRun → K → ℕ → ι) (run : SRun)
    (target : Q → E) (query : K → Ω → Q) (point : Q → X)
    (k : K) (ω : Ω) (hmpos : 0 < m k) :
    miniBatchResidualAtIterate
        (fun k q ω => miniBatchOracleAverage m oracleValue sampleIndex run k (point q) ω)
        target query k ω =
      ((m k : ℝ)⁻¹) •
        Finset.sum (Finset.Icc 1 (m k))
          (fun j =>
            oracleResidualAtRandomQuery
              (fun _ q ω => oracleValue (sampleIndex run k j) (point q) ω)
              target 0 (query k) ω) := by
  let I : Finset ℕ := Finset.Icc 1 (m k)
  let c : E := target (query k ω)
  let z : ℕ → E := fun j => oracleValue (sampleIndex run k j) (point (query k ω)) ω
  have hcard : I.card = m k := by
    dsimp [I]
    rw [Nat.card_Icc]
    omega
  have hIpos : 0 < I.card := by
    simpa [hcard] using hmpos
  have hcard_ne : ((I.card : ℝ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt hIpos)
  have hcenter :
      ((m k : ℝ)⁻¹) • Finset.sum I z - c =
        ((m k : ℝ)⁻¹) • Finset.sum I (fun j => z j - c) := by
    have hsum_sub :
        Finset.sum I (fun j => z j - c) =
          Finset.sum I z - (I.card : ℝ) • c := by
      rw [Finset.sum_sub_distrib, Finset.sum_const]
      simp [Nat.cast_smul_eq_nsmul]
    calc
      ((m k : ℝ)⁻¹) • Finset.sum I z - c
          = ((I.card : ℝ)⁻¹) • Finset.sum I z - c := by
              rw [hcard]
      _ = ((I.card : ℝ)⁻¹) • Finset.sum I z -
            (((I.card : ℝ)⁻¹) * (I.card : ℝ)) • c := by
              rw [inv_mul_cancel₀ hcard_ne]
              simp
      _ = ((I.card : ℝ)⁻¹) •
            (Finset.sum I z - (I.card : ℝ) • c) := by
              simp [smul_sub, smul_smul]
      _ = ((I.card : ℝ)⁻¹) • Finset.sum I (fun j => z j - c) := by
              rw [hsum_sub]
      _ = ((m k : ℝ)⁻¹) • Finset.sum I (fun j => z j - c) := by
              rw [hcard]
  simpa [miniBatchResidualAtIterate, miniBatchOracleAverage, oracleResidualAtRandomQuery,
    I, c, z] using hcenter

/-- Fixed-query squared stochastic-oracle residual kernel.

For a stochastic oracle `G`, target field `target`, sample map `xi`, and fixed
query `x`, this names the scalar kernel `omega |-> ‖G x (xi omega) -
target x‖ ^ 2` used in oracle variance and second-moment assumptions.

Layer: Model | Concept: Oracle
Proof: (definitional construction; fixed-query stochastic oracle residual
  composed with a sample map and squared after taking the norm)
Source: Mathlib normed additive-group algebra for stochastic oracle residuals
Used in: stochastic conditional-gradient sliding fixed-query oracle variance
  integrand before expectation bounds
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/assumptions/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
def oracleResidualSqKernel
    {Omega X Sample E : Type*} [NormedAddCommGroup E]
    (G : X -> Sample -> E) (target : X -> E) (xi : Omega -> Sample) (x : X) :
    Omega -> ℝ :=
  fun omega => ‖G x (xi omega) - target x‖ ^ 2

/-- The fixed-query squared oracle residual kernel unfolds to the squared norm
of oracle value minus target.

Layer: Model | Gap: Level 0 (fixed-query squared oracle residual unfolding)
Proof: by rfl after unfolding `oracleResidualSqKernel`.
Source: Mathlib normed additive-group algebra for stochastic oracle residuals
Used in: stochastic conditional-gradient sliding fixed-query oracle variance
  integrand before expectation bounds
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/assumptions/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
@[simp]
theorem oracleResidualSqKernel_apply
    {Omega X Sample E : Type*} [NormedAddCommGroup E]
    (G : X -> Sample -> E) (target : X -> E) (xi : Omega -> Sample) (x : X)
    (omega : Omega) :
    oracleResidualSqKernel G target xi x omega =
      ‖G x (xi omega) - target x‖ ^ 2 := by
  rfl

/-- The fixed-query squared oracle residual kernel is pointwise nonnegative.

Layer: Model | Gap: Level 0 (fixed-query squared oracle residual nonnegativity)
Proof: by unfolding and applying nonnegativity of squares in `ℝ`.
Source: Mathlib ordered-ring algebra for squares
Used in: stochastic oracle variance and second-moment bounds
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/assumptions/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem oracleResidualSqKernel_nonneg
    {Omega X Sample E : Type*} [NormedAddCommGroup E]
    (G : X -> Sample -> E) (target : X -> E) (xi : Omega -> Sample) (x : X)
    (omega : Omega) :
    0 ≤ oracleResidualSqKernel G target xi x omega := by
  rw [oracleResidualSqKernel_apply]
  exact sq_nonneg _

/-- The fixed-query squared kernel is the squared norm of the random-query
residual at the constant query.

Layer: Model | Gap: Level 0 (fixed-query squared residual bridge)
Proof: by unfolding the squared kernel and sampled residual definitions.
Source: SOptLib sampled oracle residual definitions
Used in: stochastic oracle variance and second-moment bounds that switch
  between fixed-query and random-query residual notation
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/assumptions/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem oracleResidualSqKernel_eq_norm_oracleResidualAtRandomQuery_const
    {Omega X Sample E : Type*} [NormedAddCommGroup E]
    (G : X -> Sample -> E) (target : X -> E) (xi : Omega -> Sample) (x : X)
    (omega : Omega) :
    oracleResidualSqKernel G target xi x omega =
      ‖oracleResidualAtRandomQuery
        (fun _ q omega => G q (xi omega)) target 0 (fun _ : Omega => x) omega‖ ^ 2 := by
  rfl

end SOptLib

-- Batch 2 promoted from Staging/smoothnessImportanceWeight_sum_one_of_average.lean
open scoped BigOperators

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: smoothnessImportanceWeight_sum_one_of_average exposes the
--   probability-vector normalization of smoothness-proportional finite-sum
--   importance weights; orig was componentSamplingProbability_sum_one, renamed
--   away from the paper setup field and local component-sampling notation.
-- generality used: arbitrary finite index type `ι`, real component smoothness
--   weights `Lcomp`, real count normalizer `n`, and average/global smoothness
--   scale `L`; no measure, filtration, convexity, oracle, topology, vector
--   space, completeness, or finite-dimensional hypotheses are used.
-- portable call pattern: finite-sum SGD, variance-reduced conditional-gradient,
--   and stochastic mirror-descent proofs can change the component index type,
--   component smoothness constants, and average-smoothness identity while using
--   the same normalization fact to construct PMFs or probability measures.
-- counterargument checked: not paper-local traceability because the theorem is
--   stated about the existing paper-free Model object
--   `SOptLib.smoothnessImportanceWeight`; not a pure wrapper around Mathlib,
--   because it bridges the named smoothness-importance weight to the generic
--   finite normalized-sum API after using the average-smoothness identity.
-- coverage search: searched CATALOG.md/project for
--   `smoothnessImportanceWeight`, `importance sampling sum_one`, and
--   `sum_div_sum_eq_one`; SOptLib had the weight definition and nonnegativity
--   theorem plus generic `Finset.sum_div_sum_eq_one`, but no theorem combining
--   the named smoothness-importance weight with the average identity.
--   LeanSearch for "finite sum weights divided by total sum equals one"
--   returned simplex/centroid/PMF normalization facts, all partial and none
--   about smoothness-proportional finite-sum weights.
-- minimal hypotheses: reduced setup positivity fields to the two algebraic
--   facts actually used by this normalization proof, `n ≠ 0` and nonzero total
--   component mass; callers with positive smoothness constants derive the
--   latter locally.

/-- Smoothness-proportional finite-sum importance weights sum to one under the
average-smoothness identity.

If `L = n⁻¹ * ∑ i, Lcomp i`, the count normalizer `n` is nonzero, and the
total component smoothness mass is nonzero, then the named weights
`Lcomp i / (n * L)` form a normalized finite family.

Layer: Model | Gap: Level 0 (finite smoothness-importance normalization)
Proof: rewrite `n * L` to the total component smoothness mass using the average
  identity and `n ≠ 0`, then apply the finite normalized-sum theorem.
Source: Mathlib finite-sum algebra and stochastic finite-sum importance
  sampling conventions
Used in: stochastic nonconvex conditional-gradient component sampling
  probabilities before constructing the component-index PMF
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/setup/finite_sum_probabilities
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
theorem smoothnessImportanceWeight_sum_one_of_average
    {ι : Type*} [Fintype ι] (Lcomp : ι → ℝ) {n L : ℝ}
    (hn_ne : n ≠ 0)
    (hL_average : L = n⁻¹ * ∑ i, Lcomp i)
    (hsum_ne : (∑ i, Lcomp i) ≠ 0) :
    ∑ i, smoothnessImportanceWeight Lcomp n L i = 1 := by
  have hden_eq : n * L = ∑ i, Lcomp i := by
    rw [hL_average]
    calc
      n * (n⁻¹ * ∑ i, Lcomp i) = (n * n⁻¹) * ∑ i, Lcomp i := by
        ring
      _ = 1 * ∑ i, Lcomp i := by
        rw [mul_inv_cancel₀ hn_ne]
      _ = ∑ i, Lcomp i := by
        ring
  unfold smoothnessImportanceWeight
  rw [hden_eq]
  calc
    (∑ i, Lcomp i / (∑ i, Lcomp i)) = (∑ i, Lcomp i) / (∑ i, Lcomp i) := by
      rw [← Finset.sum_div]
    _ = 1 := div_self hsum_ne

end SOptLib


-- Batch 2 promoted from Staging/smoothnessImportancePMF.lean
open scoped BigOperators

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: smoothnessImportancePMF exposes the canonical finite PMF whose
--   atom weights are smoothness-proportional finite-sum importance weights;
--   orig was componentSamplingPMF, renamed away from Algorithm 7.12's local
--   component-sampling notation.
-- generality used: arbitrary finite index type `ι`, real component smoothness
--   weights `Lcomp`, real count normalizer `n`, and average/global smoothness
--   scale `L`; no measure, filtration, convexity, oracle measurability,
--   topology, vector-space, completeness, or finite-dimensional hypotheses are
--   used.
-- portable call pattern: finite-sum SGD, stochastic conditional-gradient,
--   variance-reduced, and stochastic mirror-descent proofs instantiate the
--   component index type and smoothness constants, then call the same PMF
--   constructor before finite-PMF expectation or inverse-probability lifting.
-- counterargument checked: not merely paper-local traceability because the
--   statement is about the paper-free `smoothnessImportanceWeight` Model
--   object and constructs the reusable component-index law; not a duplicate of
--   Mathlib's `PMF.ofFintype`, because it packages the named stochastic-
--   optimization weights together with their nonnegativity and average-
--   smoothness normalization obligations.
-- coverage search: searched CATALOG.md/project for `smoothnessImportancePMF`,
--   `importance PMF`, `finiteImportancePMF`, and `smoothnessImportanceWeight`;
--   SOptLib has the weight definition, its nonnegativity theorem, the staged
--   sum-one theorem, and generic real-weight PMF constructors, but no canonical
--   smoothness-weight PMF. LeanSearch for finite nonnegative real weights
--   returned Mathlib `PMF.ofFintype`/normalization constructors, partial only.
-- minimal hypotheses: setup fields are reduced to the pointwise nonnegativity
--   of component weights, positivity of the count normalizer, the
--   average-smoothness identity, and nonzero total component mass; count
--   nonnegativity/nonzeroness and smoothness-scale nonnegativity are derived.

/-- Canonical PMF with smoothness-proportional finite-component importance weights.

Given component smoothness weights `Lcomp`, a count normalizer `n`, and an
average smoothness scale `L = n⁻¹ * ∑ i, Lcomp i`, this constructs the finite
component-index law with atom mass `Lcomp i / (n * L)`.

Layer: Model | Concept: Probability
Proof: (definitional construction; finite PMF from named smoothness-importance
  weights using their nonnegativity and average-smoothness normalization)
Source: Mathlib probability mass functions, finite sums, and finite-sum
  stochastic importance-sampling conventions
Used in: finite-sum stochastic oracle component sampling before PMF
  expectations and inverse-probability gradient corrections
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/setup/finite_sum_probabilities
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
noncomputable def smoothnessImportancePMF
    {ι : Type*} [Fintype ι] (Lcomp : ι → ℝ) {n L : ℝ}
    (hcomp_nonneg : ∀ i, 0 ≤ Lcomp i)
    (hn_pos : 0 < n)
    (hL_average : L = n⁻¹ * ∑ i, Lcomp i)
    (hsum_ne : (∑ i, Lcomp i) ≠ 0) :
    PMF ι :=
  let hn_nonneg : 0 ≤ n := le_of_lt hn_pos
  let hn_ne : n ≠ 0 := ne_of_gt hn_pos
  let hL_nonneg : 0 ≤ L := by
    rw [hL_average]
    exact mul_nonneg (inv_nonneg.mpr hn_nonneg)
      (Finset.sum_nonneg (fun i _ => hcomp_nonneg i))
  PMF.ofFintypeOfReal
    (smoothnessImportanceWeight Lcomp n L)
    (smoothnessImportanceWeight_nonneg hcomp_nonneg hn_nonneg hL_nonneg)
    (smoothnessImportanceWeight_sum_one_of_average
      (Lcomp := Lcomp) (n := n) (L := L) hn_ne hL_average hsum_ne)

/-- The smoothness-importance PMF is the finite PMF built from the named
smoothness-importance weights.

Layer: Model | Gap: paired API for the smoothness-importance PMF definition
Proof: definitional unfolding after deriving the count and smoothness
  nonnegativity obligations from the public hypotheses.
Source: Mathlib probability mass functions and finite-sum importance weights
Used in: downstream proofs that need to cross the abstraction barrier from the
  named PMF to its `PMF.ofFintypeOfReal` construction -/
@[simp]
theorem smoothnessImportancePMF_def
    {ι : Type*} [Fintype ι] (Lcomp : ι → ℝ) {n L : ℝ}
    (hcomp_nonneg : ∀ i, 0 ≤ Lcomp i)
    (hn_pos : 0 < n)
    (hL_average : L = n⁻¹ * ∑ i, Lcomp i)
    (hsum_ne : (∑ i, Lcomp i) ≠ 0) :
    smoothnessImportancePMF Lcomp hcomp_nonneg hn_pos hL_average hsum_ne =
      PMF.ofFintypeOfReal
        (smoothnessImportanceWeight Lcomp n L)
        (smoothnessImportanceWeight_nonneg hcomp_nonneg (le_of_lt hn_pos) (by
          rw [hL_average]
          exact mul_nonneg (inv_nonneg.mpr (le_of_lt hn_pos))
            (Finset.sum_nonneg (fun i _ => hcomp_nonneg i))))
        (smoothnessImportanceWeight_sum_one_of_average
          (Lcomp := Lcomp) (n := n) (L := L)
          (ne_of_gt hn_pos) hL_average hsum_ne) := by
  rfl

/-- The smoothness-importance PMF has the named smoothness-proportional atom mass.

Layer: Model | Gap: Level 0 (finite smoothness-importance PMF atom formula)
Proof: unfold the smoothness-importance PMF and use the finite real-weight PMF
  evaluation theorem.
Source: Mathlib probability mass functions, finite sums, and extended
  nonnegative real embeddings
Used in: finite-sum stochastic oracle expectations where PMF atoms are rewritten
  as smoothness-proportional real weights
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/setup/finite_sum_probabilities
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
@[simp]
theorem smoothnessImportancePMF_apply
    {ι : Type*} [Fintype ι] (Lcomp : ι → ℝ) {n L : ℝ}
    (hcomp_nonneg : ∀ i, 0 ≤ Lcomp i)
    (hn_pos : 0 < n)
    (hL_average : L = n⁻¹ * ∑ i, Lcomp i)
    (hsum_ne : (∑ i, Lcomp i) ≠ 0) (i : ι) :
    smoothnessImportancePMF Lcomp hcomp_nonneg hn_pos hL_average hsum_ne i =
      ENNReal.ofReal (smoothnessImportanceWeight Lcomp n L i) := by
  simp [smoothnessImportancePMF]

end SOptLib


-- Batch 2 promoted from Staging/importanceWeightedGradientDifference.lean
namespace SOptLib

open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: importance_weighted_gradient_difference exposes the inverse-
--   probability weighted component gradient-difference atom used by finite-sum
--   variance-reduced stochastic estimators; orig was sampledGradientCorrection,
--   renamed away from Algorithm 7.12 local sampling notation.
-- generality used: arbitrary component index type `ι`, arbitrary query type
--   `X`, target type `E` with subtraction and real scalar multiplication,
--   component weights `q`, real normalizer `n`, and component-gradient family
--   `gradF`; no measure, independence, integrability, convexity, smoothness,
--   topology, norm, inner product, completeness, or finite-dimensional
--   hypotheses are used.
-- portable call pattern: finite-sum SGD, SARAH/SPIDER-style variance
--   reduction, stochastic conditional-gradient, and finite-sum mirror-descent
--   proofs instantiate component probabilities, the finite-sum normalizer, the
--   component-gradient family, two query points, and the sampled index while
--   using the same estimator atom in expectation and moment calculations.
-- counterargument checked: not merely paper-local traceability because
--   inverse-probability weighted component differences are the reusable atom
--   behind finite-sum variance-reduced estimators; not only a caller-side
--   expression because downstream centering, measurability, and second-moment
--   bounds refer to the same named object. Existing SOptLib coverage includes
--   a measurability theorem for this kernel shape, but no Model-level named
--   estimator atom.
-- coverage search: searched CATALOG.md/SOptLib/Staging/Algorithms for
--   `importanceWeighted`, `sampledGradientCorrection`, `GradientDifference`,
--   and `component gradient difference`; relevant partial hits were
--   `SOptLib.measurable_componentWeightedGradDiffKernel` in Layer0/Oracle and
--   `SOptLib.recursiveGradientDifferenceAverage` in Model/StochasticOracle.
--   LeanSearch for "importance weighted gradient difference finite sum
--   stochastic gradient estimator" found affine weighted-subtraction lemmas
--   such as `Finset.sum_smul_vsub_eq_weightedVSub_sub`, but no stochastic
--   finite-sum estimator atom.
-- minimal hypotheses: all already minimal; the definition only uses `Sub E`,
--   `SMul ℝ E`, real multiplication/inversion, and function application.

/-- Inverse-probability weighted component gradient difference.

For component weights `q`, normalizer `n`, component-gradient family `gradF`,
and two query points `x` and `y`, this names the estimator atom
`(q i * n)⁻¹ • (gradF i x - gradF i y)`.

Layer: Model | Concept: Oracle
Proof: (definitional construction; inverse-probability weighted finite-sum
  component gradient-difference atom)
Source: finite-sum stochastic variance-reduction estimators and Mathlib real
  scalar-action primitives
Used in: finite-sum stochastic nonconvex conditional-gradient recursive
  estimator centering and second-moment bounds
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
noncomputable def importance_weighted_gradient_difference
    {ι X E : Type*} [Sub E] [SMul ℝ E]
    (q : ι → ℝ) (n : ℝ) (gradF : ι → X → E) (x y : X) (i : ι) : E :=
  ((q i * n)⁻¹) • (gradF i x - gradF i y)

/-- The inverse-probability weighted component gradient difference unfolds to
its scalar-weighted component-gradient subtraction formula.

Layer: Model | Gap: Level 0 (importance-weighted gradient-difference unfolding)
Proof: by rfl after unfolding `importance_weighted_gradient_difference`.
Source: finite-sum stochastic variance-reduction estimators and Mathlib real
  scalar-action primitives
Used in: finite-sum stochastic nonconvex conditional-gradient recursive
  estimator centering and second-moment bounds
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
@[simp]
theorem importance_weighted_gradient_difference_def
    {ι X E : Type*} [Sub E] [SMul ℝ E]
    (q : ι → ℝ) (n : ℝ) (gradF : ι → X → E) (x y : X) (i : ι) :
    importance_weighted_gradient_difference q n gradF x y i =
      ((q i * n)⁻¹) • (gradF i x - gradF i y) := by
  rfl

/-- Weighted finite means of the inverse-probability gradient-difference atom
recover the corresponding uniform finite-difference mean.

Layer: Model | Gap: Level 1 (importance-weighted gradient-difference mean
  cancellation)
Proof: cancel each pointwise scalar factor `q i * (q i * n)⁻¹` to `n⁻¹`,
  then commute the common scalar through the finite sum and distribute over
  component differences.
Source: finite-sum stochastic variance-reduction estimators and Mathlib finite
  sum/module APIs
Used in: finite-sum stochastic nonconvex conditional-gradient recursive
  estimator centering
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
theorem finset_weighted_sum_importance_weighted_gradient_difference_eq_uniform_sum_sub
    {ι X E : Type*} [AddCommGroup E] [Module ℝ E]
    (s : Finset ι) (q : ι → ℝ) (n : ℝ) (gradF : ι → X → E) (x y : X)
    (hq_ne : ∀ i ∈ s, q i ≠ 0) (hn_ne : n ≠ 0) :
    Finset.sum s
        (fun i : ι => q i • importance_weighted_gradient_difference q n gradF x y i) =
      n⁻¹ • Finset.sum s (fun i : ι => gradF i x) -
        n⁻¹ • Finset.sum s (fun i : ι => gradF i y) := by
  classical
  have hterm :
      ∀ i ∈ s,
        q i • importance_weighted_gradient_difference q n gradF x y i =
          n⁻¹ • (gradF i x - gradF i y) := by
    intro i hi
    calc
      q i • importance_weighted_gradient_difference q n gradF x y i =
          q i • (((q i * n)⁻¹) • (gradF i x - gradF i y)) := by
            rw [importance_weighted_gradient_difference_def]
      _ = (q i * (q i * n)⁻¹) • (gradF i x - gradF i y) := by
            rw [smul_smul]
      _ = n⁻¹ • (gradF i x - gradF i y) := by
            have hscalar : q i * (q i * n)⁻¹ = n⁻¹ := by
              field_simp [hq_ne i hi, hn_ne]
            rw [hscalar]
  calc
    Finset.sum s
        (fun i : ι => q i • importance_weighted_gradient_difference q n gradF x y i) =
      Finset.sum s (fun i : ι => n⁻¹ • (gradF i x - gradF i y)) := by
        exact Finset.sum_congr rfl (fun i hi => hterm i hi)
    _ = n⁻¹ • Finset.sum s (fun i : ι => gradF i x - gradF i y) := by
        rw [Finset.smul_sum]
    _ = n⁻¹ • Finset.sum s (fun i : ι => gradF i x) -
        n⁻¹ • Finset.sum s (fun i : ι => gradF i y) := by
        rw [Finset.sum_sub_distrib, smul_sub]

-- Generalization plan (G0):
-- concept/name: importance-weighted control-variate estimator; orig was
--   carrierVarianceReducedGradient, renamed away from carrier-gradient and
--   accelerated-gradient setup language.
-- generality used: arbitrary component index type `ι`, query type `X`, and
--   target type `E` with only subtraction, addition, and real scalar
--   multiplication; no measure, independence, integrability, topology, norm,
--   inner product, convexity, smoothness, completeness, or finite-dimensional
--   hypotheses are used.
-- portable call pattern: nonuniform SVRG/SAGA/control-variate finite-sum
--   estimators instantiate component weights, finite-sum normalizer,
--   component-gradient family, current point, snapshot point, sampled index,
--   and full snapshot gradient while reusing the same estimator formula.
-- counterargument checked: not paper-local traceability because the definition
--   exposes the standard inverse-probability control-variate estimator; not a
--   duplicate of `importance_weighted_gradient_difference`, which names only
--   the component-difference atom before adding the full snapshot gradient.
-- coverage search: searched CATALOG.md/SOptLib/Staging/Algorithms for
--   `importance weighted gradient difference`, `control variate estimator`,
--   `variance reduced estimator`, and `carrierVarianceReducedGradient`; relevant
--   partial hits were `SOptLib.importance_weighted_gradient_difference`,
--   `SOptLib.uniformFiniteSumControlVariateEstimator`, and staged
--   `importance_weighted_control_variate_residual_weighted_sum_eq_zero`.
--   LeanSearch for "importance weighted control variate estimator stochastic
--   variance reduced gradient" returned variance API hits, not a finite-sum
--   control-variate estimator definition.
-- minimal hypotheses: all already minimal; the formula needs subtraction for
--   component differences, real scalar multiplication for inverse-probability
--   weighting, and addition for the full snapshot-gradient control variate.

/-- Importance-weighted finite-sum control-variate estimator.

For component weights `q`, normalizer `n`, component-gradient family `gradF`,
current point `x`, snapshot point `snapshot`, sampled component `sample`, and
full snapshot gradient `fullGradAtSnapshot`, this names the SVRG-style atom
formed by adding the full snapshot gradient to the inverse-probability weighted
component-gradient difference.

Layer: Model | Concept: Oracle
Proof: (definitional construction; inverse-probability finite-sum control-variate estimator)
Source: finite-sum stochastic variance-reduction estimators and Mathlib real
  scalar-action primitives
Used in: finite-sum variance-reduced accelerated-gradient estimator definition
  before residual centering and second-moment estimates
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
noncomputable def importance_weighted_control_variate_estimator
    {ι X E : Type*} [Sub E] [Add E] [SMul ℝ E]
    (q : ι → ℝ) (n : ℝ) (gradF : ι → X → E) (x snapshot : X)
    (sample : ι) (fullGradAtSnapshot : E) : E :=
  importance_weighted_gradient_difference q n gradF x snapshot sample +
    fullGradAtSnapshot

/-- The importance-weighted control-variate estimator unfolds to the
importance-weighted component-gradient difference plus the full snapshot
gradient.

Layer: Model | Gap: Level 0 (importance-weighted control-variate estimator unfolding)
Proof: by rfl after unfolding `importance_weighted_control_variate_estimator`.
Source: finite-sum stochastic variance-reduction estimators and Mathlib real
  scalar-action primitives
Used in: finite-sum variance-reduced accelerated-gradient estimator definition
  before residual centering and second-moment estimates
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
@[simp]
theorem importance_weighted_control_variate_estimator_def
    {ι X E : Type*} [Sub E] [Add E] [SMul ℝ E]
    (q : ι → ℝ) (n : ℝ) (gradF : ι → X → E) (x snapshot : X)
    (sample : ι) (fullGradAtSnapshot : E) :
    importance_weighted_control_variate_estimator q n gradF x snapshot sample fullGradAtSnapshot =
      importance_weighted_gradient_difference q n gradF x snapshot sample +
        fullGradAtSnapshot := by
  rfl

/-- The weighted mean of the importance-weighted control-variate estimator is
the current finite-sum mean when the added control variate is the snapshot
finite-sum mean.

Layer: Model | Gap: Level 1 (importance-weighted control-variate estimator mean)
Proof: combine the finite-sum mean formula for the inverse-probability
  gradient-difference atom with the weighted sum of the constant snapshot mean.
Source: finite-sum stochastic variance-reduction estimators and Mathlib
  finite-sum module APIs
Used in: finite-sum variance-reduced accelerated-gradient estimator centering
  before residual and second-moment estimates
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem importance_weighted_control_variate_estimator_weighted_sum_eq_uniform_sum
    {ι X E : Type*} [AddCommGroup E] [Module ℝ E]
    (s : Finset ι) (q : ι → ℝ) (n : ℝ) (gradF : ι → X → E)
    (x snapshot : X) (fullGradAtSnapshot : E)
    (hqsum : s.sum q = 1)
    (hq_ne : ∀ i ∈ s, q i ≠ 0) (hn_ne : n ≠ 0)
    (hfull :
      fullGradAtSnapshot = n⁻¹ • s.sum (fun i : ι => gradF i snapshot)) :
    s.sum (fun i : ι =>
        q i •
          importance_weighted_control_variate_estimator q n gradF x snapshot i
            fullGradAtSnapshot) =
      n⁻¹ • s.sum (fun i : ι => gradF i x) := by
  classical
  let componentMean : X → E :=
    fun z => n⁻¹ • s.sum (fun i : ι => gradF i z)
  have hdiff_mean :
      s.sum (fun i : ι =>
          q i • importance_weighted_gradient_difference q n gradF x snapshot i) =
        componentMean x - componentMean snapshot := by
    have hsum :=
      finset_weighted_sum_importance_weighted_gradient_difference_eq_uniform_sum_sub
        (s := s)
        (q := q) (n := n) (gradF := gradF) (x := x) (y := snapshot)
        hq_ne hn_ne
    simpa [componentMean] using hsum
  calc
    s.sum (fun i : ι =>
        q i •
          importance_weighted_control_variate_estimator q n gradF x snapshot i
            fullGradAtSnapshot)
        =
      s.sum (fun i : ι =>
          q i • importance_weighted_gradient_difference q n gradF x snapshot i) +
        s.sum (fun i : ι => q i • fullGradAtSnapshot) := by
        simp [importance_weighted_control_variate_estimator, smul_add,
          Finset.sum_add_distrib]
    _ = (componentMean x - componentMean snapshot) + fullGradAtSnapshot := by
        rw [hdiff_mean]
        rw [← Finset.sum_smul, hqsum]
        simp
    _ = n⁻¹ • s.sum (fun i : ι => gradF i x) := by
        rw [hfull]
        simp [componentMean]


-- Generalization plan (G0):
-- concept/name: importance-weighted control-variate residual centering; orig was
--   carrierEstimatorResidual_weighted_mean_zero, renamed away from carrier and
--   accelerated-gradient setup language.
-- generality used: arbitrary finite component set in an index type `ι`, query
--   type `X`, and target module `E` with only `AddCommGroup E` and `Module ℝ E`; no
--   measure, independence, integrability, topology, norm, inner product,
--   convexity, smoothness, or finite-dimensional hypotheses are used.
-- portable call pattern: finite-sum SVRG/SAGA/SARAH/SPIDER, stochastic
--   conditional-gradient, and finite-sum mirror-descent proofs instantiate the
--   component weights, finite-sum normalizer, component-gradient family, current
--   point, and snapshot while reusing the same residual weighted-sum centering.
-- counterargument checked: not paper-local traceability because the statement
--   packages the standard finite-sum variance-reduction control-variate
--   cancellation; not a duplicate of `finset_weighted_residual_sum_eq_zero`,
--   which only centers an already-proved weighted mean and does not compute the
--   importance-weighted control-variate mean.
-- coverage search: searched CATALOG.md/SOptLib/Staging/Algorithms for
--   `weighted residual sum zero`, `importance weighted gradient difference`,
--   `control variate residual`, and `finite sum variance reduced`; relevant
--   partial hits were `SOptLib.importance_weighted_gradient_difference`,
--   `SOptLib.finset_weighted_sum_importance_weighted_gradient_difference_eq_uniform_sum_sub`,
--   and `finset_weighted_residual_sum_eq_zero`, but none states the combined
--   control-variate residual centering theorem.
-- minimal hypotheses: pointwise nonzero weights and nonzero normalizer are used
--   only to cancel inverse-probability factors; weight normalization is used
--   only to center the residual at the finite-sum mean.

/-- The importance-weighted finite-sum control-variate residual has zero weighted mean.

For a finite component set `s`, component weights `q`, normalizer `n`,
component-gradient family `gradF`, current point `x`, and snapshot `snapshot`, the estimator
`importance_weighted_gradient_difference q n gradF x snapshot i` plus the
snapshot finite-sum mean is centered at the current finite-sum mean.

Layer: Model | Gap: Level 1 (importance-weighted control-variate residual centering)
Proof: first use the existing finite-sum mean formula for the
  inverse-probability gradient-difference atom, then apply the generic finite
  weighted residual centering lemma.
Source: finite-sum stochastic variance-reduction estimators and Mathlib
  finite-sum module APIs
Used in: finite-sum variance-reduced accelerated-gradient residual centering
  before second-moment and descent estimates
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem importance_weighted_control_variate_residual_weighted_sum_eq_zero
    {ι X E : Type*} [AddCommGroup E] [Module ℝ E]
    (s : Finset ι) (q : ι → ℝ) (n : ℝ) (gradF : ι → X → E) (x snapshot : X)
    (hqsum : s.sum q = 1)
    (hq_ne : ∀ i ∈ s, q i ≠ 0) (hn_ne : n ≠ 0) :
    s.sum (fun i : ι =>
        q i •
          (SOptLib.importance_weighted_gradient_difference q n gradF x snapshot i +
              n⁻¹ • s.sum (fun j : ι => gradF j snapshot) -
            n⁻¹ • s.sum (fun j : ι => gradF j x))) = 0 := by
  classical
  let componentMean : X → E :=
    fun z => n⁻¹ • s.sum (fun i : ι => gradF i z)
  have hdiff_mean :
      s.sum (fun i : ι =>
          q i • SOptLib.importance_weighted_gradient_difference q n gradF x snapshot i) =
        componentMean x - componentMean snapshot := by
    have hsum :=
      SOptLib.finset_weighted_sum_importance_weighted_gradient_difference_eq_uniform_sum_sub
        (s := s)
        (q := q) (n := n) (gradF := gradF) (x := x) (y := snapshot)
        hq_ne hn_ne
    simpa [componentMean] using hsum
  have hest_mean :
      s.sum (fun i : ι =>
          q i •
            (SOptLib.importance_weighted_gradient_difference q n gradF x snapshot i +
              componentMean snapshot)) =
        componentMean x := by
    calc
      s.sum (fun i : ι =>
          q i •
            (SOptLib.importance_weighted_gradient_difference q n gradF x snapshot i +
              componentMean snapshot))
          =
        s.sum (fun i : ι =>
            q i • SOptLib.importance_weighted_gradient_difference q n gradF x snapshot i) +
          s.sum (fun i : ι => q i • componentMean snapshot) := by
          simp [smul_add, Finset.sum_add_distrib]
      _ = (componentMean x - componentMean snapshot) + componentMean snapshot := by
          rw [hdiff_mean]
          rw [← Finset.sum_smul, hqsum]
          simp
      _ = componentMean x := by
          abel
  calc
    s.sum (fun i : ι =>
        q i •
          (SOptLib.importance_weighted_gradient_difference q n gradF x snapshot i +
              n⁻¹ • s.sum (fun j : ι => gradF j snapshot) -
            n⁻¹ • s.sum (fun j : ι => gradF j x)))
        = s.sum (fun i : ι =>
            q i •
              (SOptLib.importance_weighted_gradient_difference q n gradF x snapshot i +
                componentMean snapshot)) -
          s.sum (fun i : ι => q i • componentMean x) := by
          simp [componentMean, sub_eq_add_neg, smul_add, Finset.sum_add_distrib]
    _ = componentMean x - componentMean x := by
          rw [hest_mean, ← Finset.sum_smul, hqsum]
          simp
    _ = 0 := by
          abel


-- Generalization plan (G0):
-- concept/name: importance-weighted control-variate estimator pairing
--   transport; orig was
--   carrierVarianceReducedGradient_inner_eq_varianceReducedGradient, renamed
--   away from carrier-gradient and variance-reduced algorithm setup language.
-- generality used: arbitrary sample index type `ι`, query type `X`, and real
--   inner product target `E`; no measure, independence, integrability,
--   convexity, smoothness, completeness, finite-dimensional, or carrier
--   hypotheses are used.
-- portable call pattern: nonuniform SVRG/SAGA/control-variate finite-sum
--   estimator proofs can replace a carrier-restricted component family by an
--   ambient component family against a feasible test direction; component
--   families, full correction vectors, sample index, current point, snapshot
--   point, and test direction vary while the estimator pairing conclusion is
--   unchanged.
-- counterargument checked: wrapper risk is real because the proof is algebraic,
--   but it is not a pure rename of Mathlib or the estimator definition: it
--   packages the recurring proof step that component and full-gradient pairing
--   equalities lift through the inverse-probability control-variate formula.
--   It is not paper-local traceability because the same pairing transport is
--   needed whenever constrained or projected variance-reduced estimators are
--   compared to ambient estimators.
-- coverage search: searched CATALOG.md/SOptLib/Staging/Algorithms for
--   `control_variate`, `varianceReducedGradient`, `inner_eq`,
--   `weighted_sum_eq_target`, `importance_weighted_gradient_difference`, and
--   `carrier gradient estimator`; relevant partial hits were
--   `SOptLib.importance_weighted_gradient_difference`,
--   staged `SOptLib.importance_weighted_control_variate_estimator`, staged
--   `importance_weighted_control_variate_weighted_sum_eq_target`, and carrier
--   pairing bridges in `SOptLib.Model.Carrier`. LeanSearch for "inner product
--   equality of two control variate estimators from component pairings" returned
--   generic inner-product extensionality and product inner lemmas, but no
--   finite-sum control-variate estimator pairing theorem.
-- minimal hypotheses: all already minimal for this statement; pointwise
--   pairings at the sampled current/snapshot components and at the full
--   correction are exactly the hypotheses used by additivity, subtraction, and
--   scalar compatibility of the real inner product.

/-- Pairing equality lifts through an importance-weighted control-variate estimator.

If two component-gradient families have the same pairings against a test
direction at the sampled current and snapshot points, and their full
control-variate corrections have the same pairing against that direction, then
their importance-weighted control-variate estimators have the same pairing.

Layer: Model | Gap: Level 1 (importance-weighted control-variate pairing transport)
Proof: unfold the control-variate estimator and its inverse-probability
  gradient-difference atom, then use additivity, subtraction, and real scalar
  compatibility of the inner product with the three supplied pairing equalities.
Source: finite-sum stochastic variance-reduction estimators and Mathlib real
  inner-product algebra APIs
Used in: finite-sum variance-reduced accelerated-gradient estimator comparison
  between carrier-restricted and ambient component-gradient realizations
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem importance_weighted_control_variate_inner_eq_of_pairings
    {ι X E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (q : ι → Real) (n : Real) (sample : ι)
    (gradA gradB : ι → X → E) (fullA fullB : E)
    (x snapshot : X) (d : E)
    (hcurrent :
      ⟪gradA sample x, d⟫_Real =
        ⟪gradB sample x, d⟫_Real)
    (hsnapshot :
      ⟪gradA sample snapshot, d⟫_Real =
        ⟪gradB sample snapshot, d⟫_Real)
    (hfull : ⟪fullA, d⟫_Real = ⟪fullB, d⟫_Real) :
    ⟪SOptLib.importance_weighted_control_variate_estimator q n gradA
        x snapshot sample fullA, d⟫_Real =
      ⟪SOptLib.importance_weighted_control_variate_estimator q n gradB
        x snapshot sample fullB, d⟫_Real := by
  unfold SOptLib.importance_weighted_control_variate_estimator
    SOptLib.importance_weighted_gradient_difference
  rw [inner_add_left, inner_add_left, hfull]
  congr 1
  rw [inner_smul_left, inner_smul_left]
  congr 1
  rw [inner_sub_left, inner_sub_left, hcurrent, hsnapshot]


-- Generalization plan (G0):
-- concept/name: importance-weighted control-variate estimator mean equals a
--   named target; orig was carrierVarianceReducedGradient_weighted_mean,
--   renamed away from carrier-gradient and accelerated-gradient setup language.
-- generality used: arbitrary finite component set `s : Finset ι`, query type
--   `X`, and target module `E` with only `AddCommGroup E` and `Module ℝ E`; no
--   measure, independence, integrability, topology, norm, inner product,
--   convexity, smoothness, completeness, or finite-dimensional hypotheses are
--   used.
-- portable call pattern: nonuniform SVRG/SAGA/control-variate finite-sum
--   estimator centering proofs instantiate component weights, finite-sum
--   normalizer, component-gradient family, current point, snapshot point, full
--   snapshot gradient, and the named full-gradient target at the current point
--   while reusing the same weighted-mean conclusion.
-- counterargument checked: wrapper risk is real because the nearby staged
--   estimator theorem concludes the raw uniform finite-sum formula; this lemma
--   adds the reusable readability boundary where downstream proofs keep their
--   named target gradient in the goal. It is not paper-local traceability
--   because the same target-mean step recurs across finite-sum
--   variance-reduction algorithms.
-- coverage search: searched CATALOG.md/SOptLib/Staging/Algorithms for
--   `control variate weighted sum target`, `weighted_sum_eq_target`,
--   `importance weighted gradient difference`, and `finiteUniformAverage`;
--   relevant partial hits were `SOptLib.importance_weighted_gradient_difference`,
--   `SOptLib.finset_weighted_sum_importance_weighted_gradient_difference_eq_uniform_sum_sub`,
--   staged `SOptLib.importance_weighted_control_variate_estimator_weighted_sum_eq_uniform_sum`,
--   staged `importance_weighted_control_variate_residual_weighted_sum_eq_zero`,
--   and `SOptLib.finiteUniformAverage`. LeanSearch for "finite sum weighted
--   mean control variate estimator equals target" returned center-of-mass and
--   real weighted-mean lemmas, but no finite-sum control-variate estimator
--   theorem.
-- minimal hypotheses: pointwise nonzero weights and nonzero normalizer are
--   inherited from inverse-probability cancellation; weight normalization
--   handles the constant control variate; the two formula equalities are the
--   caller-side bridge from named full-gradient objects to the finite-sum
--   normalizer already used by the estimator API.

/-- The weighted mean of an importance-weighted control-variate estimator equals
a named target finite-sum mean.

If the added control variate is the snapshot finite-sum mean and the target is
the current finite-sum mean, then averaging the inverse-probability
control-variate estimator with the sampling weights recovers that target.

Layer: Model | Gap: Level 1 (importance-weighted control-variate target mean)
Proof: apply the staged mean formula for the importance-weighted
  control-variate estimator, then rewrite the raw current finite-sum mean to
  the caller's named target object.
Source: finite-sum stochastic variance-reduction estimators and Mathlib
  finite-sum module APIs
Used in: finite-sum variance-reduced accelerated-gradient estimator mean
  identification before residual and second-moment estimates
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem importance_weighted_control_variate_weighted_sum_eq_target
    {ι X E : Type*} [AddCommGroup E] [Module ℝ E]
    (s : Finset ι) (q : ι → ℝ) (n : ℝ) (gradF : ι → X → E)
    (x snapshot : X) (fullAtSnapshot targetAtX : E)
    (hqsum : s.sum q = 1)
    (hq_ne : ∀ i ∈ s, q i ≠ 0) (hn_ne : n ≠ 0)
    (hfull :
      fullAtSnapshot = n⁻¹ • s.sum (fun i : ι => gradF i snapshot))
    (htarget :
      targetAtX = n⁻¹ • s.sum (fun i : ι => gradF i x)) :
    s.sum (fun i : ι =>
        q i •
          SOptLib.importance_weighted_control_variate_estimator q n gradF x
            snapshot i fullAtSnapshot) =
      targetAtX := by
  classical
  have hmean :=
    SOptLib.importance_weighted_control_variate_estimator_weighted_sum_eq_uniform_sum
      (s := s)
      (q := q) (n := n) (gradF := gradF) (x := x) (snapshot := snapshot)
      (fullGradAtSnapshot := fullAtSnapshot)
      hqsum
      hq_ne
      hn_ne
      hfull
  rw [htarget]
  exact hmean


-- Generalization plan (G0):
-- concept/name: importance-weighted gradient-gap quadratic; orig was
--   finiteGradientGapRelationLeft, renamed away from Eq. (5.3.5) side labels
--   and accelerated-gradient setup language.
-- generality used: arbitrary finite component index type `ι`, query type `X`,
--   and normed additive target type `E`; no measure, independence,
--   integrability, convexity, smoothness, inner product, completeness, or
--   finite-dimensional hypotheses are used.
-- portable call pattern: SVRG/SAGA/SARAH/SPIDER-style finite-sum variance
--   proofs instantiate component probabilities `q`, normalizer `n`,
--   component-gradient family `gradF`, and two query points while reusing the
--   same weighted squared-difference aggregate.
-- counterargument checked: not paper-local traceability because the expression
--   is the standard inverse-probability second-moment budget for finite-sum
--   variance-reduced estimators; not a pure wrapper because the companion
--   theorem connects it to the existing importance-weighted gradient-difference
--   estimator atom used in moment calculations.
-- coverage search: searched CATALOG.md/SOptLib/Staging/Algorithms for
--   `importance weighted gradient difference`, `gradient gap quadratic`,
--   `weighted second moment`, and `variance gradient norm squared`; relevant
--   partial hits were `SOptLib.importance_weighted_gradient_difference`,
--   `SOptLib.finset_weighted_sum_importance_weighted_gradient_difference_eq_uniform_sum_sub`,
--   and `Finset.weighted_variance_le_second_moment`, but none names this
--   normalized inverse-probability squared gradient-gap aggregate.
-- minimal hypotheses: all already minimal for the definition; the second-moment
--   bridge uses only nonzero sampling weights and normalizer to cancel real
--   inverse factors.

/-- Normalized importance-weighted quadratic aggregate of component-gradient gaps.

For component weights `q`, normalizer `n`, component-gradient family `gradF`,
and two query points `x` and `y`, this names
`n⁻¹ * ∑ i, (n * q i)⁻¹ * ‖gradF i x - gradF i y‖ ^ 2`.

Layer: Model | Concept: Oracle
Proof: (definitional construction; normalized inverse-probability finite-sum
  squared component-gradient gap)
Source: finite-sum stochastic variance-reduction estimators and Mathlib finite
  sum/norm APIs
Used in: finite-sum variance-reduced accelerated-gradient second-moment
  reduction before applying a gradient-gap bound
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
noncomputable def importance_weighted_gradient_gap_quadratic
    {ι X E : Type*} [Fintype ι] [SeminormedAddCommGroup E]
    (q : ι → ℝ) (n : ℝ) (gradF : ι → X → E) (x y : X) : ℝ :=
  n⁻¹ *
    Finset.univ.sum (fun i : ι =>
      (1 / (n * q i)) * ‖gradF i x - gradF i y‖ ^ 2)

/-- The normalized importance-weighted gradient-gap quadratic unfolds to its
finite-sum formula.

Layer: Model | Gap: Level 0 (importance-weighted gradient-gap quadratic unfolding)
Proof: by rfl after unfolding `importance_weighted_gradient_gap_quadratic`.
Source: finite-sum stochastic variance-reduction estimators and Mathlib finite
  sum/norm APIs
Used in: finite-sum variance-reduced accelerated-gradient second-moment
  reduction before applying a gradient-gap bound
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
@[simp]
theorem importance_weighted_gradient_gap_quadratic_def
    {ι X E : Type*} [Fintype ι] [SeminormedAddCommGroup E]
    (q : ι → ℝ) (n : ℝ) (gradF : ι → X → E) (x y : X) :
    importance_weighted_gradient_gap_quadratic q n gradF x y =
      n⁻¹ *
        Finset.univ.sum (fun i : ι =>
          (1 / (n * q i)) * ‖gradF i x - gradF i y‖ ^ 2) := by
  rfl

/-- The quadratic aggregate is the weighted second moment of the
inverse-probability gradient-difference atom.

With nonzero sampling weights and normalizer, the weighted second moment of
`importance_weighted_gradient_difference q n gradF x y` is exactly the
gradient-gap quadratic with the two query points reversed; the reversal is
immaterial because the norm square is symmetric.

Layer: Model | Gap: Level 1 (importance-weighted gradient-difference second moment)
Proof: expand the estimator atom, use `norm_smul`, swap the subtraction inside
  the norm square, and cancel the nonzero real inverse factors.
Source: finite-sum stochastic variance-reduction estimators and Mathlib
  normed-group and real-field simplification APIs
Used in: finite-sum variance-reduced accelerated-gradient residual
  second-moment reduction to a gradient-gap budget
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem importance_weighted_gradient_gap_quadratic_eq_weighted_second_moment
    {ι X E : Type*} [Fintype ι] [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (q : ι → ℝ) (n : ℝ) (gradF : ι → X → E) (x y : X)
    (hq_ne : ∀ i, q i ≠ 0) (hn_ne : n ≠ 0) :
    importance_weighted_gradient_gap_quadratic q n gradF y x =
      Finset.univ.sum (fun i : ι =>
        q i * ‖importance_weighted_gradient_difference q n gradF x y i‖ ^ 2) := by
  classical
  unfold importance_weighted_gradient_gap_quadratic
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  let d : E := gradF i x - gradF i y
  have hq_ne_i : q i ≠ 0 := hq_ne i
  have hprod_ne : q i * n ≠ 0 := mul_ne_zero hq_ne_i hn_ne
  have hprod_swap_ne : n * q i ≠ 0 := mul_ne_zero hn_ne hq_ne_i
  have hnorm :
      ‖((q i * n)⁻¹) • d‖ ^ 2 =
        ((q i * n)⁻¹) ^ 2 * ‖d‖ ^ 2 := by
    rw [norm_smul]
    rw [Real.norm_eq_abs, mul_pow, sq_abs]
  have hsymm :
      ‖d‖ ^ 2 = ‖gradF i y - gradF i x‖ ^ 2 := by
    rw [← norm_neg d]
    simp [d, sub_eq_add_neg]
  rw [importance_weighted_gradient_difference_def, hnorm, hsymm]
  field_simp [hq_ne_i, hn_ne, hprod_ne, hprod_swap_ne]


-- Generalization plan (G0):
-- concept/name: finite importance-sampling smoothness constant; orig was
--   samplingLQ, renamed away from Lan's local `L_Q` notation and the
--   accelerated-gradient setup fields.
-- generality used: arbitrary finite nonempty component index type `ι`, real
--   normalizer `n`, component constants `Lcomp`, and sampling weights `q`; no
--   measure, independence, integrability, convexity, smoothness proof,
--   topology, norm, inner product, completeness, or finite-dimensional
--   hypotheses are used by the definition.
-- portable call pattern: nonuniform finite-sum SVRG, SARAH/SPIDER, SAGA, and
--   variance-reduced mirror-descent proofs instantiate the component
--   smoothness constants and sampling probabilities while reusing the same
--   max-ratio constant in estimator second-moment bounds.
-- counterargument checked: not merely paper-local traceability because
--   `n⁻¹ * max_i L_i / q_i` is the standard importance-sampling smoothness
--   constant; the risk of a one-line wrapper is outweighed by giving this
--   recurring max-ratio formula a stable Model-level name. It is not covered
--   by `finiteRunMaxValue`, which names only the finite maximum operator.
-- coverage search: searched CATALOG.md/SOptLib/Staging/Algorithms for
--   `finite importance smoothness`, `sampling LQ`, `max ratio`, `Lcomp / q`,
--   and `finiteRunMaxValue`; the only relevant full hit was
--   `SOptLib.finiteRunMaxValue`, a generic finite maximum wrapper. LeanSearch
--   for "finite maximum of ratios L_i divided by probabilities q_i smoothness
--   constant" returned unrelated smoothing and Lipschitz API results.
-- minimal hypotheses: all already minimal; the formula only requires a
--   nonempty finite index type so the finite maximum over component ratios is
--   defined.

/-- Finite importance-sampling smoothness constant from component constants and weights.

For a finite nonempty component family with normalizer `n`, component
smoothness constants `Lcomp`, and sampling weights `q`, this names
`n⁻¹ * max_i Lcomp i / q i`, the max-ratio constant used in nonuniform
finite-sum variance-reduction bounds.

Layer: Model | Concept: Oracle
Proof: (definitional construction; finite nonempty max-ratio smoothness constant)
Source: finite-sum stochastic variance-reduction smoothness constants and
  Mathlib finite-set maximum API
Used in: finite-sum variance-reduced accelerated-gradient sampling constant
  definition before specializing to smoothness-proportional probabilities
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/assumptions/6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
noncomputable def finiteImportanceSmoothnessConstant
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (n : ℝ) (Lcomp q : ι → ℝ) : ℝ :=
  n⁻¹ *
    finiteRunMaxValue
      (Finset.univ.image (fun i : ι => Lcomp i / q i))
      ((Finset.univ_nonempty : (Finset.univ : Finset ι).Nonempty).image
        (fun i : ι => Lcomp i / q i))

/-- The finite importance-sampling smoothness constant unfolds to
`n⁻¹ * max_i Lcomp i / q i`.

Layer: Model | Gap: Level 0 (finite importance-sampling smoothness constant unfolding)
Proof: by rfl after unfolding `finiteImportanceSmoothnessConstant`.
Source: finite-sum stochastic variance-reduction smoothness constants and
  Mathlib finite-set maximum API
Used in: finite-sum variance-reduced accelerated-gradient sampling constant
  definition before specializing to smoothness-proportional probabilities
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/assumptions/6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
@[simp]
theorem finiteImportanceSmoothnessConstant_def
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (n : ℝ) (Lcomp q : ι → ℝ) :
    finiteImportanceSmoothnessConstant n Lcomp q =
      n⁻¹ *
        finiteRunMaxValue
          (Finset.univ.image (fun i : ι => Lcomp i / q i))
          ((Finset.univ_nonempty : (Finset.univ : Finset ι).Nonempty).image
            (fun i : ι => Lcomp i / q i)) := by
  rfl

/-- Each component smoothness-to-sampling ratio is bounded by the normalized
finite importance-sampling smoothness constant.

This is the reusable max-ratio fact used after introducing
`finiteImportanceSmoothnessConstant`: multiplying the normalized constant by a
positive normalizer recovers the finite maximum, which bounds every indexed
ratio.

Layer: Model | Gap: Level 0 (finite importance-sampling max-ratio bound)
Proof: `le_finite_image_max` bounds each ratio by the finite image maximum;
  positivity of `n` cancels the normalizing factor.
Source: finite-sum stochastic variance-reduction smoothness constants and
  Mathlib finite-set maximum API
Used in: finite-sum variance-reduction estimator bounds with nonuniform
  importance sampling -/
theorem ratio_le_mul_finiteImportanceSmoothnessConstant
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {n : ℝ} (hn : 0 < n) (Lcomp q : ι → ℝ) (i : ι) :
    Lcomp i / q i ≤ n * finiteImportanceSmoothnessConstant n Lcomp q := by
  classical
  let values : Finset ℝ := Finset.univ.image (fun i : ι => Lcomp i / q i)
  let hvalues : values.Nonempty :=
    (Finset.univ_nonempty : (Finset.univ : Finset ι).Nonempty).image
      (fun i : ι => Lcomp i / q i)
  have hmax :
      Lcomp i / q i ≤ SOptLib.finiteRunMaxValue values hvalues := by
    rw [SOptLib.finiteRunMaxValue_eq_finset_max]
    exact SOptLib.le_finite_image_max
      (fun i : ι => Lcomp i / q i) i hvalues
  have hscale :
      n * finiteImportanceSmoothnessConstant n Lcomp q =
        SOptLib.finiteRunMaxValue values hvalues := by
    simp [finiteImportanceSmoothnessConstant, values, hn.ne']
  rw [hscale]
  exact hmax

/-- Nat-normalizer form of
`ratio_le_mul_finiteImportanceSmoothnessConstant`, matching finite-component
algorithm parameters before coercion to `ℝ`. -/
theorem ratio_le_nat_mul_finiteImportanceSmoothnessConstant
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {n : ℕ} (hn : 0 < n) (Lcomp q : ι → ℝ) (i : ι) :
    Lcomp i / q i ≤
      (n : ℝ) * finiteImportanceSmoothnessConstant (n : ℝ) Lcomp q :=
  ratio_le_mul_finiteImportanceSmoothnessConstant
    (by exact_mod_cast hn) Lcomp q i


-- Generalization plan (G0):
-- concept/name: smoothnessImportanceWeight_pos exposes strict positivity of
--   smoothness-proportional finite-sum importance weights; orig was
--   samplingWeight_pos, renamed away from Algorithm 5.7's local sampling
--   notation and stated about the existing Model object
--   `smoothnessImportanceWeight`.
-- generality used: arbitrary index type `ι`, real component smoothness
--   weights `Lcomp`, real count normalizer `n`, real smoothness scale `L`, and
--   a selected index `i`; no measure, filtration, convexity, oracle,
--   topology, vector-space, completeness, finite-type, or finite-dimensional
--   hypotheses are used.
-- portable call pattern: finite-sum SGD, SVRG/SARAH, variance-reduced
--   accelerated-gradient, and stochastic conditional-gradient proofs can
--   change the index type, component smoothness constants, and global
--   smoothness scale while calling the same positivity theorem before
--   inverse-probability weighting or PMF atom simplification.
-- counterargument checked: this is not paper-local traceability because it is
--   stated on the paper-free `SOptLib.smoothnessImportanceWeight` definition
--   already used by finite-sum stochastic-oracle models; it is not a pure
--   duplicate of Mathlib because it packages `div_pos` for the named
--   smoothness-importance weight API.
-- coverage search: searched CATALOG.md/project for
--   `smoothnessImportanceWeight`, `smoothness importance weight positive`,
--   and `samplingWeight_pos`; SOptLib has the weight definition,
--   nonnegativity, normalization, PMF construction, and inverse-ratio theorem,
--   but no strict-positivity theorem. LeanSearch for positive real quotient
--   returned Mathlib `div_pos_iff`, `div_pos_iff_of_pos_right`, and related
--   ordered-field quotient positivity facts, partial only because they do not
--   mention the named stochastic-optimization weight.
-- minimal hypotheses: reduced setup positivity and finite-sum total positivity
--   to the pointwise facts actually needed: `0 < Lcomp i`, `0 < n`, and
--   `0 < L`.

/-- A smoothness-proportional finite-sum importance weight is strictly positive
when the selected component smoothness, count normalizer, and smoothness scale
are strictly positive.

Layer: Model | Gap: Level 0 (finite smoothness-importance weight positivity)
Proof: unfold the named weight and apply Mathlib ordered-field positivity for
  a quotient with positive numerator and denominator.
Source: Mathlib ordered-field multiplication and division positivity APIs for
  finite-sum stochastic importance-sampling weights
Used in: variance-reduced finite-sum gradient proofs before
  inverse-probability weighting and component-sampling PMF atom rewrites
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem smoothnessImportanceWeight_pos
    {ι : Type*} {Lcomp : ι → ℝ} {n L : ℝ} {i : ι}
    (hcomp : 0 < Lcomp i) (hn : 0 < n) (hL : 0 < L) :
    0 < smoothnessImportanceWeight Lcomp n L i := by
  unfold smoothnessImportanceWeight
  exact div_pos hcomp (mul_pos hn hL)


-- Generalization plan (G0):
-- concept/name: smoothnessImportanceWeight_ratio_eq_total exposes the
--   inverse-ratio identity for smoothness-proportional finite-sum importance
--   weights; orig was theorem59_sampling_ratio_eq_totalSmoothness, renamed
--   away from theorem numbering and paper-local `totalSmoothness` wording.
-- generality used: arbitrary finite index type `ι`, real component smoothness
--   weights `Lcomp`, real count normalizer `n`, and average/global smoothness
--   scale `L`; no measure, filtration, convexity, oracle, topology,
--   vector-space, completeness, or finite-dimensional hypotheses are used.
-- portable call pattern: finite-sum SGD, variance-reduced gradient, and
--   stochastic mirror-descent proofs can vary the component index type,
--   component smoothness constants, and average-smoothness identity while
--   reusing the same pointwise max-ratio simplification.
-- counterargument checked: not paper-local traceability because the statement
--   is about the existing paper-free Model object
--   `SOptLib.smoothnessImportanceWeight`; not a pure Mathlib wrapper because
--   it combines the named smoothness-importance weight with the finite-sum
--   average-smoothness identity before applying the field cancellation.
-- coverage search: searched CATALOG.md/project for
--   `smoothnessImportanceWeight`, `ratio_eq_total`, `sampling_ratio_eq`, and
--   `finiteImportanceSmoothnessConstant`; SOptLib has the weight definition,
--   nonnegativity, normalization, PMF construction, and max-ratio constant,
--   but no theorem reducing `Lcomp i / smoothnessImportanceWeight ... i` to
--   total component smoothness. Mathlib has `div_div_cancel₀`, a partial
--   algebraic cancellation fact, but no stochastic-optimization named-weight
--   bridge.
-- minimal hypotheses: reduced setup positivity to the two algebraic facts
--   actually used: the count normalizer is nonzero and the selected component
--   smoothness weight is nonzero; nonzero total smoothness is not required.

/-- The inverse ratio of a component smoothness constant to its
smoothness-proportional importance weight is the total smoothness mass.

If `L = n⁻¹ * ∑ i, Lcomp i`, then dividing `Lcomp i` by the named weight
`Lcomp i / (n * L)` cancels the selected nonzero component constant and leaves
the finite total `∑ i, Lcomp i`.

Layer: Model | Gap: Level 0 (finite smoothness-importance inverse ratio)
Proof: rewrite `n * L` to the total component smoothness mass using the
  average identity and `n ≠ 0`, then apply Mathlib's `div_div_cancel₀`.
Source: Mathlib ordered-field division cancellation and finite-sum algebra
  APIs for finite-sum stochastic importance sampling
Used in: variance-reduced accelerated-gradient importance-sampling constant
  simplification from pointwise inverse sampling ratios to total smoothness
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem smoothnessImportanceWeight_ratio_eq_total
    {ι : Type*} [Fintype ι] (Lcomp : ι → ℝ) {n L : ℝ}
    (hn_ne : n ≠ 0)
    (hL_average : L = n⁻¹ * ∑ j, Lcomp j)
    {i : ι} (hcomp_ne : Lcomp i ≠ 0) :
    Lcomp i / smoothnessImportanceWeight Lcomp n L i = ∑ j, Lcomp j := by
  have hden_eq : n * L = ∑ j, Lcomp j := by
    rw [hL_average]
    calc
      n * (n⁻¹ * ∑ j, Lcomp j) = (n * n⁻¹) * ∑ j, Lcomp j := by
        ring
      _ = 1 * ∑ j, Lcomp j := by
        rw [mul_inv_cancel₀ hn_ne]
      _ = ∑ j, Lcomp j := by
        ring
  unfold smoothnessImportanceWeight
  rw [hden_eq]
  exact div_div_cancel₀ hcomp_ne


-- Generalization plan (G0):
-- concept/name: finiteImportanceSmoothnessConstant_eq_average_of_smoothness_proportional
--   exposes the standard collapse of the finite importance-sampling
--   smoothness constant to the average smoothness under smoothness-proportional
--   sampling; orig was theorem59LQ_eq_averageSmoothness, renamed away from the
--   theorem number and local `L_Q` notation.
-- generality used: arbitrary finite nonempty component index type `ι`, real
--   component constants `Lcomp`, real count normalizer `n`, and average
--   smoothness scale `L`; no measure, filtration, convexity, oracle,
--   topology, vector-space, completeness, or finite-dimensional hypotheses are
--   used.
-- portable call pattern: finite-sum SVRG/SAGA/SARAH/SPIDER and
--   variance-reduced mirror-gradient proofs can change the component index
--   type and component smoothness constants while reusing the same
--   simplification after selecting smoothness-proportional sampling weights.
-- counterargument checked: not paper-local traceability because the statement
--   is about the paper-free Model objects `finiteImportanceSmoothnessConstant`
--   and `smoothnessImportanceWeight`; not a pure wrapper because it combines
--   the named pointwise inverse-ratio identity with the finite maximum
--   collapse to remove the importance-sampling constant from downstream goals.
-- coverage search: searched project/catalog for
--   `finiteImportanceSmoothnessConstant`, `smoothness proportional average`,
--   `finite max singleton`, and `L_Q averageSmoothness`; existing SOptLib and
--   staged entries cover the max-ratio definition and pointwise ratio
--   cancellation, while Mathlib has generic finite-max/singleton facts such as
--   `Finset.max'_singleton`; no existing theorem states this named
--   smoothness-proportional specialization.
-- minimal hypotheses: reduced setup positivity to `n ≠ 0` and pointwise
--   nonzero component smoothness constants, exactly what the ratio-cancellation
--   step needs; positivity and total-sum nonzero assumptions are caller-side
--   sufficient conditions, not required here.

/-- The finite importance-sampling smoothness constant equals the average
smoothness under smoothness-proportional sampling.

If `L = n⁻¹ * ∑ i, Lcomp i` and the sampling weights are the named
smoothness-proportional weights `Lcomp i / (n * L)`, then every ratio
`Lcomp i / q i` is the same total smoothness mass. Hence the finite max-ratio
constant `n⁻¹ * max_i Lcomp i / q i` is exactly `L`.

Layer: Model | Gap: Level 0 (finite smoothness-importance average specialization)
Proof: use the named smoothness-importance inverse-ratio theorem to show the
  finite image of ratios is a singleton, unfold the finite max wrapper, and
  rewrite the average-smoothness identity.
Source: Mathlib finite-set maximum API and finite-sum algebra for finite-sum
  stochastic variance-reduction smoothness constants
Used in: variance-reduced accelerated-gradient replacement of the
  smoothness-proportional importance constant by the average component
  smoothness in stepsize and epoch-schedule goals
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem finiteImportanceSmoothnessConstant_eq_average_of_smoothness_proportional
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (Lcomp : ι → ℝ) {n L : ℝ}
    (hn_ne : n ≠ 0)
    (hL_average : L = n⁻¹ * ∑ i, Lcomp i)
    (hcomp_ne : ∀ i, Lcomp i ≠ 0) :
    finiteImportanceSmoothnessConstant n Lcomp
      (smoothnessImportanceWeight Lcomp n L) = L := by
  classical
  let total : ℝ := ∑ j, Lcomp j
  let values : Finset ℝ :=
    Finset.univ.image
      (fun i : ι => Lcomp i / smoothnessImportanceWeight Lcomp n L i)
  let hvalues : values.Nonempty :=
    (Finset.univ_nonempty : (Finset.univ : Finset ι).Nonempty).image
      (fun i : ι => Lcomp i / smoothnessImportanceWeight Lcomp n L i)
  have hratio :
      ∀ i : ι, Lcomp i / smoothnessImportanceWeight Lcomp n L i = total := by
    intro i
    simpa [total] using
      (smoothnessImportanceWeight_ratio_eq_total
        (Lcomp := Lcomp) (n := n) (L := L)
        hn_ne hL_average (i := i) (hcomp_ne i))
  have hvalues_eq : values = {total} := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
      simp [hratio i]
    · intro hx
      have hx' : x = total := by
        simpa using hx
      subst x
      refine Finset.mem_image.mpr ?_
      exact ⟨Classical.choice ‹Nonempty ι›, by simp, by simp [hratio]⟩
  have hmax' : values.max' hvalues = total := by
    have hmem : values.max' hvalues ∈ values := Finset.max'_mem values hvalues
    simpa only [hvalues_eq, Finset.mem_singleton] using hmem
  have hmax : finiteRunMaxValue values hvalues = total := by
    simpa [finiteRunMaxValue] using hmax'
  unfold finiteImportanceSmoothnessConstant
  change n⁻¹ * finiteRunMaxValue values hvalues = L
  rw [hmax]
  exact hL_average.symm


-- Generalization plan (G0):
-- concept/name: pointwise oracle-estimator reconstruction from its centered
--   estimator error; orig was
--   `varianceReducedGradientOn_eq_fullGradient_add_estimatorResidual`, renamed
--   away from Algorithm 5.7 and stated about the existing Model object
--   `oracleEstimatorError`.
-- generality used: arbitrary query type `X`, additive commutative group `E`,
--   deterministic target field `target : X -> E`, estimator value `G : E`,
--   and query `x : X`; no measure, filtration, convexity, smoothness,
--   topology, norm, inner product, probability, or finite-dimensional
--   hypotheses are used.
-- portable call pattern: finite-sum variance-reduced gradient proofs,
--   stochastic-oracle one-step bounds, and conditional-gradient Wolfe-gap
--   estimates can rewrite a sampled estimator value as its deterministic
--   target plus the named centered error while changing only the target field,
--   estimator value, and query.
-- counterargument checked: the proof is short, but it is not paper-local
--   traceability because it exposes the reconstruction API for the existing
--   paper-free `oracleEstimatorError` definition; Mathlib has additive-group
--   cancellation lemmas, but not this theorem for SOptLib's named oracle error.
-- coverage search: searched CATALOG.md/project for `oracleEstimatorError`,
--   `estimatorResidual`, `target add`, and
--   `varianceReducedGradientOn_eq_fullGradient_add_estimatorResidual`; SOptLib
--   contains `oracleEstimatorError`, its unfolding theorem, measurability, and
--   process residual APIs, but no pointwise reconstruction theorem. Mathlib
--   cancellation lemmas such as `add_sub_cancel_right` are partial only because
--   they do not mention the named stochastic-oracle residual.
-- minimal hypotheses: reduced the Euclidean-space and finite-sum setup to the
--   `AddCommGroup` structure needed to rearrange `G = target x + (G - target x)`.

/-- An estimator value is its target plus its centered oracle-estimator error.

For a deterministic target field `target`, the named residual
`oracleEstimatorError target G x` reconstructs the estimator value `G` by
adding the residual back to the target at the query `x`.

Layer: Model | Gap: Level 0 (pointwise oracle-estimator reconstruction)
Proof: unfold the named estimator error and use additive commutative-group
  cancellation to rearrange `target x + (G - target x)` back to `G`.
Source: Mathlib additive commutative-group subtraction and cancellation APIs
Used in: variance-reduced finite-sum gradient estimator decomposition before
  unbiasedness and second-moment residual bounds
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem eq_target_add_oracleEstimatorError
    {X E : Type*} [AddCommGroup E] (target : X → E) (G : E) (x : X) :
    G = target x + oracleEstimatorError target G x := by
  simp [oracleEstimatorError]

/-- A smoothness-proportional finite-sum importance PMF has strictly positive
real atom mass at any component with positive smoothness.

For the canonical PMF built from `smoothnessImportanceWeight`, component
nonnegativity and one strictly positive selected component make the total
smoothness mass positive; the average identity then makes `L` positive, so the
corresponding PMF atom has positive `toReal`.

Layer: Model | Gap: Level 0 (finite smoothness-importance PMF atom positivity)
Proof: derive positivity of the average smoothness scale from the finite sum,
  apply strict positivity of the named smoothness-importance weight, then use
  the smoothness-importance PMF atom formula and `ENNReal.toReal_ofReal`.
Source: Mathlib finite sums, ordered-field quotient positivity, probability
  mass functions, and ENNReal real-conversion APIs
Used in: finite-sum stochastic oracle proofs before inverse-probability
  denominator cancellation under smoothness-proportional component sampling
Book citation: book/FOML/NonconvexVarianceReducedMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex variance-reduced mirror descent -/
theorem smoothnessImportancePMF_atom_toReal_pos
    {ι : Type*} [Fintype ι] (Lcomp : ι → ℝ) {n L : ℝ}
    (hcomp_nonneg : ∀ i, 0 ≤ Lcomp i)
    (hn_pos : 0 < n)
    (hL_average : L = n⁻¹ * ∑ i, Lcomp i)
    (hsum_ne : (∑ i, Lcomp i) ≠ 0)
    {i : ι} (hcomp_pos : 0 < Lcomp i) :
    0 < (smoothnessImportancePMF Lcomp hcomp_nonneg hn_pos hL_average hsum_ne i).toReal := by
  have hsum_pos : 0 < ∑ j : ι, Lcomp j := by
    exact Finset.sum_pos' (fun j _ => hcomp_nonneg j) ⟨i, Finset.mem_univ i, hcomp_pos⟩
  have hL_pos : 0 < L := by
    rw [hL_average]
    exact mul_pos (inv_pos.mpr hn_pos) hsum_pos
  have hweight_pos : 0 < smoothnessImportanceWeight Lcomp n L i :=
    smoothnessImportanceWeight_pos hcomp_pos hn_pos hL_pos
  rw [smoothnessImportancePMF_apply]
  rw [ENNReal.toReal_ofReal (le_of_lt hweight_pos)]
  exact hweight_pos

/-- Mini-batch recursive control-variate estimator with importance-weighted component
gradient differences.

For component weights `q`, normalizer `normalizer`, component-gradient family
`gradF`, sampled component map `sample`, current point `x`, previous point
`xPrev`, and previous estimator `GPrev`, this is the finite mini-batch average
of inverse-probability weighted gradient differences plus `GPrev`.

Layer: Model | Concept: Oracle
Proof: (definitional construction; finite mini-batch average of inverse-probability
  gradient-difference atoms added to a previous estimator)
Source: finite-sum stochastic variance-reduction estimators and Mathlib finite-sum
  scalar-action primitives
Used in: nonconvex variance-reduced mirror descent recursive estimator branch before
  estimator-error residual centering
Book citation: book/FOML/NonconvexVarianceReducedMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  nonconvex variance-reduced mirror descent -/
noncomputable def miniBatchRecursiveControlVariateEstimator
    {ι ρ X E : Type*} [Fintype ρ] [AddCommMonoid E] [Sub E] [Module ℝ E]
    (q : ι → ℝ) (normalizer : ℝ) (gradF : ι → X → E) (sample : ρ → ι)
    (x xPrev : X) (GPrev : E) : E :=
  finiteUniformAverage
      (fun r : ρ =>
        importance_weighted_gradient_difference q normalizer gradF x xPrev (sample r)) +
    GPrev

/-- The mini-batch recursive control-variate estimator unfolds to the average of
importance-weighted component-gradient differences plus the previous estimator.

Layer: Model | Gap: Level 0 (mini-batch recursive control-variate estimator formula)
Proof: by rfl after unfolding `miniBatchRecursiveControlVariateEstimator`.
Source: finite-sum stochastic variance-reduction estimators and Mathlib finite-sum
  scalar-action primitives
Used in: nonconvex variance-reduced mirror descent recursive estimator branch before
  estimator-error residual centering
Book citation: book/FOML/NonconvexVarianceReducedMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  nonconvex variance-reduced mirror descent -/
@[simp]
theorem miniBatchRecursiveControlVariateEstimator_def
    {ι ρ X E : Type*} [Fintype ρ] [AddCommMonoid E] [Sub E] [Module ℝ E]
    (q : ι → ℝ) (normalizer : ℝ) (gradF : ι → X → E) (sample : ρ → ι)
    (x xPrev : X) (GPrev : E) :
    miniBatchRecursiveControlVariateEstimator q normalizer gradF sample x xPrev GPrev =
      finiteUniformAverage
          (fun r : ρ =>
            importance_weighted_gradient_difference q normalizer gradF x xPrev (sample r)) +
        GPrev := by
  rfl

end SOptLib

namespace PMF

/-- The canonical probability mass function on the support subtype of a finite PMF.

Its atom at a support element `a` is the original mass `p a.1`, so algorithms
can sample from the nonzero support without adding a full-support assumption on
the original index type.

Layer: Model | Concept: Probability mass function support restriction
Proof: (definitional construction; finite PMF over the support subtype with the inherited atom weights)
Source: Mathlib ProbabilityMassFunction finite construction and support APIs
Used in: random primal-dual gradient support-valued block sampling for inverse-probability coordinate updates
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, random primal-dual gradient -/
noncomputable def supportSubtypePMF {α : Type*} [Fintype α] (p : PMF α) : PMF p.support := by
  classical
  letI : Fintype p.support :=
    Set.Finite.fintype (Set.finite_univ.subset (by intro a _; exact Set.mem_univ a))
  refine PMF.ofFintype (fun a : p.support => p a.1) ?_
  have hsupport : (∑ a : p.support, p a.1) = (∑ a : α, p a) := by
    have hsub :
        (∑ a : p.support, p a.1) =
          ∑ a ∈ (Finset.univ : Finset α) with a ∈ p.support, p a := by
      simpa using
        (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset α))
          (f := fun a : α => p a) (p := fun a : α => a ∈ p.support))
    have hmem :
        (∑ a ∈ (Finset.univ : Finset α) with a ∈ p.support, p a) =
          ∑ a ∈ (Finset.univ : Finset α) with p a ≠ 0, p a := by
      apply Finset.sum_congr
      · ext a
        simp [PMF.mem_support_iff]
      · intro a _
        rfl
    have hnonzero :
        (∑ a ∈ (Finset.univ : Finset α) with p a ≠ 0, p a) =
          (∑ a : α, p a) := by
      simpa using
        (Finset.sum_filter_ne_zero (s := (Finset.univ : Finset α))
          (f := fun a : α => p a))
    exact hsub.trans (hmem.trans hnonzero)
  rw [hsupport]
  simpa using p.tsum_coe

/-- The support-subtype PMF has exactly the original PMF's atom at each support element.

Layer: Model | Gap: Level 0 (support-subtype PMF atom formula)
Proof: unfold `PMF.supportSubtypePMF` and reduce the finite-PMF constructor with `PMF.ofFintype_apply`.
Source: Mathlib ProbabilityMassFunction finite construction and support APIs
Used in: random primal-dual gradient projection of support-valued block laws to original singleton probabilities
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, random primal-dual gradient -/
@[simp]
theorem supportSubtypePMF_apply {α : Type*} [Fintype α] (p : PMF α) (a : p.support) :
    supportSubtypePMF p a = p a.1 := by
  classical
  unfold supportSubtypePMF
  simp

/-- Mapping the support-subtype PMF back along the subtype coercion recovers the original PMF.

Layer: Model | Gap: Level 0 (support-subtype PMF projection)
Proof: extensionality and the atom formula for `PMF.map`
Source: Mathlib ProbabilityMassFunction map and support APIs
Used in: stochastic-optimization proofs that sample on positive support but state laws on the ambient index type -/
@[simp]
theorem supportSubtypePMF_map_val {α : Type*} [Fintype α] (p : PMF α) :
    (supportSubtypePMF p).map Subtype.val = p := by
  classical
  ext a
  rw [PMF.map_apply]
  by_cases ha : a ∈ p.support
  · let a' : p.support := ⟨a, ha⟩
    calc
      (∑' b : p.support, if a = b.1 then supportSubtypePMF p b else 0) =
          supportSubtypePMF p a' := by
        refine (tsum_eq_single a' ?_).trans ?_
        · intro b hb
          have hne : a ≠ b.1 := by
            intro h
            exact hb (Subtype.ext h.symm)
          simp [hne]
        · simp [a']
      _ = p a := by simp [a']
  · have hzero : p a = 0 := (p.apply_eq_zero_iff a).2 ha
    calc
      (∑' b : p.support, if a = b.1 then supportSubtypePMF p b else 0) = 0 := by
        rw [ENNReal.tsum_eq_zero]
        intro b
        have hne : a ≠ b.1 := by
          intro h
          exact ha (h ▸ b.2)
        simp [hne]
      _ = p a := hzero.symm

/-- The measure induced by restricting a PMF to its positive-support subtype.

For a PMF `p`, `supportSubtypeLaw p` is the canonical probability measure on
`p.support` obtained from the inherited support-subtype PMF.

Layer: Model | Concept: Probability mass function support restriction
Proof: (definitional construction; support-subtype PMF followed by `PMF.toMeasure`)
Source: Mathlib probability mass functions, support subtypes, and measures
  induced by discrete laws
Used in: support-valued coordinate sampling for inverse-probability stochastic
  coordinate updates
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
noncomputable def supportSubtypeLaw {α : Type*} [Fintype α] [MeasurableSpace α] (p : PMF α) :
    Measure p.support :=
  (supportSubtypePMF p).toMeasure

/-- Definitional formula for the support-subtype law.

Layer: Model | Gap: Level 0 (support-subtype law formula)
Proof: by rfl after unfolding `PMF.supportSubtypeLaw`
Source: Mathlib probability mass functions and measure construction from PMFs
Used in: support-valued coordinate sampling law construction
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
@[simp]
theorem supportSubtypeLaw_def {α : Type*} [Fintype α] [MeasurableSpace α] (p : PMF α) :
    supportSubtypeLaw p = (supportSubtypePMF p).toMeasure := by
  rfl

/-- The support-subtype law is a probability measure.

Layer: Model | Gap: Level 0 (support-subtype law probability measure)
Proof: unfold the support-subtype law and use the probability-measure instance
  for the measure induced by a PMF.
Source: Mathlib probability mass functions and probability-measure instances
Used in: support-valued coordinate sampling probability-space construction
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
@[instance]
theorem supportSubtypeLaw_isProbabilityMeasure
    {α : Type*} [Fintype α] [MeasurableSpace α] (p : PMF α) :
    IsProbabilityMeasure (supportSubtypeLaw p) := by
  unfold supportSubtypeLaw
  infer_instance

/-- The support-subtype law assigns a support singleton its inherited PMF mass.

Layer: Model | Gap: Level 0 (support-subtype law singleton mass)
Proof: unfold the support-subtype law, apply `PMF.toMeasure_apply_singleton`,
  and reduce the support-subtype PMF atom by its definitional equation.
Source: Mathlib probability mass functions, singleton measurable sets, and
  measures induced by discrete laws
Used in: projection of support-valued coordinate laws to original singleton
  sampling probabilities
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
@[simp]
theorem supportSubtypeLaw_singleton
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : PMF α) (a : p.support) :
    supportSubtypeLaw p ({a} : Set p.support) = p a.1 := by
  rw [supportSubtypeLaw_def, PMF.toMeasure_apply_singleton]
  · simp
  · exact measurableSet_singleton a

/-- Projecting the support-subtype law back to the ambient type recovers the
original PMF law.

Layer: Model | Gap: Level 0 (support-subtype law projection)
Proof: apply Mathlib's `PMF.toMeasure_map` to the subtype coercion, then use the
  PMF-level projection identity for `PMF.supportSubtypePMF`.
Source: Mathlib probability mass function map/toMeasure compatibility and
  support-subtype projection APIs
Used in: coordinate-sampling proofs that sample on positive support but state
  singleton probabilities on the original index type
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
@[simp]
theorem supportSubtypeLaw_map_val {α : Type*} [Fintype α] [MeasurableSpace α] (p : PMF α) :
    Measure.map Subtype.val (supportSubtypeLaw p) = p.toMeasure := by
  calc
    Measure.map Subtype.val (supportSubtypeLaw p)
        = Measure.map Subtype.val (supportSubtypePMF p).toMeasure := by
          rfl
    _ = ((supportSubtypePMF p).map Subtype.val).toMeasure := by
          simpa using
            (PMF.toMeasure_map (p := supportSubtypePMF p) (f := Subtype.val)
              measurable_subtype_coe)
    _ = p.toMeasure := by
          rw [supportSubtypePMF_map_val]

/-- Projecting the support-subtype law back to the ambient PMF gives the original
mass on every singleton.

If samples are drawn from the positive-support subtype of a PMF and then coerced
back to the original index type, the probability of the ambient singleton `{a}`
is exactly the original PMF mass at `a`.

Layer: Model | Gap: Level 0 (support-subtype law projected singleton mass)
Proof: rewrite the projected support-subtype law by `PMF.supportSubtypeLaw_map_val`,
  then evaluate the resulting PMF-induced measure on a singleton by
  `PMF.toMeasure_apply_singleton`.
Source: Mathlib probability mass functions, map/toMeasure compatibility, and
  singleton evaluation of discrete laws
Used in: support-valued coordinate sampling projected back to ambient block
  singleton probabilities for inverse-probability stochastic updates
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
@[simp]
theorem supportSubtypeLaw_map_val_singleton
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : PMF α) (a : α) :
    Measure.map (fun x : p.support => x.1) (supportSubtypeLaw p) ({a} : Set α) =
      p a := by
  rw [supportSubtypeLaw_map_val]
  exact PMF.toMeasure_apply_singleton p a (measurableSet_singleton a)

end PMF

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: inverse-probability coordinate prediction; orig was dualPrediction.
-- generality used: arbitrary coordinate type with decidable equality, an additive commutative group with real module structure, a real coordinate probability function, previous/next coordinate vectors, and one sampled coordinate; no measure, filtration, convexity, smoothness, topology, finite-dimensionality, or positivity hypothesis is used to form the totalized prediction.
-- portable call pattern: randomized coordinate, block-oracle, variance-reduced memory, and primal-dual algorithms form a full vector by lifting one sampled coordinate increment with an inverse sampling probability before unbiasedness or moment calculations; the probability law, previous/next vectors, and sampled index change while the selected/unchanged coordinate equations stay the same.
-- counterargument checked: not paper-local traceability because the object is the standard one-coordinate inverse-probability lift used before expectation identities; not covered by `Function.update` alone because the selected value has the named probability-weighted increment formula, and not covered by `sampledAffineMemoryRefresh`, whose selected value is a different affine memory blend.
-- coverage search: searched catalog/project tokens "inverse probability coordinate prediction", "sampled affine memory refresh", "coordinate replacement", and "weighted block lift"; LeanSearch query "function updated at one coordinate inverse probability scaled increment previous next sampled coordinate" returned `Function.update` and update lemmas only. Closest SOptLib hits were `sampledAffineMemoryRefresh` and `integral_weighted_block_lift_coord_eq_self`; both are partial and structurally different.
-- minimal hypotheses: dropped the paper setup, carrier subtypes, PMF support, finite-dimensional Hilbert assumptions, and denominator certificates; the construction is total using the field inverse on the supplied real probability.

/-- The inverse-probability lift of one sampled coordinate increment.

At the sampled coordinate, the prediction is the previous value plus the
increment from `prev` to `next` scaled by the inverse sampling probability.
Every other coordinate keeps the previous value.

Layer: Model | Concept: Iterates
Proof: (definitional construction; one-coordinate update by an inverse-probability
  scaled increment)
Source: Mathlib coordinate-update and real module scalar APIs
Used in: random primal-dual gradient sampled dual prediction before block
  unbiasedness and second-moment identities
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
noncomputable def inverseProbabilityCoordinatePrediction
    {ι E : Type*} [DecidableEq ι] [AddCommGroup E] [Module ℝ E]
    (prob : ι → ℝ) (prev next : ι → E) (sampled : ι) : ι → E :=
  Function.update prev sampled
    (((prob sampled)⁻¹ • (next sampled - prev sampled)) + prev sampled)

/-- The inverse-probability coordinate prediction unfolds to its selected and
non-selected coordinate cases.

Layer: Model | Gap: Level 0 (inverse-probability coordinate prediction unfolding)
Proof: unfold `inverseProbabilityCoordinatePrediction`, split on the queried
  coordinate, and simplify `Function.update`.
Source: Mathlib `Function.update` and real module scalar APIs
Used in: random primal-dual gradient sampled dual prediction case split
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
@[simp]
theorem inverseProbabilityCoordinatePrediction_def
    {ι E : Type*} [DecidableEq ι] [AddCommGroup E] [Module ℝ E]
    (prob : ι → ℝ) (prev next : ι → E) (sampled i : ι) :
    inverseProbabilityCoordinatePrediction prob prev next sampled i =
      if i = sampled then
        (prob i)⁻¹ • (next i - prev i) + prev i
      else
        prev i := by
  by_cases h : i = sampled
  · subst i
    simp [inverseProbabilityCoordinatePrediction]
  · simp [inverseProbabilityCoordinatePrediction, h]

/-- The sampled coordinate of an inverse-probability coordinate prediction is
the inverse-probability scaled sampled increment added to the previous value.

Layer: Model | Gap: Level 0 (inverse-probability selected-coordinate formula)
Proof: unfold `inverseProbabilityCoordinatePrediction` and simplify the selected
  coordinate of `Function.update`.
Source: Mathlib `Function.update_self` and real module scalar APIs
Used in: random primal-dual gradient sampled dual prediction selected-block
  equation
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
@[simp]
theorem inverseProbabilityCoordinatePrediction_sampled
    {ι E : Type*} [DecidableEq ι] [AddCommGroup E] [Module ℝ E]
    (prob : ι → ℝ) (prev next : ι → E) (sampled : ι) :
    inverseProbabilityCoordinatePrediction prob prev next sampled sampled =
      (prob sampled)⁻¹ • (next sampled - prev sampled) + prev sampled := by
  simp [inverseProbabilityCoordinatePrediction]

/-- Non-sampled coordinates of an inverse-probability coordinate prediction keep
their previous value.

Layer: Model | Gap: Level 0 (inverse-probability non-selected-coordinate preservation)
Proof: unfold `inverseProbabilityCoordinatePrediction` and simplify
  `Function.update` at a coordinate different from the sampled one.
Source: Mathlib `Function.update_of_ne`
Used in: random primal-dual gradient sampled dual prediction off-block equation
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem inverseProbabilityCoordinatePrediction_of_ne
    {ι E : Type*} [DecidableEq ι] [AddCommGroup E] [Module ℝ E]
    (prob : ι → ℝ) (prev next : ι → E) {sampled i : ι}
    (hi : i ≠ sampled) :
    inverseProbabilityCoordinatePrediction prob prev next sampled i = prev i := by
  simp [inverseProbabilityCoordinatePrediction, hi]

-- Generalization plan (G0):
-- concept/name: inverse-probability coordinate prediction residual branch; orig was yTildeIter_sub_yHatIter_branch.
-- generality used: arbitrary coordinate type with decidable equality and an additive commutative group with real module structure; no measure, filtration, convexity, smoothness, topology, probability normalization, or finite-dimensional assumptions are used.
-- portable call pattern: randomized coordinate primal-dual, block-oracle, and variance-reduced memory proofs compare the inverse-probability predicted full vector with the candidate full vector before proving unbiasedness or variance identities; only the probability weights, previous vector, candidate vector, sampled coordinate, and queried coordinate change.
-- counterargument checked: not a paper-local traceability lemma because it is the pointwise algebraic residual of the already-staged inverse-probability coordinate prediction; not a pure wrapper around `Function.update` because the conclusion normalizes the selected residual to `(p_i⁻¹ - 1) • (cand_i - prev_i)` and the off-selected residual to `-(cand_i - prev_i)`.
-- coverage search: searched project/SOptLib tokens "inverseProbabilityCoordinatePrediction", "inverse probability coordinate prediction residual", "weighted block lift", and LeanSearch query "inverse probability coordinate update residual sampled coordinate vector subtraction"; Mathlib hits were only `VSub`/Pi subtraction APIs, and the closest SOptLib hit `integral_weighted_block_lift_coord_eq_self` is an expectation reconstruction theorem, not this pointwise branch identity.
-- minimal hypotheses: replaced the paper setup, carrier subtypes, positive-support sample, denominator certificates, Hilbert-space structure, complete space, and finite-dimensional assumptions by the module laws actually needed for the coordinate residual algebra.

/-- The residual of an inverse-probability coordinate prediction against the
candidate vector splits into sampled and non-sampled coordinate branches.

At the sampled coordinate the residual is `(p_i⁻¹ - 1)` times the candidate
increment. At any other coordinate the prediction kept the previous value, so
the residual is the negative candidate increment.

Layer: Model | Gap: Level 0 (inverse-probability coordinate prediction residual branch)
Proof: unfold the inverse-probability prediction through its staged branch
  equation, split on whether the queried coordinate was sampled, and normalize
  the resulting module expression.
Source: Mathlib `Function.update` coordinate-update API and real module algebra
Used in: random primal-dual gradient sampled dual-prediction residual before
  coordinate unbiasedness and variance calculations
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem inverseProbabilityCoordinatePrediction_sub_candidate_branch
    {ι E : Type*} [DecidableEq ι] [AddCommGroup E] [Module ℝ E]
    (prob : ι → ℝ) (prev cand : ι → E) (sampled i : ι) :
    inverseProbabilityCoordinatePrediction prob prev cand sampled i - cand i =
      if i = sampled then
        ((prob i)⁻¹ - 1) • (cand i - prev i)
      else
        -(cand i - prev i) := by
  by_cases hsample : i = sampled
  · subst sampled
    simp
    module
  · simp [hsample]

end SOptLib


-- Merged from Staging/finiteComponentInitialGradientSecondMomentBound.lean
open scoped BigOperators

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: finite-component initial-gradient second-moment bound; orig was
--   `InitialGradientBound`, renamed away from the paper-local setup field while
--   retaining the standard finite-sum initialization assumption
--   `card⁻¹ * ∑ᵢ dualNorm (gradF i x0)^2 = sigma0^2`.
-- generality used: finite component index type, arbitrary query type, arbitrary
--   gradient codomain, real-valued dual-norm functional, component-gradient
--   family, initial point, and real variance scale; no measure, convexity,
--   smoothness, topology, inner-product, completeness, or finite-dimensional
--   hypotheses are used by the definitional predicate.
-- portable call pattern: finite-sum stochastic, table-gradient, randomized
--   block, and variance-reduced methods call the same initialization predicate
--   when converting an averaged squared initial component-gradient sum into a
--   named scale `sigma0^2`; the index type, gradient family, initial point, and
--   dual norm vary while the conclusion shape stays fixed.
-- counterargument checked: the body is a small formula, but it is not merely a
--   source-traceability wrapper: it packages a recurring finite-sum
--   second-moment initialization assumption, including the nonnegative scale
--   convention needed by later square-root and budget arguments.
-- coverage search: searched `InitialGradientBound`, `finite component initial
--   gradient second moment`, `second moment dual norm finite average component
--   gradient`, SOptLib catalog second-moment entries, and Mathlib LeanSearch for
--   finite averages of squared norms; closest hits were finite-average algebra,
--   oracle second-moment integral bounds, and variance APIs, with no full
--   predicate covering this deterministic finite-component initialization
--   assumption.
-- minimal hypotheses: all setup fields are replaced by explicit parameters;
--   no positivity or nonemptiness of the component type is required to state
--   the totalized finite-average formula.

/-- Finite-average initial component-gradient second-moment bound.

The predicate records that the normalized finite sum of squared dual norms of
component gradients at `x0` is the scale `sigma0 ^ 2`, and that the chosen scale
`sigma0` is nonnegative.

Layer: Model | Concept: Oracle
Proof: (definitional construction; deterministic finite-component squared
  dual-norm second-moment initialization predicate)
Source: finite-sum stochastic-optimization initialization assumptions and
  Mathlib finite-sum arithmetic over real scalars
Used in: randomized gradient extrapolation conversion of the initial stale
  gradient finite sum into the named variance scale
Book citation: book/FOML/RandomGradientExtrapolation.json#/assumptions/11/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
def finiteComponentInitialGradientSecondMomentBound
    {ι X E : Type*} [Fintype ι]
    (dualNorm : E → ℝ) (gradF : ι → X → E) (x0 : X) (sigma0 : ℝ) : Prop :=
  (Fintype.card ι : ℝ)⁻¹ *
      Finset.sum Finset.univ (fun i : ι => dualNorm (gradF i x0) ^ 2) =
        sigma0 ^ 2 ∧
    0 ≤ sigma0

/-- The finite-component initial-gradient second-moment bound unfolds to the
normalized squared-dual-norm formula and nonnegative scale convention.

Layer: Model | Gap: Level 0 (finite-component initial-gradient moment unfolding)
Proof: by rfl after unfolding `finiteComponentInitialGradientSecondMomentBound`.
Source: finite-sum stochastic-optimization initialization assumptions and
  Mathlib finite-sum arithmetic over real scalars
Used in: randomized gradient extrapolation conversion of the initial stale
  gradient finite sum into the named variance scale
Book citation: book/FOML/RandomGradientExtrapolation.json#/assumptions/11/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
@[simp]
theorem finiteComponentInitialGradientSecondMomentBound_def
    {ι X E : Type*} [Fintype ι]
    (dualNorm : E → ℝ) (gradF : ι → X → E) (x0 : X) (sigma0 : ℝ) :
    finiteComponentInitialGradientSecondMomentBound dualNorm gradF x0 sigma0 ↔
      (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ (fun i : ι => dualNorm (gradF i x0) ^ 2) =
            sigma0 ^ 2 ∧
        0 ≤ sigma0 := by
  rfl

end SOptLib

-- Phase 4 merged from focused staging declarations.

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: adaptive centered oracle residual process; orig was
--   `AdaptiveOracleProcess`, renamed to `AdaptiveCenteredOracleProcess` to
--   expose the paper-free time-indexed residual process contract.
-- generality used: arbitrary measurable sample space, arbitrary time index,
--   arbitrary real Banach-valued residuals with a measurable-space structure,
--   arbitrary base measure, past/current sigma-algebras, residual process, and
--   time-dependent variance budget; no objective, gradient, convexity,
--   smoothness, independence, probability, or finite-dimensional assumption is
--   used by the predicate itself.
-- portable call pattern: adaptive stochastic gradient, mirror-descent,
--   variance-reduction, and stochastic approximation proofs can supply their
--   residual process, strict-past and current-observation sigma-algebras, base
--   law, and variance budget while keeping the conditional centering,
--   second-moment, and observability conclusions unchanged.
-- counterargument checked: not merely paper traceability because downstream
--   martingale-noise proofs repeatedly pass exactly this three-part process
--   boundary; not a pure wrapper over Mathlib because Mathlib has no
--   stochastic-optimization residual-process predicate bundling these fields.
-- coverage search: searched `conditional expectation equality mean zero
--   process second moment measurable`, `adaptive centered residual process
--   conditional mean zero second moment observability`, `expectationLe squared
--   norm second moment bound`, and CATALOG/SOptLib/Staging for centered
--   residual process terms; relevant hits were
--   `SOptLib.ConditionalExpectation.conditionalExpectationEq`,
--   `SOptLib.expectationLe`, and several mini-batch second-moment theorems,
--   none of which packages this process-level contract.
-- minimal hypotheses: kept only the typeclasses required by
--   `conditionalExpectationEq`, squared norms, and `Measurable`; probability,
--   Hilbert, finite-dimensional, oracle-kernel, and objective assumptions were
--   dropped.

/-- Time-indexed centered residual process with conditional mean zero,
second-moment control, and current-observation measurability.

For each time `t`, the residual `delta t` has conditional expectation zero with
respect to the past sigma-algebra, its squared norm has expectation at most
`varianceBound t`, and the residual is observable at the current sigma-algebra.

Layer: Model | Concept: Adaptive centered oracle process
Proof: (definitional construction; bundles conditional centering,
  second-moment bounds, and current-observation measurability for a residual
  process)
Source: Mathlib conditional expectation, Bochner expectation, norm, and
  measurability APIs as wrapped by SOptLib conditional-expectation and
  expectation-bound predicates
Used in: stochastic accelerated-gradient martingale-noise setup where generated
  oracle errors are projected into conditional centering, variance, and
  observability facts
Book citation: book/FOML/NonconvexStochasticAcceleratedGD.json#/assumptions/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic accelerated gradient descent
  (Algorithm 6.4 and Theorem 6.12) -/
def AdaptiveCenteredOracleProcess
    {Ω T E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
    (μ : Measure Ω) (past current : T → MeasurableSpace Ω)
    (delta : T → Ω → E) (varianceBound : T → ℝ) : Prop :=
  (∀ t : T,
    ConditionalExpectation.conditionalExpectationEq μ (past t) (delta t) (0 : Ω → E)) ∧
  (∀ t : T, expectationLe μ (fun ω => ‖delta t ω‖ ^ 2) (varianceBound t)) ∧
  (∀ t : T, Measurable[current t] (delta t))

/-- The adaptive centered oracle process predicate unfolds to conditional
centering, second-moment control, and current-observation measurability at every
time.

Layer: Model | Gap: Level 0 (adaptive centered residual process unfolding)
Proof: by rfl after unfolding `AdaptiveCenteredOracleProcess`.
Source: Mathlib conditional expectation, Bochner expectation, norm, and
  measurability APIs as wrapped by SOptLib conditional-expectation and
  expectation-bound predicates
Used in: exposing stochastic accelerated-gradient generated oracle errors as
  separate martingale-noise hypotheses
Book citation: book/FOML/NonconvexStochasticAcceleratedGD.json#/assumptions/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic accelerated gradient descent
  (Algorithm 6.4 and Theorem 6.12) -/
@[simp]
theorem AdaptiveCenteredOracleProcess_def
    {Ω T E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
    (μ : Measure Ω) (past current : T → MeasurableSpace Ω)
    (delta : T → Ω → E) (varianceBound : T → ℝ) :
    AdaptiveCenteredOracleProcess μ past current delta varianceBound ↔
      (∀ t : T,
        ConditionalExpectation.conditionalExpectationEq μ (past t) (delta t)
          (0 : Ω → E)) ∧
      (∀ t : T, expectationLe μ (fun ω => ‖delta t ω‖ ^ 2) (varianceBound t)) ∧
      (∀ t : T, Measurable[current t] (delta t)) := by
  rfl

end SOptLib

-- Phase 4 batch 1 merge from Staging/splitBlockOracleRunSample.lean (law)
namespace SOptLib

/-- The canonical split block/oracle run law.

For a block-index marginal `blockLaw` and an oracle-sample marginal
`oracleLaw`, this is the product of the iid block stream law and the iid oracle
stream law on `split_block_oracle_run_sample I S`.

Layer: Model | Concept: split block/oracle run law
Proof: (definitional construction; product of two iid Nat-indexed stream laws)
Source: SOptLib iid stream law and Mathlib product measure APIs
Used in: stochastic block mirror descent construction of a run law from independent block-index and oracle-sample streams
Book citation: book/book/FOML/NonconvexStochasticBlockMirrorDescent.json#/algorithm_spec/steps/1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, nonconvex stochastic block mirror descent -/
noncomputable def split_block_oracle_run_law
    {I S : Type*} [MeasurableSpace I] [MeasurableSpace S]
    (blockLaw : Measure I) (oracleLaw : Measure S) :
    Measure (split_block_oracle_run_sample I S) :=
  (iidStreamLaw blockLaw).prod (iidStreamLaw oracleLaw)

/-- The split block/oracle run law unfolds to the product of the two iid stream laws. -/
@[simp]
theorem split_block_oracle_run_law_def
    {I S : Type*} [MeasurableSpace I] [MeasurableSpace S]
    (blockLaw : Measure I) (oracleLaw : Measure S) :
    split_block_oracle_run_law blockLaw oracleLaw =
      (iidStreamLaw blockLaw).prod (iidStreamLaw oracleLaw) := rfl

/-- The split block/oracle run law is a probability measure when both marginals are. -/
@[instance]
theorem split_block_oracle_run_law_is_probability_measure
    {I S : Type*} [MeasurableSpace I] [MeasurableSpace S]
    (blockLaw : Measure I) (oracleLaw : Measure S)
    [IsProbabilityMeasure blockLaw] [IsProbabilityMeasure oracleLaw] :
    IsProbabilityMeasure (split_block_oracle_run_law blockLaw oracleLaw) := by
  unfold split_block_oracle_run_law
  infer_instance

/-- The first stream projection of the split run law has the iid block-stream law. -/
theorem split_block_oracle_run_law_map_fst
    {I S : Type*} [MeasurableSpace I] [MeasurableSpace S]
    (blockLaw : Measure I) (oracleLaw : Measure S)
    [IsProbabilityMeasure oracleLaw] :
    Measure.map Prod.fst (split_block_oracle_run_law blockLaw oracleLaw) =
      iidStreamLaw blockLaw := by
  rw [split_block_oracle_run_law_def, Measure.map_fst_prod, measure_univ, one_smul]

/-- The second stream projection of the split run law has the iid oracle-stream law. -/
theorem split_block_oracle_run_law_map_snd
    {I S : Type*} [MeasurableSpace I] [MeasurableSpace S]
    (blockLaw : Measure I) (oracleLaw : Measure S)
    [IsProbabilityMeasure blockLaw] :
    Measure.map Prod.snd (split_block_oracle_run_law blockLaw oracleLaw) =
      iidStreamLaw oracleLaw := by
  classical
  haveI : SFinite (iidStreamLaw oracleLaw) := by
    unfold iidStreamLaw
    by_cases h : ∀ _ : ℕ, IsProbabilityMeasure oracleLaw
    · letI : ∀ _ : ℕ, IsProbabilityMeasure oracleLaw := h
      infer_instance
    · rw [Measure.infinitePi, dif_neg h]
      infer_instance
  rw [split_block_oracle_run_law_def, Measure.map_snd_prod, measure_univ, one_smul]

/-- Every block coordinate `ω.1 k` has marginal law `blockLaw`. -/
theorem split_block_oracle_run_law_map_block_eval
    {I S : Type*} [MeasurableSpace I] [MeasurableSpace S]
    (blockLaw : Measure I) (oracleLaw : Measure S)
    [IsProbabilityMeasure blockLaw] [IsProbabilityMeasure oracleLaw] (k : Nat) :
    Measure.map (fun omega : split_block_oracle_run_sample I S => omega.1 k)
        (split_block_oracle_run_law blockLaw oracleLaw) = blockLaw := by
  change Measure.map ((fun stream : Nat -> I => stream k) ∘ Prod.fst)
      (split_block_oracle_run_law blockLaw oracleLaw) = blockLaw
  rw [← Measure.map_map]
  · rw [split_block_oracle_run_law_map_fst]
    exact iidStreamLaw_map_eval blockLaw k
  · exact measurable_pi_apply k
  · exact measurable_fst

/-- Every oracle coordinate `ω.2 k` has marginal law `oracleLaw`. -/
theorem split_block_oracle_run_law_map_oracle_eval
    {I S : Type*} [MeasurableSpace I] [MeasurableSpace S]
    (blockLaw : Measure I) (oracleLaw : Measure S)
    [IsProbabilityMeasure blockLaw] [IsProbabilityMeasure oracleLaw] (k : Nat) :
    Measure.map (fun omega : split_block_oracle_run_sample I S => omega.2 k)
        (split_block_oracle_run_law blockLaw oracleLaw) = oracleLaw := by
  change Measure.map ((fun stream : Nat -> S => stream k) ∘ Prod.snd)
      (split_block_oracle_run_law blockLaw oracleLaw) = oracleLaw
  rw [← Measure.map_map]
  · rw [split_block_oracle_run_law_map_snd]
    exact iidStreamLaw_map_eval oracleLaw k
  · exact measurable_pi_apply k
  · exact measurable_snd

/-- The split block/oracle run law is a probability measure with the expected
one-time block and oracle marginals. -/
theorem split_block_oracle_run_law_spec
    {I S : Type*} [MeasurableSpace I] [MeasurableSpace S]
    (blockLaw : Measure I) (oracleLaw : Measure S)
    [IsProbabilityMeasure blockLaw] [IsProbabilityMeasure oracleLaw] :
    IsProbabilityMeasure (split_block_oracle_run_law blockLaw oracleLaw) ∧
      (∀ k : Nat,
        Measure.map (fun omega : split_block_oracle_run_sample I S => omega.1 k)
          (split_block_oracle_run_law blockLaw oracleLaw) = blockLaw) ∧
      (∀ k : Nat,
        Measure.map (fun omega : split_block_oracle_run_sample I S => omega.2 k)
          (split_block_oracle_run_law blockLaw oracleLaw) = oracleLaw) := by
  exact ⟨inferInstance, split_block_oracle_run_law_map_block_eval blockLaw oracleLaw,
    split_block_oracle_run_law_map_oracle_eval blockLaw oracleLaw⟩

end SOptLib


namespace SOptLib


-- Generalization plan (G0):
-- concept/name: fixed-query unbiased bounded-variance stochastic oracle; orig
--   was SFOAssumption13.
-- generality used: arbitrary query type X, sampled space S with a measurable
--   space, normed real vector codomain E with measurable codomain structure,
--   sample law P, stochastic kernel G, deterministic target field, and variance
--   scale sigma; no objective, gradient, smoothness, convexity, or
--   finite-dimensional assumptions are needed.
-- portable call pattern: stochastic gradient, zeroth-order smoothing, and
--   variance-reduced oracle proofs can replace the objective gradient by any
--   target field and the sample gradient by any fixed-query oracle kernel while
--   keeping measurable fibers, Bochner mean unbiasedness, and centered
--   second-moment control.
-- counterargument checked: not paper-local traceability because the same
--   fixed-query oracle contract feeds random-query variance transfer and
--   mini-batch residual bounds; not a pure duplicate of
--   BoundedVarianceUnbiasedOracleOn, which is carrier/set-based, fixes queries
--   in the vector codomain, uses an explicit dual-norm gauge, and adds joint
--   residual measurability.
-- coverage search: searched "fixed query stochastic oracle measurable
--   integrable unbiased variance bounded centered second moment" and "oracle
--   mean unbiased variance bounded centered second moment integrable"; top hits
--   included SOptLib.BoundedVarianceUnbiasedOracleOn and random-query variance
--   transfer lemmas, all partial rather than this global fixed-query ambient
--   norm predicate over an arbitrary query type.
-- minimal hypotheses: the codomain measurable-space instance is needed for
--   Measurable fibers; the normed real vector structure is needed for Bochner
--   integration and residual subtraction; probability and nonnegativity of
--   sigma are caller-side assumptions, not needed by the predicate.

/-- Fixed-query stochastic oracle assumptions with unbiased mean and bounded
centered second moment.

For every deterministic query, the sampled oracle fiber is measurable and
integrable, its Bochner mean equals the deterministic target field, and its
squared norm residual around that target is integrable with expectation at most
`sigma ^ 2`.

Layer: Model | Concept: Fixed-query unbiased bounded-variance stochastic oracle
Proof: (definitional construction; conjunction of measurable fibers, Bochner
  integrability, unbiased mean equality, and centered norm-square moment bound)
Source: Stochastic first-order oracle assumptions, Mathlib Bochner integral
  notation, and normed-space residual second-moment predicates
Used in: randomized stochastic gradient-free proofs when Assumption 13 turns
  sample gradients into unbiased fixed-query oracle values with a uniform
  centered second-moment budget before the finite-difference oracle estimates
Book citation: book/FOML/StochasticZerothOrder.json#/assumptions
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic gradient-free method -/
def FixedQueryUnbiasedVarianceOracle
    {X S E : Type*} [MeasurableSpace S] [MeasurableSpace E]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Measure S) (G : X → S → E) (target : X → E) (sigma : ℝ) : Prop :=
  (∀ x : X, Measurable (fun ξ => G x ξ)) ∧
    (∀ x : X, Integrable (fun ξ => G x ξ) P) ∧
    (∀ x : X, Integrable (fun ξ => ‖G x ξ - target x‖ ^ (2 : ℕ)) P) ∧
    (∀ x : X, (∫ ξ, G x ξ ∂P) = target x) ∧
    (∀ x : X, (∫ ξ, ‖G x ξ - target x‖ ^ (2 : ℕ) ∂P) ≤ sigma ^ (2 : ℕ))

@[simp]
theorem FixedQueryUnbiasedVarianceOracle_def
    {X S E : Type*} [MeasurableSpace S] [MeasurableSpace E]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Measure S) (G : X → S → E) (target : X → E) (sigma : ℝ) :
    FixedQueryUnbiasedVarianceOracle P G target sigma ↔
      (∀ x : X, Measurable (fun ξ => G x ξ)) ∧
        (∀ x : X, Integrable (fun ξ => G x ξ) P) ∧
        (∀ x : X, Integrable (fun ξ => ‖G x ξ - target x‖ ^ (2 : ℕ)) P) ∧
        (∀ x : X, (∫ ξ, G x ξ ∂P) = target x) ∧
        (∀ x : X, (∫ ξ, ‖G x ξ - target x‖ ^ (2 : ℕ) ∂P) ≤
          sigma ^ (2 : ℕ)) := by
  rfl

theorem FixedQueryUnbiasedVarianceOracle.measurable
    {X S E : Type*} [MeasurableSpace S] [MeasurableSpace E]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Measure S} {G : X → S → E} {target : X → E} {sigma : ℝ}
    (h : FixedQueryUnbiasedVarianceOracle P G target sigma) (x : X) :
    Measurable (fun ξ => G x ξ) :=
  h.1 x

theorem FixedQueryUnbiasedVarianceOracle.integrable
    {X S E : Type*} [MeasurableSpace S] [MeasurableSpace E]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Measure S} {G : X → S → E} {target : X → E} {sigma : ℝ}
    (h : FixedQueryUnbiasedVarianceOracle P G target sigma) (x : X) :
    Integrable (fun ξ => G x ξ) P :=
  h.2.1 x

theorem FixedQueryUnbiasedVarianceOracle.centered_sq_integrable
    {X S E : Type*} [MeasurableSpace S] [MeasurableSpace E]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Measure S} {G : X → S → E} {target : X → E} {sigma : ℝ}
    (h : FixedQueryUnbiasedVarianceOracle P G target sigma) (x : X) :
    Integrable (fun ξ => ‖G x ξ - target x‖ ^ (2 : ℕ)) P :=
  h.2.2.1 x

theorem FixedQueryUnbiasedVarianceOracle.mean_eq
    {X S E : Type*} [MeasurableSpace S] [MeasurableSpace E]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Measure S} {G : X → S → E} {target : X → E} {sigma : ℝ}
    (h : FixedQueryUnbiasedVarianceOracle P G target sigma) (x : X) :
    (∫ ξ, G x ξ ∂P) = target x :=
  h.2.2.2.1 x

theorem FixedQueryUnbiasedVarianceOracle.variance_bound
    {X S E : Type*} [MeasurableSpace S] [MeasurableSpace E]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Measure S} {G : X → S → E} {target : X → E} {sigma : ℝ}
    (h : FixedQueryUnbiasedVarianceOracle P G target sigma) (x : X) :
    (∫ ξ, ‖G x ξ - target x‖ ^ (2 : ℕ) ∂P) ≤ sigma ^ (2 : ℕ) :=
  h.2.2.2.2 x




-- Generalization plan (G0):
-- concept/name: forward finite-difference zeroth-order oracle; orig was
--   `rsgfOracle`, renamed away from the paper acronym while keeping the
--   stochastic-optimization domain term `oracle`.
-- generality used: arbitrary real normed vector space E and arbitrary sample
--   type Sample; no measure, filtration, convexity, smoothness, integrability,
--   positivity, or finite-dimensional hypotheses are needed to name the
--   pointwise finite-difference oracle value.
-- portable call pattern: randomized gradient-free, Gaussian random-search, and
--   stochastic zeroth-order algorithms can instantiate the objective kernel,
--   smoothing scale, query point, sample, and search direction while reusing the
--   same two-query scaled directional estimator before unbiasedness and moment
--   proofs.
-- counterargument checked: not merely paper-local traceability because the
--   same pointwise oracle atom is reused across zeroth-order methods; not only
--   a caller-side expression because downstream measurability, expectation, and
--   second-moment lemmas benefit from a stable named oracle. Mathlib `fwdDiff`
--   covers only the additive difference operator `f (x + h) - f x`, not the
--   sampled kernel, scale division, and returned direction vector.
-- coverage search: searched `forward finite difference zeroth order oracle`,
--   `finite difference oracle sampled direction output equality`, project
--   grep for `forwardDifference`/`finite difference`, and LeanSearch for
--   `forward finite difference oracle zeroth order stochastic optimization`.
--   Top exact hits were private `rsgfOracle` lemmas in the algorithm file;
--   public SOptLib hits were unrelated oracle-difference moment/scalarization
--   facts, and Mathlib hits were `fwdDiff` APIs with only partial coverage.
-- minimal hypotheses: the body only needs addition on E, real scalar
--   multiplication on E, and real-valued subtraction/division. Normed-space
--   assumptions are needed only for API facts that mention norms.

/-- Forward finite-difference zeroth-order oracle from two sampled function
queries.

For a sample objective kernel `F`, query point `x`, sample `xi`, search
direction `u`, and scale `mu`, this names the estimator
`((F (x + mu • u) xi - F x xi) / mu) • u`.

Layer: Model | Concept: forward finite-difference oracle
Proof: (definitional construction; scaled two-query sampled objective
  difference returned in the queried direction)
Source: stochastic zeroth-order finite-difference oracle models and Mathlib
  real module scalar-action primitives
Used in: randomized stochastic gradient-free proofs when the two sampled
  zeroth-order function queries are packaged as the oracle value before
  unbiasedness, measurability, and second-moment estimates
Book citation: book/FOML/StochasticZerothOrder.json#/assumptions/5
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic gradient-free method -/
noncomputable def forwardDifferenceOracle
    {E Sample : Type*} [AddCommMonoid E] [Module ℝ E]
    (F : E → Sample → ℝ) (mu : ℝ) (x : E) (xi : Sample) (u : E) : E :=
  ((F (x + mu • u) xi - F x xi) / mu) • u

/-- The forward finite-difference oracle unfolds to its scaled two-query
sampled objective formula.

Layer: Model | Gap: Level 0 (forward finite-difference oracle unfolding)
Proof: by rfl after unfolding `forwardDifferenceOracle`.
Source: stochastic zeroth-order finite-difference oracle models and Mathlib
  real module scalar-action primitives
Used in: randomized stochastic gradient-free proofs when rewriting the named
  oracle value back to the sampled finite-difference expression for
  integration, measurability, and second-moment calculations
Book citation: book/FOML/StochasticZerothOrder.json#/assumptions/5
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic gradient-free method -/
@[simp]
theorem forwardDifferenceOracle_def
    {E Sample : Type*} [AddCommMonoid E] [Module ℝ E]
    (F : E → Sample → ℝ) (mu : ℝ) (x : E) (xi : Sample) (u : E) :
    forwardDifferenceOracle F mu x xi u =
      ((F (x + mu • u) xi - F x xi) / mu) • u := by
  rfl

/-- The norm of a forward finite-difference oracle value is the absolute
scaled sampled function difference times the search-direction norm.

Layer: Model | Gap: Level 0 (forward finite-difference oracle norm formula)
Proof: unfold `forwardDifferenceOracle` and use Mathlib's scalar norm formula.
Source: stochastic zeroth-order finite-difference oracle models and Mathlib
  real normed-space scalar norm APIs
Used in: second-moment and domination estimates for finite-difference
  zeroth-order oracle values
Book citation: book/FOML/StochasticZerothOrder.json#/assumptions/5
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic gradient-free method -/
theorem norm_forwardDifferenceOracle
    {E Sample : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → Sample → ℝ) (mu : ℝ) (x : E) (xi : Sample) (u : E) :
    ‖forwardDifferenceOracle F mu x xi u‖ =
      |(F (x + mu • u) xi - F x xi) / mu| * ‖u‖ := by
  rw [forwardDifferenceOracle, norm_smul, Real.norm_eq_abs]

/-- The forward finite-difference oracle returns zero in the zero search
direction.

Layer: Model | Gap: Level 0 (forward finite-difference oracle zero direction)
Proof: unfold `forwardDifferenceOracle` and simplify the zero scalar action.
Source: stochastic zeroth-order finite-difference oracle models and Mathlib
  real module scalar-action APIs
Used in: endpoint and degenerate-direction simplifications for zeroth-order
  oracle estimates
Book citation: book/FOML/StochasticZerothOrder.json#/assumptions/5
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic gradient-free method -/
@[simp]
theorem forwardDifferenceOracle_zero_direction
    {E Sample : Type*} [AddCommMonoid E] [Module ℝ E]
    (F : E → Sample → ℝ) (mu : ℝ) (x : E) (xi : Sample) :
    forwardDifferenceOracle F mu x xi (0 : E) = 0 := by
  simp [forwardDifferenceOracle]


end SOptLib
