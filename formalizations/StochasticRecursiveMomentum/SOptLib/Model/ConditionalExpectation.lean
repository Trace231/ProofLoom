import Mathlib.Probability.ConditionalExpectation
import SOptLib.Model.Objective

open MeasureTheory
open scoped MeasureTheory

namespace SOptLib.ConditionalExpectation

-- Merged from Staging/conditionalExpectationWellDefined.lean
-- Generalization plan (G0):
-- concept/name: conditional-expectation nonfallback well-definedness domain;
--   orig was `conditionalExpectationWellDefined`, retained because it exposes
--   the Mathlib `condExp` domain condition rather than a paper-local label.
-- generality used: arbitrary measurable source type, arbitrary target normed
--   additive group, arbitrary measure, conditioning measurable space, and
--   random variable; no probability, filtration, independence, completeness,
--   finite-dimensionality, convexity, smoothness, oracle, or algorithm-state
--   assumptions are used by the predicate itself.
-- portable call pattern: stochastic approximation, randomized block, martingale,
--   and variance-reduction proofs assert a conditional expectation identity
--   together with the same nonfallback domain condition while changing the
--   sample space, target Banach space, measure, conditioning sigma-algebra, and
--   random variable.
-- counterargument checked: not merely paper traceability because Mathlib's
--   `condExp` is total and future proofs need a reusable name for exactly the
--   nonfallback branch; not a pure wrapper over an existing SOptLib predicate.
-- coverage search: searched CATALOG/SOptLib/Staging for `conditional
--   expectation well defined`, `condExp well defined`, `SigmaFinite trim
--   Integrable`, and the precise shape; LeanSearch top hits were Mathlib
--   `MeasureTheory.condExp_def`, `condExp_of_sigmaFinite`, and `condExpL1`,
--   which expose the branch but do not provide a reusable domain predicate.
-- minimal hypotheses: dropped the unused `NormedSpace ℝ F` and `CompleteSpace F`
--   requirements from the local wrapper; `NormedAddCommGroup F` is retained
--   because `Integrable Z μ` is a normed target-space predicate.

/-- Nonfallback domain predicate for a Mathlib conditional expectation.

The predicate records the two facts that put `μ[Z | m]` in the genuine
conditional-expectation branch of Mathlib's total definition: `m` is a
sub-sigma-algebra of the ambient measurable space with sigma-finite trimmed
measure, and `Z` is integrable.

Layer: Model | Concept: Conditional expectation
Proof: (definitional construction; packages the `condExp` nonfallback branch
  as a reusable domain predicate)
Source: Mathlib conditional expectation branch definition and Bochner
  integrability APIs
Used in: randomized gradient extrapolation conditional sampled-block identities
  before passing from conditional expectations to total expectations
Book citation: book/FOML/RandomGradientExtrapolation.json#/key_lemmas/1/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
def conditionalExpectationWellDefined
    {Ω F : Type*} [m0 : MeasurableSpace Ω] [NormedAddCommGroup F]
    (μ : Measure[m0] Ω) (m : MeasurableSpace Ω) (Z : Ω → F) : Prop :=
  ∃ hm : m ≤ m0, @SigmaFinite Ω m (μ.trim hm) ∧ Integrable Z μ

/-- The conditional-expectation well-definedness predicate unfolds to a
sub-sigma-algebra witness, sigma-finiteness of the trimmed measure, and
integrability of the random variable.

Layer: Model | Gap: Level 0 (conditional-expectation nonfallback-domain unfolding)
Proof: by rfl after unfolding `conditionalExpectationWellDefined`.
Source: Mathlib conditional expectation branch definition and Bochner
  integrability APIs
Used in: randomized gradient extrapolation conditional sampled-block identities
  before passing from conditional expectations to total expectations
Book citation: book/FOML/RandomGradientExtrapolation.json#/key_lemmas/1/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
@[simp]
theorem conditionalExpectationWellDefined_def
    {Ω F : Type*} [m0 : MeasurableSpace Ω] [NormedAddCommGroup F]
    (μ : Measure[m0] Ω) (m : MeasurableSpace Ω) (Z : Ω → F) :
    @conditionalExpectationWellDefined Ω F m0 _ μ m Z ↔
      ∃ hm : m ≤ m0, @SigmaFinite Ω m (μ.trim hm) ∧ Integrable Z μ := by
  rfl

/-- The sub-sigma-algebra witness from conditional-expectation
well-definedness.

Layer: Model | Gap: Level 0 (conditional-expectation domain projection)
Proof: projection from `conditionalExpectationWellDefined`.
Source: Mathlib conditional expectation branch definition and Bochner
  integrability APIs
Used in: turning a bundled conditional-expectation domain hypothesis into
  Mathlib `condExp` hypotheses. -/
theorem conditionalExpectationWellDefined.subSigmaLe
    {Ω F : Type*} [m0 : MeasurableSpace Ω] [NormedAddCommGroup F]
    {μ : Measure[m0] Ω} {m : MeasurableSpace Ω} {Z : Ω → F}
    (h : @conditionalExpectationWellDefined Ω F m0 _ μ m Z) : m ≤ m0 :=
  Exists.elim h fun hm _ => hm

/-- Conditional-expectation well-definedness supplies sigma-finiteness of the
trimmed measure along a sub-sigma-algebra witness.

Layer: Model | Gap: Level 0 (conditional-expectation domain projection)
Proof: projection from `conditionalExpectationWellDefined`.
Source: Mathlib conditional expectation branch definition and Bochner
  integrability APIs
Used in: supplying the `[SigmaFinite (μ.trim hm)]` instance required by
  Mathlib conditional-expectation API. -/
theorem conditionalExpectationWellDefined.sigmaFinite_trim
    {Ω F : Type*} [m0 : MeasurableSpace Ω] [NormedAddCommGroup F]
    {μ : Measure[m0] Ω} {m : MeasurableSpace Ω} {Z : Ω → F}
    (h : @conditionalExpectationWellDefined Ω F m0 _ μ m Z) :
    ∃ hm : m ≤ m0, @SigmaFinite Ω m (μ.trim hm) :=
  Exists.elim h fun hm hrest => ⟨hm, hrest.1⟩

/-- Conditional-expectation well-definedness includes integrability of the
random variable.

Layer: Model | Gap: Level 0 (conditional-expectation domain projection)
Proof: choice-spec projection from `conditionalExpectationWellDefined`.
Source: Mathlib conditional expectation branch definition and Bochner
  integrability APIs
Used in: downstream stochastic-optimization estimates that need the original
  variable's Bochner integrability after opening a bundled domain hypothesis. -/
theorem conditionalExpectationWellDefined.integrable
    {Ω F : Type*} [m0 : MeasurableSpace Ω] [NormedAddCommGroup F]
    {μ : Measure[m0] Ω} {m : MeasurableSpace Ω} {Z : Ω → F}
    (h : @conditionalExpectationWellDefined Ω F m0 _ μ m Z) :
    Integrable Z μ :=
  Exists.elim h fun _hm hrest => hrest.2

/-- The integral of a well-defined conditional expectation equals the integral
of the original random variable.

Layer: Model | Gap: Level 0 (conditional-expectation integral bridge)
Proof: unpack `conditionalExpectationWellDefined` into the sub-sigma witness
  and sigma-finite trim instance required by `MeasureTheory.integral_condExp`.
Source: `MeasureTheory.integral_condExp`
Used in: passing from conditional-expectation identities to total-expectation
  identities in stochastic-optimization proofs. -/
theorem conditionalExpectationWellDefined.integral_condExp
    {Ω F : Type*} [m0 : MeasurableSpace Ω] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F]
    {μ : Measure[m0] Ω} {m : MeasurableSpace Ω} {Z : Ω → F}
    (h : @conditionalExpectationWellDefined Ω F m0 _ μ m Z) :
    ∫ ω, (μ[Z | m]) ω ∂μ = ∫ ω, Z ω ∂μ := by
  rcases h with ⟨hm, hsf, _hZ⟩
  haveI : @SigmaFinite Ω m (μ.trim hm) := hsf
  exact MeasureTheory.integral_condExp (μ := μ) (m := m) (m₀ := m0) (f := Z) hm

-- Merged from Staging/conditionalExpectationEq.lean
-- Generalization plan (G0):
-- concept/name: conditional-expectation target equality predicate; orig was
--   `conditionalExpectationEq`, retained because it names the paper-free
--   mathematical object `μ[Z | m] = target` together with the nonfallback
--   Mathlib conditional-expectation domain.
-- generality used: arbitrary measurable source type, arbitrary real Banach
--   target, arbitrary measure, conditioning measurable space, random variable,
--   and target process; no probability, filtration, independence, convexity,
--   smoothness, oracle, iterate, or finite-dimensional assumptions are used.
-- portable call pattern: stochastic approximation, martingale-difference,
--   randomized block-sampling, and variance-reduction proofs state unbiasedness
--   or conditional laws by changing `μ`, `m`, `Z`, and `target` while keeping
--   the same bundled conditional-expectation identity.
-- counterargument checked: not merely paper traceability because future proofs
--   repeatedly need to distinguish Mathlib `condExp`'s nonfallback branch from
--   its total fallback value; not covered by Mathlib, which exposes raw
--   `condExp` equality lemmas, or by staged `conditionalExpectationWellDefined`,
--   which has no target equality component.
-- coverage search: searched CATALOG/SOptLib/Staging for `conditional
--   expectation equality`, `conditionalExpectationEq`, `condExp target`, and
--   `conditional expectation well defined`; LeanSearch top hits were
--   `MeasureTheory.condExp_def`, `condExp_of_sigmaFinite`,
--   `condExp_of_aestronglyMeasurable'`, and
--   `ae_eq_condExp_of_forall_setIntegral_eq`, all raw conditional-expectation
--   API rather than the bundled predicate shape.
-- minimal hypotheses: kept only the Banach-space assumptions required by
--   `MeasureTheory.condExp`; probability, finite-measure, finite-dimensional,
--   and algorithm-specific setup assumptions were dropped.

/-- Bundled predicate for a well-defined conditional expectation equaling a
target process a.e.

The predicate records both the nonfallback domain condition for Mathlib's total
`condExp` and the conditional-expectation identity itself. This keeps stochastic
algorithm statements from silently relying on the fallback value of `condExp`.

Layer: Model | Concept: Conditional expectation
Proof: (definitional construction; pairs the conditional-expectation
  nonfallback domain predicate with an a.e. target equality)
Source: Mathlib conditional expectation branch definition and a.e. equality API
Used in: randomized gradient extrapolation conditional sampled-block laws and
  martingale-style unbiasedness identities
Book citation: book/FOML/RandomGradientExtrapolation.json#/key_lemmas/1/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
def conditionalExpectationEq
    {Ω F : Type*} [m0 : MeasurableSpace Ω]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure[m0] Ω) (m : MeasurableSpace Ω) (Z target : Ω → F) : Prop :=
  @conditionalExpectationWellDefined Ω F m0 _ μ m Z ∧
    @MeasureTheory.condExp Ω F m (m₀ := m0) _ _ _ μ Z =ᵐ[μ] target

/-- The bundled conditional-expectation equality unfolds to well-definedness
and the a.e. target equality.

Layer: Model | Gap: Level 0 (conditional-expectation equality unfolding)
Proof: by rfl after unfolding `conditionalExpectationEq`.
Source: Mathlib conditional expectation branch definition and a.e. equality API
Used in: exposing conditional sampled-block law hypotheses to Mathlib
  conditional-expectation lemmas
Book citation: book/FOML/RandomGradientExtrapolation.json#/key_lemmas/1/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
@[simp]
theorem conditionalExpectationEq_def
    {Ω F : Type*} [m0 : MeasurableSpace Ω]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure[m0] Ω) (m : MeasurableSpace Ω) (Z target : Ω → F) :
    @conditionalExpectationEq Ω F m0 _ _ _ μ m Z target ↔
      @conditionalExpectationWellDefined Ω F m0 _ μ m Z ∧
        @MeasureTheory.condExp Ω F m (m₀ := m0) _ _ _ μ Z =ᵐ[μ] target := by
  rfl

/-- A bundled conditional-expectation equality includes the nonfallback domain
condition for the conditional expectation.

Layer: Model | Gap: Level 0 (conditional-expectation equality projection)
Proof: projection from `conditionalExpectationEq`.
Source: Mathlib conditional expectation branch definition and Bochner
  integrability APIs
Used in: recovering the hypotheses required by Mathlib `condExp` integration
  and pull-out lemmas
Book citation: book/FOML/RandomGradientExtrapolation.json#/key_lemmas/1/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem conditionalExpectationEq.wellDefined
    {Ω F : Type*} [m0 : MeasurableSpace Ω]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {μ : Measure[m0] Ω} {m : MeasurableSpace Ω} {Z target : Ω → F}
    (h : @conditionalExpectationEq Ω F m0 _ _ _ μ m Z target) :
    @conditionalExpectationWellDefined Ω F m0 _ μ m Z :=
  h.1

/-- A bundled conditional-expectation equality includes the a.e. equality to
the target process.

Layer: Model | Gap: Level 0 (conditional-expectation equality projection)
Proof: projection from `conditionalExpectationEq`.
Source: Mathlib conditional expectation branch definition and a.e. equality API
Used in: rewriting conditional sampled-block laws from `condExp` form to target
  process form
Book citation: book/FOML/RandomGradientExtrapolation.json#/key_lemmas/1/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem conditionalExpectationEq.ae_eq
    {Ω F : Type*} [m0 : MeasurableSpace Ω]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {μ : Measure[m0] Ω} {m : MeasurableSpace Ω} {Z target : Ω → F}
    (h : @conditionalExpectationEq Ω F m0 _ _ _ μ m Z target) :
    @MeasureTheory.condExp Ω F m (m₀ := m0) _ _ _ μ Z =ᵐ[μ] target :=
  h.2

/-- Integrating a bundled conditional-expectation equality gives equality of
the unconditional integrals.

Layer: Model | Gap: Level 1 (bundled conditional-expectation integral transfer)
Proof: unpack `conditionalExpectationEq`; use
  `conditionalExpectationWellDefined.integral_condExp` for the nonfallback
  branch and `integral_congr_ae` for the target equality.
Source: Mathlib conditional expectation and Bochner integral APIs
Used in: passing randomized gradient extrapolation conditional identities to
  unconditional expectation identities
Book citation: book/FOML/RandomGradientExtrapolation.json#/key_lemmas/2/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem conditionalExpectationEq.integral_eq
    {Ω F : Type*} [m0 : MeasurableSpace Ω]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {μ : Measure[m0] Ω} {m : MeasurableSpace Ω} {Z target : Ω → F}
    (h : @conditionalExpectationEq Ω F m0 _ _ _ μ m Z target) :
    ∫ ω, Z ω ∂μ = ∫ ω, target ω ∂μ := by
  rcases h with ⟨hwd, hce⟩
  rcases hwd with ⟨hm, hsf, _hZ⟩
  haveI : @SigmaFinite Ω m (μ.trim hm) := hsf
  calc
    ∫ ω, Z ω ∂μ =
        ∫ ω, (@MeasureTheory.condExp Ω F m (m₀ := m0) _ _ _ μ Z) ω ∂μ := by
      exact (MeasureTheory.integral_condExp (μ := μ) (m := m) (m₀ := m0) (f := Z) hm).symm
    _ = ∫ ω, target ω ∂μ := by
      exact integral_congr_ae hce

-- Merged from Staging/conditionalExpectationEq_expectation_eq.lean
-- Generalization plan (G0):
-- concept/name: conditional-expectation expectation transfer; orig was
--   `conditionalExpectationEq_expectation_eq`, renamed to
--   `conditionalExpectationEq.expectation_eq` as the expectation-valued API for
--   the bundled conditional-expectation equality predicate.
-- generality used: arbitrary measurable source type, arbitrary real Banach
--   target, arbitrary measure, conditioning measurable space, random variable,
--   and target process; no probability, filtration, independence, convexity,
--   smoothness, oracle, iterate, or finite-dimensional assumptions are used.
-- portable call pattern: stochastic approximation, randomized block-sampling,
--   martingale-difference, and variance-reduction proofs first prove a bundled
--   conditional identity and then convert it to an unconditional
--   `SOptLib.expectation` equality while changing only `μ`, `m`, `Z`, and
--   `target`.
-- counterargument checked: not paper-local traceability because it exposes the
--   reusable predicate-level bridge from conditional identities to named
--   expectations; not a pure Mathlib rename because Mathlib supplies
--   `integral_condExp`, while SOptLib's `expectation` is a separate named
--   object used by algorithm statements.
-- coverage search: searched CATALOG/SOptLib/Staging for `conditional
--   expectation equality`, `conditionalExpectationEq expectation_eq`,
--   `integral_eq_of_condExp_ae_eq`, and `expectationEq.expectation_eq`;
--   closest hits were `conditionalExpectationEq.integral_eq`, which returns
--   raw Bochner integrals, `SOptLib.integral_eq_of_condExp_ae_eq`, which is
--   over raw `condExp` hypotheses, and `expectationEq.expectation_eq`, which
--   projects a different predicate to a constant target value.
-- minimal hypotheses: all already minimal for the imported
--   `conditionalExpectationEq` predicate and `SOptLib.expectation`; completeness
--   is inherited from Mathlib conditional expectation, and no finite-measure or
--   finite-dimensional assumptions are needed.

/-- A bundled conditional-expectation identity gives equality of the
corresponding named unconditional expectations.

This is the `SOptLib.expectation` form of
`conditionalExpectationEq.integral_eq`, so algorithm statements can stay in
expectation notation after conditional identities have been discharged.

Layer: Model | Gap: Level 1 (conditional-expectation expectation transfer)
Proof: apply the integral transfer theorem for `conditionalExpectationEq` and
  unfold only the named `SOptLib.expectation` wrapper.
Source: Mathlib conditional expectation and Bochner integral APIs, via the
  SOptLib conditional-expectation predicate
Used in: randomized gradient extrapolation conditional sampled-block laws
  converted to total expectation identities
Book citation: book/FOML/RandomGradientExtrapolation.json#/key_lemmas/2/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem conditionalExpectationEq.expectation_eq
    {Ω F : Type*} [m0 : MeasurableSpace Ω]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {μ : Measure[m0] Ω} {m : MeasurableSpace Ω} {Z target : Ω → F}
    (h : @conditionalExpectationEq Ω F m0 _ _ _ μ m Z target) :
    @SOptLib.expectation Ω F m0 _ _ μ Z =
      @SOptLib.expectation Ω F m0 _ _ μ target := by
  simpa [SOptLib.expectation] using
    (@conditionalExpectationEq.integral_eq Ω F m0 _ _ _ μ m Z target h)

end SOptLib.ConditionalExpectation
