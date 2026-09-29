import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Logic.Function.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Basic
import SOptLib.Analysis.ConvexSmoothExtension
import SOptLib.Model.Bregman
import SOptLib.Model.Budget
import SOptLib.Model.ConditionalExpectation
import SOptLib.Model.Filtration
import SOptLib.Model.Iterates
import SOptLib.Model.Norms
import SOptLib.Model.Objective
import SOptLib.Model.ParameterChoices
import SOptLib.Model.Selection
import SOptLib.Model.StochasticOracle
import SOptLib.Glue.Algebra
import SOptLib.Glue.Analysis
import SOptLib.Glue.Calculus
import SOptLib.Glue.Martingale
import SOptLib.Glue.Probability
import SOptLib.Layer0.ConvexFOC
import SOptLib.Layer0.Objective
import SOptLib.Layer0.Oracle
import SOptLib.Layer1.Descent
import SOptLib.Layer1.Proximal
import SOptLib.Layer1.Telescope

/-!
# Random Gradient Extrapolation Method

Object-layer formalization of Lan's randomized gradient extrapolation method
(RGEM), Algorithm 5.4 and Theorem 5.4 in
*First-order and stochastic optimization methods for machine learning*.

This file deliberately keeps the algorithmic spine def-centric: the prox point,
block update, component-gradient update, generated state process, and weighted
output are definitions. Nontrivial mathematical properties are exposed as
theorems with proof obligations for later phases.
-/

/-!
Compatibility declarations for the current build surface.

The corresponding declarations already live in the SOptLib source tree, but the
compiled dependency surface used by the verifier in this workspace does not
export them. These target-local copies keep this file executable without editing
`SOptLib/**` or changing any paper-facing theorem boundary.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace

namespace SOptLib

theorem aestronglyMeasurable_of_countable_key_reconstruction
    {Ω Key E : Type*} [MeasurableSpace Ω] [MeasurableSpace Key]
    [Countable Key] [MeasurableSingletonClass Key] [TopologicalSpace E]
    {μ : MeasureTheory.Measure Ω} {Y : Ω → Key} {Z : Ω → E}
    (hY : AEMeasurable Y μ) (reconstruct : Key → E)
    (hZ : reconstruct ∘ Y =ᵐ[μ] Z) :
    AEStronglyMeasurable Z μ := by
  have hrec : AEStronglyMeasurable reconstruct (MeasureTheory.Measure.map Y μ) := by
    exact AEStronglyMeasurable.of_discrete
  exact (hrec.comp_aemeasurable hY).congr hZ

theorem integrable_of_finite_range
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    {Z : Ω → E} (hZ : MeasureTheory.AEStronglyMeasurable Z μ)
    (hfin : (Set.range Z).Finite) :
    MeasureTheory.Integrable Z μ := by
  classical
  let S : Finset ℝ := hfin.toFinset.image fun z => ‖z‖
  let C : ℝ := if hS : S.Nonempty then S.max' hS else 0
  have hC : ∀ ω, ‖Z ω‖ ≤ C := by
    intro ω
    have hmem : ‖Z ω‖ ∈ S := by
      simp [S, Set.Finite.mem_toFinset]
    have hS : S.Nonempty := ⟨‖Z ω‖, hmem⟩
    simpa [C, hS] using Finset.le_max' S (‖Z ω‖) hmem
  exact MeasureTheory.Integrable.of_bound hZ C (MeasureTheory.ae_of_all μ hC)

end SOptLib

open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace

namespace RandomGradientExtrapolation

variable {ι E : Type*}
variable [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Canonical RGEM sampled-block path space.

No SOptLib match: checked `SOptLib.blockSamplePath`, `SOptLib.iidStreamLaw`, and
`SOptLib.finiteBlockIndexLaw`; the first carries oracle samples paired with blocks,
while RGEM Algorithm 5.4 needs only the literal block-index stream `i_t`. The law
below reuses the SOptLib iid stream and finite block-index primitives. -/
abbrev BlockSamplePath (ι : Type*) := ℕ → ι

/-- Canonical sample table for Algorithm 5.5's stochastic oracle calls.

The table coordinate `(i,t,j)` represents the source sample `ξ_{i,t}^j`. -/
abbrev StochasticSampleTable (ι Ξ : Type*) := ι → ℕ → ℕ → Ξ

/-- Canonical stochastic RGEM path: sampled blocks together with oracle-sample tables.

No SOptLib match: searched "mini batch oracle average stochastic sample" and checked
`SOptLib.miniBatchOracleAverage`; that primitive averages staged oracle values but
does not provide the paper's joint conditioning space for Lemma 5.11, which must
condition on `i_1,...,i_{t-1}, ξ_1^t,...,ξ_m^t`. -/
abbrev StochasticRunPath (ι Ξ : Type*) := BlockSamplePath ι × StochasticSampleTable ι Ξ




/-- Canonical iid law of the Algorithm 5.4 sampled-block stream. -/
noncomputable def uniformBlockStreamLaw : Measure (BlockSamplePath ι) :=
  SOptLib.iidStreamLaw ((PMF.uniformOfFintype ι).toMeasure)

/-- Coordinate sampled block `i_t` on the canonical stream space. -/
def blockSample (t : ℕ) (ω : BlockSamplePath ι) : ι :=
  ω t

/-- The canonical sampled-block coordinates are measurable. -/
theorem blockSample_measurable (t : ℕ) : Measurable (blockSample (ι := ι) t) :=
  measurable_pi_apply t

/-- The canonical sampled-block coordinates are iid. -/
theorem uniformBlockStream_iIndepFun :
    ProbabilityTheory.iIndepFun (blockSample (ι := ι)) (uniformBlockStreamLaw (ι := ι)) := by
  simpa [uniformBlockStreamLaw, blockSample, BlockSamplePath] using
    SOptLib.iidStreamLaw_iIndepFun_eval ((PMF.uniformOfFintype ι).toMeasure)

/-- The canonical sampled-block stream has the Algorithm 5.4 marginal law. -/
theorem uniformBlockStream_singleton (t : ℕ) (i : ι) :
    uniformBlockStreamLaw (ι := ι) ((blockSample (ι := ι) t) ⁻¹' ({i} : Set ι)) =
      ENNReal.ofReal ((Fintype.card ι : ℝ)⁻¹) := by
  classical
  have hmap := SOptLib.iidStreamLaw_map_eval ((PMF.uniformOfFintype ι).toMeasure) t
  have hsingleton :
      (PMF.uniformOfFintype ι).toMeasure ({i} : Set ι) =
        ENNReal.ofReal ((Fintype.card ι : ℝ)⁻¹) := by
    have hcard_pos : 0 < (Fintype.card ι : ℝ) := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
    rw [PMF.toMeasure_apply_singleton (PMF.uniformOfFintype ι) i (measurableSet_singleton i)]
    rw [PMF.uniformOfFintype_apply]
    rw [ENNReal.ofReal_inv_of_pos hcard_pos]
    simp
  rw [← hsingleton, ← hmap]
  exact (Measure.map_apply (blockSample_measurable (ι := ι) t)
    (measurableSet_singleton i)).symm

/-- Canonical sampled-block law for Algorithm 5.4.

Algorithm 5.4 states `Prob{i_t=i}=1/m`. This declaration is now tied to the
canonical coordinate process on `BlockSamplePath ι` under `uniformBlockStreamLaw`,
rather than an arbitrary `(Ω, P, sample)` witness. SOptLib candidates checked:
`SOptLib.finiteBlockIndexLaw` supplies the finite one-step law and
`SOptLib.iidStreamLaw` supplies the stream law; `SOptLib.blockSamplePath` is not
available in the current import closure, so the local `BlockSamplePath` alias is
kept for the literal block-index stream. -/
def UniformBlockSampling : Prop :=
  ∀ (t : ℕ) (i : ι),
    uniformBlockStreamLaw (ι := ι) ((blockSample (ι := ι) t) ⁻¹' ({i} : Set ι)) =
      ENNReal.ofReal ((Fintype.card ι : ℝ)⁻¹)

/-- The canonical sampled-block stream satisfies Algorithm 5.4's uniform law. -/
theorem uniformBlockSampling : UniformBlockSampling (ι := ι) := by
  intro t i
  exact uniformBlockStream_singleton (ι := ι) t i

/-- State of RGEM after a completed iteration.

At time `t`, `x` is the primal point `x^t`, `blockX i` is the stored block point
`x_i^t`, `yCurr i` is `y_i^t`, and `yPrev i` is `y_i^{t-1}`. This stores exactly
the two gradient tables needed for the extrapolation formula (5.2.49). -/
structure State (ι E : Type*) where
  x : E
  blockX : ι → E
  yPrev : ι → E
  yCurr : ι → E

/-- Scalar expectation upper-bound predicate for RGEM source-facing estimates.

The paper states bounds of the form `E[Z] ≤ c` in Proposition 5.6 and
Theorem 5.4. The intended SOptLib candidate `SOptLib.expectationLe` was checked
but is not available in the active import environment; this paper-local
abbreviation reconstructs exactly its documented model-layer object:
`expectationWellDefined P Z ∧ expectation P Z ≤ bound`, using the two SOptLib
primitives that do elaborate. -/
abbrev expectationLe {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : Ω → ℝ) (bound : ℝ) : Prop :=
  SOptLib.expectationWellDefined P Z ∧ SOptLib.expectation P Z ≤ bound

/-- Definitional form of the RGEM expectation upper-bound predicate. -/
@[simp] theorem expectationLe_def {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : Ω → ℝ) (bound : ℝ) :
    expectationLe P Z bound ↔
      SOptLib.expectationWellDefined P Z ∧ SOptLib.expectation P Z ≤ bound := by
  rfl

/-- Add two scalar expectation upper bounds under an a.e. pointwise domination.

Candidate audit: searched `expectationLe pointwise less equal add expectation add
integral_mono_ae`; SOptLib provides `expectationLe_of_integrable_integral_le` and
finite-sum expectation monotonicity, but no two-term `expectationLe` constructor
for `F ≤ G + H`, so this paper-local bridge is the direct Bochner-integral
specialization needed in Theorem 5.4. -/
private theorem expectationLe_of_pointwise_le_add
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {F G H : Ω → ℝ} {bG bH : ℝ}
    (hF : SOptLib.expectationWellDefined P F)
    (hG : expectationLe P G bG)
    (hH : expectationLe P H bH)
    (hpoint : ∀ᵐ ω ∂P, F ω ≤ G ω + H ω) :
    expectationLe P F (bG + bH) := by
  simpa [expectationLe, SOptLib.expectationLe] using
    SOptLib.expectationLe_of_ae_le_add (μ := P) (F := F) (G := G) (H := H)
      (bG := bG) (bH := bH) hF hG hH hpoint

/-- Dual support function restricted to the feasible affine-hull direction.

This source-facing name delegates to `SOptLib.affineDirectionDualNorm`, the
paper-free support function over `(affineSpan ℝ X).direction`. -/
noncomputable def affineDirectionDualNorm (X : Set E) (p : Seminorm ℝ E) (zeta : E) :
    ℝ :=
  SOptLib.affineDirectionDualNorm X p zeta

/-- Source-facing setup data and assumptions for RGEM.

The original problem data and assumptions are supplemented by the explicit
component_extension repair condition below. In particular, there is no primitive iterate sequence,
prox map, output point, weighted-recursion condition, sampling-regularity contract,
or lemma result field. -/
structure Setup
    (ι : Type*) [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] where
  /-- Book citation: `book/FOML/RandomGradientExtrapolation.json#/setup/variable_space/math`.
  Quote: `X\subseteq \mathbb{R}^n is a closed convex set`. -/
  X : Set E
  /-- Book citation: `book/FOML/RandomGradientExtrapolation.json#/algorithm_spec/input/math`.
  Quote: `Let x^0\in X`. -/
  x0 : E
  /-- Realization of the paper norm `‖·‖` used in Eqs. (5.2.2)--(5.2.4).

  Book citation: `book/FOML/RandomGradientExtrapolation.json#/assumptions/1/math`.
  Quote: `‖∇ f_i(x_1)-∇ f_i(x_2)‖_* ≤ L_i ‖x_1-x_2‖`. -/
  primalNorm : Seminorm ℝ E
  /-- Component functions in the finite-sum objective.

  Book citation: `book/FOML/RandomGradientExtrapolation.json#/setup/problem/math`.
  Quote: `ψ(x) := 1/m ∑_{i=1}^m f_i(x)+μν(x)`. -/
  f : ι → E → ℝ
  /-- Component gradients on the feasible carrier, appearing in Eqs. (5.2.2),
  (5.2.49), and (5.2.52).

  Book citation: `book/FOML/RandomGradientExtrapolation.json#/assumptions/2/math`.
  Quote: `f_i ... are smooth convex functions with Lipschitz continuous gradients over X`.

  The paper's gradients are gradients of `f_i : X → R`; storing them in the
  affine-span direction of `X` is the Lean realization that removes arbitrary
  normal components invisible to `HasGradientWithinAt`. -/
  gradFOn : ι → {x : E // x ∈ X} → (affineSpan ℝ X).direction
  /-- Regularizer/distance-generating function in `ψ(x)`.

  Book citation: `book/FOML/RandomGradientExtrapolation.json#/setup/problem/math`.
  Quote: `ψ(x) := 1/m ∑_{i=1}^m f_i(x)+μν(x)`. -/
  ν : E → ℝ
  /-- Gradient `ν'` used in the Bregman distance and strong convexity condition.

  Book citation: `book/FOML/RandomGradientExtrapolation.json#/assumptions/3/math`.
  Quote: `ν(x_1)-ν(x_2)-<ν'(x_2),x_1-x_2> ≥ 1/2 ‖x_1-x_2‖^2`. -/
  gradν : E → E
  /-- Regularization parameter.

  Book citation: `book/FOML/RandomGradientExtrapolation.json#/assumptions/6/math`.
  Quote: `μ≥0 is a given constant`. -/
  μ : ℝ
  /-- Component smoothness constants `L_i`.

  Book citation: `book/FOML/RandomGradientExtrapolation.json#/assumptions/1/parameters/0`.
  Quote: `L_i≥0`. -/
  Lcomp : ι → ℝ
  /-- Average-gradient smoothness constant `L_f`.

  Book citation: `book/FOML/RandomGradientExtrapolation.json#/assumptions/4/math`.
  Quote: `‖∇ f(x_1)-∇ f(x_2)‖_* ≤ L_f ‖x_1-x_2‖`. -/
  Lf : ℝ
  /-- Extrapolation parameters `α_t`.

  Book citation: `book/FOML/RandomGradientExtrapolation.json#/assumptions/9/math`.
  Quote: `the nonnegative parameters {α_t}, {η_t}, and {τ_t} be given`. -/
  α : ℕ → ℝ
  /-- Prox parameters `η_t`.

  Book citation: `book/FOML/RandomGradientExtrapolation.json#/assumptions/9/math`.
  Quote: `the nonnegative parameters {α_t}, {η_t}, and {τ_t} be given`. -/
  η : ℕ → ℝ
  /-- Block averaging parameters `τ_t`.

  Book citation: `book/FOML/RandomGradientExtrapolation.json#/assumptions/9/math`.
  Quote: `the nonnegative parameters {α_t}, {η_t}, and {τ_t} be given`. -/
  τ : ℕ → ℝ
  /-- Output/proposition weights `θ_t`.

  Book citation: `book/FOML/RandomGradientExtrapolation.json#/algorithm_spec/output/math`.
  Quote: `For some θ_t>0 ... set underline{x}^k := (∑θ_t)^{-1}∑θ_t x^t`. -/
  θ : ℕ → ℝ
  /-- Closedness part of the stated feasible-set datum.

  Book citation: `book/FOML/RandomGradientExtrapolation.json#/assumptions/0/math`.
  Quote: `X\subseteq \mathbb{R}^n is a closed convex set`. -/
  hX_closed : IsClosed X
  /-- Convexity part of the stated feasible-set datum.

  Book citation: `book/FOML/RandomGradientExtrapolation.json#/assumptions/0/math`.
  Quote: `X\subseteq \mathbb{R}^n is a closed convex set`. -/
  hX_convex : Convex ℝ X
  /-- Initial feasibility from Algorithm 5.4 input.

  Book citation: `book/FOML/RandomGradientExtrapolation.json#/algorithm_spec/input/math`.
  Quote: `Let x^0\in X`. -/
  hx0_mem : x0 ∈ X
  /-- Lean realization of the paper norm as a separating seminorm.

  Book citation: `book/FOML/RandomGradientExtrapolation.json#/assumptions/1/math`.
  Quote: `‖·‖` and `‖·‖_*` appear as a primal/dual norm pair in the smoothness condition. -/
  hprimalNorm_separating : primalNorm.IsSeparating
  /-- Component convexity assumption.

  Book citation: `book/FOML/RandomGradientExtrapolation.json#/assumptions/2/math`.
  Quote: `f_i ... are smooth convex functions with Lipschitz continuous gradients over X`. -/
  hcomponent_convex : ∀ i, ConvexOn ℝ X (f i)
  /-- Differentiability witness for the printed gradients `∇f_i`.

  Book citation: `book/FOML/RandomGradientExtrapolation.json#/assumptions/2/math`.
  Quote: `f_i ... are smooth convex functions with Lipschitz continuous gradients over X`. -/
  hcomponent_hasGradient_on :
    ∀ i x, HasGradientWithinAt (f i) (gradFOn i x : E) X x.1
  /-- Differentiability witness for the printed regularizer gradient `ν'`.

  Book citation: `book/FOML/RandomGradientExtrapolation.json#/key_lemmas/0/statement_math`
  and PDF Lemma 3.5.
  Quote: `Let ν:X→R be a differentiable convex function`; the Chapter 3
  distance-generating setup also states that `ν` is continuously differentiable on
  the prox domain. -/
  hν_hasGradientWithinAt : ∀ x, x ∈ X → HasGradientWithinAt ν (gradν x) X x
  /-- Component Lipschitz-gradient assumption.

  Book citation: `book/FOML/RandomGradientExtrapolation.json#/assumptions/1/math`.
  Quote: `‖∇ f_i(x_1)-∇ f_i(x_2)‖_*≤ L_i ‖x_1-x_2‖`. -/
  hcomponent_smooth_on :
    ∀ i x y,
      affineDirectionDualNorm X primalNorm ((gradFOn i x : E) - (gradFOn i y : E)) ≤
        Lcomp i * primalNorm (x.1 - y.1)
  /-- Nonnegativity of component smoothness constants.

  Book citation: `book/FOML/RandomGradientExtrapolation.json#/assumptions/1/parameters/0`.
  Quote: `L_i≥0`. -/
  hLcomp_nonneg : ∀ i, 0 ≤ Lcomp i
  /-- Strong convexity of `ν` in the paper norm.

  Book citation: `book/FOML/RandomGradientExtrapolation.json#/assumptions/3/math`.
  Quote: `ν(x_1)-ν(x_2)-<ν'(x_2),x_1-x_2>≥1/2‖x_1-x_2‖^2`. -/
  hν_strong :
    ∀ x y, x ∈ X → y ∈ X →
      ν x - ν y - ⟪gradν y, x - y⟫_ℝ ≥ (1 / 2 : ℝ) * primalNorm (x - y) ^ 2
  /-- Nonnegativity of the regularization parameter.

  Book citation: `book/FOML/RandomGradientExtrapolation.json#/assumptions/6/math`.
  Quote: `μ≥0 is a given constant`. -/
  hμ_nonneg : 0 ≤ μ
  /-- Nonnegativity needed for the paper's average smoothness chain.

  Book citation: `book/FOML/RandomGradientExtrapolation.json#/assumptions/4/math`.
  Quote: `‖∇ f(x_1)-∇ f(x_2)‖_*≤ L_f‖x_1-x_2‖≤ L‖x_1-x_2‖`. -/
  hLf_nonneg : 0 ≤ Lf
  /-- Average smoothness assumption (5.2.4).

  Book citation: `book/FOML/RandomGradientExtrapolation.json#/assumptions/4/math`.
  Quote: `‖∇ f(x_1)-∇ f(x_2)‖_*≤L_f‖x_1-x_2‖≤L‖x_1-x_2‖`. -/
  haverage_smooth_on :
    ∀ x y : {x : E // x ∈ X},
      affineDirectionDualNorm X primalNorm
        ((Fintype.card ι : ℝ)⁻¹ •
            Finset.sum Finset.univ (fun i => (gradFOn i x : E)) -
          (Fintype.card ι : ℝ)⁻¹ •
            Finset.sum Finset.univ (fun i => (gradFOn i y : E))) ≤
        Lf * primalNorm (x.1 - y.1) ∧
          Lf * primalNorm (x.1 - y.1) ≤
            ((Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ Lcomp) *
              primalNorm (x.1 - y.1)
  /-- Algorithm 5.4 nonnegative input-parameter assumption.

  Book citation: `book/FOML/RandomGradientExtrapolation.json#/assumptions/9/math`.
  Quote: `the nonnegative parameters {α_t}, {η_t}, and {τ_t} be given`. -/
  hparam_nonneg : ∀ t : ℕ, 0 ≤ α t ∧ 0 ≤ η t ∧ 0 ≤ τ t
  /-- Prox-computability assumption with the source's arbitrary `g` and strict `η>0` domain.

  Book citation: `book/FOML/RandomGradientExtrapolation.json#/assumptions/5/math`.
  Quote: `argmin_{x∈X}{<g,x>+μν(x)+η V(x^0,x)}` with parameters including `η>0`.

  SOptLib prox candidates were checked: the prox search found variational,
  uniqueness, and descent theorems such as `prox_variational_inequality_of_argmin`,
  `paperMirrorObjective_argmin_unique_of_strict_bregman`, and
  `two_bregman_argmin_descent`; none is the paper's primitive computability datum
  for arbitrary `g`, feasible center, and positive `η`, so the Setup field records
  exactly Eq. (5.2.9)'s source assumption. -/
  hprox_exists :
    ∀ (xCenter g : E) (eta : ℝ), xCenter ∈ X → 0 < eta →
      ∃ z, z ∈ X ∧
        IsMinOn
          (fun x => ⟪g, x⟫_ℝ + μ * ν x +
            eta * (ν x - (ν xCenter + ⟪gradν xCenter, x - xCenter⟫_ℝ))) X z

  /-- Additional repair condition: each component admits a convex whole-space
  extension with its original primal norm, smoothness constant, values and
  selected intrinsic gradient. The zero-L branch uses convexity directly. -/
  component_extension : ∀ i, 0 < Lcomp i →
    Nonempty (SOptLib.ConvexSmoothExtensionOn X
      (fun x => f i x.1) (fun x => (gradFOn i x : E)) primalNorm (Lcomp i))

namespace Setup

variable (S : RandomGradientExtrapolation.Setup ι E)

/-- Ambient totalization of the paper's feasible-carrier component gradient.

Book citation: `book/FOML/RandomGradientExtrapolation.json#/assumptions/2/math`.
Quote: `f_i ... are smooth convex functions with Lipschitz continuous gradients
over X`.

On feasible points this is the stored affine-span-direction gradient. Outside
`X`, the value is irrelevant to the paper and is totalized only because the Lean
algorithmic expressions are ambient functions. -/
noncomputable def gradF (S : RandomGradientExtrapolation.Setup ι E) (i : ι) (x : E) : E := by
  classical
  exact if hx : x ∈ S.X then (S.gradFOn i ⟨x, hx⟩ : E) else 0

@[simp] theorem gradF_of_mem (S : RandomGradientExtrapolation.Setup ι E) (i : ι)
    {x : E} (hx : x ∈ S.X) :
    S.gradF i x = (S.gradFOn i ⟨x, hx⟩ : E) := by
  simp [gradF, hx]

/-- The feasible-carrier component gradient has no affine-normal component. -/
theorem gradF_mem_direction (S : RandomGradientExtrapolation.Setup ι E) (i : ι)
    {x : E} (hx : x ∈ S.X) :
    S.gradF i x ∈ (affineSpan ℝ S.X).direction := by
  simpa [S.gradF_of_mem i hx] using (S.gradFOn i ⟨x, hx⟩).2

/-- Compatibility form of the component within-gradient assumption. -/
theorem hcomponent_hasGradient (S : RandomGradientExtrapolation.Setup ι E)
    (i : ι) (x : E) (hx : x ∈ S.X) :
    HasGradientWithinAt (S.f i) (S.gradF i x) S.X x := by
  simpa [S.gradF_of_mem i hx] using
    S.hcomponent_hasGradient_on i ⟨x, hx⟩

/-- Compatibility form of the component Lipschitz-gradient assumption. -/
theorem hcomponent_smooth (S : RandomGradientExtrapolation.Setup ι E)
    (i : ι) (x y : E) (hx : x ∈ S.X) (hy : y ∈ S.X) :
    affineDirectionDualNorm S.X S.primalNorm (S.gradF i x - S.gradF i y) ≤
      S.Lcomp i * S.primalNorm (x - y) := by
  simpa [S.gradF_of_mem i hx, S.gradF_of_mem i hy] using
    S.hcomponent_smooth_on i ⟨x, hx⟩ ⟨y, hy⟩

/-- Compatibility form of the average smoothness assumption. -/
theorem haverage_smooth (S : RandomGradientExtrapolation.Setup ι E)
    (x y : E) (hx : x ∈ S.X) (hy : y ∈ S.X) :
    affineDirectionDualNorm S.X S.primalNorm
        ((Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ (fun i => S.gradF i x) -
          (Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ (fun i => S.gradF i y)) ≤
      S.Lf * S.primalNorm (x - y) ∧
        S.Lf * S.primalNorm (x - y) ≤
          ((Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ S.Lcomp) *
            S.primalNorm (x - y) := by
  simpa [S.gradF_of_mem, hx, hy] using
    S.haverage_smooth_on ⟨x, hx⟩ ⟨y, hy⟩

/-- Canonical sampled-block stream law for RGEM Algorithm 5.4.

Book citation: `book/FOML/RandomGradientExtrapolation.json#/assumptions/8/math`.
Quote: `Prob{i_t=i}=1/m`.

This replaces the earlier arbitrary `Ω, P, sample` witness fields with the iid
coordinate process on `ℕ → ι`, using `SOptLib.iidStreamLaw` over the finite-uniform
block-index law. -/
noncomputable def P (_S : RandomGradientExtrapolation.Setup ι E) :
    Measure (BlockSamplePath ι) :=
  uniformBlockStreamLaw (ι := ι)

/-- Canonical sampled block `i_t` for RGEM Algorithm 5.4.

Book citation: `book/FOML/RandomGradientExtrapolation.json#/algorithm_spec/steps/0/math`.
Quote: `Prob{i_t=i}=1/m`. -/
def sample (_S : RandomGradientExtrapolation.Setup ι E) (t : ℕ)
    (ω : BlockSamplePath ι) : ι :=
  blockSample (ι := ι) t ω

/-- The finite-uniform average of component function values, `f(x) = m^{-1} ∑ᵢ fᵢ(x)`.

Book citation: `book/FOML/RandomGradientExtrapolation.json#/assumptions/4/parameters/0`.
Quote: `f(x)≡1/m∑_{i=1}^m f_i(x)`.

Aligns with Eq. (5.2.1) and the notation after Eq. (5.2.3). The SOptLib finite
average objective candidates were considered; this local projection names only the
unregularized smooth term needed separately by RGEM's `Q`. -/
noncomputable def fAvg (x : E) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => S.f i x)

/-- Average component smoothness `L = m^{-1}∑ᵢ L_i` from Eq. (5.2.4).

Book citation: `book/FOML/RandomGradientExtrapolation.json#/assumptions/4/parameters/1`.
Quote: `L≡1/m∑_{i=1}^m L_i`.

This replaces the previous Setup witness field `Lavg` plus equality proof.
SOptLib candidates checked: `finiteUniformAverage_smooth_quadratic_upper_bound_of_component_lipschitz`
and `finiteUniformAverage_smooth_quadratic_upper_bound_of_component_lipschitzWithin`
use this scalar as a theorem parameter, and `smoothnessImportanceWeight_ratio_eq_total`
is an importance-sampling algebra lemma; none is the source's named scalar
definition itself. Scanned `SOptLib/Layer0/Objective.lean` and
`SOptLib/Model/StochasticOracle.lean`; the local definition is the literal
Eq. (5.2.4) object. -/
noncomputable def Lavg : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ S.Lcomp

@[simp] theorem Lavg_def :
    S.Lavg = (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ S.Lcomp := by
  rfl

/-- The paper objective `ψ(x) = m^{-1}∑ᵢ fᵢ(x) + μν(x)`.

Book citation: `book/FOML/RandomGradientExtrapolation.json#/setup/problem/math`.
Quote: `ψ(x) := 1/m∑_{i=1}^m f_i(x)+μν(x)`.

Aligns with Eq. (5.2.1). This specializes `SOptLib.finiteAverageRegularizedObjectiveOn`
with regularizer `x ↦ μν(x)`, so the finite-sum objective is not a Setup witness. -/
noncomputable def psi (x : E) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => S.f i x) + S.μ * S.ν x

@[simp] theorem psi_def (x : E) :
    S.psi x = (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ (fun i => S.f i x) + S.μ * S.ν x := by
  rfl

/-- Bregman distance `V(x0,x)` induced by `ν`, as in Eq. (5.2.7).

Book citation: `book/FOML/RandomGradientExtrapolation.json#/key_lemmas/1/statement_math`.
Quote: `V(x^0,x)≥1/2‖x-x^0‖^2`, derived from the paper definition of `V`.

`SOptLib.Model.Bregman` has paper-neutral Bregman primitives, but RGEM's prox and
Theorem 5.4 use the literal `ν(x) - (ν(x0)+<ν'(x0),x-x0>)` form from Eq. (5.2.7),
so this local definition records that paper notation directly. -/
noncomputable def V (x0 x : E) : ℝ :=
  S.ν x - (S.ν x0 + ⟪S.gradν x0, x - x0⟫_ℝ)

/-- Lower bound `V(x0,x) ≥ 1/2 ‖x-x0‖²` derived from Eq. (5.2.3), stated as Eq. (5.2.8). -/
theorem V_lower_bound {x0 x : E} (hx0 : x0 ∈ S.X) (hx : x ∈ S.X) :
    (1 / 2 : ℝ) * S.primalNorm (x - x0) ^ 2 ≤ S.V x0 x := by
  simpa [V, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using S.hν_strong x x0 hx hx0

/-- Three-point identity for RGEM's literal Bregman distance. -/
theorem V_three_point_identity (a b c : E) :
    S.V a c =
      S.V a b + ⟪S.gradν b - S.gradν a, c - b⟫_ℝ + S.V b c := by
  unfold V
  have hsplit : c - a = (b - a) + (c - b) := by
    abel
  rw [hsplit, inner_add_right, inner_sub_left]
  ring

/-- Endpoint-feasible segment derivative of RGEM's literal Bregman distance.

This is the source-backed derivative law needed in Lemma 3.5: the endpoint is
feasible, so convexity of `X` keeps the segment inside the within-gradient domain
where `hν_hasGradientWithinAt` applies. -/
theorem V_segment_difference_hasDerivWithinAt_zero
    (a z u : E) (hz : z ∈ S.X) (hu : u ∈ S.X) :
    let d : E := u - z
    let β : ℝ → ℝ := fun t =>
      if _ht : t ∈ Set.Icc (0 : ℝ) 1 then
        S.V a (AffineMap.lineMap z u t) - S.V a z
      else 0
    HasDerivWithinAt β
      ⟪S.gradν z - S.gradν a, d⟫_ℝ
      (Set.Icc (0 : ℝ) 1) 0 := by
  simpa [V, carrierBregmanFormula, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
    SOptLib.bregmanFormula_segment_difference_hasDerivWithinAt_zero
      (X := S.X) (nu := S.ν) (grad := S.gradν) S.hX_convex
      (a := a) (z := z) (u := u) hz hu (S.hν_hasGradientWithinAt z hz)

/-- The paper's dual norm `‖·‖_*` induced by the stated primal norm on the
feasible affine-hull direction.

Book citation: `book/FOML/RandomGradientExtrapolation.json#/assumptions/1/math`.
Quote: `‖∇ f_i(x_1)-∇ f_i(x_2)‖_*≤L_i‖x_1-x_2‖`.

Aligns with Eq. (5.2.2) and Eq. (5.2.4). Since the component gradients are
represented on `X`, the dual support vectors live in the direction of
`affineSpan ℝ S.X`, not in unrelated ambient directions. -/
noncomputable def dualNorm (z : E) : ℝ :=
  affineDirectionDualNorm S.X S.primalNorm z

@[simp] theorem dualNorm_def (z : E) :
    S.dualNorm z = affineDirectionDualNorm S.X S.primalNorm z := by
  rfl

private theorem dualNorm_sq_sub_comm (a b : E) :
    S.dualNorm (a - b) ^ 2 = S.dualNorm (b - a) ^ 2 := by
  have hset :
      {r : ℝ |
        ∃ d : E, d ∈ (affineSpan ℝ S.X).direction ∧
          S.primalNorm d ≤ 1 ∧ r = |⟪a - b, d⟫_ℝ|} =
      {r : ℝ |
        ∃ d : E, d ∈ (affineSpan ℝ S.X).direction ∧
          S.primalNorm d ≤ 1 ∧ r = |⟪b - a, d⟫_ℝ|} := by
    ext r
    constructor
    · intro hr
      rcases hr with ⟨d, hd, hpd, rfl⟩
      refine ⟨d, hd, hpd, ?_⟩
      have hba : b - a = -(a - b) := by abel
      rw [hba, inner_neg_left, abs_neg]
    · intro hr
      rcases hr with ⟨d, hd, hpd, rfl⟩
      refine ⟨d, hd, hpd, ?_⟩
      have hab : a - b = -(b - a) := by abel
      rw [hab, inner_neg_left, abs_neg]
  simp [dualNorm, affineDirectionDualNorm, hset]

/-- Average smoothness (5.2.4), stated using the canonical scalar `S.Lavg`.

The raw Setup assumption stores the displayed inequality with `L` unfolded; this
theorem restores the source notation after `Lavg` was changed from a field to a
definition. -/
theorem average_smooth {x y : E} (hx : x ∈ S.X) (hy : y ∈ S.X) :
    S.dualNorm
        ((Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ (fun i => S.gradF i x) -
          (Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ (fun i => S.gradF i y)) ≤
      S.Lf * S.primalNorm (x - y) ∧
        S.Lf * S.primalNorm (x - y) ≤ S.Lavg * S.primalNorm (x - y) := by
  simpa [dualNorm, Lavg] using S.haverage_smooth x y hx hy

/-- The canonical sampled-block coordinate is measurable. -/
theorem sample_measurable (t : ℕ) : Measurable (S.sample t) := by
  simpa [sample] using blockSample_measurable (ι := ι) t

/-- The canonical sampled-block stream is iid under `S.P`. -/
theorem sample_iIndepFun :
    ProbabilityTheory.iIndepFun S.sample S.P := by
  simpa [P, sample] using uniformBlockStream_iIndepFun (ι := ι)

/-- The one-step block law is uniform over the finite component set. -/
theorem sample_uniform (t : ℕ) (i : ι) :
    S.P ((S.sample t) ⁻¹' ({i} : Set ι)) =
      ENNReal.ofReal ((Fintype.card ι : ℝ)⁻¹) :=
  by
    simpa [P, sample] using uniformBlockStream_singleton (ι := ι) t i

/-- Strict sampled-block prefix σ-algebra generated by `i_0, ..., i_{t-1}`.

This is the source-facing conditioning object for Lemma 5.9. `SOptLib.filtration`
was checked and is reused below; the coordinate process is now the canonical iid
stream over `ℕ → ι`, not an arbitrary marginally-uniform witness. -/
@[reducible] def samplePrefixSigma (t : ℕ) : MeasurableSpace (BlockSamplePath ι) :=
  ⨆ j < t, MeasurableSpace.comap (S.sample j)
    (by infer_instance : MeasurableSpace ι)

/-- Paper strict-past block σ-algebra generated by `i_1, ..., i_{t-1}`.

Lemma 5.9 conditions on the strict paper past `i_1, ..., i_{t-1}`. The SOptLib
filtration primitive is zero-based and still used for generated-process infrastructure;
this source-facing object records the paper's one-based conditioning boundary
literally. -/
@[reducible] def paperStrictPastSigma (t : ℕ) :
    MeasurableSpace (BlockSamplePath ι) :=
  ⨆ (j : ℕ) (_hj : 1 ≤ j ∧ j < t), MeasurableSpace.comap (S.sample j)
    (by infer_instance : MeasurableSpace ι)

/-- The paper strict-past σ-algebra is generated by the same strict-past index set
used by the iid freshness theorem. -/
private theorem paperStrictPastSigma_le_generated_pastSet (t : ℕ) :
    S.paperStrictPastSigma t ≤
      (⨆ q ∈ ({j : ℕ | 1 ≤ j ∧ j < t} : Set ℕ),
        MeasurableSpace.comap (S.sample q)
          (by infer_instance : MeasurableSpace ι)) := by
  dsimp [paperStrictPastSigma]
  refine iSup_le ?_
  intro j
  refine iSup_le ?_
  intro hj
  exact le_iSup_of_le j (le_iSup_of_le hj le_rfl)

/-- Finite-key representation of the paper strict-past conditioning sigma algebra.

Aligns with Lan Lemma 5.9's phrase "given `i_1,...,i_{t-1}`". Search audit:
checked SOptLib `sampleBlockMeasurableSpace`,
`strictPastSampleBlockMeasurableSpace_coordinate_measurable`, and Mathlib
`measurable_pi_lambda`; those provide finite block generators or coordinate
measurability, but not this literal one-based `paperStrictPastSigma` equality. -/
private theorem paperStrictPastSigma_eq_strictPastWindow_comap (t : ℕ) :
    S.paperStrictPastSigma t =
      MeasurableSpace.comap
        (fun ω : BlockSamplePath ι => fun r : Fin (t - 1) => S.sample (1 + r.1) ω)
        (by infer_instance : MeasurableSpace (Fin (t - 1) → ι)) := by
  simpa [paperStrictPastSigma, SOptLib.sampleWindow] using
    (SOptLib.sampleWindowMeasurableSpace_eq_comap
      (xi := S.sample) (offset := 1) (stop := t))

/-- The paper strict-past index set does not contain the current sampled block time. -/
private theorem paperStrictPastSet_disjoint_current (t : ℕ) :
    Disjoint ({j : ℕ | 1 ≤ j ∧ j < t} : Set ℕ) ({t} : Set ℕ) := by
  rw [Set.disjoint_singleton_right]
  intro htmem
  exact Nat.lt_irrefl t htmem.2

/-- Source-facing fresh conditional block law behind Lemma 5.9.

Book citation: `book/FOML/RandomGradientExtrapolation.json#/key_lemmas/3/statement_math`.
Quote: `E_t denotes the conditional expectation w.r.t. i_t given i_1,...,i_{t-1}`.

Lemma 5.9 conditions on `i_1, ..., i_{t-1}` and uses
`Prob_t {i_t = i} = 1/m`. This canonical Lean boundary encodes that as
independence of the current block σ-algebra from the strict sampled-block prefix,
together with the finite-uniform singleton law. -/
def FreshConditionalBlockSampling : Prop :=
  ∀ (t : ℕ) (i : ι),
    Indep (S.paperStrictPastSigma t)
        (MeasurableSpace.comap (S.sample t)
          (by infer_instance : MeasurableSpace ι)) S.P ∧
      S.P ((S.sample t) ⁻¹' ({i} : Set ι)) =
        ENNReal.ofReal ((Fintype.card ι : ℝ)⁻¹)

/-- Natural filtration generated by the canonical sampled block prefix. -/
noncomputable def sampleFiltration :
    Filtration ℕ (by infer_instance : MeasurableSpace (BlockSamplePath ι)) :=
  SOptLib.filtration S.sample S.sample_measurable

/-- The current block draw is independent of the generated strict-past filtration. -/
theorem sample_current_indep_prefix (t : ℕ) :
    Indep ((S.sampleFiltration).seq t)
      (MeasurableSpace.comap (S.sample t)
        (by infer_instance : MeasurableSpace ι)) S.P := by
  simpa [sampleFiltration] using
    samplePrefixFiltration_indep_current
      (ξ := S.sample) (μ := S.P)
      S.sample_measurable S.sample_iIndepFun t

/-- Fresh-uniform block property used to realize Lemma 5.9's `Prob_t`.

The conditional-expectation identities are later proof obligations; object-layer
wise, freshness now follows from the canonical iid sampled-block stream rather
than from a marginal-uniform arbitrary process. -/
theorem currentBlock_fresh_uniform (t : ℕ) (i : ι) :
    Indep (S.paperStrictPastSigma t)
        (MeasurableSpace.comap (S.sample t)
          (by infer_instance : MeasurableSpace ι)) S.P ∧
      S.P ((S.sample t) ⁻¹' ({i} : Set ι)) =
        ENNReal.ofReal ((Fintype.card ι : ℝ)⁻¹) :=
  by
    -- The proof is the one-based strict-past specialization of the iid prefix
    -- independence theorem used by `sample_current_indep_prefix`.
    refine ⟨?_, S.sample_uniform t i⟩
    let pastSet : Set ℕ := {j | 1 ≤ j ∧ j < t}
    have hpast_disj : Disjoint pastSet ({t} : Set ℕ) := by
      change Disjoint ({j : ℕ | 1 ≤ j ∧ j < t} : Set ℕ) ({t} : Set ℕ)
      exact paperStrictPastSet_disjoint_current t
    have hstrict_le :
        S.paperStrictPastSigma t ≤
          (⨆ q ∈ pastSet,
            MeasurableSpace.comap (S.sample q)
              (by infer_instance : MeasurableSpace ι)) := by
      exact S.paperStrictPastSigma_le_generated_pastSet t
    exact SOptLib.iIndepFun_indep_strictPast_singleton
      (xi := S.sample) (mu := S.P)
      (hxi_meas := S.sample_measurable)
      (hxi_iIndep := S.sample_iIndepFun)
      (strictPast := S.paperStrictPastSigma t)
      (pastSet := pastSet) (current := t)
      hpast_disj hstrict_le

/-- Lemma 5.9's fresh conditional sampled-block law.

Algorithm 5.4 says to choose the current block by `Prob{i_t=i}=1/m`; Lemma 5.9's
proof uses the conditional form `Prob_t{i_t=i}=1/m` given the strict sampled-block
past. The canonical iid coordinate stream supplies that freshness without adding
it to Proposition 5.6 or Theorem 5.4 theorem heads. -/
theorem freshConditionalBlockSampling : S.FreshConditionalBlockSampling := by
  intro t i
  simpa [FreshConditionalBlockSampling] using S.currentBlock_fresh_uniform t i

/-- Well-definedness boundary for a Mathlib conditional expectation used as paper `E_t`.

Mathlib's `condExp` is total and returns `0` outside its sigma-finite/integrable
domain. The paper conditional expectations in Lemmas 5.9 and 5.11 are therefore
modeled through this predicate, so the original lemma heads assert the identities
together with the well-definedness facts instead of relying on fallback values. -/
def conditionalExpectationWellDefined {Ω F : Type*} [m0 : MeasurableSpace Ω]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : Measure Ω) (m : MeasurableSpace Ω) (Z : Ω → F) : Prop :=
  @SOptLib.ConditionalExpectation.conditionalExpectationWellDefined Ω F m0 _ P m Z

/-- Source-facing conditional-expectation equality.

No SOptLib match: searched "conditional expectation well defined condExp" and
scanned `SOptLib/Glue/Probability.lean` and `SOptLib/Glue/Martingale.lean`;
they provide proof lemmas over raw `condExp`, while Lemmas 5.9 and 5.11 need a
paper-facing object that records the non-fallback well-definedness boundary. -/
def conditionalExpectationEq {Ω F : Type*} [m0 : MeasurableSpace Ω]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (P : Measure Ω) (m : MeasurableSpace Ω) (Z target : Ω → F) : Prop :=
  @SOptLib.ConditionalExpectation.conditionalExpectationEq Ω F m0 _ _ _ P m Z target

/-- A paper conditional-expectation identity gives equality of total expectations.

Search audit: considered SOptLib `integral_eq_zero_of_condExp_ae_eq_zero`,
`expectationEq.expectation_eq`, and Mathlib `MeasureTheory.integral_condExp`.
The SOptLib facts either handle zero conditional expectations or already-packaged
unconditional expectation equalities, while Lemma 5.10 needs this file's
`conditionalExpectationEq` wrapper from Lemma 5.9. -/
private theorem conditionalExpectationEq_expectation_eq {Ω F : Type*}
    [m0 : MeasurableSpace Ω]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {P : Measure Ω} {m : MeasurableSpace Ω} {Z target : Ω → F}
    (h : @conditionalExpectationEq Ω F m0 _ _ _ P m Z target) :
    @SOptLib.expectation Ω F m0 _ _ P Z =
      @SOptLib.expectation Ω F m0 _ _ P target := by
  exact
    @SOptLib.ConditionalExpectation.conditionalExpectationEq.expectation_eq
      Ω F m0 _ _ _ P m Z target h

/-- Average of an extrapolated gradient table.

Book citation: `book/FOML/RandomGradientExtrapolation.json#/algorithm_spec/steps/2/math`.
Quote: `1/m∑_i \tilde y_i^t` appears in the prox objective (5.2.50).

This is only the finite-uniform vector average used inside the source formulas;
it is not an independent Setup datum. -/
noncomputable def tableAverage (y : ι → E) : E :=
  (Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ (fun i => y i)


/-- The objective minimized in the RGEM primal prox step (5.2.50).

Book citation: `book/FOML/RandomGradientExtrapolation.json#/algorithm_spec/steps/2/math`.
Quote: `x^t=argmin_{x∈X}{<1/m∑_i \tilde y_i^t,x>+μν(x)+η_t V(x^{t-1},x)}`. -/
noncomputable def proxObjective (t : ℕ) (xPrev : E) (yTilde : ι → E) (x : E) : ℝ :=
  ⟪tableAverage yTilde, x⟫_ℝ + S.μ * S.ν x + S.η t * S.V xPrev x

@[simp] theorem proxObjective_def (t : ℕ) (xPrev : E) (yTilde : ι → E) (x : E) :
    S.proxObjective t xPrev yTilde x =
      ⟪tableAverage yTilde, x⟫_ℝ + S.μ * S.ν x + S.η t * S.V xPrev x := by
  rfl

/-- Positive-stepsize well-definedness of the prox call displayed in Eq. (5.2.50).

Eq. (5.2.9) states prox computability for `η > 0`; this theorem deliberately
does not manufacture a prox point outside that source-backed domain. -/
theorem proxPoint_exists_of_eta_pos (t : ℕ) (xPrev : E) (yTilde : ι → E)
    (hxPrev : xPrev ∈ S.X) (hη : 0 < S.η t) :
    ∃ z, z ∈ S.X ∧ IsMinOn (S.proxObjective t xPrev yTilde) S.X z := by
  simpa [proxObjective, tableAverage, V] using
    S.hprox_exists xPrev (tableAverage yTilde) (S.η t) hxPrev hη

/-- Canonical RGEM prox point selected from the argmin in Eq. (5.2.50).

The candidates `SOptLib.proxStep` and `SOptLib.IsCompositeProxStepOn` were checked.
They model generic mirror/composite prox steps, but RGEM needs the literal finite
extrapolated-gradient objective from Eq. (5.2.50) over the ambient feasible set `X`;
therefore this selector specializes the paper objective via `Classical.choose`
from Eq. (5.2.9)'s positive-eta computability theorem, rather than accepting a
prox map, an iterate witness, or an eta-free argmin existence theorem as Setup
data. -/
noncomputable def proxPoint (t : ℕ) (xPrev : E) (yTilde : ι → E)
    (hxPrev : xPrev ∈ S.X) (hη : 0 < S.η t) : E :=
  Classical.choose (S.proxPoint_exists_of_eta_pos t xPrev yTilde hxPrev hη)

theorem proxPoint_mem (t : ℕ) (xPrev : E) (yTilde : ι → E)
    (hxPrev : xPrev ∈ S.X) (hη : 0 < S.η t) :
    S.proxPoint t xPrev yTilde hxPrev hη ∈ S.X :=
  (Classical.choose_spec (S.proxPoint_exists_of_eta_pos t xPrev yTilde hxPrev hη)).1

theorem proxPoint_isMinOn
    (t : ℕ) (xPrev : E) (yTilde : ι → E)
    (hxPrev : xPrev ∈ S.X) (hη : 0 < S.η t) :
    IsMinOn (S.proxObjective t xPrev yTilde) S.X
      (S.proxPoint t xPrev yTilde hxPrev hη) :=
  (Classical.choose_spec (S.proxPoint_exists_of_eta_pos t xPrev yTilde hxPrev hη)).2

/-- Auxiliary point `x̂_i^t = (1+τ_t)^{-1}(x^t+τ_t x_i^{t-1})`, Eq. (5.2.57).

Book citation: `book/FOML/RandomGradientExtrapolation.json#/algorithm_spec/parameters/1/math`.
Quote: `\hat x_i^t=(1+τ_t)^{-1}(x^t+τ_t x_i^{t-1})`.

No SOptLib candidate matched this exact RGEM auxiliary block point; this is the
literal source formula. -/
noncomputable def auxiliaryPoint (t : ℕ) (x blockPrev : E) : E :=
  ((1 : ℝ) + S.τ t)⁻¹ • (x + S.τ t • blockPrev)

@[simp] theorem auxiliaryPoint_def (t : ℕ) (x blockPrev : E) :
    S.auxiliaryPoint t x blockPrev = (1 + S.τ t)⁻¹ • (x + S.τ t • blockPrev) := by
  rfl

/-- Rearranged form of Eq. (5.2.57) used in the Lemma 5.10 Q expansion.

Search audit: checked target `AuxiliaryPointIdentity_Eq_5_2_57` and SOptLib
`acceleratedAuxiliaryPoint_def`/`relaxedMemoryRefreshPoint`; those expose the
forward averaged form, while Lemma 5.10 needs the solved form
`x = (1 + τ_t) x_hat - τ_t x_i^{t-1}`. -/
private theorem auxiliaryPoint_solve (t : ℕ) (x blockPrev : E) :
    x = (1 + S.τ t) • S.auxiliaryPoint t x blockPrev - S.τ t • blockPrev := by
  have hτ : 0 ≤ S.τ t := (S.hparam_nonneg t).2.2
  have hne : (1 + S.τ t : ℝ) ≠ 0 := by
    nlinarith
  simpa [S.auxiliaryPoint_def] using
    (SOptLib.relaxedMemoryRefreshPoint_solve (tau := S.τ t) hne x blockPrev)

/-- Random block point update from Eq. (5.2.51).

Book citation: `book/FOML/RandomGradientExtrapolation.json#/algorithm_spec/steps/3/math`.
Quote: `x_i^t=(1+τ_t)^{-1}(x^t+τ_t x_i^{t-1})` if `i=i_t`, otherwise `x_i^{t-1}`. -/
noncomputable def blockPointUpdate (t : ℕ) (selected : ι) (x : E) (blockPrev : ι → E) :
    ι → E :=
  fun i => if i = selected then S.auxiliaryPoint t x (blockPrev i) else blockPrev i

@[simp] theorem blockPointUpdate_selected (t : ℕ) (selected : ι) (x : E)
    (blockPrev : ι → E) :
    S.blockPointUpdate t selected x blockPrev selected =
      S.auxiliaryPoint t x (blockPrev selected) := by
  simp [blockPointUpdate]

theorem blockPointUpdate_other (t : ℕ) {selected i : ι} (h : i ≠ selected) (x : E)
    (blockPrev : ι → E) :
    S.blockPointUpdate t selected x blockPrev i = blockPrev i := by
  simp [blockPointUpdate, h]

/-- Auxiliary gradient `ŷ_i^t = ∇f_i(x̂_i^t)`, Eq. (5.2.58).

Book citation: `book/FOML/RandomGradientExtrapolation.json#/algorithm_spec/parameters/2/math`.
Quote: `\hat y_i^t=∇f_i(\hat x_i^t)`. -/
noncomputable def auxiliaryGradient (t : ℕ) (x : E) (blockPrev : ι → E) (i : ι) : E :=
  S.gradF i (S.auxiliaryPoint t x (blockPrev i))

/-- Positive batch-size domain for Algorithm 5.5 stochastic RGEM.

Book citation: `book/FOML/RandomGradientExtrapolation.json#/key_lemmas/4/statement_math`.
Quote: `B_t^{-1}∑_{j=1}^{B_t} G_i(x_i^t,ξ_{i,t}^j)`.

The PDF calls `B_t` the batch size used to compute (5.2.85), so positivity is a
well-definedness domain for the displayed denominator, not a deterministic RGEM
Setup field. -/
def StochasticBatchDomain (_S : RandomGradientExtrapolation.Setup ι E) (B : ℕ → ℕ) : Prop :=
  ∀ t : ℕ, 1 ≤ t → 0 < B t

/-- Product law for Algorithm 5.5 stochastic paths.

The block component is the canonical finite-uniform iid stream from Algorithm 5.4;
the second component is an explicit law for the oracle-sample table. The paper
conditions on the table values in Lemma 5.11, so this object keeps those samples
as random variables instead of theorem-local constants. -/
noncomputable def stochasticRunLaw {Ξ : Type*} [MeasurableSpace Ξ]
    (S : RandomGradientExtrapolation.Setup ι E)
    (Pξ : Measure (StochasticSampleTable ι Ξ)) :
    Measure (StochasticRunPath ι Ξ) :=
  S.P.prod Pξ

/-- Block coordinate `i_t` on the stochastic Algorithm 5.5 path space. -/
def stochasticBlockSample {Ξ : Type*}
    (S : RandomGradientExtrapolation.Setup ι E) (t : ℕ)
    (ω : StochasticRunPath ι Ξ) : ι :=
  S.sample t ω.1

/-- Oracle-sample coordinate `ξ_{i,t}^j` on the stochastic Algorithm 5.5 path space. -/
def stochasticOracleSample {Ξ : Type*}
    (_S : RandomGradientExtrapolation.Setup ι E) (i : ι) (t j : ℕ)
    (ω : StochasticRunPath ι Ξ) : Ξ :=
  ω.2 i t j

/-- Component stochastic oracle kernel `G_i(x,ξ)` used in Algorithm 5.5.

Book citation: `book/FOML/RandomGradientExtrapolation.json#/key_lemmas/4/statement_math`.
Quote: `B_t^{-1}∑_{j=1}^{B_t} G_i(x_i^t,ξ_{i,t}^j)`.

Aligns with the source's component-indexed stochastic oracle. The SOptLib
candidates `oracleKernel`, `stagedOracleValue`, and `miniBatchOracleAverage` were
checked: `oracleKernel` is the reusable sampled-kernel primitive, while
`stagedOracleValue` and `miniBatchOracleAverage` use a single time-indexed sample
stream rather than RGEM's explicit component/time/batch table. -/
def stochasticOracleKernel {Ξ : Type*}
    (_S : RandomGradientExtrapolation.Setup ι E) (G : ι → E → Ξ → E)
    (i : ι) : E → Ξ → E :=
  fun x ξ => G i x ξ

@[simp] theorem stochasticOracleKernel_apply {Ξ : Type*}
    (G : ι → E → Ξ → E) (i : ι) (x : E) (ξ : Ξ) :
    S.stochasticOracleKernel G i x ξ = G i x ξ := by
  rfl

/-- Sampled stochastic oracle value
`ω ↦ G_i(x, ξ_{i,t}^j(ω))`, routed through `SOptLib.oracleKernel`. -/
def stochasticOracleValue {Ξ : Type*} [MeasurableSpace Ξ]
    (S : RandomGradientExtrapolation.Setup ι E) (G : ι → E → Ξ → E)
    (i : ι) (t j : ℕ) (x : E) : StochasticRunPath ι Ξ → E :=
  SOptLib.oracleKernel (S.stochasticOracleKernel G i)
    (S.stochasticOracleSample i t j) x

@[simp] theorem stochasticOracleValue_apply {Ξ : Type*} [MeasurableSpace Ξ]
    (G : ι → E → Ξ → E) (i : ι) (t j : ℕ) (x : E)
    (ω : StochasticRunPath ι Ξ) :
    S.stochasticOracleValue G i t j x ω =
      G i x (S.stochasticOracleSample i t j ω) := by
  rfl

/-- Current stochastic batch table `ξ_1^t,...,ξ_m^t` used in Lemma 5.11.

This is the explicit conditioning object printed in Lemma 5.11. -/
def currentStochasticBatch {Ξ : Type*}
    (S : RandomGradientExtrapolation.Setup ι E) (t : ℕ)
    (ω : StochasticRunPath ι Ξ) : ι → ℕ → Ξ :=
  fun i j => S.stochasticOracleSample i t j ω

/-- Lemma 5.11 conditioning σ-algebra for the stochastic RGEM path.

This is the sigma algebra printed in the stochastic Lemma 5.11 statement:
strict sampled-block past together with the current stochastic batch table
`ξ_1^t,...,ξ_m^t`.  It is intentionally separate from the internal
`stochasticConditioningSigma` below, whose stronger oracle-history component is
used to prove generated-process adaptedness before a tower/conditioning bridge
returns to the printed statement. -/
@[reducible] def stochasticPaperConditioningSigma {Ξ : Type*} [MeasurableSpace Ξ]
    (S : RandomGradientExtrapolation.Setup ι E) (t : ℕ) :
    MeasurableSpace (StochasticRunPath ι Ξ) :=
  MeasurableSpace.comap Prod.fst (S.paperStrictPastSigma t) ⊔
    MeasurableSpace.comap (S.currentStochasticBatch (Ξ := Ξ) t) inferInstance

/-- Internal Lemma 5.11 conditioning σ-algebra for generated-process payloads.

The PDF states this as conditional probability "with respect to `i_t`" given the
strict block past and the stochastic samples used by the stochastic update.  In
the formal product path, the generated previous state also depends on earlier
oracle samples, so the faithful sigma algebra for conditioning only over the
current block fixes the oracle table component and the strict block past.  This
contains the printed current batch `ξ_1^t,...,ξ_m^t` while avoiding the too-small
current-batch-only encoding that made `state^{t-1}` non-adapted. -/
@[reducible] def stochasticConditioningSigma {Ξ : Type*} [MeasurableSpace Ξ]
    (S : RandomGradientExtrapolation.Setup ι E) (t : ℕ) :
    MeasurableSpace (StochasticRunPath ι Ξ) :=
  MeasurableSpace.comap Prod.fst (S.paperStrictPastSigma t) ⊔
    MeasurableSpace.comap Prod.snd
      (by infer_instance : MeasurableSpace (StochasticSampleTable ι Ξ))

/-- The corrected Lemma 5.11 conditioning sigma is a genuine sub-sigma algebra
of the ambient stochastic path space, not a fallback object. -/
private theorem stochasticConditioningSigma_le {Ξ : Type*} [MeasurableSpace Ξ]
    (t : ℕ) :
    S.stochasticConditioningSigma (Ξ := Ξ) t ≤
      (by infer_instance : MeasurableSpace (StochasticRunPath ι Ξ)) := by
  classical
  dsimp [stochasticConditioningSigma]
  refine sup_le ?_ ?_
  · have hpast_le :
        S.paperStrictPastSigma t ≤
          (by infer_instance : MeasurableSpace (BlockSamplePath ι)) := by
      rw [S.paperStrictPastSigma_eq_strictPastWindow_comap t]
      exact (show Measurable
        (fun ω : BlockSamplePath ι => fun r : Fin (t - 1) => S.sample (1 + r.1) ω) from
          @measurable_pi_lambda (BlockSamplePath ι) (Fin (t - 1)) (fun _ => ι)
            (by infer_instance : MeasurableSpace (BlockSamplePath ι)) (fun _ => by infer_instance)
            (fun ω : BlockSamplePath ι => fun r : Fin (t - 1) => S.sample (1 + r.1) ω)
            (fun r : Fin (t - 1) => S.sample_measurable (1 + r.1))).comap_le
    exact (measurable_fst.mono le_rfl hpast_le).comap_le
  · exact measurable_snd.comap_le

/-- The whole oracle table is available under the corrected Lemma 5.11
conditioning sigma. This is the first adaptedness bridge needed for the generated
stochastic payloads; the generated previous state can now be proved from block
strict-past determinism plus this oracle-history measurability, rather than from
the insufficient current-batch-only sigma. -/
private theorem stochasticOracleTable_measurable_conditioning {Ξ : Type*}
    [MeasurableSpace Ξ] (t : ℕ) :
    Measurable[S.stochasticConditioningSigma (Ξ := Ξ) t]
      (fun ω : StochasticRunPath ι Ξ => ω.2) := by
  exact
    (show Measurable[
        MeasurableSpace.comap Prod.snd
          (by infer_instance : MeasurableSpace (StochasticSampleTable ι Ξ))]
        (fun ω : StochasticRunPath ι Ξ => ω.2) from
      Measurable.of_comap_le le_rfl).sup_of_right

/-- The printed current stochastic batch is a measurable projection of the
oracle-history part of the corrected Lemma 5.11 conditioning sigma. -/
private theorem currentStochasticBatch_measurable_conditioning {Ξ : Type*}
    [MeasurableSpace Ξ] (t : ℕ) :
    Measurable[S.stochasticConditioningSigma (Ξ := Ξ) t]
      (S.currentStochasticBatch (Ξ := Ξ) t) := by
  classical
  have htable := S.stochasticOracleTable_measurable_conditioning (Ξ := Ξ) t
  have hbatch : Measurable
      (fun ξ : StochasticSampleTable ι Ξ => fun i : ι => fun j : ℕ => ξ i t j) := by
    exact measurable_pi_lambda _ (fun i =>
      measurable_pi_lambda _ (fun j =>
        (measurable_pi_apply j).comp
          ((measurable_pi_apply t).comp (measurable_pi_apply i))))
  simpa [currentStochasticBatch, stochasticOracleSample, Function.comp_def] using hbatch.comp htable

/-- The printed Lemma 5.11 conditioning sigma is contained in the internal
oracle-history conditioning sigma. -/
private theorem stochasticPaperConditioningSigma_le_conditioningSigma {Ξ : Type*}
    [MeasurableSpace Ξ] (t : ℕ) :
    S.stochasticPaperConditioningSigma (Ξ := Ξ) t ≤
      S.stochasticConditioningSigma (Ξ := Ξ) t := by
  classical
  dsimp [stochasticPaperConditioningSigma, stochasticConditioningSigma]
  refine sup_le ?_ ?_
  · exact le_sup_left
  · exact (S.currentStochasticBatch_measurable_conditioning (Ξ := Ξ) t).comap_le

/-- Stochastic batch-gradient average `B_t^{-1} ∑_{j=1}^{B_t} G_i(x,ξ_{i,t}^j)`.

Book citation: `book/FOML/RandomGradientExtrapolation.json#/key_lemmas/4/statement_math`.
Quote: `B_t^{-1}∑_{j=1}^{B_t}G_i(x_i^t,ξ_{i,t}^j)`.

Aligns with Eqs. (5.2.85) and (5.2.86). `SOptLib.miniBatchOracleAverage` was
checked; it packages process-indexed mini-batch oracle values, while RGEM's
source formulas carry the explicit component/time sample table `ξ_{i,t}^j`.
The `StochasticBatchDomain` argument exposes the source's batch-size domain and
prevents the displayed denominator from being read through Lean's total inverse
when `B_t = 0`. -/
noncomputable def stochasticBatchGradient (S : RandomGradientExtrapolation.Setup ι E) {Ξ : Type*}
    (B : ℕ → ℕ) (hB : S.StochasticBatchDomain B) (G : ι → E → Ξ → E)
    (ξ : ι → ℕ → ℕ → Ξ) (t : ℕ) (ht : 1 ≤ t) (i : ι) (x : E) : E :=
  have _hBt_pos : 0 < B t := hB t ht
  ((B t : ℝ)⁻¹) •
    Finset.sum (Finset.Icc 1 (B t)) (fun j => S.stochasticOracleKernel G i x (ξ i t j))

/-- Stochastic batch-gradient random variable from Eq. (5.2.85).

This is the path-level version of `stochasticBatchGradient`: every summand is the
canonical sampled oracle value `SOptLib.oracleKernel (G_i) ξ_{i,t}^j x`. -/
noncomputable def stochasticBatchGradientValue
    (S : RandomGradientExtrapolation.Setup ι E) {Ξ : Type*} [MeasurableSpace Ξ]
    (B : ℕ → ℕ) (hB : S.StochasticBatchDomain B) (G : ι → E → Ξ → E)
    (t : ℕ) (ht : 1 ≤ t) (i : ι) (x : E) : StochasticRunPath ι Ξ → E :=
  fun ω =>
    have _hBt_pos : 0 < B t := hB t ht
    ((B t : ℝ)⁻¹) •
      Finset.sum (Finset.Icc 1 (B t))
        (fun j => S.stochasticOracleValue G i t j x ω)

theorem stochasticBatchGradientValue_apply
    (S : RandomGradientExtrapolation.Setup ι E) {Ξ : Type*} [MeasurableSpace Ξ]
    (B : ℕ → ℕ) (hB : S.StochasticBatchDomain B) (G : ι → E → Ξ → E)
    (t : ℕ) (ht : 1 ≤ t) (i : ι) (x : E) (ω : StochasticRunPath ι Ξ) :
    S.stochasticBatchGradientValue B hB G t ht i x ω =
      S.stochasticBatchGradient B hB G
        (fun i n j => S.stochasticOracleSample i n j ω) t ht i x := by
  rfl

/-- Stochastic auxiliary gradient `ŷ_i^t` from Eq. (5.2.86). -/
noncomputable def stochasticAuxiliaryGradient (S : RandomGradientExtrapolation.Setup ι E) {Ξ : Type*}
    (B : ℕ → ℕ) (hB : S.StochasticBatchDomain B) (G : ι → E → Ξ → E)
    (ξ : ι → ℕ → ℕ → Ξ) (t : ℕ) (ht : 1 ≤ t) (x : E)
    (blockPrev : ι → E) (i : ι) : E :=
  S.stochasticBatchGradient B hB G ξ t ht i (S.auxiliaryPoint t x (blockPrev i))

/-- Stochastic component-gradient table update from Eq. (5.2.85). -/
noncomputable def stochasticComponentGradientUpdate (S : RandomGradientExtrapolation.Setup ι E)
    {Ξ : Type*}
    (B : ℕ → ℕ) (hB : S.StochasticBatchDomain B) (G : ι → E → Ξ → E)
    (ξ : ι → ℕ → ℕ → Ξ) (t : ℕ) (ht : 1 ≤ t) (selected : ι)
    (blockNext : ι → E) (yPrev : ι → E) : ι → E :=
  fun i =>
    if i = selected then
      S.stochasticBatchGradient B hB G ξ t ht i (blockNext i)
    else
      yPrev i

@[simp] theorem stochasticComponentGradientUpdate_selected {Ξ : Type*}
    (B : ℕ → ℕ) (hB : S.StochasticBatchDomain B) (G : ι → E → Ξ → E)
    (ξ : ι → ℕ → ℕ → Ξ) (t : ℕ) (ht : 1 ≤ t) (selected : ι)
    (blockNext yPrev : ι → E) :
    S.stochasticComponentGradientUpdate B hB G ξ t ht selected blockNext yPrev selected =
      S.stochasticBatchGradient B hB G ξ t ht selected (blockNext selected) := by
  simp [stochasticComponentGradientUpdate]

theorem stochasticComponentGradientUpdate_other {Ξ : Type*}
    (B : ℕ → ℕ) (hB : S.StochasticBatchDomain B) (G : ι → E → Ξ → E)
    (ξ : ι → ℕ → ℕ → Ξ) (t : ℕ) (ht : 1 ≤ t) {selected i : ι}
    (h : i ≠ selected) (blockNext yPrev : ι → E) :
    S.stochasticComponentGradientUpdate B hB G ξ t ht selected blockNext yPrev i =
      yPrev i := by
  simp [stochasticComponentGradientUpdate, h]

/-- Feasibility invariant for the RGEM state tables. -/
def StateFeasible (s : State ι E) : Prop :=
  s.x ∈ S.X ∧ ∀ i, s.blockX i ∈ S.X

/-- Helper equation characterization for a deterministic RGEM process.

The exported Algorithm 5.4 process is `positiveEtaGeneratedProcess`; this relation is kept
only for theorem statements that transport facts from an externally supplied
implementation. It unfolds the displayed equations (5.2.49)--(5.2.52), with
membership recorded because Mathlib's `IsMinOn` does not itself assert
`x^t ∈ X`. -/
def DeterministicRGEMProcessEquations
    (process : ℕ → BlockSamplePath ι → State ι E) : Prop :=
  (∀ ω, process 0 ω =
      ({ x := S.x0
         blockX := fun _ => S.x0
         yPrev := fun _ => 0
         yCurr := fun _ => 0 } : State ι E)) ∧
    ∀ (t : ℕ) (ht : 1 ≤ t), ∀ ω,
      let prev : State ι E := process (t - 1) ω
      let curr : State ι E := process t ω
      let yTilde : ι → E := fun i => SOptLib.extrapolatedPoint (S.α t) ((prev).yCurr i) ((prev).yPrev i)
      curr.x ∈ S.X ∧
        IsMinOn (S.proxObjective t prev.x yTilde) S.X curr.x ∧
        curr.blockX = S.blockPointUpdate t (S.sample t ω) curr.x prev.blockX ∧
        curr.yPrev = prev.yCurr ∧
        curr.yCurr =
          Function.update prev.yCurr (S.sample t ω)
            (S.gradF (S.sample t ω) (curr.blockX (S.sample t ω)))

/-- Helper equation characterization of a stochastic RGEM process.

The exported stochastic run is `positiveEtaGeneratedStochasticProcess`. This relation is
kept only as transport scaffolding for externally supplied implementations: Eq.
(5.2.50) defines the primal prox point, while Eq. (5.2.85) replaces the
deterministic gradient-table update. -/
def StochasticRGEMProcessEquations {Ξ : Type*}
    (B : ℕ → ℕ) (hB : S.StochasticBatchDomain B) (G : ι → E → Ξ → E)
    (process : ℕ → StochasticRunPath ι Ξ → State ι E) : Prop :=
  (∀ ω, process 0 ω =
      ({ x := S.x0
         blockX := fun _ => S.x0
         yPrev := fun _ => 0
         yCurr := fun _ => 0 } : State ι E)) ∧
    ∀ (t : ℕ) (ht : 1 ≤ t), ∀ ω,
      let prev : State ι E := process (t - 1) ω
      let curr : State ι E := process t ω
      let yTilde : ι → E := fun i => SOptLib.extrapolatedPoint (S.α t) ((prev).yCurr i) ((prev).yPrev i)
      let ξ : ι → ℕ → ℕ → Ξ := fun i n j => S.stochasticOracleSample i n j ω
      curr.x ∈ S.X ∧
        IsMinOn (S.proxObjective t prev.x yTilde) S.X curr.x ∧
        curr.blockX = S.blockPointUpdate t (S.stochasticBlockSample t ω) curr.x prev.blockX ∧
        curr.yPrev = prev.yCurr ∧
        curr.yCurr =
          S.stochasticComponentGradientUpdate B hB G ξ t ht
            (S.stochasticBlockSample t ω) curr.blockX prev.yCurr

/-- Positive-eta corrected domain needed to realize every prox call in a generated run.

Book JSON `#/assumptions/5` quotes the prox-mapping parameters as
`x^0∈X`, `g∈R^n`, `μ≥0`, and `η>0`. Algorithm 5.4 lists `η_t` as nonnegative,
so generated runs expose this well-definedness domain instead of silently
totalizing the prox selector. Search checked the SOptLib positive-stepsize prox
wrapper, but it wraps a raw prox map rather than the literal RGEM argmin in
Eq. (5.2.50). -/
def PositiveEtaDomain : Prop :=
  ∀ t : ℕ, 1 ≤ t → 0 < S.η t

/-- Initial RGEM state: `x_i^0 = x^0` and `y_i^{-1}=y_i^0=0`. -/
noncomputable def initialState : {s : State ι E // S.StateFeasible s} :=
  ⟨({ x := S.x0
      blockX := fun _ => S.x0
      yPrev := fun _ => 0
      yCurr := fun _ => 0 } : State ι E),
    ⟨S.hx0_mem, fun _ => S.hx0_mem⟩⟩

/-- One RGEM transition for the printed Algorithm 5.4 equations.

This uses `proxPoint`, the selected argmin from Eq. (5.2.50), whose existence is
derived directly from Eq. (5.2.9)'s positive-eta prox computability. Thus the
generated process does not use an arbitrary iterate witness or eta-free prox
selector. -/
noncomputable def stateStep (t : ℕ) (hηt : 0 < S.η t) (selected : ι)
    (s : {s : State ι E // S.StateFeasible s}) :
    {s : State ι E // S.StateFeasible s} :=
  let yTilde : ι → E := fun i => SOptLib.extrapolatedPoint (S.α t) ((s.1).yCurr i) ((s.1).yPrev i)
  let xNext := S.proxPoint t s.1.x yTilde s.2.1 hηt
  let blockNext := S.blockPointUpdate t selected xNext s.1.blockX
  let yNext := Function.update s.1.yCurr selected (S.gradF selected (blockNext selected))
  ⟨({ x := xNext
      blockX := blockNext
      yPrev := s.1.yCurr
      yCurr := yNext } : State ι E),
    by
      refine ⟨S.proxPoint_mem t s.1.x yTilde s.2.1 hηt, ?_⟩
      intro i
      by_cases hi : i = selected
      · subst hi
        -- Same feasibility obligation as Eq. (5.2.51): convexity of `X` and the
        -- Algorithm 5.4 parameter regime make the displayed affine point feasible.
        have hτ : 0 ≤ S.τ t := (S.hparam_nonneg t).2.2
        have hxNext : xNext ∈ S.X := S.proxPoint_mem t s.1.x yTilde s.2.1 hηt
        have hprev : s.1.blockX i ∈ S.X := s.2.2 i
        have hrefresh :
            SOptLib.relaxedMemoryRefreshPoint (S.τ t) xNext (s.1.blockX i) ∈ S.X :=
          SOptLib.relaxedMemoryRefreshPoint_mem_of_convex S.hX_convex hτ hxNext hprev
        simpa [blockNext, blockPointUpdate, auxiliaryPoint, SOptLib.relaxedMemoryRefreshPoint]
          using hrefresh
      · simp [blockNext, blockPointUpdate, hi, s.2.2 i]⟩

/-- Compatibility name for the generated deterministic RGEM transition.

The algorithmic spine is the single canonical definition `stateStep`. This alias
keeps older generated-process references from reintroducing a second copy of the
Algorithm 5.4 update equations. -/
noncomputable def generatedStateStep (t : ℕ) (hηt : 0 < S.η t) (selected : ι)
    (s : {s : State ι E // S.StateFeasible s}) :
    {s : State ι E // S.StateFeasible s} :=
  S.stateStep t hηt selected s

/-- Corrected-domain RGEM state process driven by the sampled block stream.

This constructive realization is deliberately named `positiveEtaProcess`: it
requires the positive-eta domain supplied by Eq. (5.2.9)'s prox-computability
statement and therefore is not the unqualified paper process. -/
noncomputable def positiveEtaProcess (hη : S.PositiveEtaDomain) :
    ℕ → BlockSamplePath ι → {s : State ι E // S.StateFeasible s}
  | 0 => fun _ => S.initialState
  | t + 1 => fun ω =>
      S.stateStep (t + 1) (hη (t + 1) (Nat.succ_pos t)) (S.sample (t + 1) ω)
        (positiveEtaProcess hη t ω)

@[simp] theorem positiveEtaProcess_zero (hη : S.PositiveEtaDomain) (ω : BlockSamplePath ι) :
    S.positiveEtaProcess hη 0 ω = S.initialState := by
  rfl

theorem positiveEtaProcess_succ (hη : S.PositiveEtaDomain) (t : ℕ) (ω : BlockSamplePath ι) :
    S.positiveEtaProcess hη (t + 1) ω =
      S.stateStep (t + 1) (hη (t + 1) (Nat.succ_pos t)) (S.sample (t + 1) ω)
        (S.positiveEtaProcess hη t ω) := by
  rfl

/-- Corrected-domain generated RGEM process from Eqs. (5.2.49)--(5.2.52).

Book JSON `#/algorithm_spec/steps/2/math` quotes the primal update
`x^t=argmin_{x∈X}{<m^{-1}∑_i ytilde_i^t,x>+μν(x)+η_tV(x^{t-1},x)}`.
This is the selected Algorithm 5.4 run under the extra positive-eta realization
domain from `#/assumptions/5`, not the unqualified paper theorem boundary. The
SOptLib `recursiveIterateProcess` candidates were checked; RGEM keeps the local
recursion because the paper time is one-based and each step carries the selected
block, literal Eq. (5.2.50) prox selector, and feasibility subtype. -/
noncomputable def positiveEtaGeneratedProcess (hη : S.PositiveEtaDomain) :
    ℕ → BlockSamplePath ι → State ι E :=
  fun t ω => (S.positiveEtaProcess hη t ω).1

/-- The corrected-domain generated process satisfies the displayed RGEM equations. -/
theorem positiveEtaGeneratedProcess_equations (hη : S.PositiveEtaDomain) :
    S.DeterministicRGEMProcessEquations (S.positiveEtaGeneratedProcess hη) := by
  constructor
  · intro ω
    rfl
  · intro t ht ω
    cases t with
    | zero => cases ht
    | succ n =>
        dsimp [positiveEtaGeneratedProcess, positiveEtaProcess, stateStep]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · exact S.proxPoint_mem (n + 1) (S.positiveEtaGeneratedProcess hη n ω).x
            (fun i => SOptLib.extrapolatedPoint (S.α (n + 1)) (((S.positiveEtaGeneratedProcess hη n ω)).yCurr i) (((S.positiveEtaGeneratedProcess hη n ω)).yPrev i))
            (S.positiveEtaProcess hη n ω).2.1 (hη (n + 1) (Nat.succ_pos n))
        · exact S.proxPoint_isMinOn (n + 1) (S.positiveEtaGeneratedProcess hη n ω).x
            (fun i => SOptLib.extrapolatedPoint (S.α (n + 1)) (((S.positiveEtaGeneratedProcess hη n ω)).yCurr i) (((S.positiveEtaGeneratedProcess hη n ω)).yPrev i))
            (S.positiveEtaProcess hη n ω).2.1 (hη (n + 1) (Nat.succ_pos n))
        · rfl
        · rfl
        · rfl

@[simp] theorem positiveEtaGeneratedProcess_zero
    (hη : S.PositiveEtaDomain) (ω : BlockSamplePath ι) :
    S.positiveEtaGeneratedProcess hη 0 ω = S.initialState.1 := by
  rfl

/-- Source-equation successor characterization for the corrected generated process. -/
theorem positiveEtaGeneratedProcess_succ_equations
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 1 ≤ t) (ω : BlockSamplePath ι) :
    let prev : State ι E := S.positiveEtaGeneratedProcess hη (t - 1) ω
    let curr : State ι E := S.positiveEtaGeneratedProcess hη t ω
    let yTilde : ι → E := fun i => SOptLib.extrapolatedPoint (S.α t) ((prev).yCurr i) ((prev).yPrev i)
    curr.x ∈ S.X ∧
      IsMinOn (S.proxObjective t prev.x yTilde) S.X curr.x ∧
      curr.blockX = S.blockPointUpdate t (S.sample t ω) curr.x prev.blockX ∧
      curr.yPrev = prev.yCurr ∧
      curr.yCurr =
        Function.update prev.yCurr (S.sample t ω)
          (S.gradF (S.sample t ω) (curr.blockX (S.sample t ω))) :=
  (S.positiveEtaGeneratedProcess_equations hη).2 t ht ω

/-- Generated primal iterate `x^t` of Algorithm 5.4.

This projects the canonical generated run selected above; externally supplied
processes are available only through `xIterateOfProcess`. -/
noncomputable def positiveEtaXIterate
    (S : RandomGradientExtrapolation.Setup ι E)
    (hη : S.PositiveEtaDomain)
    (t : ℕ) (ω : BlockSamplePath ι) : E :=
  (S.positiveEtaGeneratedProcess hη t ω).x

/-- Generated component point table `x_i^t` of Algorithm 5.4. -/
noncomputable def positiveEtaBlockIterate
    (S : RandomGradientExtrapolation.Setup ι E)
    (hη : S.PositiveEtaDomain)
    (t : ℕ) (ω : BlockSamplePath ι) (i : ι) : E :=
  (S.positiveEtaGeneratedProcess hη t ω).blockX i

/-- Generated component gradient table `y_i^t` of Algorithm 5.4. -/
noncomputable def positiveEtaYIterate
    (S : RandomGradientExtrapolation.Setup ι E)
    (hη : S.PositiveEtaDomain)
    (t : ℕ) (ω : BlockSamplePath ι) (i : ι) : E :=
  (S.positiveEtaGeneratedProcess hη t ω).yCurr i

private theorem positiveEtaGeneratedProcess_yPrev_eq_yIterate_pred
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 1 ≤ t)
    (ω : BlockSamplePath ι) (i : ι) :
    (S.positiveEtaGeneratedProcess hη (t - 1) ω).yPrev i =
      S.positiveEtaYIterate hη (t - 2) ω i := by
  by_cases ht2 : 2 ≤ t
  · have htprev : 1 ≤ t - 1 := by omega
    have hstep :=
      S.positiveEtaGeneratedProcess_succ_equations hη (t := t - 1) htprev ω
    rcases hstep with ⟨_hxmem, _hmin, _hblock, hyprev, _hycurr⟩
    have hpred : t - 1 - 1 = t - 2 := by omega
    simpa [positiveEtaYIterate, hpred] using congrFun hyprev i
  · have ht_eq : t = 1 := by omega
    subst ht_eq
    change (S.initialState.1).yPrev i = (S.initialState.1).yCurr i
    rfl

theorem positiveEtaXIterate_mem (hη : S.PositiveEtaDomain) (t : ℕ) (ω : BlockSamplePath ι) :
    S.positiveEtaXIterate hη t ω ∈ S.X :=
  (S.positiveEtaProcess hη t ω).2.1

/-- General helper for externally supplied processes satisfying the displayed RGEM equations.

This is not the paper-facing Algorithm 5.4 process; it is retained only as proof
scaffolding for transporting facts from a relation-preserving implementation. -/
noncomputable def xIterateOfProcess
    (_S : RandomGradientExtrapolation.Setup ι E)
    (process : ℕ → BlockSamplePath ι → State ι E) (t : ℕ)
    (ω : BlockSamplePath ι) : E :=
  (process t ω).x

/-- General helper for externally supplied component point tables. -/
noncomputable def blockIterateOfProcess
    (_S : RandomGradientExtrapolation.Setup ι E)
    (process : ℕ → BlockSamplePath ι → State ι E) (t : ℕ)
    (ω : BlockSamplePath ι) (i : ι) : E :=
  (process t ω).blockX i

/-- General helper for externally supplied component gradient tables. -/
noncomputable def yIterateOfProcess
    (_S : RandomGradientExtrapolation.Setup ι E)
    (process : ℕ → BlockSamplePath ι → State ι E) (t : ℕ)
    (ω : BlockSamplePath ι) (i : ι) : E :=
  (process t ω).yCurr i

theorem xIterateOfProcess_mem {process : ℕ → BlockSamplePath ι → State ι E}
    (hprocess : S.DeterministicRGEMProcessEquations process)
    (t : ℕ) (ω : BlockSamplePath ι) :
    S.xIterateOfProcess process t ω ∈ S.X := by
  by_cases ht : t = 0
  · subst ht
    have hx : (process 0 ω).x = S.x0 := congrArg State.x (hprocess.1 ω)
    simpa [xIterateOfProcess, hx] using S.hx0_mem
  · have htpos : 1 ≤ t := Nat.succ_le_of_lt (Nat.pos_of_ne_zero ht)
    simpa [xIterateOfProcess] using (hprocess.2 t htpos ω).1

/-- One stochastic RGEM transition for Algorithm 5.5.

This is Algorithm 5.4's transition with only Eq. (5.2.52) replaced by the
stochastic batch-gradient update (5.2.85), exactly as Algorithm 5.5 states.
SOptLib recursive-process primitives and `miniBatchOracleAverage` were checked;
they provide process skeletons and generic mini-batch averages, while the paper
needs this literal RGEM state transition over the explicit sample table
`ξ_{i,t}^j` and the positive batch-size domain for `B_t^{-1}`. -/
noncomputable def stochasticStateStep {Ξ : Type*}
    (B : ℕ → ℕ) (hB : S.StochasticBatchDomain B) (G : ι → E → Ξ → E)
    (ξ : ι → ℕ → ℕ → Ξ) (t : ℕ) (ht : 1 ≤ t) (hηt : 0 < S.η t) (selected : ι)
    (s : {s : State ι E // S.StateFeasible s}) :
    {s : State ι E // S.StateFeasible s} :=
  let yTilde : ι → E := fun i => SOptLib.extrapolatedPoint (S.α t) ((s.1).yCurr i) ((s.1).yPrev i)
  let xNext := S.proxPoint t s.1.x yTilde s.2.1 hηt
  let blockNext := S.blockPointUpdate t selected xNext s.1.blockX
  let yNext := S.stochasticComponentGradientUpdate B hB G ξ t ht selected blockNext s.1.yCurr
  ⟨({ x := xNext
      blockX := blockNext
      yPrev := s.1.yCurr
      yCurr := yNext } : State ι E),
    by
      refine ⟨S.proxPoint_mem t s.1.x yTilde s.2.1 hηt, ?_⟩
      intro i
      by_cases hi : i = selected
      · subst hi
        -- Same feasibility obligation as Eq. (5.2.51): convexity of `X` and the
        -- Algorithm 5.5 parameter regime make the displayed affine point feasible.
        have hτ : 0 ≤ S.τ t := (S.hparam_nonneg t).2.2
        have hxNext : xNext ∈ S.X := S.proxPoint_mem t s.1.x yTilde s.2.1 hηt
        have hprev : s.1.blockX i ∈ S.X := s.2.2 i
        have hrefresh :
            SOptLib.relaxedMemoryRefreshPoint (S.τ t) xNext (s.1.blockX i) ∈ S.X :=
          SOptLib.relaxedMemoryRefreshPoint_mem_of_convex S.hX_convex hτ hxNext hprev
        simpa [blockNext, blockPointUpdate, auxiliaryPoint, SOptLib.relaxedMemoryRefreshPoint]
          using hrefresh
      · simp [blockNext, blockPointUpdate, hi, s.2.2 i]⟩

/-- One stochastic RGEM transition for Algorithm 5.5.

This is the stochastic analogue of `generatedStateStep`: the primal prox point is
the printed Eq. (5.2.50) argmin selected by `proxPoint`, and Eq. (5.2.85)
supplies the stochastic gradient table update. -/
noncomputable def generatedStochasticStateStep {Ξ : Type*}
    (B : ℕ → ℕ) (hB : S.StochasticBatchDomain B) (G : ι → E → Ξ → E)
    (ξ : ι → ℕ → ℕ → Ξ) (t : ℕ) (ht : 1 ≤ t) (hηt : 0 < S.η t) (selected : ι)
    (s : {s : State ι E // S.StateFeasible s}) :
    {s : State ι E // S.StateFeasible s} :=
  S.stochasticStateStep B hB G ξ t ht hηt selected s

/-- Stochastic RGEM process generated by Algorithm 5.5.

This process is driven by the canonical stochastic path and uses Eq. (5.2.85)
for the component-gradient table. It replaces the previous Lemma 5.11 encoding
that reused the deterministic RGEM process while inserting stochastic gradients
only theorem-locally. -/
noncomputable def positiveEtaStochasticProcess {Ξ : Type*}
    (B : ℕ → ℕ) (hB : S.StochasticBatchDomain B) (G : ι → E → Ξ → E)
    (hη : S.PositiveEtaDomain) :
    ℕ → StochasticRunPath ι Ξ → {s : State ι E // S.StateFeasible s}
  | 0 => fun _ => S.initialState
  | t + 1 => fun ω =>
      let ξ : ι → ℕ → ℕ → Ξ := fun i n j => S.stochasticOracleSample i n j ω
      S.stochasticStateStep B hB G ξ (t + 1) (Nat.succ_pos t)
        (hη (t + 1) (Nat.succ_pos t))
        (S.stochasticBlockSample (t + 1) ω)
        (positiveEtaStochasticProcess B hB G hη t ω)

@[simp] theorem positiveEtaStochasticProcess_zero {Ξ : Type*}
    (B : ℕ → ℕ) (hB : S.StochasticBatchDomain B) (G : ι → E → Ξ → E)
    (hη : S.PositiveEtaDomain) (ω : StochasticRunPath ι Ξ) :
    S.positiveEtaStochasticProcess B hB G hη 0 ω = S.initialState := by
  rfl

theorem positiveEtaStochasticProcess_succ {Ξ : Type*}
    (B : ℕ → ℕ) (hB : S.StochasticBatchDomain B) (G : ι → E → Ξ → E)
    (hη : S.PositiveEtaDomain) (t : ℕ) (ω : StochasticRunPath ι Ξ) :
    S.positiveEtaStochasticProcess B hB G hη (t + 1) ω =
      (let ξ : ι → ℕ → ℕ → Ξ := fun i n j => S.stochasticOracleSample i n j ω
       S.stochasticStateStep B hB G ξ (t + 1) (Nat.succ_pos t)
        (hη (t + 1) (Nat.succ_pos t))
        (S.stochasticBlockSample (t + 1) ω)
        (S.positiveEtaStochasticProcess B hB G hη t ω)) := by
  rfl

/-- Stochastic RGEM process generated by Algorithm 5.5. -/
noncomputable def positiveEtaGeneratedStochasticProcess {Ξ : Type*}
    (B : ℕ → ℕ) (hB : S.StochasticBatchDomain B) (G : ι → E → Ξ → E)
    (hη : S.PositiveEtaDomain) :
    ℕ → StochasticRunPath ι Ξ → State ι E :=
  fun t ω => (S.positiveEtaStochasticProcess B hB G hη t ω).1

/-- The canonical stochastic process satisfies Eqs. (5.2.50), (5.2.51), and (5.2.85). -/
theorem positiveEtaGeneratedStochasticProcess_equations {Ξ : Type*}
    (B : ℕ → ℕ) (hB : S.StochasticBatchDomain B) (G : ι → E → Ξ → E)
    (hη : S.PositiveEtaDomain) :
    S.StochasticRGEMProcessEquations B hB G
      (S.positiveEtaGeneratedStochasticProcess B hB G hη) := by
  constructor
  · intro ω
    rfl
  · intro t ht ω
    cases t with
    | zero => cases ht
    | succ n =>
        dsimp [positiveEtaGeneratedStochasticProcess, positiveEtaStochasticProcess,
          stochasticStateStep]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · exact S.proxPoint_mem (n + 1)
            (S.positiveEtaGeneratedStochasticProcess B hB G hη n ω).x
            (fun i =>
              SOptLib.extrapolatedPoint (S.α (n + 1))
                ((S.positiveEtaGeneratedStochasticProcess B hB G hη n ω).yCurr i)
                ((S.positiveEtaGeneratedStochasticProcess B hB G hη n ω).yPrev i))
            (S.positiveEtaStochasticProcess B hB G hη n ω).2.1
            (hη (n + 1) (Nat.succ_pos n))
        · exact S.proxPoint_isMinOn (n + 1)
            (S.positiveEtaGeneratedStochasticProcess B hB G hη n ω).x
            (fun i =>
              SOptLib.extrapolatedPoint (S.α (n + 1))
                ((S.positiveEtaGeneratedStochasticProcess B hB G hη n ω).yCurr i)
                ((S.positiveEtaGeneratedStochasticProcess B hB G hη n ω).yPrev i))
            (S.positiveEtaStochasticProcess B hB G hη n ω).2.1
            (hη (n + 1) (Nat.succ_pos n))
        · rfl
        · rfl
        · rfl

@[simp] theorem positiveEtaGeneratedStochasticProcess_zero {Ξ : Type*}
    (B : ℕ → ℕ) (hB : S.StochasticBatchDomain B) (G : ι → E → Ξ → E)
    (hη : S.PositiveEtaDomain) (ω : StochasticRunPath ι Ξ) :
    S.positiveEtaGeneratedStochasticProcess B hB G hη 0 ω = S.initialState.1 := by
  rfl

/-- Source-equation successor characterization for the corrected stochastic process. -/
theorem positiveEtaGeneratedStochasticProcess_succ_equations {Ξ : Type*}
    (B : ℕ → ℕ) (hB : S.StochasticBatchDomain B) (G : ι → E → Ξ → E)
    (hη : S.PositiveEtaDomain)
    {t : ℕ} (ht : 1 ≤ t) (ω : StochasticRunPath ι Ξ) :
    let prev : State ι E := S.positiveEtaGeneratedStochasticProcess B hB G hη (t - 1) ω
    let curr : State ι E := S.positiveEtaGeneratedStochasticProcess B hB G hη t ω
    let yTilde : ι → E := fun i => SOptLib.extrapolatedPoint (S.α t) ((prev).yCurr i) ((prev).yPrev i)
    let ξ : ι → ℕ → ℕ → Ξ := fun i n j => S.stochasticOracleSample i n j ω
    curr.x ∈ S.X ∧
      IsMinOn (S.proxObjective t prev.x yTilde) S.X curr.x ∧
      curr.blockX = S.blockPointUpdate t (S.stochasticBlockSample t ω) curr.x prev.blockX ∧
      curr.yPrev = prev.yCurr ∧
      curr.yCurr =
        S.stochasticComponentGradientUpdate B hB G ξ t ht
          (S.stochasticBlockSample t ω) curr.blockX prev.yCurr :=
  (S.positiveEtaGeneratedStochasticProcess_equations B hB G hη).2 t ht ω

/-- Generated stochastic primal iterate `x^t` of Algorithm 5.5. -/
noncomputable def positiveEtaStochasticXIterate {Ξ : Type*}
    (S : RandomGradientExtrapolation.Setup ι E)
    (B : ℕ → ℕ) (hB : S.StochasticBatchDomain B) (G : ι → E → Ξ → E)
    (hη : S.PositiveEtaDomain)
    (t : ℕ) (ω : StochasticRunPath ι Ξ) : E :=
  (S.positiveEtaGeneratedStochasticProcess B hB G hη t ω).x

/-- Generated stochastic component point table `x_i^t` of Algorithm 5.5. -/
noncomputable def positiveEtaStochasticBlockIterate {Ξ : Type*}
    (S : RandomGradientExtrapolation.Setup ι E)
    (B : ℕ → ℕ) (hB : S.StochasticBatchDomain B) (G : ι → E → Ξ → E)
    (hη : S.PositiveEtaDomain)
    (t : ℕ) (ω : StochasticRunPath ι Ξ) (i : ι) : E :=
  (S.positiveEtaGeneratedStochasticProcess B hB G hη t ω).blockX i

/-- Generated stochastic component gradient table `y_i^t` of Algorithm 5.5. -/
noncomputable def positiveEtaStochasticYIterate {Ξ : Type*}
    (S : RandomGradientExtrapolation.Setup ι E)
    (B : ℕ → ℕ) (hB : S.StochasticBatchDomain B) (G : ι → E → Ξ → E)
    (hη : S.PositiveEtaDomain)
    (t : ℕ) (ω : StochasticRunPath ι Ξ) (i : ι) : E :=
  (S.positiveEtaGeneratedStochasticProcess B hB G hη t ω).yCurr i

/-- General helper for externally supplied stochastic processes satisfying Algorithm 5.5. -/
noncomputable def stochasticXIterateOfProcess {Ξ : Type*}
    (_S : RandomGradientExtrapolation.Setup ι E)
    (process : ℕ → StochasticRunPath ι Ξ → State ι E)
    (t : ℕ) (ω : StochasticRunPath ι Ξ) : E :=
  (process t ω).x

/-- General helper for externally supplied stochastic component point tables. -/
noncomputable def stochasticBlockIterateOfProcess {Ξ : Type*}
    (_S : RandomGradientExtrapolation.Setup ι E)
    (process : ℕ → StochasticRunPath ι Ξ → State ι E)
    (t : ℕ) (ω : StochasticRunPath ι Ξ) (i : ι) : E :=
  (process t ω).blockX i

/-- General helper for externally supplied stochastic component gradient tables. -/
noncomputable def stochasticYIterateOfProcess {Ξ : Type*}
    (_S : RandomGradientExtrapolation.Setup ι E)
    (process : ℕ → StochasticRunPath ι Ξ → State ι E)
    (t : ℕ) (ω : StochasticRunPath ι Ξ) (i : ι) : E :=
  (process t ω).yCurr i

theorem stochasticXIterateOfProcess_mem {Ξ : Type*}
    (B : ℕ → ℕ) (hB : S.StochasticBatchDomain B) (G : ι → E → Ξ → E)
    {process : ℕ → StochasticRunPath ι Ξ → State ι E}
    (hprocess : S.StochasticRGEMProcessEquations B hB G process)
    (t : ℕ) (ω : StochasticRunPath ι Ξ) :
    S.stochasticXIterateOfProcess process t ω ∈ S.X := by
  by_cases htzero : t = 0
  · subst htzero
    have hx : (process 0 ω).x = S.x0 := congrArg State.x (hprocess.1 ω)
    simpa [stochasticXIterateOfProcess, hx] using S.hx0_mem
  · have htpos : 1 ≤ t := Nat.succ_le_of_lt (Nat.pos_of_ne_zero htzero)
    simpa [stochasticXIterateOfProcess] using (hprocess.2 t htpos ω).1

theorem positiveEtaStochasticXIterate_mem {Ξ : Type*}
    (B : ℕ → ℕ) (hB : S.StochasticBatchDomain B) (G : ι → E → Ξ → E)
    (hη : S.PositiveEtaDomain) (t : ℕ) (ω : StochasticRunPath ι Ξ) :
    S.positiveEtaStochasticXIterate B hB G hη t ω ∈ S.X :=
  (S.positiveEtaStochasticProcess B hB G hη t ω).2.1

/-- Output window `{1, ..., k}` used in Eq. (5.2.53).

Book citation: `book/FOML/RandomGradientExtrapolation.json#/algorithm_spec/output/math`.
Quote: `θ_t>0, t=1,...,k` and `∑_{t=1}^k θ_t x^t`. -/
def outputWindow (k : ℕ) : Finset ℕ :=
  Finset.Icc 1 k

/-- Denominator `∑_{t=1}^k θ_t` in the weighted RGEM output.

Book citation: `book/FOML/RandomGradientExtrapolation.json#/algorithm_spec/output/math`.
Quote: `underline{x}^k := (∑_{t=1}^k θ_t)^{-1}∑_{t=1}^k θ_t x^t`. -/
noncomputable def outputWeightSum (k : ℕ) : ℝ :=
  Finset.sum (outputWindow k) S.θ

/-- Finite-window strict positivity of the Algorithm 5.4 output weights.

Book citation: `book/FOML/RandomGradientExtrapolation.json#/algorithm_spec/parameters/0/math`.
Quote: `θ_t>0, t=1,...,k`. -/
def OutputWeightsPositive (k : ℕ) : Prop :=
  ∀ t, t ∈ outputWindow k → 0 < S.θ t

/-- Finite-window nonnegativity of the Proposition 5.6 output weights.

Book citation: `book/FOML/RandomGradientExtrapolation.json#/assumptions/10/math`.
Quote: `θ_t≥0, t=1,...,k`. -/
def OutputWeightsNonnegative (k : ℕ) : Prop :=
  ∀ t, t ∈ outputWindow k → 0 ≤ S.θ t

/-- Positive output weights give the nonnegativity condition printed in Proposition 5.6. -/
theorem outputWeightsNonnegative_of_positive {k : ℕ}
    (hθ : S.OutputWeightsPositive k) : S.OutputWeightsNonnegative k := by
  intro t ht
  exact (hθ t ht).le

/-- The Eq. (5.2.53) normalizer is positive when `k ≥ 1` and `θ_t > 0`. -/
theorem outputWeightSum_pos {k : ℕ} (hk : 1 ≤ k)
    (hθ : S.OutputWeightsPositive k) : 0 < S.outputWeightSum k := by
  have hnonempty : (outputWindow k).Nonempty :=
    ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hk⟩⟩
  exact SOptLib.outputWeightDenominator_pos (outputWindow k) S.θ hθ hnonempty

/-- Corrected-domain weighted output `x̲^k = (∑θ_t)^{-1}∑θ_t x^t`, Eq. (5.2.53).

Book citation: `book/FOML/RandomGradientExtrapolation.json#/algorithm_spec/output/math`.
Quote: `set underline{x}^k := (∑θ_t)^{-1}∑θ_t x^t`.

Aligns with `SOptLib.weightedAverageOutputValue`, specialized to the one-based
output window of RGEM. The proof argument enforces the source's `θ_t > 0`
domain for the displayed normalizer, while the name records the extra positive-eta
realization domain required by Eq. (5.2.9). -/
noncomputable def positiveEtaWeightedOutput
    (hη : S.PositiveEtaDomain) (k : ℕ) (_hk : 1 ≤ k) (_hθ : S.OutputWeightsPositive k)
    (ω : BlockSamplePath ι) : E :=
  SOptLib.weightedAverageOutputValue
    (Ω := BlockSamplePath ι) (T := ℕ) (W := ℕ) (E := E)
    (fun k => outputWindow k) S.θ (S.positiveEtaXIterate hη) S.outputWeightSum k ω

theorem positiveEtaWeightedOutput_def
    (hη : S.PositiveEtaDomain) (k : ℕ) (hk : 1 ≤ k) (hθ : S.OutputWeightsPositive k)
    (ω : BlockSamplePath ι) :
    S.positiveEtaWeightedOutput hη k hk hθ ω =
      (S.outputWeightSum k)⁻¹ •
        Finset.sum (outputWindow k) (fun t => S.θ t • S.positiveEtaXIterate hη t ω) := by
  rfl

/-- Feasible optimizer predicate for problem (5.2.1).

Book citation: `book/FOML/RandomGradientExtrapolation.json#/setup/problem/math`.
Quote: `ψ* := min_{x∈X}{ψ(x)}`. -/
def IsOptimalSolution (xStar : E) : Prop :=
  xStar ∈ S.X ∧ ∀ x, x ∈ S.X → S.psi xStar ≤ S.psi x

/-- The source-defined maximum component smoothness `L̂ = max_i L_i`.

Book citation: `book/FOML/RandomGradientExtrapolation.json#/main_theorem/statement_math`.
Quote: `Lhat=max_{i=1,...,m} L_i`. -/
noncomputable def Lhat : ℝ :=
  Finset.max' (Finset.univ.image S.Lcomp) (by
    classical
    exact Finset.image_nonempty.mpr (Finset.univ_nonempty : (Finset.univ : Finset ι).Nonempty))

/-- The source maximum `Lhat=max_i L_i` is nonnegative because every component
smoothness constant is nonnegative.

Aligns with Lan §5.2.4 / Theorem 5.4's `Lhat=max_i L_i`. Reuses
`SOptLib.le_finite_image_max`, which exactly matches the finite-image maximum
comparison; no separate SOptLib primitive was found for this paper-specific
`Lhat` projection. -/
private theorem Lhat_nonneg : 0 ≤ S.Lhat := by
  classical
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  have hnonempty : (Finset.univ.image S.Lcomp).Nonempty :=
    Finset.image_nonempty.mpr (Finset.univ_nonempty : (Finset.univ : Finset ι).Nonempty)
  have hi_le : S.Lcomp i ≤ S.Lhat := by
    simpa [Lhat] using SOptLib.le_finite_image_max (f := S.Lcomp) i hnonempty
  exact le_trans (S.hLcomp_nonneg i) hi_le

/-- Constant `α` from Eq. (5.2.77), under Theorem 5.4's `μ > 0` denominator domain.

Book JSON `algorithm_spec/parameters/7` prints
`α=1-1/(m+sqrt(m^2+16m Lhat/μ))`, and PDF Theorem 5.4 uses this only in the
strongly convex branch where the displayed bounds also divide by `μ`. The
`hμ_pos` argument prevents this source object from being exported as a totalized
Real value at `μ = 0`. -/
noncomputable def theoremAlpha (_hμ_pos : 0 < S.μ) : ℝ :=
  SOptLib.sqrtDenominatorContractionAlpha (Fintype.card ι : ℝ) S.Lhat S.μ

/-- The Eq. (5.2.77) Theorem 5.4 contraction factor lies in `(0,1)`.

Aligns with Lan Eq. (5.2.77). Considered
`SOptLib.sqrt_alpha_schedule_pos_lt_one_log_neg`, but that lemma has the
different closed form `1 - 2/(m*(sqrt(1+16*c/m)+1))`; this proof uses the
literal RGEM denominator `m + sqrt(m^2 + 16*m*Lhat/mu)` together with
`S.hLcomp_nonneg`, `Fintype.card_pos`, and `hμ_pos`. -/
private theorem theoremAlpha_pos_lt_one (hμ_pos : 0 < S.μ) :
    0 < S.theoremAlpha hμ_pos ∧ S.theoremAlpha hμ_pos < 1 := by
  classical
  have hm_pos : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hm_one : 1 ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos : 0 < Fintype.card ι))
  have hterm_nonneg :
      0 ≤ 16 * (Fintype.card ι : ℝ) * S.Lhat / S.μ := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hm_pos.le) S.Lhat_nonneg)
      hμ_pos.le
  have hrad_pos :
      0 < (Fintype.card ι : ℝ) ^ 2 +
        16 * (Fintype.card ι : ℝ) * S.Lhat / S.μ := by
    have hm_sq_pos : 0 < (Fintype.card ι : ℝ) ^ 2 := pow_pos hm_pos 2
    nlinarith
  have hsqrt_pos :
      0 < Real.sqrt ((Fintype.card ι : ℝ) ^ 2 +
        16 * (Fintype.card ι : ℝ) * S.Lhat / S.μ) :=
    Real.sqrt_pos.2 hrad_pos
  have hden_gt_one :
      1 < (Fintype.card ι : ℝ) + Real.sqrt ((Fintype.card ι : ℝ) ^ 2 +
        16 * (Fintype.card ι : ℝ) * S.Lhat / S.μ) := by
    linarith
  have hden_pos :
      0 < (Fintype.card ι : ℝ) + Real.sqrt ((Fintype.card ι : ℝ) ^ 2 +
        16 * (Fintype.card ι : ℝ) * S.Lhat / S.μ) :=
    lt_trans zero_lt_one hden_gt_one
  have hinv_pos :
      0 < ((Fintype.card ι : ℝ) + Real.sqrt ((Fintype.card ι : ℝ) ^ 2 +
        16 * (Fintype.card ι : ℝ) * S.Lhat / S.μ))⁻¹ :=
    inv_pos.mpr hden_pos
  have hinv_lt_one :
      ((Fintype.card ι : ℝ) + Real.sqrt ((Fintype.card ι : ℝ) ^ 2 +
        16 * (Fintype.card ι : ℝ) * S.Lhat / S.μ))⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ hden_gt_one
  constructor
  · simpa [theoremAlpha] using sub_pos.mpr hinv_lt_one
  · simpa [theoremAlpha] using sub_lt_self (1 : ℝ) hinv_pos

/-- Constant `τ` from Eq. (5.2.76), under Theorem 5.4's `μ > 0` branch. -/
noncomputable def constantTau (hμ_pos : 0 < S.μ) : ℝ :=
  ((Fintype.card ι : ℝ) * (1 - S.theoremAlpha hμ_pos))⁻¹ - 1

/-- Constant `η` from Eq. (5.2.76), under Theorem 5.4's `μ > 0` branch. -/
noncomputable def constantEta (hμ_pos : 0 < S.μ) : ℝ :=
  S.theoremAlpha hμ_pos / (1 - S.theoremAlpha hμ_pos) * S.μ

/-- Constant per-iteration extrapolation parameter `α_t ≡ mα`, Eq. (5.2.76). -/
noncomputable def constantAlphaStep (hμ_pos : 0 < S.μ) : ℝ :=
  (Fintype.card ι : ℝ) * S.theoremAlpha hμ_pos

/-- Canonical Theorem 5.4 constant `τ_t` schedule from Eq. (5.2.76).

No SOptLib match: searched "parameter choice constant alpha eta tau theorem" and
checked the geometric/terminal epoch schedule candidates in
`SOptLib/Model/ParameterChoices.lean`; those model epoch-local accelerated
variance-reduction schedules, while FOML Theorem 5.4 requires the literal RGEM
constant policy `τ_t≡τ=1/(m(1-α))-1`. -/
noncomputable def theoremTauSchedule (hμ_pos : 0 < S.μ) (_t : ℕ) : ℝ :=
  S.constantTau hμ_pos

/-- Canonical Theorem 5.4 constant `η_t` schedule from Eq. (5.2.76).

No SOptLib match: searched "parameter choice constant alpha eta tau theorem" and
checked the geometric/terminal epoch schedule candidates in
`SOptLib/Model/ParameterChoices.lean`; those do not encode RGEM's strongly
convex constant policy `η_t≡η=αμ/(1-α)`. -/
noncomputable def theoremEtaSchedule (hμ_pos : 0 < S.μ) (_t : ℕ) : ℝ :=
  S.constantEta hμ_pos

/-- Canonical Theorem 5.4 constant `α_t` schedule from Eq. (5.2.76).

No SOptLib match: searched "parameter choice constant alpha eta tau theorem" and
checked the geometric/terminal epoch schedule candidates in
`SOptLib/Model/ParameterChoices.lean`; those are epoch schedules for other Lan
algorithms, while Theorem 5.4 prints the RGEM policy `α_t≡mα`. -/
noncomputable def theoremAlphaStepSchedule (hμ_pos : 0 < S.μ) (_t : ℕ) : ℝ :=
  S.constantAlphaStep hμ_pos

/-- The canonical Theorem 5.4 parameter policy from Eq. (5.2.76).

Book citation: `book/FOML/RandomGradientExtrapolation.json#/main_theorem/statement_math`.
Quote: `τ_t≡τ=1/(m(1-α))-1`, `η_t≡η=αμ/(1-α)`, and `α_t≡mα`.

This replaces theorem-facing raw equality triples with a single source-named
policy object built from the canonical schedule definitions above. -/
def Theorem54ParameterPolicy (hμ_pos : 0 < S.μ) : Prop :=
  (∀ t, 1 ≤ t → S.τ t = S.theoremTauSchedule hμ_pos t) ∧
    (∀ t, 1 ≤ t → S.η t = S.theoremEtaSchedule hμ_pos t) ∧
    (∀ t, 1 ≤ t → S.α t = S.theoremAlphaStepSchedule hμ_pos t)

theorem theorem54ParameterPolicy_tau {hμ_pos : 0 < S.μ}
    (hpolicy : S.Theorem54ParameterPolicy hμ_pos) :
    ∀ t, 1 ≤ t → S.τ t = S.constantTau hμ_pos := by
  intro t ht
  simpa [Theorem54ParameterPolicy, theoremTauSchedule] using hpolicy.1 t ht

theorem theorem54ParameterPolicy_eta {hμ_pos : 0 < S.μ}
    (hpolicy : S.Theorem54ParameterPolicy hμ_pos) :
    ∀ t, 1 ≤ t → S.η t = S.constantEta hμ_pos := by
  intro t ht
  simpa [Theorem54ParameterPolicy, theoremEtaSchedule] using hpolicy.2.1 t ht

theorem theorem54ParameterPolicy_alpha {hμ_pos : 0 < S.μ}
    (hpolicy : S.Theorem54ParameterPolicy hμ_pos) :
    ∀ t, 1 ≤ t → S.α t = S.constantAlphaStep hμ_pos := by
  intro t ht
  simpa [Theorem54ParameterPolicy, theoremAlphaStepSchedule] using hpolicy.2.2 t ht

/-- The Theorem 5.4 proof-selected weights `θ_t = α^{-t}`.

No SOptLib match: searched "geometric output weights alpha theta weighted average",
checked `weightedAverageOutputValue` and scanned `Model/ParameterChoices.lean`;
`geometricEpochTheta` is an epoch terminal/nonterminal schedule, while Theorem 5.4
requires the literal one-based schedule `θ_t = α^{-t}` from the proof. -/
noncomputable def theoremTheta (hμ_pos : 0 < S.μ) (t : ℕ) : ℝ :=
  (S.theoremAlpha hμ_pos ^ t)⁻¹

/-- Denominator for the Theorem 5.4 output with `θ_t = α^{-t}`. -/
noncomputable def theoremOutputWeightSum (hμ_pos : 0 < S.μ) (k : ℕ) : ℝ :=
  Finset.sum (outputWindow k) (S.theoremTheta hμ_pos)

/-- Positivity of the proof-selected Theorem 5.4 output weights on the output window.

Book citation: `book/FOML/RandomGradientExtrapolation.json#/main_theorem/proof/0/description`.
Quote: `Set θ_t=α^{-t}, t=1,...,k`. -/
def TheoremOutputWeightsPositive (hμ_pos : 0 < S.μ) (k : ℕ) : Prop :=
  ∀ t, t ∈ outputWindow k → 0 < S.theoremTheta hμ_pos t

/-- The Theorem 5.4 proof-selected output-weight policy `θ_t = α^{-t}` on `{1,...,k}`.

Book citation: `book/FOML/RandomGradientExtrapolation.json#/main_theorem/proof/0/description`.
Quote: `Set θ_t=α^{-t}, t=1,...,k`. -/
def TheoremOutputWeightPolicy (hμ_pos : 0 < S.μ) (k : ℕ) : Prop :=
  ∀ t, t ∈ outputWindow k → S.θ t = S.theoremTheta hμ_pos t

/-- The Theorem 5.4 schedule `θ_t = α^{-t}` satisfies the output positivity domain. -/
theorem theoremTheta_outputWeightsPositive {k : ℕ} (hk : 1 ≤ k) (hμ_pos : 0 < S.μ) :
    S.TheoremOutputWeightsPositive hμ_pos k := by
  intro t _ht
  rcases S.theoremAlpha_pos_lt_one hμ_pos with ⟨ha_pos, _ha_lt⟩
  simpa [theoremTheta] using inv_pos.mpr (pow_pos ha_pos t)

/-- The proof-selected Theorem 5.4 weight policy supplies Eq. (5.2.53)'s positivity. -/
theorem outputWeightsPositive_of_theoremThetaPolicy {k : ℕ} (hk : 1 ≤ k)
    (hμ_pos : 0 < S.μ) (hθ_policy : S.TheoremOutputWeightPolicy hμ_pos k) :
    S.OutputWeightsPositive k := by
  intro t ht
  rw [hθ_policy t ht]
  exact S.theoremTheta_outputWeightsPositive hk hμ_pos t ht

/-- The Theorem 5.4 parameter policy keeps generated prox calls inside `η_t > 0`.

This is derived from the theorem's positive-`μ` branch and Eq. (5.2.76), not a
Setup assumption. -/
theorem theoremPositiveEtaDomain (hμ_pos : 0 < S.μ)
    (hη_policy : ∀ t, 1 ≤ t → S.η t = S.constantEta hμ_pos) :
    S.PositiveEtaDomain := by
  intro t ht
  rw [hη_policy t ht]
  rcases S.theoremAlpha_pos_lt_one hμ_pos with ⟨ha_pos, ha_lt⟩
  have hden_pos : 0 < 1 - S.theoremAlpha hμ_pos :=
    sub_pos.mpr ha_lt
  simpa [constantEta] using mul_pos (div_pos ha_pos hden_pos) hμ_pos

/-- Theorem 5.4's generated primal iterate under the printed constant-eta policy.

The eta-policy argument is retained because Theorem 5.4 states that policy; the
iterate is the Eq. (5.2.50) generated iterate under the derived positive-eta
domain required by Eq. (5.2.9). -/
noncomputable def theoremXIterate
    (hμ_pos : 0 < S.μ)
    (hη_policy : ∀ t, 1 ≤ t → S.η t = S.constantEta hμ_pos)
    (t : ℕ) (ω : BlockSamplePath ι) : E :=
  S.positiveEtaXIterate (S.theoremPositiveEtaDomain hμ_pos hη_policy) t ω

/-- Bridge from the theorem-policy iterate name to the corrected-domain iterate. -/
theorem theoremXIterate_eq_positiveEtaXIterate
    (hμ_pos : 0 < S.μ)
    (hη_policy : ∀ t, 1 ≤ t → S.η t = S.constantEta hμ_pos)
    (t : ℕ) (ω : BlockSamplePath ι) :
    S.theoremXIterate hμ_pos hη_policy t ω =
      S.positiveEtaXIterate (S.theoremPositiveEtaDomain hμ_pos hη_policy) t ω := by
  rfl

/-- Updating only the output-weight schedule `θ` does not change the generated
positive-eta state process.

This is a proof-transport bridge for Theorem 5.4: Proposition 5.6 is applied to
`{S with θ := theoremTheta}`, but Algorithm 5.4's generated iterates do not read
`θ`; only the weighted output does. Candidate audit: searched
`positiveEtaXIterate proof irrelevance equal PositiveEtaDomain` and checked
target-file hits `positiveEtaXIterate_eq_of_strictPastWindow_eq` and
`theoremXIterate_eq_positiveEtaXIterate`; those handle sample-window equality or
the theorem iterate name, not record updates of the unused `θ` field. -/
private theorem positiveEtaProcess_theta_update_eq
    (theta' : ℕ → ℝ)
    (hηθ : ({ S with θ := theta' } : Setup ι E).PositiveEtaDomain)
    (hη : S.PositiveEtaDomain) :
    ∀ t ω,
      ({ S with θ := theta' } : Setup ι E).positiveEtaProcess hηθ t ω =
        S.positiveEtaProcess hη t ω := by
  intro t
  induction t with
  | zero =>
      intro ω
      rfl
  | succ n ih =>
      intro ω
      rw [positiveEtaProcess_succ, positiveEtaProcess_succ, ih ω]
      have hη_step :
          hηθ (n + 1) (Nat.succ_pos n) = hη (n + 1) (Nat.succ_pos n) := by
        apply Subsingleton.elim
      rw [hη_step]
      rfl

/-- Updating only `θ` does not change generated primal iterates. -/
private theorem positiveEtaXIterate_theta_update_eq
    (theta' : ℕ → ℝ)
    (hηθ : ({ S with θ := theta' } : Setup ι E).PositiveEtaDomain)
    (hη : S.PositiveEtaDomain) (t : ℕ) (ω : BlockSamplePath ι) :
    ({ S with θ := theta' } : Setup ι E).positiveEtaXIterate hηθ t ω =
      S.positiveEtaXIterate hη t ω := by
  simp [positiveEtaXIterate, positiveEtaGeneratedProcess,
    S.positiveEtaProcess_theta_update_eq theta' hηθ hη t ω]

/-- The Theorem 5.4 weighted output with the proof-selected weights `θ_t = α^{-t}`.

The output is built from `theoremXIterate`, so it is indexed only by the paper's
Theorem 5.4 parameter-policy evidence, not by an arbitrary positive-eta witness. -/
noncomputable def theoremWeightedOutput
    (hμ_pos : 0 < S.μ)
    (hη_policy : ∀ t, 1 ≤ t → S.η t = S.constantEta hμ_pos)
    (k : ℕ) (_hk : 1 ≤ k) (_hθ : S.TheoremOutputWeightsPositive hμ_pos k)
    (ω : BlockSamplePath ι) : E :=
  SOptLib.weightedAverageOutputValue
    (Ω := BlockSamplePath ι) (T := ℕ) (W := ℕ) (E := E)
    (fun k => outputWindow k) (S.theoremTheta hμ_pos)
    (S.theoremXIterate hμ_pos hη_policy) (S.theoremOutputWeightSum hμ_pos) k ω

theorem theoremWeightedOutput_def
    (hμ_pos : 0 < S.μ)
    (hη_policy : ∀ t, 1 ≤ t → S.η t = S.constantEta hμ_pos)
    (k : ℕ) (hk : 1 ≤ k) (hθ : S.TheoremOutputWeightsPositive hμ_pos k)
    (ω : BlockSamplePath ι) :
    S.theoremWeightedOutput hμ_pos hη_policy k hk hθ ω =
      (S.theoremOutputWeightSum hμ_pos k)⁻¹ •
        Finset.sum (outputWindow k)
          (fun t => S.theoremTheta hμ_pos t •
            S.theoremXIterate hμ_pos hη_policy t ω) := by
  rfl

/-- Initial-gradient quantity `σ_0² = m^{-1}∑ᵢ ‖∇f_i(x⁰)‖_*²`, Eq. (5.2.56).

Book citation: `book/FOML/RandomGradientExtrapolation.json#/assumptions/11/math`.
Quote: `1/m∑_{i=1}^m‖∇f_i(x^0)‖_*^2=σ_0^2`. -/
def InitialGradientBound (sigma0 : ℝ) : Prop :=
  SOptLib.finiteComponentInitialGradientSecondMomentBound S.dualNorm S.gradF S.x0 sigma0

/-- `Δ_{0,σ_0}` from Eq. (5.2.80), using `ψ(x*)` for `ψ*` when `x*` is optimal.

Theorem 5.4 is the strongly convex branch and uses denominators containing `μ`;
the `hμ_pos` argument records that source domain instead of reading Lean's
total inverse at `μ = 0` as a paper object. -/
noncomputable def Delta0Sigma0 (_hμ_pos : 0 < S.μ) (xStar : E) (sigma0 : ℝ) : ℝ :=
  strongConvexInitialVarianceBudget S.μ (Fintype.card ι : ℝ)
    (S.V S.x0 xStar) (S.psi S.x0 - S.psi xStar) sigma0

/-- `Δ̃_{0,σ_0}` from Proposition 5.6, Eq. (5.2.70).

No SOptLib match: searched "Delta stochastic gradient initial sigma budget" and
scanned `Model/Budget.lean`; the available budget primitives are paper-neutral
or for other Lan algorithms, while Eq. (5.2.70) has RGEM's stale-gradient
geometric sum with `θ_t α_{t+1}/η_{t+1}`. The positive-eta argument exposes the
source domain required by the displayed denominator `η_{t+1}`. -/
noncomputable def DeltaTilde0Sigma0
    (hη : S.PositiveEtaDomain) (k : ℕ) (xStar : E) (sigma0 : ℝ) : ℝ :=
  staleGradientGeometricInitialBudget outputWindow S.θ S.τ S.η S.α
    (Fintype.card ι : ℝ) (S.psi S.x0 - S.psi xStar) (S.V S.x0 xStar) sigma0 k

/-- Nonnegativity of the Theorem 5.4 initial budget `Δ_{0,σ₀}`.

Aligns with Lan Theorem 5.4 proof steps 16--21, where the final scalar
inequalities are multiplied by `Δ_{0,σ₀}`. Candidate audit: searched
`Delta0Sigma0 nonnegative optimal sigma` and grepped target/SOptLib for
`Delta0Sigma0` nonnegativity; no existing helper matched this RGEM budget, so
the proof unfolds Eq. (5.2.80) and uses optimality, `V_lower_bound`, and
`sigma0^2 ≥ 0`. -/
private theorem Delta0Sigma0_nonneg
    {xStar : E} (hμ_pos : 0 < S.μ) (hopt : S.IsOptimalSolution xStar)
    (sigma0 : ℝ) :
    0 ≤ S.Delta0Sigma0 hμ_pos xStar sigma0 := by
  classical
  have hV_nonneg : 0 ≤ S.V S.x0 xStar := by
    have hlow := S.V_lower_bound S.hx0_mem hopt.1
    have hsq : 0 ≤ (1 / 2 : ℝ) * S.primalNorm (xStar - S.x0) ^ 2 := by
      nlinarith [sq_nonneg (S.primalNorm (xStar - S.x0))]
    exact le_trans hsq hlow
  have hgap_nonneg : 0 ≤ S.psi S.x0 - S.psi xStar := by
    exact sub_nonneg.mpr (hopt.2 S.x0 S.hx0_mem)
  have hcard_pos : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hden_pos : 0 < (Fintype.card ι : ℝ) * S.μ :=
    mul_pos hcard_pos hμ_pos
  have hμV_nonneg : 0 ≤ S.μ * S.V S.x0 xStar :=
    mul_nonneg hμ_pos.le hV_nonneg
  have hsigma_nonneg : 0 ≤ sigma0 ^ 2 / ((Fintype.card ι : ℝ) * S.μ) :=
    div_nonneg (sq_nonneg sigma0) hden_pos.le
  unfold Delta0Sigma0 strongConvexInitialVarianceBudget
  nlinarith

/-- Gap comparison functional `Q(underline{x},x)` from Eq. (5.2.59). -/
noncomputable def Q (xUnder x : E) : ℝ :=
  SOptLib.finiteAverageGradientRegularizerGap S.gradF S.ν S.μ xUnder x

/-- Proposition 5.6 / Lemma 5.10 condition (5.2.61).

This recurrence is proposition-local proof input, not Setup data. -/
def WeightCondition5261 (k : ℕ) : Prop :=
  ∀ t, 2 ≤ t → t ≤ k →
    S.θ t * ((Fintype.card ι : ℝ) * (1 + S.τ t) - 1) =
      S.θ (t - 1) * (Fintype.card ι : ℝ) * (1 + S.τ (t - 1))

private theorem two_bregman_argmin_descent_feasible_endpoint
    {X : Set E} (p : E → ℝ) (V : E → E → ℝ) (grad : E → E)
    (hp_convex : ConvexOn ℝ X p)
    {xTilde yTilde uHat : E} {mu1 mu2 : ℝ}
    (huHat : uHat ∈ X)
    (hmu1 : 0 ≤ mu1)
    (hmu2 : 0 ≤ mu2)
    (hV_segment_deriv :
      ∀ (a z u : E), z ∈ X → u ∈ X →
        let d : E := u - z
        let β : ℝ → ℝ := fun t =>
          if _ht : t ∈ Set.Icc (0 : ℝ) 1 then
            V a (AffineMap.lineMap z u t) - V a z
          else 0
        HasDerivWithinAt β
          ⟪grad z - grad a, d⟫_ℝ
          (Set.Icc (0 : ℝ) 1) 0)
    (hV_three :
      ∀ a b c : E,
        V a c = V a b + ⟪grad b - grad a, c - b⟫_ℝ + V b c)
    (h_opt :
      ∀ u, u ∈ X →
        p uHat + mu1 * V xTilde uHat + mu2 * V yTilde uHat ≤
          p u + mu1 * V xTilde u + mu2 * V yTilde u) :
    ∀ u, u ∈ X →
      p uHat + mu1 * V xTilde uHat + mu2 * V yTilde uHat ≤
        p u + mu1 * V xTilde u + mu2 * V yTilde u -
          (mu1 + mu2) * V uHat u := by
  exact
    SOptLib.two_bregman_argmin_descent_of_feasible_endpoint_deriv
      (X := X) (p := p) (V := V) (grad := grad)
      hp_convex huHat hV_segment_deriv hV_three h_opt

/-- Paper Lemma 3.5, specialized to RGEM's Bregman distance `V`.

This is a proof theorem, not Setup data: the paper proves the prox-mapping
inequality and later applies it to (5.2.50). -/
theorem ProxMappingInequality_Lemma_3_5
    (p : E → ℝ) (xCenter yCenter uHat u : E) (mu1 mu2 : ℝ)
    (hp_convex : ConvexOn ℝ S.X p)
    (hxCenter : xCenter ∈ S.X) (hyCenter : yCenter ∈ S.X)
    (huHat : uHat ∈ S.X) (hu : u ∈ S.X)
    (hmu1 : 0 ≤ mu1) (hmu2 : 0 ≤ mu2)
    (hmin : IsMinOn
      (fun z => p z + mu1 * S.V xCenter z + mu2 * S.V yCenter z) S.X uHat) :
    p uHat + mu1 * S.V xCenter uHat + mu2 * S.V yCenter uHat ≤
      p u + mu1 * S.V xCenter u + mu2 * S.V yCenter u -
        (mu1 + mu2) * S.V uHat u := by
  have hopt :
      ∀ v, v ∈ S.X →
        p uHat + mu1 * S.V xCenter uHat + mu2 * S.V yCenter uHat ≤
          p v + mu1 * S.V xCenter v + mu2 * S.V yCenter v := by
    intro v hv
    rw [isMinOn_iff] at hmin
    exact hmin v hv
  exact
    two_bregman_argmin_descent_feasible_endpoint
      (X := S.X) p S.V S.gradν hp_convex huHat hmu1 hmu2
      (fun a z v hz hv => S.V_segment_difference_hasDerivWithinAt_zero a z v hz hv)
      S.V_three_point_identity hopt u hu

/-- Named source theorem for Eq. (5.2.8), derived from strong convexity of `ν`. -/
theorem ProxLowerBound_Eq_5_2_8 {x0 x : E} (hx0 : x0 ∈ S.X) (hx : x ∈ S.X) :
    (1 / 2 : ℝ) * S.primalNorm (x - x0) ^ 2 ≤ S.V x0 x :=
  S.V_lower_bound hx0 hx

/-- Support-function algebra for the reconstructed direction-dual norm.

If every primal-unit feasible direction has squared pairing with `zeta` bounded
by `B`, then the squared support function itself is bounded by `B`. This is the
non-analytic part of Lemma 5.8: it only unfolds the paper dual norm as the
affine-direction support function and manages the supremum. -/
private theorem dualNorm_sq_le_of_forall_unit_direction_inner_sq_le
    (S : Setup ι E) {zeta : E} {B : ℝ} (hB_nonneg : 0 ≤ B)
    (hunit :
      ∀ d : E, d ∈ (affineSpan ℝ S.X).direction → S.primalNorm d ≤ 1 →
        |⟪zeta, d⟫_ℝ| ^ 2 ≤ B) :
    S.dualNorm zeta ^ 2 ≤ B := by
  classical
  rcases Seminorm.exists_norm_le_mul_self_of_finiteDimensional_separating
      S.primalNorm S.hprimalNorm_separating with ⟨C, hCnonneg, hC⟩
  let A : Set ℝ := {r : ℝ |
    ∃ d : E, d ∈ (affineSpan ℝ S.X).direction ∧
      S.primalNorm d ≤ 1 ∧ r = |inner ℝ zeta d|}
  have h_bdd : BddAbove A := by
    refine ⟨‖zeta‖ * C, ?_⟩
    intro r hr
    rcases hr with ⟨d, _hd_dir, hpd, rfl⟩
    have hinner : |inner ℝ zeta d| ≤ ‖zeta‖ * ‖d‖ := by
      simpa using (norm_inner_le_norm (𝕜 := ℝ) zeta d)
    have hd_norm : ‖d‖ ≤ C := by
      calc
        ‖d‖ ≤ C * S.primalNorm d := hC d
        _ ≤ C * 1 := mul_le_mul_of_nonneg_left hpd hCnonneg
        _ = C := by simp
    exact hinner.trans (mul_le_mul_of_nonneg_left hd_norm (norm_nonneg zeta))
  have hzero_mem : (0 : ℝ) ∈ A := by
    refine ⟨0, ?_, ?_, ?_⟩
    · exact (affineSpan ℝ S.X).direction.zero_mem
    · simp
    · simp
  have hdual_nonneg : 0 ≤ S.dualNorm zeta := by
    rw [dualNorm, affineDirectionDualNorm]
    exact le_csSup h_bdd hzero_mem
  have hdual_le_sqrt : S.dualNorm zeta ≤ Real.sqrt B := by
    rw [dualNorm, affineDirectionDualNorm]
    change sSup A ≤ Real.sqrt B
    refine csSup_le ⟨0, hzero_mem⟩ ?_
    intro r hr
    rcases hr with ⟨d, hd_dir, hpd, rfl⟩
    exact Real.le_sqrt_of_sq_le (hunit d hd_dir hpd)
  have hsquare : S.dualNorm zeta ^ 2 ≤ Real.sqrt B ^ 2 := by
    rwa [sq_le_sq₀ hdual_nonneg (Real.sqrt_nonneg B)]
  simpa [Real.sq_sqrt hB_nonneg] using hsquare

/-- Nonnegativity of the reconstructed affine-direction dual norm. -/
private theorem dualNorm_nonneg_for_component_smoothness
    (S : Setup ι E) (zeta : E) :
    0 ≤ S.dualNorm zeta := by
  classical
  rcases Seminorm.exists_norm_le_mul_self_of_finiteDimensional_separating
      S.primalNorm S.hprimalNorm_separating with ⟨C, hCnonneg, hC⟩
  have h_bdd :
      BddAbove {r : ℝ |
        ∃ u : E, u ∈ (affineSpan ℝ S.X).direction ∧
          S.primalNorm u ≤ 1 ∧ r = |inner ℝ zeta u|} := by
    refine ⟨‖zeta‖ * C, ?_⟩
    intro r hr
    rcases hr with ⟨u, _hu_dir, hpu, rfl⟩
    have hinner : |inner ℝ zeta u| ≤ ‖zeta‖ * ‖u‖ := by
      simpa using (norm_inner_le_norm (𝕜 := ℝ) zeta u)
    have hu_norm : ‖u‖ ≤ C := by
      calc
        ‖u‖ ≤ C * S.primalNorm u := hC u
        _ ≤ C * 1 := mul_le_mul_of_nonneg_left hpu hCnonneg
        _ = C := by simp
    exact hinner.trans (mul_le_mul_of_nonneg_left hu_norm (norm_nonneg zeta))
  have hzero_mem :
      (0 : ℝ) ∈ {r : ℝ |
        ∃ u : E, u ∈ (affineSpan ℝ S.X).direction ∧
          S.primalNorm u ≤ 1 ∧ r = |inner ℝ zeta u|} := by
    refine ⟨0, ?_, ?_, ?_⟩
    · exact (affineSpan ℝ S.X).direction.zero_mem
    · simp
    · simp
  rw [dualNorm, affineDirectionDualNorm]
  exact le_csSup h_bdd hzero_mem

/-- Route-local support inequality for the component smooth upper model.

This is the same direction-dual support fact used later in the file, placed here
so Lemma 5.8's component upper-model bridge can be checked before the later
Proposition 5.6 support section. -/
private theorem dualNorm_inner_le_mul_primalNorm_for_component_smoothness
    (S : Setup ι E) (zeta d : E) (hd : d ∈ (affineSpan ℝ S.X).direction) :
    |⟪zeta, d⟫_ℝ| ≤ S.dualNorm zeta * S.primalNorm d := by
  classical
  rcases Seminorm.exists_norm_le_mul_self_of_finiteDimensional_separating
      S.primalNorm S.hprimalNorm_separating with ⟨C, hCnonneg, hC⟩
  have h_bdd :
      BddAbove {r : ℝ |
        ∃ u : E, u ∈ (affineSpan ℝ S.X).direction ∧
          S.primalNorm u ≤ 1 ∧ r = |inner ℝ zeta u|} := by
    refine ⟨‖zeta‖ * C, ?_⟩
    intro r hr
    rcases hr with ⟨u, _hu_dir, hpu, rfl⟩
    have hinner : |inner ℝ zeta u| ≤ ‖zeta‖ * ‖u‖ := by
      simpa using (norm_inner_le_norm (𝕜 := ℝ) zeta u)
    have hu_norm : ‖u‖ ≤ C := by
      calc
        ‖u‖ ≤ C * S.primalNorm u := hC u
        _ ≤ C * 1 := mul_le_mul_of_nonneg_left hpu hCnonneg
        _ = C := by simp
    exact hinner.trans (mul_le_mul_of_nonneg_left hu_norm (norm_nonneg zeta))
  simpa [dualNorm] using
    SOptLib.abs_inner_le_affineDirectionDualNorm_mul
      (X := S.X) S.primalNorm S.hprimalNorm_separating
      (zeta := zeta) (d := d) h_bdd hd

/-- Nonnegativity of the canonical affine-direction support dual. -/
private theorem affineDirectionDualNorm_nonneg_of_separating
    {X : Set E} (p : Seminorm ℝ E) (hp : p.IsSeparating) (zeta : E) :
    0 ≤ affineDirectionDualNorm X p zeta := by
  classical
  rcases Seminorm.exists_norm_le_mul_self_of_finiteDimensional_separating
      p hp with ⟨C, hCnonneg, hC⟩
  have h_bdd :
      BddAbove {r : ℝ |
        ∃ u : E, u ∈ (affineSpan ℝ X).direction ∧
          p u ≤ 1 ∧ r = |inner ℝ zeta u|} := by
    refine ⟨‖zeta‖ * C, ?_⟩
    intro r hr
    rcases hr with ⟨u, _hu_dir, hpu, rfl⟩
    have hinner : |inner ℝ zeta u| ≤ ‖zeta‖ * ‖u‖ := by
      simpa using (norm_inner_le_norm (𝕜 := ℝ) zeta u)
    have hu_norm : ‖u‖ ≤ C := by
      calc
        ‖u‖ ≤ C * p u := hC u
        _ ≤ C * 1 := mul_le_mul_of_nonneg_left hpu hCnonneg
        _ = C := by simp
    exact hinner.trans (mul_le_mul_of_nonneg_left hu_norm (norm_nonneg zeta))
  have hzero_mem :
      (0 : ℝ) ∈ {r : ℝ |
        ∃ u : E, u ∈ (affineSpan ℝ X).direction ∧
          p u ≤ 1 ∧ r = |inner ℝ zeta u|} := by
    refine ⟨0, ?_, ?_, ?_⟩
    · exact (affineSpan ℝ X).direction.zero_mem
    · simp
    · simp
  rw [affineDirectionDualNorm]
  exact le_csSup h_bdd hzero_mem

/-- Subadditivity of the affine-direction support dual used by RGEM's
paper dual norm.

Aligns with Lan Proposition 5.6 proof step 16, where the squared dual norm of
a memory-gradient difference is split through the stored gradient. Candidate
audit: checked `SOptLib.canonicalDualNorm_add_le`; it proves the same support
function fact for an unrestricted primal unit ball, while RGEM's
`affineDirectionDualNorm` restricts support directions to
`(affineSpan ℝ X).direction`, so this is the local restricted analogue. -/
private theorem affineDirectionDualNorm_add_le_of_separating
    {X : Set E} (p : Seminorm ℝ E) (hp : p.IsSeparating)
    (zeta eta : E) :
    affineDirectionDualNorm X p (zeta + eta) ≤
      affineDirectionDualNorm X p zeta + affineDirectionDualNorm X p eta := by
  classical
  rcases Seminorm.exists_norm_le_mul_self_of_finiteDimensional_separating
      p hp with ⟨C, hCnonneg, hC⟩
  have hbdd : ∀ z : E,
      BddAbove {r : ℝ |
        ∃ u : E, u ∈ (affineSpan ℝ X).direction ∧
          p u ≤ 1 ∧ r = |inner ℝ z u|} := by
    intro z
    refine ⟨‖z‖ * C, ?_⟩
    intro r hr
    rcases hr with ⟨u, _hu_dir, hpu, rfl⟩
    have hinner : |inner ℝ z u| ≤ ‖z‖ * ‖u‖ := by
      simpa using (norm_inner_le_norm (𝕜 := ℝ) z u)
    have hu_norm : ‖u‖ ≤ C := by
      calc
        ‖u‖ ≤ C * p u := hC u
        _ ≤ C * 1 := mul_le_mul_of_nonneg_left hpu hCnonneg
        _ = C := by simp
    exact hinner.trans (mul_le_mul_of_nonneg_left hu_norm (norm_nonneg z))
  simpa [affineDirectionDualNorm] using
    SOptLib.affineDirectionDualNorm_add_le
      (X := X) (p := p) (zeta := zeta) (eta := eta) (hbdd zeta) (hbdd eta)

/-- Two-term squared split for RGEM's affine-direction dual norm.

Aligns with Lan Proposition 5.6 proof step 16. Candidate audit: checked
`SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq`; it applies to the
ambient norm, while the residual statement uses the paper dual norm
`S.dualNorm`, so this specializes the same algebra after proving restricted
dual-norm subadditivity. -/
private theorem dualNorm_add_sq_le_two_mul_dualNorm_sq_add_two_mul_dualNorm_sq
    (S : Setup ι E) (a b : E) :
    S.dualNorm (a + b) ^ 2 ≤
      2 * S.dualNorm a ^ 2 + 2 * S.dualNorm b ^ 2 := by
  classical
  rcases Seminorm.exists_norm_le_mul_self_of_finiteDimensional_separating
      S.primalNorm S.hprimalNorm_separating with ⟨C, hCnonneg, hC⟩
  have hbdd : ∀ z : E,
      BddAbove {r : ℝ |
        ∃ u : E, u ∈ (affineSpan ℝ S.X).direction ∧
          S.primalNorm u ≤ 1 ∧ r = |inner ℝ z u|} := by
    intro z
    refine ⟨‖z‖ * C, ?_⟩
    intro r hr
    rcases hr with ⟨u, _hu_dir, hpu, rfl⟩
    have hinner : |inner ℝ z u| ≤ ‖z‖ * ‖u‖ := by
      simpa using (norm_inner_le_norm (𝕜 := ℝ) z u)
    have hu_norm : ‖u‖ ≤ C := by
      calc
        ‖u‖ ≤ C * S.primalNorm u := hC u
        _ ≤ C * 1 := mul_le_mul_of_nonneg_left hpu hCnonneg
        _ = C := by simp
    exact hinner.trans (mul_le_mul_of_nonneg_left hu_norm (norm_nonneg z))
  simpa [dualNorm] using
    SOptLib.affineDirectionDualNorm_add_sq_le_two_mul_sq_add_two_mul_sq
      (X := S.X) (p := S.primalNorm) a b (hbdd a) (hbdd b)

/-- Support inequality for the canonical affine-direction support dual. -/
private theorem affineDirectionDualNorm_inner_le_mul_primalNorm_of_separating
    {X : Set E} (p : Seminorm ℝ E) (hp : p.IsSeparating)
    (zeta d : E) (hd : d ∈ (affineSpan ℝ X).direction) :
    |⟪zeta, d⟫_ℝ| ≤ affineDirectionDualNorm X p zeta * p d := by
  classical
  rcases Seminorm.exists_norm_le_mul_self_of_finiteDimensional_separating
      p hp with ⟨C, hCnonneg, hC⟩
  have h_bdd :
      BddAbove {r : ℝ |
        ∃ u : E, u ∈ (affineSpan ℝ X).direction ∧
          p u ≤ 1 ∧ r = |inner ℝ zeta u|} := by
    refine ⟨‖zeta‖ * C, ?_⟩
    intro r hr
    rcases hr with ⟨u, _hu_dir, hpu, rfl⟩
    have hinner : |inner ℝ zeta u| ≤ ‖zeta‖ * ‖u‖ := by
      simpa using (norm_inner_le_norm (𝕜 := ℝ) zeta u)
    have hu_norm : ‖u‖ ≤ C := by
      calc
        ‖u‖ ≤ C * p u := hC u
        _ ≤ C * 1 := mul_le_mul_of_nonneg_left hpu hCnonneg
        _ = C := by simp
    exact hinner.trans (mul_le_mul_of_nonneg_left hu_norm (norm_nonneg zeta))
  by_cases hd0 : p d = 0
  · have hd_zero : d = 0 := (hp d).mp hd0
    simp [hd_zero]
  · have hpd_nonneg : 0 ≤ p d := apply_nonneg p d
    have hpd_pos : 0 < p d := lt_of_le_of_ne hpd_nonneg (Ne.symm hd0)
    let u : E := (p d)⁻¹ • d
    have hu_dir : u ∈ (affineSpan ℝ X).direction := by
      exact (affineSpan ℝ X).direction.smul_mem _ hd
    have hu_le : p u ≤ 1 := by
      simp [u, map_smul_eq_mul, abs_of_pos hpd_pos, hpd_pos.ne']
    have hsup : |inner ℝ zeta u| ≤ affineDirectionDualNorm X p zeta := by
      rw [affineDirectionDualNorm]
      exact le_csSup h_bdd ⟨u, hu_dir, hu_le, rfl⟩
    have hscale : |inner ℝ zeta u| = (p d)⁻¹ * |inner ℝ zeta d| := by
      simp [u, inner_smul_right, abs_mul, abs_of_pos (inv_pos.mpr hpd_pos)]
    have hinv_le :
        (p d)⁻¹ * |inner ℝ zeta d| ≤ affineDirectionDualNorm X p zeta := by
      simpa [hscale] using hsup
    calc
      |inner ℝ zeta d| = ((p d)⁻¹ * |inner ℝ zeta d|) * p d := by
        field_simp [hpd_pos.ne']
      _ ≤ affineDirectionDualNorm X p zeta * p d :=
        mul_le_mul_of_nonneg_right hinv_le hpd_pos.le

/-- Scalar carrier-gradient pairings are continuous under the paper
affine-direction dual Lipschitz hypothesis.

This is the continuity ingredient for the closed-carrier boundary transport in
Lemma 5.8.  It uses only the existing source-backed smoothness assumption and
finite-dimensional seminorm control; it does not assert continuity of the whole
ambient gradient field. -/
private theorem continuous_scalar_inner_of_affine_dual_lipschitz
    {X : Set E} (grad : {x : E // x ∈ X} → E)
    (p : Seminorm ℝ E) (L : ℝ) (d : E)
    (hp : p.IsSeparating)
    (hL_nonneg : 0 ≤ L)
    (hd : d ∈ (affineSpan ℝ X).direction)
    (hgrad_lipschitz :
      ∀ x y : {x : E // x ∈ X},
        affineDirectionDualNorm X p (grad x - grad y) ≤ L * p (x.1 - y.1)) :
    Continuous (fun x : {x : E // x ∈ X} => ⟪grad x, d⟫_ℝ) := by
  classical
  rcases Seminorm.exists_bound_by_norm_of_finiteDimensional p with
    ⟨K, hK_nonneg, hK⟩
  let M : ℝ := L * p d * K
  have hdiff :
      ∀ x y : {x : E // x ∈ X},
        ‖⟪grad x, d⟫_ℝ - ⟪grad y, d⟫_ℝ‖ ≤ M * dist x y := by
    intro x y
    have hinner :
        |⟪grad x - grad y, d⟫_ℝ| ≤
          affineDirectionDualNorm X p (grad x - grad y) * p d :=
      affineDirectionDualNorm_inner_le_mul_primalNorm_of_separating
        p hp (grad x - grad y) d hd
    have hdual := hgrad_lipschitz x y
    have hpd_nonneg : 0 ≤ p d := apply_nonneg p d
    have hstep1 :
        |⟪grad x - grad y, d⟫_ℝ| ≤ (L * p (x.1 - y.1)) * p d :=
      hinner.trans (mul_le_mul_of_nonneg_right hdual hpd_nonneg)
    have hp_bound : p (x.1 - y.1) ≤ K * ‖x.1 - y.1‖ := hK _
    have hstep2 :
        (L * p (x.1 - y.1)) * p d ≤ M * ‖x.1 - y.1‖ := by
      have hmul := mul_le_mul_of_nonneg_left hp_bound hL_nonneg
      have hmul2 := mul_le_mul_of_nonneg_right hmul hpd_nonneg
      dsimp [M] at hmul2 ⊢
      nlinarith
    have hrewrite :
        ‖⟪grad x, d⟫_ℝ - ⟪grad y, d⟫_ℝ‖ =
          |⟪grad x - grad y, d⟫_ℝ| := by
      rw [Real.norm_eq_abs]
      congr 1
      simp [inner_sub_left]
    calc
      ‖⟪grad x, d⟫_ℝ - ⟪grad y, d⟫_ℝ‖
          = |⟪grad x - grad y, d⟫_ℝ| := hrewrite
      _ ≤ (L * p (x.1 - y.1)) * p d := hstep1
      _ ≤ M * ‖x.1 - y.1‖ := hstep2
      _ = M * dist x y := by
        simp [Subtype.dist_eq, dist_eq_norm]
  exact (lipschitzWith_of_norm_sub_le_mul
    (fun x : {x : E // x ∈ X} => ⟪grad x, d⟫_ℝ) M hdiff).continuous

/-- Square bound for the affine-direction support dual from scalar bounds on all
primal-unit feasible directions. -/
private theorem _voucher_step_affineDirectionDualNorm_sq_le_of_unit_inner_sq
    {X : Set E} (p : Seminorm ℝ E) (hp : p.IsSeparating) (zeta : E) {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hunit :
      ∀ d : E, d ∈ (affineSpan ℝ X).direction → p d ≤ 1 →
        |⟪zeta, d⟫_ℝ| ^ 2 ≤ C) :
    affineDirectionDualNorm X p zeta ^ 2 ≤ C := by
  classical
  let A : Set ℝ := {r : ℝ |
    ∃ d : E, d ∈ (affineSpan ℝ X).direction ∧ p d ≤ 1 ∧
      r = |⟪zeta, d⟫_ℝ|}
  have hA_nonempty : A.Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨0, (affineSpan ℝ X).direction.zero_mem, ?_, ?_⟩
    · simp
    · simp
  have hA_le : ∀ r ∈ A, r ≤ Real.sqrt C := by
    intro r hr
    rcases hr with ⟨d, hd, hpd, rfl⟩
    have hsquare : |⟪zeta, d⟫_ℝ| ^ 2 ≤ (Real.sqrt C) ^ 2 := by
      simpa [Real.sq_sqrt hC_nonneg] using hunit d hd hpd
    exact (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg C)).1 hsquare
  have hdual_le : affineDirectionDualNorm X p zeta ≤ Real.sqrt C := by
    rw [affineDirectionDualNorm]
    exact csSup_le hA_nonempty hA_le
  have hdual_nonneg : 0 ≤ affineDirectionDualNorm X p zeta :=
    affineDirectionDualNorm_nonneg_of_separating p hp zeta
  have hsquare :=
    (sq_le_sq₀ hdual_nonneg (Real.sqrt_nonneg C)).2 hdual_le
  simpa [Real.sq_sqrt hC_nonneg] using hsquare

/-- V0: the canonical support-dual controls every primal-unit affine direction. -/
private theorem _voucher_step_scalar_unit_support_from_affine_dual
    {X : Set E} (p : Seminorm ℝ E) (hp : p.IsSeparating)
    (zeta d : E) (hd : d ∈ (affineSpan ℝ X).direction) (hpd : p d ≤ 1) :
    |⟪zeta, d⟫_ℝ| ≤ affineDirectionDualNorm X p zeta := by
  have hsupport :
      |⟪zeta, d⟫_ℝ| ≤ affineDirectionDualNorm X p zeta * p d :=
    affineDirectionDualNorm_inner_le_mul_primalNorm_of_separating p hp zeta d hd
  have hdual_nonneg : 0 ≤ affineDirectionDualNorm X p zeta :=
    affineDirectionDualNorm_nonneg_of_separating p hp zeta
  calc
    |⟪zeta, d⟫_ℝ| ≤ affineDirectionDualNorm X p zeta * p d := hsupport
    _ ≤ affineDirectionDualNorm X p zeta * 1 :=
      mul_le_mul_of_nonneg_left hpd hdual_nonneg
    _ = affineDirectionDualNorm X p zeta := by ring

/-- V1: selected carrier gradients give an affine-direction gradient gap. -/
private theorem _voucher_step_scalar_gradient_gap_mem_direction
    {X : Set E} (grad : {x : E // x ∈ X} → E)
    (hgrad_mem_direction :
      ∀ z : {x : E // x ∈ X}, grad z ∈ (affineSpan ℝ X).direction)
    (x y : {x : E // x ∈ X}) :
    grad x - grad y ∈ (affineSpan ℝ X).direction := by
  exact (affineSpan ℝ X).direction.sub_mem
    (hgrad_mem_direction x) (hgrad_mem_direction y)

/-- V2: convex first-order support gives nonnegative carrier Bregman gaps. -/
private theorem _voucher_step_scalar_gap_nonneg
    {X : Set E} (v : {x : E // x ∈ X} → ℝ)
    (grad : {x : E // x ∈ X} → E)
    (hBreg_nonneg :
      ∀ x y : {x : E // x ∈ X},
        0 ≤ v x - v y - ⟪grad y, x.1 - y.1⟫_ℝ)
    (x y : {x : E // x ∈ X}) :
    0 ≤ v x - v y - ⟪grad y, x.1 - y.1⟫_ℝ :=
  hBreg_nonneg x y

/-- V3: the smooth upper model supplies the quadratic upper bound for the same
carrier gap. -/
private theorem _voucher_step_scalar_gap_upper
    {X : Set E} (v : {x : E // x ∈ X} → ℝ)
    (grad : {x : E // x ∈ X} → E) (p : Seminorm ℝ E) (L : ℝ)
    (hBreg_upper :
      ∀ x y : {x : E // x ∈ X},
        v x - v y - ⟪grad y, x.1 - y.1⟫_ℝ ≤
          L / 2 * p (x.1 - y.1) ^ 2)
    (x y : {x : E // x ∈ X}) :
    v x - v y - ⟪grad y, x.1 - y.1⟫_ℝ ≤
      L / 2 * p (x.1 - y.1) ^ 2 :=
  hBreg_upper x y

/-- V4: the paper smoothness assumption is already in the canonical
affine-direction dual norm used by Lemma 5.8. -/
private theorem _voucher_step_scalar_gradient_lipschitz
    {X : Set E} (grad : {x : E // x ∈ X} → E)
    (p : Seminorm ℝ E) (L : ℝ)
    (hgrad_lipschitz :
      ∀ x y : {x : E // x ∈ X},
        affineDirectionDualNorm X p (grad x - grad y) ≤ L * p (x.1 - y.1))
    (x y : {x : E // x ∈ X}) :
    affineDirectionDualNorm X p (grad x - grad y) ≤ L * p (x.1 - y.1) :=
  hgrad_lipschitz x y

/-- Feasible inverse-step subcase of the scalar directional Lemma 5.8 endpoint.

This proves exactly the calculation in Lan's displayed proof after specializing
the inverse gradient step to a support direction `d`.  It is intentionally only
a subcase: the source proof evaluates this shifted point without checking
whether it remains in a closed constrained carrier. -/
private theorem _voucher_step_scalar_directional_of_descent_point_mem
    {X : Set E} (v : {x : E // x ∈ X} → ℝ)
    (grad : {x : E // x ∈ X} → E) (p : Seminorm ℝ E) (L : ℝ)
    (hBreg_nonneg :
      ∀ x y : {x : E // x ∈ X},
        0 ≤ v x - v y - ⟪grad y, x.1 - y.1⟫_ℝ)
    (hBreg_upper :
      ∀ x y : {x : E // x ∈ X},
        v x - v y - ⟪grad y, x.1 - y.1⟫_ℝ ≤
          L / 2 * p (x.1 - y.1) ^ 2)
    (x y : {x : E // x ∈ X}) (d : E)
    (hpd : p d ≤ 1) (hL_pos : 0 < L)
    (hdescent :
      x.1 - (⟪grad x - grad y, d⟫_ℝ / L) • d ∈ X) :
    |⟪grad x - grad y, d⟫_ℝ| ^ 2 ≤
      2 * L * (v x - v y - ⟪grad y, x.1 - y.1⟫_ℝ) := by
  let a : ℝ := ⟪grad x - grad y, d⟫_ℝ
  let wPoint : E := x.1 - (a / L) • d
  let w : {x : E // x ∈ X} := ⟨wPoint, by simpa [wPoint, a] using hdescent⟩
  have hsupport_wy :
      0 ≤ v w - v y - ⟪grad y, w.1 - y.1⟫_ℝ :=
    hBreg_nonneg w y
  have hupper_wx :
      v w - v x - ⟪grad x, w.1 - x.1⟫_ℝ ≤
        L / 2 * p (w.1 - x.1) ^ 2 :=
    hBreg_upper w x
  have hw_sub : w.1 - x.1 = - (a / L) • d := by
    dsimp [w, wPoint]
    simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have hprimal_wx :
      p (w.1 - x.1) ≤ |a| / L := by
    have hnorm_nonneg : 0 ≤ ‖a / L‖ := norm_nonneg _
    have hscale :
        p (w.1 - x.1) = ‖a / L‖ * p d := by
      rw [hw_sub]
      simp [map_smul_eq_mul]
    have hmul : ‖a / L‖ * p d ≤ ‖a / L‖ * 1 :=
      mul_le_mul_of_nonneg_left hpd hnorm_nonneg
    calc
      p (w.1 - x.1) = ‖a / L‖ * p d := hscale
      _ ≤ ‖a / L‖ * 1 := hmul
      _ = |a| / L := by
        rw [Real.norm_eq_abs, abs_div, abs_of_pos hL_pos]
        ring
  have hprimal_sq :
      p (w.1 - x.1) ^ 2 ≤ (|a| / L) ^ 2 := by
    exact (sq_le_sq₀ (apply_nonneg p (w.1 - x.1))
      (div_nonneg (abs_nonneg a) hL_pos.le)).2 hprimal_wx
  have hinner_wx :
      ⟪grad x - grad y, w.1 - x.1⟫_ℝ = - a ^ 2 / L := by
    rw [hw_sub]
    simp [a, inner_smul_right]
    ring
  have hphi_upper :
      v w - v y - ⟪grad y, w.1 - y.1⟫_ℝ ≤
        (v x - v y - ⟪grad y, x.1 - y.1⟫_ℝ) -
          a ^ 2 / L + (L / 2) * p (w.1 - x.1) ^ 2 := by
    calc
      v w - v y - ⟪grad y, w.1 - y.1⟫_ℝ
          = (v w - v x - ⟪grad x, w.1 - x.1⟫_ℝ) +
              (v x - v y - ⟪grad y, x.1 - y.1⟫_ℝ) +
              ⟪grad x - grad y, w.1 - x.1⟫_ℝ := by
            have hwy : w.1 - y.1 = (x.1 - y.1) + (w.1 - x.1) := by
              abel
            rw [hwy, inner_add_right, inner_sub_left]
            ring
      _ ≤ (L / 2) * p (w.1 - x.1) ^ 2 +
            (v x - v y - ⟪grad y, x.1 - y.1⟫_ℝ) +
            ⟪grad x - grad y, w.1 - x.1⟫_ℝ := by
            linarith [hupper_wx]
      _ = (v x - v y - ⟪grad y, x.1 - y.1⟫_ℝ) -
            a ^ 2 / L + (L / 2) * p (w.1 - x.1) ^ 2 := by
            rw [hinner_wx]
            ring
  have hquad_le :
      (L / 2) * p (w.1 - x.1) ^ 2 ≤ a ^ 2 / (2 * L) := by
    have hmul :=
      mul_le_mul_of_nonneg_left hprimal_sq (by nlinarith [hL_pos] : 0 ≤ L / 2)
    have habs_sq : |a| ^ 2 = a ^ 2 := by exact sq_abs a
    calc
      (L / 2) * p (w.1 - x.1) ^ 2
          ≤ (L / 2) * (|a| / L) ^ 2 := hmul
      _ = a ^ 2 / (2 * L) := by
        rw [div_pow, habs_sq]
        field_simp [hL_pos.ne']
  have hgap_lower :
      a ^ 2 / (2 * L) ≤ v x - v y - ⟪grad y, x.1 - y.1⟫_ℝ := by
    let gap : ℝ := v x - v y - ⟪grad y, x.1 - y.1⟫_ℝ
    let phi_w : ℝ := v w - v y - ⟪grad y, w.1 - y.1⟫_ℝ
    have hphi_le2 : phi_w ≤ gap - a ^ 2 / L + a ^ 2 / (2 * L) := by
      dsimp [phi_w, gap]
      nlinarith [hphi_upper, hquad_le]
    have hnonneg : 0 ≤ gap - a ^ 2 / L + a ^ 2 / (2 * L) := by
      exact le_trans (by simpa [phi_w] using hsupport_wy) hphi_le2
    have hrewrite :
        gap - a ^ 2 / L + a ^ 2 / (2 * L) =
          gap - a ^ 2 / (2 * L) := by
      field_simp [hL_pos.ne']
      ring
    have : 0 ≤ gap - a ^ 2 / (2 * L) := by
      simpa [hrewrite] using hnonneg
    dsimp [gap] at this ⊢
    linarith
  have hmul_nonneg : 0 ≤ 2 * L := by nlinarith
  have hscaled :
      a ^ 2 ≤ 2 * L * (v x - v y - ⟪grad y, x.1 - y.1⟫_ℝ) := by
    have h := mul_le_mul_of_nonneg_left hgap_lower hmul_nonneg
    field_simp [hL_pos.ne'] at h
    nlinarith
  simpa [a, sq_abs] using hscaled

/-- Typed source-gap witness for Lan Lemma 5.8's printed shifted-point step.

Closed convex feasibility alone does not force the inverse-gradient-style point
used in the textbook proof to remain feasible.  The actual Lemma 5.8 route below
therefore still needs a closed-carrier transport theorem, not another attempt to
prove shifted-point membership from `IsClosed X` and `Convex ℝ X`. -/
private theorem lemma58_shifted_point_not_forced_by_closed_convex_carrier :
    ∃ (X : Set ℝ) (x d L : ℝ),
      IsClosed X ∧ Convex ℝ X ∧ x ∈ X ∧ 0 < L ∧ x - (1 / L) • d ∉ X := by
  refine ⟨Set.Ici (0 : ℝ), 0, 1, 1, ?_, ?_, ?_, ?_, ?_⟩
  · exact isClosed_Ici
  · exact convex_Ici _
  · simp
  · norm_num
  · norm_num

/-- Same branch obstruction at the support-direction granularity used by the
closed-carrier Baillon-Haddad bridge.

Even with a separating primal seminorm, a nonzero primal-unit affine direction,
and a nonzero scalar step, closed convexity does not force the inverse-step point
used in Lan Lemma 5.8's proof to stay feasible.  This certificate is not a
replacement proof route; it keeps the remaining bridge obligation focused on
closed-carrier boundary transport rather than shifted-point membership. -/
private theorem lemma58_unit_inverse_step_not_forced_by_closed_convex_carrier :
    ∃ (X : Set ℝ) (p : Seminorm ℝ ℝ) (x d L a : ℝ),
      IsClosed X ∧ Convex ℝ X ∧ x ∈ X ∧ p.IsSeparating ∧
        d ∈ (affineSpan ℝ X).direction ∧ p d ≤ 1 ∧ p d ≠ 0 ∧
          0 < L ∧ a ≠ 0 ∧ x - (a / L) • d ∉ X := by
  refine ⟨Set.Ici (0 : ℝ), normSeminorm ℝ ℝ, 0, 1, 1, 1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isClosed_Ici
  · exact convex_Ici _
  · simp
  · intro y
    rw [coe_normSeminorm]
    exact norm_eq_zero
  · have h1 : (1 : ℝ) ∈ Set.Ici (0 : ℝ) := by norm_num
    have h0 : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := by norm_num
    simpa using
      (AffineSubspace.vsub_mem_direction
        (subset_affineSpan ℝ (Set.Ici (0 : ℝ)) h1)
        (subset_affineSpan ℝ (Set.Ici (0 : ℝ)) h0))
  · rw [coe_normSeminorm]
    norm_num
  · rw [coe_normSeminorm]
    norm_num
  · norm_num
  · norm_num
  · norm_num

/-- The residual intrinsic-interior branch in the closed-carrier bridge is real.

Even after moving the endpoint to the intrinsic interior, closed convexity and a
nonzero affine support direction do not force the inverse step used in Lan's
printed Lemma 5.8 proof to remain feasible.  This is exact same-branch evidence:
the remaining proof below must use a genuine constrained Baillon-Haddad argument,
not a contradiction from `hu ∈ intrinsicInterior ℝ X`. -/
private theorem lemma58_intrinsic_nonzero_inverse_step_not_forced :
    ∃ (X : Set ℝ) (p : Seminorm ℝ ℝ) (u d L a : ℝ),
      IsClosed X ∧ Convex ℝ X ∧ u ∈ intrinsicInterior ℝ X ∧
        p.IsSeparating ∧ d ∈ (affineSpan ℝ X).direction ∧ p d ≤ 1 ∧
          p d ≠ 0 ∧ 0 < L ∧ a ≠ 0 ∧ u - (a / L) • d ∉ X := by
  refine ⟨Set.Icc (0 : ℝ) 1, normSeminorm ℝ ℝ, (1 / 2 : ℝ), 1, 1, 1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isClosed_Icc
  · exact convex_Icc _ _
  · exact interior_subset_intrinsicInterior
      (by norm_num : (1 / 2 : ℝ) ∈ interior (Set.Icc (0 : ℝ) 1))
  · intro y
    rw [coe_normSeminorm]
    exact norm_eq_zero
  · have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
    simpa using
      (AffineSubspace.vsub_mem_direction
        (subset_affineSpan ℝ (Set.Icc (0 : ℝ) 1) h1)
        (subset_affineSpan ℝ (Set.Icc (0 : ℝ) 1) h0))
  · rw [coe_normSeminorm]
    norm_num
  · rw [coe_normSeminorm]
    norm_num
  · norm_num
  · norm_num
  · norm_num

set_option maxHeartbeats 800000

-- The retired unconditional carrier bridge has been removed.
-- The component gap below is proved from the explicit extension condition.
set_option maxHeartbeats 200000

/-- Component smooth quadratic upper model in the paper seminorm.

This is the descent-lemma part of Lan Lemma 5.8, before the
Baillon-Haddad/co-coercivity step. It consumes the reconstructed component
gradient semantics and the paper's primal/dual norm smoothness assumption
directly, so the remaining Lemma 5.8 leaf no longer has to derive the smooth
upper model as part of the same obligation. -/
private theorem component_smooth_quadratic_upper_bound
    (S : Setup ι E) (i : ι) {base y : E} (hbase : base ∈ S.X) (hy : y ∈ S.X) :
    S.f i y ≤ S.f i base + ⟪S.gradF i base, y - base⟫_ℝ +
      (S.Lcomp i / 2) * S.primalNorm (y - base) ^ 2 := by
  exact
    SOptLib.carrier_smooth_quadratic_upper_bound_of_affineDirectionDualNorm_lipschitz
      (X := S.X) (F := S.f i) (grad := S.gradF i)
      (p := S.primalNorm) (L := S.Lcomp i)
      S.hprimalNorm_separating S.hX_convex
      (fun z hz => S.hcomponent_hasGradient i z hz)
      (by
        intro x hx y hy
        simpa [dualNorm] using S.hcomponent_smooth i x y hx hy)
      hbase hy

/-- Single-sided component gap from the explicit convex smooth extension.
The global quadratic upper model uses the original primal norm and Lcomp.
The proved affine-direction dual estimate preserves the corresponding dual
norm, the carrier gradient, and the single-sided coefficient. -/
private theorem component_carrier_baillon_haddad_gap
    (S : Setup ι E) (i : ι) {x z : E}
    (hx : x ∈ S.X) (hz : z ∈ S.X) (hLpos : 0 < S.Lcomp i) :
    (1 / (2 * S.Lcomp i)) * S.dualNorm (S.gradF i x - S.gradF i z) ^ 2 ≤
      S.f i x - S.f i z - ⟪S.gradF i z, x - z⟫_ℝ := by
  obtain ⟨ext⟩ := S.component_extension i hLpos
  simpa only [dualNorm, affineDirectionDualNorm, S.gradF_of_mem i hx,
    S.gradF_of_mem i hz] using ext.affineDual_gap hLpos ⟨x, hx⟩ ⟨z, hz⟩

private theorem unit_direction_inner_sq_le_component_smoothness_gap_of_descent_point_mem
    (S : Setup ι E) (i : ι) {x z d : E}
    (hx : x ∈ S.X) (hz : z ∈ S.X)
    (hpd : S.primalNorm d ≤ 1)
    (hLpos : 0 < S.Lcomp i)
    (hdescent :
      x - (⟪S.gradF i x - S.gradF i z, d⟫_ℝ / S.Lcomp i) • d ∈ S.X) :
    |⟪S.gradF i x - S.gradF i z, d⟫_ℝ| ^ 2 ≤
      2 * S.Lcomp i *
        (S.f i x - S.f i z - ⟪S.gradF i z, x - z⟫_ℝ) := by
  let a : ℝ := ⟪S.gradF i x - S.gradF i z, d⟫_ℝ
  let y : E := x - (a / S.Lcomp i) • d
  have hy : y ∈ S.X := by
    simpa [y, a] using hdescent
  have hgrad_z : HasGradientWithinAt (S.f i) (S.gradF i z) S.X z :=
    S.hcomponent_hasGradient i z hz
  have hsupport_yz :
      0 ≤ S.f i y - S.f i z - ⟪S.gradF i z, y - z⟫_ℝ := by
    have h :=
      ConvexOn.firstOrderLinearModel_le_of_hasGradientWithinAt
        S.hX_convex (S.hcomponent_convex i) hz hy hgrad_z
    linarith
  have hupper_xy :
      S.f i y ≤ S.f i x + ⟪S.gradF i x, y - x⟫_ℝ +
        (S.Lcomp i / 2) * S.primalNorm (y - x) ^ 2 :=
    component_smooth_quadratic_upper_bound S i hx hy
  have hy_sub : y - x = - (a / S.Lcomp i) • d := by
    simp [y, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have hprimal_yx :
      S.primalNorm (y - x) ≤ |a| / S.Lcomp i := by
    have hnorm_nonneg : 0 ≤ ‖a / S.Lcomp i‖ := norm_nonneg _
    have hscale :
        S.primalNorm (y - x) = ‖a / S.Lcomp i‖ * S.primalNorm d := by
      rw [hy_sub]
      simp [map_smul_eq_mul]
    have hmul : ‖a / S.Lcomp i‖ * S.primalNorm d ≤ ‖a / S.Lcomp i‖ * 1 :=
      mul_le_mul_of_nonneg_left hpd hnorm_nonneg
    calc
      S.primalNorm (y - x) = ‖a / S.Lcomp i‖ * S.primalNorm d := hscale
      _ ≤ ‖a / S.Lcomp i‖ * 1 := hmul
      _ = |a| / S.Lcomp i := by
        rw [Real.norm_eq_abs, abs_div, abs_of_pos hLpos]
        ring
  have hprimal_sq :
      S.primalNorm (y - x) ^ 2 ≤ (|a| / S.Lcomp i) ^ 2 := by
    exact (sq_le_sq₀ (apply_nonneg S.primalNorm (y - x))
      (div_nonneg (abs_nonneg a) hLpos.le)).2 hprimal_yx
  have hinner_yx :
      ⟪S.gradF i x - S.gradF i z, y - x⟫_ℝ = - a ^ 2 / S.Lcomp i := by
    rw [hy_sub]
    simp [a, inner_smul_right]
    ring
  have hphi_upper :
      S.f i y - S.f i z - ⟪S.gradF i z, y - z⟫_ℝ ≤
        (S.f i x - S.f i z - ⟪S.gradF i z, x - z⟫_ℝ) -
          a ^ 2 / S.Lcomp i +
            (S.Lcomp i / 2) * S.primalNorm (y - x) ^ 2 := by
    calc
      S.f i y - S.f i z - ⟪S.gradF i z, y - z⟫_ℝ
          ≤ (S.f i x + ⟪S.gradF i x, y - x⟫_ℝ +
              (S.Lcomp i / 2) * S.primalNorm (y - x) ^ 2) -
              S.f i z - ⟪S.gradF i z, y - z⟫_ℝ := by
            linarith [hupper_xy]
      _ = (S.f i x - S.f i z - ⟪S.gradF i z, x - z⟫_ℝ) +
            ⟪S.gradF i x - S.gradF i z, y - x⟫_ℝ +
              (S.Lcomp i / 2) * S.primalNorm (y - x) ^ 2 := by
            have hyz : y - z = (x - z) + (y - x) := by abel
            rw [hyz, inner_add_right, inner_sub_left]
            ring
      _ = (S.f i x - S.f i z - ⟪S.gradF i z, x - z⟫_ℝ) -
            a ^ 2 / S.Lcomp i +
              (S.Lcomp i / 2) * S.primalNorm (y - x) ^ 2 := by
            rw [hinner_yx]
            ring
  have hquad_le :
      (S.Lcomp i / 2) * S.primalNorm (y - x) ^ 2 ≤
        a ^ 2 / (2 * S.Lcomp i) := by
    have hmul :=
      mul_le_mul_of_nonneg_left hprimal_sq (by nlinarith [hLpos] :
        0 ≤ S.Lcomp i / 2)
    have habs_sq : |a| ^ 2 = a ^ 2 := by exact sq_abs a
    calc
      (S.Lcomp i / 2) * S.primalNorm (y - x) ^ 2
          ≤ (S.Lcomp i / 2) * (|a| / S.Lcomp i) ^ 2 := hmul
      _ = a ^ 2 / (2 * S.Lcomp i) := by
        rw [div_pow, habs_sq]
        field_simp [hLpos.ne']
  have hgap_lower :
      a ^ 2 / (2 * S.Lcomp i) ≤
        S.f i x - S.f i z - ⟪S.gradF i z, x - z⟫_ℝ := by
    let gap : ℝ := S.f i x - S.f i z - ⟪S.gradF i z, x - z⟫_ℝ
    let phi_y : ℝ := S.f i y - S.f i z - ⟪S.gradF i z, y - z⟫_ℝ
    have hphi_le2 : phi_y ≤ gap - a ^ 2 / S.Lcomp i + a ^ 2 / (2 * S.Lcomp i) := by
      dsimp [phi_y, gap]
      nlinarith [hphi_upper, hquad_le]
    have hnonneg : 0 ≤ gap - a ^ 2 / S.Lcomp i + a ^ 2 / (2 * S.Lcomp i) := by
      exact le_trans (by simpa [phi_y] using hsupport_yz) hphi_le2
    have hrewrite :
        gap - a ^ 2 / S.Lcomp i + a ^ 2 / (2 * S.Lcomp i) =
          gap - a ^ 2 / (2 * S.Lcomp i) := by
      field_simp [hLpos.ne']
      ring
    have : 0 ≤ gap - a ^ 2 / (2 * S.Lcomp i) := by
      simpa [hrewrite] using hnonneg
    dsimp [gap] at this ⊢
    linarith
  have hmul_nonneg : 0 ≤ 2 * S.Lcomp i := by nlinarith
  have hscaled :
      a ^ 2 ≤
        2 * S.Lcomp i *
          (S.f i x - S.f i z - ⟪S.gradF i z, x - z⟫_ℝ) := by
    have h := mul_le_mul_of_nonneg_left hgap_lower hmul_nonneg
    field_simp [hLpos.ne'] at h
    nlinarith
  simpa [a, sq_abs] using hscaled

/-- Scalar directional form of Lan Lemma 5.8.

This is the remaining analytic co-coercivity leaf after the object-model
repair: for each primal-unit affine direction, the squared pairing with the
component gradient gap is controlled by the smoothness gap. The source proof is
Lan Lemma 5.8, lines 14735--14756, after specializing the dual support vector. -/
private theorem unit_direction_inner_sq_le_component_smoothness_gap
    (S : Setup ι E) (i : ι) {x z d : E}
    (hx : x ∈ S.X) (hz : z ∈ S.X)
    (hd : d ∈ (affineSpan ℝ S.X).direction) (hpd : S.primalNorm d ≤ 1)
    (hLpos : 0 < S.Lcomp i) :
    |⟪S.gradF i x - S.gradF i z, d⟫_ℝ| ^ 2 ≤
      2 * S.Lcomp i *
        (S.f i x - S.f i z - ⟪S.gradF i z, x - z⟫_ℝ) := by
  have hgrad_x : HasGradientWithinAt (S.f i) (S.gradF i x) S.X x :=
    S.hcomponent_hasGradient i x hx
  have hgrad_z : HasGradientWithinAt (S.f i) (S.gradF i z) S.X z :=
    S.hcomponent_hasGradient i z hz
  have hsupport_xz :
      0 ≤ S.f i x - S.f i z - ⟪S.gradF i z, x - z⟫_ℝ := by
    have h :=
      ConvexOn.firstOrderLinearModel_le_of_hasGradientWithinAt
        S.hX_convex (S.hcomponent_convex i) hz hx hgrad_z
    linarith
  have hsmooth_xz :
      S.dualNorm (S.gradF i x - S.gradF i z) ≤
        S.Lcomp i * S.primalNorm (x - z) := by
    simpa [dualNorm] using S.hcomponent_smooth i x z hx hz
  have hupper_xz :
      S.f i x ≤ S.f i z + ⟪S.gradF i z, x - z⟫_ℝ +
        (S.Lcomp i / 2) * S.primalNorm (x - z) ^ 2 :=
    component_smooth_quadratic_upper_bound S i hz hx
  have hupper_zx :
      S.f i z ≤ S.f i x + ⟪S.gradF i x, z - x⟫_ℝ +
        (S.Lcomp i / 2) * S.primalNorm (z - x) ^ 2 :=
    component_smooth_quadratic_upper_bound S i hx hz
  let zeta : E := S.gradF i x - S.gradF i z
  let gap : ℝ := S.f i x - S.f i z - ⟪S.gradF i z, x - z⟫_ℝ
  have hdual_gap :
      (1 / (2 * S.Lcomp i)) * S.dualNorm zeta ^ 2 ≤ gap := by
    simpa [zeta, gap] using
      component_carrier_baillon_haddad_gap (S := S) i hx hz hLpos
  have hdual_sq_gap :
      S.dualNorm zeta ^ 2 ≤ 2 * S.Lcomp i * gap := by
    have hden_pos : 0 < 2 * S.Lcomp i := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hdual_gap hden_pos.le
    have hleft :
        (2 * S.Lcomp i) * ((1 / (2 * S.Lcomp i)) * S.dualNorm zeta ^ 2) =
          S.dualNorm zeta ^ 2 := by
      field_simp [hden_pos.ne']
    have hright :
        (2 * S.Lcomp i) * gap = 2 * S.Lcomp i * gap := by ring
    nlinarith
  have hinner_dual :
      |⟪zeta, d⟫_ℝ| ≤ S.dualNorm zeta := by
    have hsupport :=
      dualNorm_inner_le_mul_primalNorm_for_component_smoothness S zeta d hd
    have hdual_nonneg : 0 ≤ S.dualNorm zeta :=
      dualNorm_nonneg_for_component_smoothness S zeta
    calc
      |⟪zeta, d⟫_ℝ| ≤ S.dualNorm zeta * S.primalNorm d := hsupport
      _ ≤ S.dualNorm zeta * 1 := mul_le_mul_of_nonneg_left hpd hdual_nonneg
      _ = S.dualNorm zeta := by ring
  have hinner_sq :
      |⟪zeta, d⟫_ℝ| ^ 2 ≤ S.dualNorm zeta ^ 2 := by
    exact (sq_le_sq₀ (abs_nonneg _) (dualNorm_nonneg_for_component_smoothness S zeta)).2
      hinner_dual
  simpa [zeta, gap] using le_trans hinner_sq hdual_sq_gap

/-- Paper Lemma 5.8 for a component function of the RGEM finite sum. -/
theorem SmoothnessGradientGap_Lemma_5_8
    (i : ι) {x z : E} (hx : x ∈ S.X) (hz : z ∈ S.X) (hLpos : 0 < S.Lcomp i) :
    (1 / (2 * S.Lcomp i)) * S.dualNorm (S.gradF i x - S.gradF i z) ^ 2 ≤
      S.f i x - S.f i z - ⟪S.gradF i z, x - z⟫_ℝ := by
  exact component_carrier_baillon_haddad_gap (S := S) i hx hz hLpos

/-- Totalized nonnegative-`L_i` form of Lan Lemma 5.8 used in Proposition 5.6.

Aligns with Lan Proposition 5.6 proof step 4 and the paper assumption
`L_i >= 0`: in the positive branch it is exactly
`S.SmoothnessGradientGap_Lemma_5_8`, while in the zero branch Lean's total
division makes the left side vanish and component convexity gives the
first-order gap. Candidate audit: searched `component smoothness gradient gap
nonnegative L convex first order`, checked the strict paper lemma
`S.SmoothnessGradientGap_Lemma_5_8`, `ConvexOn.firstOrderLinearModel_le_of_hasGradientWithinAt`,
and SOptLib Layer0/Objective smoothness-gap candidates; none already states the
paper's totalized nonnegative-`L_i` form because the reusable smoothness-gap
theorems require strict `L > 0` or use projected ambient gradients rather than
this setup's affine-direction dual norm. -/
private theorem component_smoothness_bound_of_nonnegative_L
    (i : ι) {x z : E} (hx : x ∈ S.X) (hz : z ∈ S.X) :
    (1 / (2 * S.Lcomp i)) * S.dualNorm (S.gradF i x - S.gradF i z) ^ 2 ≤
      S.f i x - S.f i z - ⟪S.gradF i z, x - z⟫_ℝ := by
  by_cases hL : 0 < S.Lcomp i
  · exact component_carrier_baillon_haddad_gap S i hx hz hL
  · have hzero : S.Lcomp i = 0 := le_antisymm (le_of_not_gt hL) (S.hLcomp_nonneg i)
    simp only [hzero, mul_zero, div_zero, zero_mul]
    have h := ConvexOn.firstOrderLinearModel_le_of_hasGradientWithinAt
      S.hX_convex (S.hcomponent_convex i) hz hx (S.hcomponent_hasGradient i z hz)
    linarith

theorem GradientExtrapolationDefinition_Eq_5_2_49
    (t : ℕ) (s : State ι E) (i : ι) :
    SOptLib.extrapolatedPoint (S.α t) ((s).yCurr i) ((s).yPrev i) =
      s.yCurr i + S.α t • (s.yCurr i - s.yPrev i) := by
  simp [SOptLib.extrapolatedPoint, add_comm]

/-- Source theorem head for Eq. (5.2.50), the prox update and one-step inequality (5.2.71). -/
theorem ProxStepInequality_Eq_5_2_71
    (t : ℕ) (s : {s : State ι E // S.StateFeasible s})
    (hηt : 0 < S.η t) {x : E} (hx : x ∈ S.X) :
    let yTilde : ι → E := fun i => SOptLib.extrapolatedPoint (S.α t) ((s.1).yCurr i) ((s.1).yPrev i)
    let xNext : E := S.proxPoint t s.1.x yTilde s.2.1 hηt
    ⟪xNext - x, tableAverage yTilde⟫_ℝ + S.μ * S.ν xNext - S.μ * S.ν x ≤
      S.η t * S.V s.1.x x - (S.μ + S.η t) * S.V xNext x -
        S.η t * S.V s.1.x xNext := by
  dsimp only
  let yTilde : ι → E := fun i => SOptLib.extrapolatedPoint (S.α t) ((s.1).yCurr i) ((s.1).yPrev i)
  let xNext : E := S.proxPoint t s.1.x yTilde s.2.1 hηt
  let g : E := tableAverage yTilde
  let p : E → ℝ := fun z =>
    ⟪g, z⟫_ℝ + S.μ * (S.ν x + ⟪S.gradν x, z - x⟫_ℝ)
  have hp : ConvexOn ℝ S.X p := by
    unfold ConvexOn
    constructor
    · exact S.hX_convex
    · intro x1 hx1 x2 hx2 a b ha hb hab
      have hb_eq : b = 1 - a := by linarith
      subst b
      dsimp [p]
      simp only [inner_add_right, inner_smul_right, inner_sub_right]
      ring_nf
      exact le_rfl
  have hxNext : xNext ∈ S.X :=
    S.proxPoint_mem t s.1.x yTilde s.2.1 hηt
  have hmin0 : IsMinOn (S.proxObjective t s.1.x yTilde) S.X xNext := by
    simpa [xNext] using S.proxPoint_isMinOn t s.1.x yTilde s.2.1 hηt
  have hobj_eq : ∀ z,
      p z + S.η t * S.V s.1.x z + S.μ * S.V x z =
        S.proxObjective t s.1.x yTilde z := by
    intro z
    dsimp [p, g]
    unfold proxObjective V
    ring_nf
  have hmin' :
      IsMinOn (fun z => p z + S.η t * S.V s.1.x z + S.μ * S.V x z) S.X
        xNext := by
    rw [isMinOn_iff] at hmin0 ⊢
    intro z hz
    rw [hobj_eq xNext, hobj_eq z]
    exact hmin0 z hz
  have h3 := S.ProxMappingInequality_Lemma_3_5 p s.1.x x xNext x
    (S.η t) S.μ hp s.2.1 hx hxNext hx (le_of_lt hηt) S.hμ_nonneg hmin'
  have h3obj :
      S.proxObjective t s.1.x yTilde xNext ≤
        S.proxObjective t s.1.x yTilde x -
          (S.η t + S.μ) * S.V xNext x := by
    rw [← hobj_eq xNext, ← hobj_eq x]
    exact h3
  have h3' :
      ⟪g, xNext⟫_ℝ + S.μ * S.ν xNext + S.η t * S.V s.1.x xNext ≤
        ⟪g, x⟫_ℝ + S.μ * S.ν x + S.η t * S.V s.1.x x -
          (S.η t + S.μ) * S.V xNext x := by
    dsimp [g] at h3obj ⊢
    unfold proxObjective at h3obj
    simpa [add_assoc, add_comm, add_left_comm] using h3obj
  have hinner :
      ⟪xNext - x, g⟫_ℝ = ⟪g, xNext⟫_ℝ - ⟪g, x⟫_ℝ := by
    rw [inner_sub_left]
    rw [real_inner_comm xNext g, real_inner_comm x g]
  rw [hinner]
  nlinarith [h3']

/-- Generated positive-eta specialization of the prox inequality (5.2.71).

Aligns with Lan Proposition 5.6 proof step 1 before expectation. Candidate audit:
`S.ProxStepInequality_Eq_5_2_71` is the matching source theorem for the abstract
feasible state; `S.SmoothnessGradientGap_Lemma_5_8` and
`S.ConditionalBlockExpectation_Lemma_5_9_positive_domain` are later ingredients
for (5.2.72)/(5.2.73), not the generated-run prox specialization itself. -/
private theorem proposition56_generated_prox_step_inequality_5_2_71_positive_domain
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 1 ≤ t) (ω : BlockSamplePath ι)
    {x : E} (hx : x ∈ S.X) :
    let prev : State ι E := S.positiveEtaGeneratedProcess hη (t - 1) ω
    let yTilde : ι → E := fun i => SOptLib.extrapolatedPoint (S.α t) ((prev).yCurr i) ((prev).yPrev i)
    let xNext : E := S.positiveEtaXIterate hη t ω
    ⟪xNext - x, tableAverage yTilde⟫_ℝ + S.μ * S.ν xNext - S.μ * S.ν x ≤
      S.η t * S.V prev.x x - (S.μ + S.η t) * S.V xNext x -
        S.η t * S.V prev.x xNext := by
  classical
  cases t with
  | zero =>
      cases ht
  | succ n =>
      let s : {s : State ι E // S.StateFeasible s} := S.positiveEtaProcess hη n ω
      have hprox := S.ProxStepInequality_Eq_5_2_71 (n + 1) s
        (hη (n + 1) (Nat.succ_pos n)) hx
      simpa [s, positiveEtaXIterate, positiveEtaGeneratedProcess, positiveEtaProcess,
        Nat.succ_sub_one] using hprox

/-- Auxiliary point feasibility for the generated positive-eta process.

Aligns with Lan Eq. (5.2.57) in the Proposition 5.6 smoothness step. Candidate
audit: checked `SOptLib.relaxedMemoryRefreshPoint_mem_of_convex`, which exactly
matches the convex-combination feasibility argument after unfolding this paper's
`auxiliaryPoint`; no target-file theorem previously exposed this generated
`x_hat_i^t ∈ X` fact. -/
private theorem proposition56_auxiliary_point_mem_positive_domain
    (hη : S.PositiveEtaDomain) (t : ℕ) (ω : BlockSamplePath ι) (i : ι) :
    S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
        ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i) ∈ S.X := by
  classical
  have hτ : 0 ≤ S.τ t := (S.hparam_nonneg t).2.2
  have hxNext : S.positiveEtaXIterate hη t ω ∈ S.X :=
    S.positiveEtaXIterate_mem hη t ω
  have hprev :
      (S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i ∈ S.X := by
    simpa [positiveEtaGeneratedProcess] using
      (S.positiveEtaProcess hη (t - 1) ω).2.2 i
  have hrefresh :
      SOptLib.relaxedMemoryRefreshPoint (S.τ t) (S.positiveEtaXIterate hη t ω)
          ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i) ∈ S.X :=
    SOptLib.relaxedMemoryRefreshPoint_mem_of_convex S.hX_convex hτ hxNext hprev
  simpa [auxiliaryPoint, SOptLib.relaxedMemoryRefreshPoint] using hrefresh

/-- Generated positive-eta specialization of Lemma 5.8 for the auxiliary point.

Aligns with Lan Proposition 5.6 proof step 4, the smoothness part of Eq.
(5.2.72). Candidate audit: `S.SmoothnessGradientGap_Lemma_5_8` is the matching
strict-positive source theorem, but Proposition 5.6 only assumes `L_i >= 0`;
the private nonnegative-`L_i` component bound combines that strict theorem with
convex first-order support in the zero case. -/
private theorem proposition56_auxiliary_smoothness_gap_5_2_72_positive_domain
    (hη : S.PositiveEtaDomain) {t : ℕ} (ω : BlockSamplePath ι) (i : ι) :
    (1 / (2 * S.Lcomp i)) *
        S.dualNorm
          (S.gradF i
              (S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
                ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) -
            S.gradF i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) ^ 2 ≤
      S.f i
          (S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
            ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) -
        S.f i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i) -
        ⟪S.gradF i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i),
          S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
              ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i) -
            (S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i⟫_ℝ := by
  classical
  have haux :
      S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
          ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i) ∈ S.X :=
    S.proposition56_auxiliary_point_mem_positive_domain hη t ω i
  have hprev :
      (S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i ∈ S.X := by
    simpa [positiveEtaGeneratedProcess] using
      (S.positiveEtaProcess hη (t - 1) ω).2.2 i
  simpa using S.component_smoothness_bound_of_nonnegative_L i haux hprev

/-- Pointwise component part of Lan Eq. (5.2.72), before taking expectations.

This is the literal source orientation of Lemma 5.8 used in Proposition 5.6:
the smoothness gap is applied with `x = x_i^{t-1}` and
`z = \hat x_i^t`, so the linear term uses the auxiliary gradient
`\hat y_i^t = ∇ f_i(\hat x_i^t)`.  This is strictly below the expected
one-step theorem and does not use the tombstoned y-window helper. -/
private theorem proposition56_component_eq_5_2_72_pointwise_positive_domain
    (hη : S.PositiveEtaDomain) {t : ℕ} (ω : BlockSamplePath ι)
    {x : E} (hx : x ∈ S.X) :
    (1 + S.τ t) * (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ
          (fun i =>
            S.f i
              (S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
                ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i))) -
      S.fAvg x ≤
      S.τ t * (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ
            (fun i => S.f i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) +
        (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ
            (fun i =>
              ⟪S.positiveEtaXIterate hη t ω - x,
                S.auxiliaryGradient t (S.positiveEtaXIterate hη t ω)
                  (S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i⟫_ℝ) -
        S.τ t * (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ
            (fun i =>
              (1 / (2 * S.Lcomp i)) *
                S.dualNorm
                  (S.gradF i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i) -
                    S.gradF i
                      (S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
                        ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i))) ^ 2) := by
  classical
  let m : ℝ := (Fintype.card ι : ℝ)
  let xNext : E := S.positiveEtaXIterate hη t ω
  let prev : State ι E := S.positiveEtaGeneratedProcess hη (t - 1) ω
  let a : ι → E := fun i => S.auxiliaryPoint t xNext (prev.blockX i)
  let g : ι → E := fun i => S.auxiliaryGradient t xNext prev.blockX i
  let gap : ι → ℝ := fun i =>
    (1 / (2 * S.Lcomp i)) *
      S.dualNorm (S.gradF i (prev.blockX i) - S.gradF i (a i)) ^ 2
  have hτ_nonneg : 0 ≤ S.τ t := (S.hparam_nonneg t).2.2
  have hcomponent : ∀ i,
      (1 + S.τ t) * S.f i (a i) - S.f i x ≤
        S.τ t * S.f i (prev.blockX i) + ⟪xNext - x, g i⟫_ℝ -
          S.τ t * gap i := by
    intro i
    have haux_mem : a i ∈ S.X := by
      simpa [a, xNext, prev] using
        S.proposition56_auxiliary_point_mem_positive_domain hη t ω i
    have hprev_mem : prev.blockX i ∈ S.X := by
      simpa [prev, positiveEtaGeneratedProcess] using
        (S.positiveEtaProcess hη (t - 1) ω).2.2 i
    have hconv :
        S.f i (a i) - S.f i x ≤ ⟪a i - x, S.gradF i (a i)⟫_ℝ := by
      have hsupport :
          S.f i (a i) + ⟪S.gradF i (a i), x - a i⟫_ℝ ≤ S.f i x :=
        ConvexOn.firstOrderLinearModel_le_of_hasGradientWithinAt
          S.hX_convex (S.hcomponent_convex i) haux_mem hx
          (S.hcomponent_hasGradient i (a i) haux_mem)
      have hdir :
          S.f i (a i) - S.f i x ≤ -⟪S.gradF i (a i), x - a i⟫_ℝ := by
        linarith
      have hinner :
          -⟪S.gradF i (a i), x - a i⟫_ℝ =
            ⟪a i - x, S.gradF i (a i)⟫_ℝ := by
        rw [real_inner_comm]
        simp [sub_eq_add_neg, inner_add_left]
      linarith
    have hsmooth :
        gap i ≤
          S.f i (prev.blockX i) - S.f i (a i) -
            ⟪S.gradF i (a i), prev.blockX i - a i⟫_ℝ := by
      have h :=
        S.component_smoothness_bound_of_nonnegative_L
          i (x := prev.blockX i) (z := a i) hprev_mem haux_mem
      simpa [gap] using h
    have hrefresh :
        xNext = (1 + S.τ t) • a i - S.τ t • prev.blockX i := by
      simpa [a, xNext, prev] using S.auxiliaryPoint_solve t xNext (prev.blockX i)
    have hdesc :=
      relaxedMemoryRefresh_component_descent_of_smooth_gap
        (f := S.f i) (grad := S.gradF i) (tau := S.τ t)
        (xNext := xNext) (prev := prev.blockX i) (x := x) (a := a i)
        (gap := gap i) hτ_nonneg hconv hsmooth hrefresh
    simpa [g, a, auxiliaryGradient] using hdesc
  have hsum :
      Finset.sum Finset.univ
          (fun i => (1 + S.τ t) * S.f i (a i) - S.f i x) ≤
        Finset.sum Finset.univ
          (fun i =>
            S.τ t * S.f i (prev.blockX i) + ⟪xNext - x, g i⟫_ℝ -
              S.τ t * gap i) :=
    Finset.sum_le_sum (fun i _hi => hcomponent i)
  have hm_ne : m ≠ 0 := by
    dsimp [m]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
  have hscaled := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ m⁻¹)
  have hleft :
      m⁻¹ *
          Finset.sum Finset.univ
            (fun i => (1 + S.τ t) * S.f i (a i) - S.f i x) =
        (1 + S.τ t) * m⁻¹ * Finset.sum Finset.univ (fun i => S.f i (a i)) -
          S.fAvg x := by
    dsimp [Setup.fAvg, m]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    field_simp [hm_ne]
  have hright :
      m⁻¹ *
          Finset.sum Finset.univ
            (fun i =>
              S.τ t * S.f i (prev.blockX i) + ⟪xNext - x, g i⟫_ℝ -
                S.τ t * gap i) =
        S.τ t * m⁻¹ * Finset.sum Finset.univ (fun i => S.f i (prev.blockX i)) +
          m⁻¹ * Finset.sum Finset.univ (fun i => ⟪xNext - x, g i⟫_ℝ) -
          S.τ t * m⁻¹ * Finset.sum Finset.univ gap := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    ring
  rw [hleft, hright] at hscaled
  simpa [a, g, gap, xNext, prev, m] using hscaled

/-- Helper feasibility theorem for an externally supplied process satisfying Eq. (5.2.50).

Book JSON `#/key_lemmas[name=PrimalUpdateFeasibility_Eq_5_2_50]/statement_math`
quotes
`x^t=argmin_{x∈X}{...+η_t V(x^{t-1},x)}` for the generated paper iterate.
This process-parametric declaration is retained only as transport scaffolding;
the exported source-boundary realization is the positive-eta generated theorem
`PrimalUpdateFeasibility_Eq_5_2_50_positive_domain`. -/
theorem primalUpdateFeasibility_of_process_equations
    {process : ℕ → BlockSamplePath ι → State ι E}
    (hprocess : S.DeterministicRGEMProcessEquations process)
    (t : ℕ) (ω : BlockSamplePath ι) :
    S.xIterateOfProcess process t ω ∈ S.X :=
  S.xIterateOfProcess_mem hprocess t ω

/-- Corrected-domain generated-run feasibility for Eq. (5.2.50).

This is not the printed theorem head: it adds
`PositiveEtaDomain`, justified by book JSON `#/assumptions/5`, which lists the
prox mapping parameters with `η>0`. -/
theorem PrimalUpdateFeasibility_Eq_5_2_50_positive_domain
    (hη : S.PositiveEtaDomain) (t : ℕ) (ω : BlockSamplePath ι) :
    S.positiveEtaXIterate hη t ω ∈ S.X :=
  S.positiveEtaXIterate_mem hη t ω

/-- Source theorem head for Eq. (5.2.57), the auxiliary block point. -/
theorem AuxiliaryPointIdentity_Eq_5_2_57 (t : ℕ) (x blockPrev : E) :
    S.auxiliaryPoint t x blockPrev =
      ((1 : ℝ) + S.τ t)⁻¹ • (x + S.τ t • blockPrev) := by
  rfl

/-- Source theorem head for Eq. (5.2.58), the auxiliary gradient. -/
theorem AuxiliaryGradientIdentity_Eq_5_2_58 (t : ℕ) (x : E) (blockPrev : ι → E)
    (i : ι) :
    S.auxiliaryGradient t x blockPrev i =
      S.gradF i (S.auxiliaryPoint t x (blockPrev i)) := by
  rfl

/-- Helper unfolding for `SOptLib.weightedAverageOutputValue`.

This is intentionally not the paper-named Eq. (5.2.53): book JSON
`#/algorithm_spec/output` defines the weighted output from the generated RGEM
iterates `x^t`, not from an arbitrary sequence. -/
theorem weightedAverageOutputValue_unfold
    (x : ℕ → BlockSamplePath ι → E)
    (k : ℕ) (hk : 1 ≤ k) (hθ : S.OutputWeightsPositive k)
    (ω : BlockSamplePath ι) :
    SOptLib.weightedAverageOutputValue
        (Ω := BlockSamplePath ι) (T := ℕ) (W := ℕ) (E := E)
        (fun k => outputWindow k) S.θ x S.outputWeightSum k ω =
      (S.outputWeightSum k)⁻¹ •
        Finset.sum (outputWindow k) (fun t => S.θ t • x t ω) := by
  rfl

/-- Bridge from the proof-selected Theorem 5.4 output to Eq. (5.2.53)'s output.

Theorem 5.4's proof sets `θ_t = α^{-t}`. Under that source policy, the auxiliary
`theoremWeightedOutput` is the same object as the Algorithm 5.4 weighted output
`positiveEtaWeightedOutput` built from the Eq. (5.2.50) iterates. -/
theorem theoremWeightedOutput_eq_positiveEtaWeightedOutput
    (hμ_pos : 0 < S.μ)
    (hη_policy : ∀ t, 1 ≤ t → S.η t = S.constantEta hμ_pos)
    {k : ℕ} (hk : 1 ≤ k)
    (hθ_policy : S.TheoremOutputWeightPolicy hμ_pos k)
    (ω : BlockSamplePath ι) :
    S.theoremWeightedOutput hμ_pos hη_policy k hk
        (S.theoremTheta_outputWeightsPositive hk hμ_pos) ω =
      S.positiveEtaWeightedOutput (S.theoremPositiveEtaDomain hμ_pos hη_policy) k hk
        (S.outputWeightsPositive_of_theoremThetaPolicy hk hμ_pos hθ_policy) ω := by
  -- Finite-sum extensionality over the output window and the theta-policy
  -- identify the two displayed normalized sums.
  rw [S.theoremWeightedOutput_def, S.positiveEtaWeightedOutput_def]
  have hden : S.theoremOutputWeightSum hμ_pos k = S.outputWeightSum k := by
    unfold theoremOutputWeightSum outputWeightSum
    apply Finset.sum_congr rfl
    intro t ht
    exact (hθ_policy t ht).symm
  have hsum :
      Finset.sum (outputWindow k)
          (fun t => S.theoremTheta hμ_pos t • S.theoremXIterate hμ_pos hη_policy t ω) =
        Finset.sum (outputWindow k)
          (fun t => S.θ t •
            S.positiveEtaXIterate (S.theoremPositiveEtaDomain hμ_pos hη_policy) t ω) := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [← hθ_policy t ht]
    rfl
  rw [hden, hsum]

/-- Corrected-domain generated-output specialization of Eq. (5.2.53). -/
theorem WeightedOutputDefinition_Eq_5_2_53_positive_domain
    (hη : S.PositiveEtaDomain) (k : ℕ) (hk : 1 ≤ k) (hθ : S.OutputWeightsPositive k)
    (ω : BlockSamplePath ι) :
    S.positiveEtaWeightedOutput hη k hk hθ ω =
      (S.outputWeightSum k)⁻¹ •
        Finset.sum (outputWindow k) (fun t => S.θ t • S.positiveEtaXIterate hη t ω) := by
  simpa [positiveEtaWeightedOutput] using
    S.weightedAverageOutputValue_unfold (S.positiveEtaXIterate hη) k hk hθ ω

/-- Source theorem head for Eq. (5.2.59), the definition of `Q`. -/
theorem QDefinition_Eq_5_2_59 (xUnder x : E) :
    S.Q xUnder x =
      ⟪(Fintype.card ι : ℝ)⁻¹ •
          Finset.sum Finset.univ (fun i => S.gradF i x), xUnder - x⟫_ℝ +
        S.μ * S.ν xUnder - S.μ * S.ν x := by
  rfl

/-- Optimality condition for a solution of problem (5.2.1), used before Eq. (5.2.60). -/
theorem OptimalityCondition_Problem_5_2_1
    {xStar x : E} (hopt : S.IsOptimalSolution xStar) (hx : x ∈ S.X) :
    0 ≤ ⟪tableAverage (fun i => S.gradF i xStar) + S.μ • S.gradν xStar,
        x - xStar⟫_ℝ := by
  rcases hopt with ⟨hxStar, hmin⟩
  have hbase : HasGradientWithinAt (fun y : E => S.μ * S.ν y)
      (S.μ • S.gradν xStar) S.X xStar := by
    have hderiv := (S.hν_hasGradientWithinAt xStar hxStar).hasFDerivWithinAt.const_smul S.μ
    simpa [smul_eq_mul, map_smul] using hderiv.hasGradientWithinAt
  have hsplit : 0 ≤
      ⟪S.μ • S.gradν xStar, x - xStar⟫_ℝ +
        (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ (fun i : ι => ⟪S.gradF i xStar, x - xStar⟫_ℝ) := by
    exact Convex.first_order_condition_sum_add_of_isMinOn
      (X := S.X) (x := xStar) (y := x)
      (phi := fun y : E => S.μ * S.ν y) (psi := fun i => S.f i)
      (gradPhi := S.μ • S.gradν xStar) (gradPsi := fun i => S.gradF i xStar)
      S.hX_convex hxStar hx (by
        intro u hu
        simpa [S.psi_def] using hmin u hu) hbase
      (fun i => S.hcomponent_hasGradient i xStar hxStar)
  simpa [tableAverage, inner_add_left, inner_smul_left, sum_inner,
    add_comm, add_left_comm, add_assoc] using hsplit

/-- Nonnegativity fact for `Q(·,x*)` recorded before Eq. (5.2.60). -/
theorem QNonnegativity_Optimality_Pre_5_2_60
    {xStar x : E} (hopt : S.IsOptimalSolution xStar) (hx : x ∈ S.X) :
    0 ≤ S.Q x xStar := by
  simpa [Q] using
    regularizedFirstOrderGap_nonneg_of_minimizer
      (X := S.X) (F := S.f) (gradF := S.gradF) (nu := S.ν) (gradNu := S.gradν)
      (mu := S.μ) (x := x) (xStar := xStar)
      S.hX_convex hopt.1 hx
      (by intro y hy; simpa [S.psi_def] using hopt.2 y hy)
      (S.hν_hasGradientWithinAt xStar hopt.1)
      (fun i => S.hcomponent_hasGradient i xStar hopt.1)
      S.hμ_nonneg
      (by nlinarith [S.hν_strong x xStar hx hopt.1,
        sq_nonneg (S.primalNorm (x - xStar))])

/-- Convexity of the distance-generating function on the feasible carrier.

The setup stores the stronger Eq. (5.2.3) inequality rather than a separate
convexity field for `ν`. Candidate audit: searched `nu convex strong convex
ConvexOn` and checked SOptLib convexity helpers; no existing lemma specializes
this RGEM carrier-gradient strong-convexity field, so this local bridge derives
the ordinary convexity consequence used by Proposition 5.6's Jensen step. -/
private theorem nu_convexOn_from_strong : ConvexOn ℝ S.X S.ν := by
  exact ConvexOn.of_first_order_lower_support
    (X := S.X) (phi := S.ν)
    (support := fun z => (innerSL ℝ (S.gradν z)).toLinearMap) S.hX_convex
    (fun x z hx hz => by
      simpa [innerSL_apply_apply] using
        (show S.ν z + ⟪S.gradν z, x - z⟫_ℝ ≤ S.ν x by
          nlinarith [S.hν_strong x z hx hz, sq_nonneg (S.primalNorm (x - z))]))

/-- Convexity of `Q(·,x*)` on the feasible carrier for Proposition 5.6 Jensen.

This aligns with Lan Proposition 5.6 proof step 25: `Q` is the sum of an affine
term and the nonnegative scalar `μ` times the convex regularizer `ν`. Candidate
audit: searched `Q convex affine mu nu weighted output Jensen`; the reusable
generic Jensen lemmas require this paper-specific convexity bridge, and no
target-file helper previously exposed it. -/
private theorem q_convexOn_positive_domain (xStar : E) :
    ConvexOn ℝ S.X (fun x => S.Q x xStar) := by
  classical
  refine ⟨S.hX_convex, ?_⟩
  intro x hx y hy a b ha hb hab
  let z : E := a • x + b • y
  have hνconv := (S.nu_convexOn_from_strong).2 hx hy ha hb hab
  let g : E := (Fintype.card ι : ℝ)⁻¹ •
      Finset.sum Finset.univ (fun i => S.gradF i xStar)
  have hlin :
      ⟪g, z - xStar⟫_ℝ =
        a * ⟪g, x - xStar⟫_ℝ + b * ⟪g, y - xStar⟫_ℝ := by
    subst z
    have hvec : a • x + b • y - xStar =
        a • (x - xStar) + b • (y - xStar) := by
      have hb_eq : b = 1 - a := by linarith
      subst b
      module
    rw [hvec, inner_add_right, inner_smul_right, inner_smul_right]
  have hνconv' : S.ν z ≤ a * S.ν x + b * S.ν y := by
    simpa [z, smul_eq_mul] using hνconv
  have hμν : S.μ * S.ν z ≤ S.μ * (a * S.ν x + b * S.ν y) :=
    mul_le_mul_of_nonneg_left hνconv' S.hμ_nonneg
  unfold Q SOptLib.finiteAverageGradientRegularizerGap
  change
    ⟪g, z - xStar⟫_ℝ + S.μ * S.ν z - S.μ * S.ν xStar ≤
      a * (⟪g, x - xStar⟫_ℝ + S.μ * S.ν x - S.μ * S.ν xStar) +
        b * (⟪g, y - xStar⟫_ℝ + S.μ * S.ν y - S.μ * S.ν xStar)
  calc
    ⟪g, z - xStar⟫_ℝ + S.μ * S.ν z - S.μ * S.ν xStar
        ≤ ⟪g, z - xStar⟫_ℝ + S.μ * (a * S.ν x + b * S.ν y) -
            S.μ * S.ν xStar := by
          nlinarith [hμν]
    _ = a * (⟪g, x - xStar⟫_ℝ + S.μ * S.ν x - S.μ * S.ν xStar) +
        b * (⟪g, y - xStar⟫_ℝ + S.μ * S.ν y - S.μ * S.ν xStar) := by
          rw [hlin]
          have hb_eq : b = 1 - a := by linarith
          subst b
          ring

/-- Weighted nonnegativity of the Proposition 5.6 `Q(x^t,x*)` sum.

This is the Lean form of the nonnegativity side used in Lan Proposition 5.6
proof steps 22 and 26. Candidate audit: searched `pre Delta Proposition 5.6
weighted Q sum`, `integral nonnegative expectation nonnegative ae`, and `iterate
feasibility positive eta primal update`; the matching paper-specific ingredients
are `QNonnegativity_Optimality_Pre_5_2_60` and
`PrimalUpdateFeasibility_Eq_5_2_50_positive_domain`, while SOptLib only provides
generic integral monotonicity infrastructure. -/
private theorem q_nonnegative_weighted_sum_positive_domain
    (hη : S.PositiveEtaDomain) {k : ℕ} {xStar : E}
    (hopt : S.IsOptimalSolution xStar)
    (hθ : S.OutputWeightsNonnegative k) :
    0 ≤
      Finset.sum (outputWindow k)
        (fun t => S.θ t *
          SOptLib.expectation S.P
            (fun ω => S.Q (S.positiveEtaXIterate hη t ω) xStar)) := by
  refine Finset.sum_nonneg ?_
  intro t ht
  have hθt : 0 ≤ S.θ t := hθ t ht
  have hEt_nonneg :
      0 ≤ SOptLib.expectation S.P
        (fun ω => S.Q (S.positiveEtaXIterate hη t ω) xStar) := by
    unfold SOptLib.expectation
    exact integral_nonneg (fun ω =>
      S.QNonnegativity_Optimality_Pre_5_2_60 hopt
        (S.PrimalUpdateFeasibility_Eq_5_2_50_positive_domain hη t ω))
  exact mul_nonneg hθt hEt_nonneg

/-- Optimality turns the initial linearized smooth gap into the initial `ψ` gap.

This is Lan Proposition 5.6 proof step 23. Candidate audit: searched the target
for `OptimalityCondition_Problem_5_2_1`, `psi`, and `fAvg`; the exact reusable
ingredient is the local optimality condition, while SOptLib convex FOC lemmas do
not mention RGEM's `fAvg`/`ψ` split. -/
private theorem proposition56_initial_linearized_gap_le_psi_gap
    {xStar : E} (hopt : S.IsOptimalSolution xStar) :
    S.fAvg S.x0 -
        ⟪S.x0 - xStar, tableAverage (fun i => S.gradF i xStar)⟫_ℝ -
        S.fAvg xStar ≤
      S.psi S.x0 - S.psi xStar := by
  classical
  let d : E := S.x0 - xStar
  let g : E := tableAverage (fun i => S.gradF i xStar)
  let ngrad : E := S.gradν xStar
  have hoptlin := S.OptimalityCondition_Problem_5_2_1 hopt S.hx0_mem
  have hsmul :
      ⟪S.μ • ngrad, d⟫_ℝ = S.μ * ⟪ngrad, d⟫_ℝ := by
    simpa [ngrad] using (real_inner_smul_left (S.gradν xStar) d S.μ)
  have hopt_scalar : 0 ≤ ⟪g, d⟫_ℝ + S.μ * ⟪ngrad, d⟫_ℝ := by
    simpa [g, d, ngrad, inner_add_left, hsmul] using hoptlin
  have hnu_strong := S.hν_strong S.x0 xStar S.hx0_mem hopt.1
  have hnu_lin : ⟪ngrad, d⟫_ℝ ≤ S.ν S.x0 - S.ν xStar := by
    have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) * S.primalNorm d ^ 2 := by
      nlinarith [sq_nonneg (S.primalNorm d)]
    simp [V, d, ngrad] at hnu_strong
    nlinarith
  have hmu_nu :
      S.μ * ⟪ngrad, d⟫_ℝ ≤ S.μ * (S.ν S.x0 - S.ν xStar) :=
    mul_le_mul_of_nonneg_left hnu_lin S.hμ_nonneg
  have hlinear :
      -⟪S.x0 - xStar, tableAverage (fun i => S.gradF i xStar)⟫_ℝ ≤
        S.μ * (S.ν S.x0 - S.ν xStar) := by
    have hgcomm : ⟪S.x0 - xStar, tableAverage (fun i => S.gradF i xStar)⟫_ℝ =
        ⟪g, d⟫_ℝ := by
      simp [g, d, real_inner_comm]
    rw [hgcomm]
    nlinarith [hopt_scalar, hmu_nu]
  have hpsi0 : S.psi S.x0 = S.fAvg S.x0 + S.μ * S.ν S.x0 := by
    simp [fAvg, psi]
  have hpsistar : S.psi xStar = S.fAvg xStar + S.μ * S.ν xStar := by
    simp [fAvg, psi]
  rw [hpsi0, hpsistar]
  nlinarith [hlinear]

/-- Rearrangement of the Proposition 5.6 pre-Delta inequality to the final `V` bound.

This is Lan Proposition 5.6 proof step 26 after the source-derived pre-Delta
estimate has been obtained. Candidate audit: searched `le division iff positive
real` and `mul_le_mul_left positive iff`; no RGEM-specific bridge existed, so
the proof uses the local `q_nonnegative_weighted_sum_positive_domain` plus
ordered-field arithmetic to divide by the positive coefficient
`θ_k(μ+η_k)/2`. -/
private theorem proposition56_pre_delta_to_v_bound_positive_domain
    {k : ℕ} {xStar : E} {sigma0 : ℝ}
    (hk : 1 ≤ k)
    (hη : S.PositiveEtaDomain)
    (hopt : S.IsOptimalSolution xStar)
    (hθ_pos : S.OutputWeightsPositive k)
    (hwdV : SOptLib.expectationWellDefined S.P
      (fun ω => S.V (S.positiveEtaXIterate hη k ω) xStar))
    (hpre :
      Finset.sum (outputWindow k)
          (fun t => S.θ t *
            SOptLib.expectation S.P
              (fun ω => S.Q (S.positiveEtaXIterate hη t ω) xStar)) +
        (S.θ k * (S.μ + S.η k) / 2) *
          SOptLib.expectation S.P
            (fun ω => S.V (S.positiveEtaXIterate hη k ω) xStar) ≤
        S.DeltaTilde0Sigma0 hη k xStar sigma0) :
    expectationLe S.P
      (fun ω => S.V (S.positiveEtaXIterate hη k ω) xStar)
      (2 * S.DeltaTilde0Sigma0 hη k xStar sigma0 /
        (S.θ k * (S.μ + S.η k))) := by
  refine And.intro hwdV ?_
  let qSum : ℝ :=
    Finset.sum (outputWindow k)
      (fun t => S.θ t *
        SOptLib.expectation S.P
          (fun ω => S.Q (S.positiveEtaXIterate hη t ω) xStar))
  let vExp : ℝ :=
    SOptLib.expectation S.P
      (fun ω => S.V (S.positiveEtaXIterate hη k ω) xStar)
  let den : ℝ := S.θ k * (S.μ + S.η k)
  let Δ : ℝ := S.DeltaTilde0Sigma0 hη k xStar sigma0
  have hq_nonneg : 0 ≤ qSum := by
    simpa [qSum] using
      (S.q_nonnegative_weighted_sum_positive_domain hη hopt
        (S.outputWeightsNonnegative_of_positive hθ_pos))
  have hk_mem : k ∈ outputWindow k := Finset.mem_Icc.mpr ⟨hk, le_rfl⟩
  have hθk_pos : 0 < S.θ k := hθ_pos k hk_mem
  have hηk_pos : 0 < S.η k := hη k hk
  have hmu_eta_pos : 0 < S.μ + S.η k :=
    add_pos_of_nonneg_of_pos S.hμ_nonneg hηk_pos
  have hden_pos : 0 < den := by
    simpa [den] using mul_pos hθk_pos hmu_eta_pos
  have hv_bound : vExp ≤ 2 * Δ / den := by
    exact le_two_mul_div_of_nonneg_add_half_mul_le qSum vExp Δ den
      hq_nonneg hden_pos (by simpa [qSum, vExp, den, Δ] using hpre)
  simpa [vExp, den, Δ] using hv_bound

/-- Route-local scalar integration lemma used for the paper-seminorm smoothness bridge.

The SOptLib lemma `le_value_add_of_hasDerivWithinAt_le_affine_on_Icc` was searched
and its source inspected, but the name is not available under this target's current
imports; this local copy keeps only the `[0,1]` derivative-bound form needed for
Lan Eq. (5.2.60). -/
private theorem scalar_value_le_add_of_hasDerivWithinAt_le_affine_on_Icc
    (F phi : ℝ → ℝ) (A B : ℝ)
    (hderiv : ∀ (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1),
      HasDerivWithinAt F (phi t) (Set.Icc (0 : ℝ) 1) t)
    (hbound : ∀ (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1),
      phi t ≤ A + B * t) :
    F 1 ≤ F 0 + A + B / 2 := by
  let I : Set ℝ := Set.Icc (0 : ℝ) 1
  let q : ℝ → ℝ := fun t => F 0 + A * t + (B / 2) * t ^ 2 - F t
  have hq_deriv_Icc : ∀ (t : ℝ), t ∈ I →
      HasDerivWithinAt q (A + B * t - phi t) I t := by
    intro t ht
    have h0 : HasDerivWithinAt (fun _ : ℝ => F 0) 0 I t := by
      simpa using (hasDerivWithinAt_const (c := F 0) (s := I) (x := t))
    have hA : HasDerivWithinAt (fun u : ℝ => A * u) A I t := by
      simpa using ((hasDerivWithinAt_id t I).const_mul A)
    have hB : HasDerivWithinAt (fun u : ℝ => (B / 2) * u ^ 2) (B * t) I t := by
      have hp : HasDerivWithinAt (fun u : ℝ => u ^ 2) (2 * t ^ (2 - 1)) I t := by
        simpa using (hasDerivWithinAt_pow (2 : ℕ) (x := t) (s := I))
      have h := hp.const_mul (B / 2)
      convert h using 1 <;> ring
    have hsum := (h0.add hA).add hB
    have hq := hsum.sub (hderiv t ht)
    convert hq using 1 <;> ring
  have hq_cont : ContinuousOn q I := by
    intro t ht
    exact (hq_deriv_Icc t ht).continuousWithinAt
  have hq_deriv_int : ∀ (t : ℝ), t ∈ interior I →
      HasDerivWithinAt q (A + B * t - phi t) (interior I) t := by
    intro t ht
    exact (hq_deriv_Icc t (interior_subset ht)).mono interior_subset
  have hq_nonneg : ∀ (t : ℝ), t ∈ interior I → 0 ≤ A + B * t - phi t := by
    intro t ht
    have hb := hbound t (interior_subset ht)
    linarith
  have hmono : MonotoneOn q I :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) 1)
      hq_cont hq_deriv_int hq_nonneg
  have h01 : q 0 ≤ q 1 :=
    hmono (by norm_num [I]) (by norm_num [I]) (by norm_num)
  dsimp [q] at h01
  norm_num at h01
  linarith

/-- Finite-average gradient identity used in the smoothness proof for Eq. (5.2.60).

Candidate audit: searched `HasGradientWithinAt finite average sum gradient`; SOptLib's
`HasGradientWithinAt.fintype_average` matches this statement but is not available under
the current imports, so this proof reproduces the narrow finite-sum derivative step from
the component witnesses `S.hcomponent_hasGradient`. -/
private theorem fAvg_hasGradientWithinAt
    (S : Setup ι E) {z : E} (hz : z ∈ S.X) :
    HasGradientWithinAt S.fAvg (tableAverage (fun i => S.gradF i z)) S.X z := by
  classical
  unfold fAvg tableAverage
  have hsum : HasFDerivWithinAt
      (fun y : E => Finset.sum Finset.univ (fun i : ι => S.f i y))
      (Finset.sum Finset.univ
        (fun i : ι => InnerProductSpace.toDual ℝ E (S.gradF i z))) S.X z := by
    refine HasFDerivWithinAt.fun_sum ?_
    intro i _hi
    exact (S.hcomponent_hasGradient i z hz).hasFDerivWithinAt
  have hscaled := hsum.const_smul ((Fintype.card ι : ℝ)⁻¹)
  convert hscaled.hasGradientWithinAt using 1
  simp [map_smul, map_sum]

/-- Canonical dual-norm support inequality in the paper's primal seminorm.

Aligns with the primal/dual norm pairing in Eq. (5.2.4). The proof reuses
`SOptLib.abs_inner_le_canonicalDualNorm_mul` after deriving finite-dimensional
ambient boundedness of the primal unit ball from `S.hprimalNorm_separating`. -/
private theorem dualNorm_inner_le_mul_primalNorm
    (S : Setup ι E) (zeta d : E) (hd : d ∈ (affineSpan ℝ S.X).direction) :
    |⟪zeta, d⟫_ℝ| ≤ S.dualNorm zeta * S.primalNorm d := by
  classical
  rcases Seminorm.exists_norm_le_mul_self_of_finiteDimensional_separating
      S.primalNorm S.hprimalNorm_separating with ⟨C, hCnonneg, hC⟩
  have h_bdd :
      BddAbove {r : ℝ |
        ∃ u : E, u ∈ (affineSpan ℝ S.X).direction ∧
          S.primalNorm u ≤ 1 ∧ r = |inner ℝ zeta u|} := by
    refine ⟨‖zeta‖ * C, ?_⟩
    intro r hr
    rcases hr with ⟨u, _hu_dir, hpu, rfl⟩
    have hinner : |inner ℝ zeta u| ≤ ‖zeta‖ * ‖u‖ := by
      simpa using (norm_inner_le_norm (𝕜 := ℝ) zeta u)
    have hu_norm : ‖u‖ ≤ C := by
      calc
        ‖u‖ ≤ C * S.primalNorm u := hC u
        _ ≤ C * 1 := mul_le_mul_of_nonneg_left hpu hCnonneg
        _ = C := by simp
    exact hinner.trans (mul_le_mul_of_nonneg_left hu_norm (norm_nonneg zeta))
  by_cases hd0 : S.primalNorm d = 0
  · have hd_zero : d = 0 := (S.hprimalNorm_separating d).mp hd0
    simp [hd_zero]
  · have hpd_nonneg : 0 ≤ S.primalNorm d := apply_nonneg S.primalNorm d
    have hpd_pos : 0 < S.primalNorm d := lt_of_le_of_ne hpd_nonneg (Ne.symm hd0)
    let u : E := (S.primalNorm d)⁻¹ • d
    have hu_dir : u ∈ (affineSpan ℝ S.X).direction := by
      exact (affineSpan ℝ S.X).direction.smul_mem _ hd
    have hu_le : S.primalNorm u ≤ 1 := by
      simp [u, map_smul_eq_mul, abs_of_pos hpd_pos, hpd_pos.ne']
    have hsup : |inner ℝ zeta u| ≤ S.dualNorm zeta := by
      rw [dualNorm, affineDirectionDualNorm]
      exact le_csSup h_bdd ⟨u, hu_dir, hu_le, rfl⟩
    have hscale : |inner ℝ zeta u| = (S.primalNorm d)⁻¹ * |inner ℝ zeta d| := by
      simp [u, inner_smul_right, abs_mul, abs_of_pos (inv_pos.mpr hpd_pos)]
    have hinv_le :
        (S.primalNorm d)⁻¹ * |inner ℝ zeta d| ≤ S.dualNorm zeta := by
      simpa [hscale] using hsup
    calc
      |inner ℝ zeta d| = ((S.primalNorm d)⁻¹ * |inner ℝ zeta d|) *
          S.primalNorm d := by
        field_simp [hpd_pos.ne']
      _ ≤ S.dualNorm zeta * S.primalNorm d :=
        mul_le_mul_of_nonneg_right hinv_le hpd_pos.le

/-- Smooth quadratic upper model for the finite-average objective in the paper seminorm.

This is the source-derived bridge for Lan Eq. (5.2.60): searched SOptLib/Mathlib
for `average smooth quadratic upper bound primal dual seminorm`; ambient-norm
finite-average candidates would not preserve the exact `S.Lf`/`S.primalNorm`
constant, so the proof consumes `S.average_smooth`, `S.hcomponent_hasGradient`,
`S.hX_convex`, `S.hprimalNorm_separating`, and `S.hLf_nonneg` directly. -/
private theorem fAvg_smooth_quadratic_upper_bound
    (S : Setup ι E) {base y : E} (hbase : base ∈ S.X) (hy : y ∈ S.X) :
    S.fAvg y ≤ S.fAvg base + ⟪tableAverage (fun i => S.gradF i base), y - base⟫_ℝ +
      (S.Lf / 2) * S.primalNorm (y - base) ^ 2 := by
  classical
  let d : E := y - base
  let s : Set ℝ := Set.Icc (0 : ℝ) 1
  let line : ℝ → E := fun t => AffineMap.lineMap base y t
  let Fseg : ℝ → ℝ := fun t => S.fAvg (line t)
  have hLf_nonneg : 0 ≤ S.Lf := S.hLf_nonneg
  have hF0 : Fseg 0 = S.fAvg base := by
    simp [Fseg, line]
  have hF1 : Fseg 1 = S.fAvg y := by
    simp [Fseg, line]
  have hline_mem : ∀ t ∈ s, line t ∈ S.X := by
    intro t ht
    exact S.hX_convex.lineMap_mem hbase hy ht
  have hmaps : Set.MapsTo line s S.X := by
    intro t ht
    exact hline_mem t ht
  have hderiv : ∀ (t : ℝ) (ht : t ∈ s),
      HasDerivWithinAt Fseg
        ⟪tableAverage (fun i => S.gradF i (line t)), d⟫_ℝ s t := by
    intro t ht
    have hline_deriv : HasDerivWithinAt line d s t := by
      simpa [line, d] using
        (AffineMap.hasDerivWithinAt_lineMap (a := base) (b := y)
          (s := s) (x := t))
    have hfseg : HasDerivWithinAt Fseg
        ((InnerProductSpace.toDual ℝ E
          (tableAverage (fun i => S.gradF i (line t)))) d) s t := by
      simpa [Fseg, Function.comp_def] using
        (fAvg_hasGradientWithinAt S (hline_mem t ht)).hasFDerivWithinAt
          |>.comp_hasDerivWithinAt_of_eq t hline_deriv hmaps (by simp [line])
    simpa using hfseg
  have hbound : ∀ (t : ℝ) (ht : t ∈ s),
      ⟪tableAverage (fun i => S.gradF i (line t)), d⟫_ℝ ≤
        ⟪tableAverage (fun i => S.gradF i base), d⟫_ℝ +
          (S.Lf * S.primalNorm d ^ 2) * t := by
    intro t ht
    have ht_nonneg : 0 ≤ t := ht.1
    have hseg_sub : line t - base = t • d := by
      simp [line, d, AffineMap.lineMap_apply_module']
    have hprimal_line : S.primalNorm (line t - base) = t * S.primalNorm d := by
      rw [hseg_sub]
      simp [map_smul_eq_mul, Real.norm_of_nonneg ht_nonneg]
    have hd_dir : d ∈ (affineSpan ℝ S.X).direction :=
      AffineSubspace.vsub_mem_direction
        (subset_affineSpan ℝ S.X hy) (subset_affineSpan ℝ S.X hbase)
    let delta : E :=
      tableAverage (fun i => S.gradF i (line t)) -
        tableAverage (fun i => S.gradF i base)
    have hinner_diff :
        ⟪tableAverage (fun i => S.gradF i (line t)), d⟫_ℝ -
            ⟪tableAverage (fun i => S.gradF i base), d⟫_ℝ =
          ⟪delta, d⟫_ℝ := by
      simp [delta, inner_sub_left]
    have hdual_smooth :
        S.dualNorm delta ≤ S.Lf * S.primalNorm (line t - base) := by
      have hs := (S.average_smooth (hline_mem t ht) hbase).1
      simpa [delta, tableAverage] using hs
    have habs :
        |⟪delta, d⟫_ℝ| ≤ S.dualNorm delta * S.primalNorm d :=
      dualNorm_inner_le_mul_primalNorm S delta d hd_dir
    have hinner_le :
        ⟪delta, d⟫_ℝ ≤ S.dualNorm delta * S.primalNorm d :=
      (le_abs_self _).trans habs
    have hmul_le :
        S.dualNorm delta * S.primalNorm d ≤
          (S.Lf * S.primalNorm (line t - base)) * S.primalNorm d :=
      mul_le_mul_of_nonneg_right hdual_smooth (apply_nonneg S.primalNorm d)
    have hquad :
        (S.Lf * S.primalNorm (line t - base)) * S.primalNorm d =
          (S.Lf * S.primalNorm d ^ 2) * t := by
      rw [hprimal_line]
      ring
    have hdiff :
        ⟪tableAverage (fun i => S.gradF i (line t)), d⟫_ℝ -
            ⟪tableAverage (fun i => S.gradF i base), d⟫_ℝ ≤
          (S.Lf * S.primalNorm d ^ 2) * t := by
      calc
        ⟪tableAverage (fun i => S.gradF i (line t)), d⟫_ℝ -
            ⟪tableAverage (fun i => S.gradF i base), d⟫_ℝ
            = ⟪delta, d⟫_ℝ := hinner_diff
        _ ≤ S.dualNorm delta * S.primalNorm d := hinner_le
        _ ≤ (S.Lf * S.primalNorm (line t - base)) * S.primalNorm d := hmul_le
        _ = (S.Lf * S.primalNorm d ^ 2) * t := hquad
    have hbudget_nonneg : 0 ≤ (S.Lf * S.primalNorm d ^ 2) * t := by
      have hp_sq_nonneg : 0 ≤ S.primalNorm d ^ 2 := sq_nonneg (S.primalNorm d)
      exact mul_nonneg (mul_nonneg hLf_nonneg hp_sq_nonneg) ht_nonneg
    linarith [hdiff, hbudget_nonneg]
  have hscalar :
      Fseg 1 ≤ Fseg 0 + ⟪tableAverage (fun i => S.gradF i base), d⟫_ℝ +
        (S.Lf * S.primalNorm d ^ 2) / 2 := by
    exact scalar_value_le_add_of_hasDerivWithinAt_le_affine_on_Icc Fseg
      (fun t => ⟪tableAverage (fun i => S.gradF i (line t)), d⟫_ℝ)
      ⟪tableAverage (fun i => S.gradF i base), d⟫_ℝ
      (S.Lf * S.primalNorm d ^ 2) hderiv hbound
  rw [hF0, hF1] at hscalar
  change S.fAvg y ≤
    S.fAvg base + ⟪tableAverage (fun i => S.gradF i base), y - base⟫_ℝ +
      (S.Lf / 2) * S.primalNorm (y - base) ^ 2
  nlinarith

/-- Source theorem head for Eq. (5.2.60), comparing `Q` with the objective gap. -/
theorem QComparison_Eq_5_2_60
    {xStar x : E} (hopt : S.IsOptimalSolution xStar) (hx : x ∈ S.X) :
    -(S.Lf / 2) * S.primalNorm (x - xStar) ^ 2 + S.psi x - S.psi xStar ≤
      S.Q x xStar := by
  have hxStar : xStar ∈ S.X := hopt.1
  have hsmooth :
      S.fAvg x ≤ S.fAvg xStar + ⟪tableAverage (fun i => S.gradF i xStar), x - xStar⟫_ℝ +
        (S.Lf / 2) * S.primalNorm (x - xStar) ^ 2 := by
    exact fAvg_smooth_quadratic_upper_bound S hxStar hx
  have hlin :
      S.fAvg x - S.fAvg xStar - (S.Lf / 2) * S.primalNorm (x - xStar) ^ 2 ≤
        ⟪tableAverage (fun i => S.gradF i xStar), x - xStar⟫_ℝ := by
    nlinarith [hsmooth]
  have hlin_expanded :
      (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i : ι => S.f i x) -
          (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i : ι => S.f i xStar) -
            (S.Lf / 2) * S.primalNorm (x - xStar) ^ 2 ≤
        ⟪(Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ (fun i : ι => S.gradF i xStar),
          x - xStar⟫_ℝ := by
    simpa [fAvg, tableAverage] using hlin
  unfold Q SOptLib.finiteAverageGradientRegularizerGap psi
  nlinarith [hlin_expanded]

/-- Helper for Eq. (5.2.64), characterizing stale gradients for an external process.

Book JSON `#/key_lemmas[name=GradientStateCharacterization_Eq_5_2_64]/statement_math`
quotes the two-case formula
`y_i^t=0` if block `i` has never been updated and
`y_i^t=grad f_i(x_i^t)` otherwise. The printed characterization depends only on
the algorithm equations, not on the corrected positive-eta generated selector. -/
theorem gradientStateCharacterization_of_process_equations
    {process : ℕ → BlockSamplePath ι → State ι E}
    (hprocess : S.DeterministicRGEMProcessEquations process)
    (t : ℕ) (ω : BlockSamplePath ι) (i : ι) :
    ((¬ ∃ r, 1 ≤ r ∧ r ≤ t ∧ S.sample r ω = i) →
        S.yIterateOfProcess process t ω i = 0) ∧
      ((∃ r, 1 ≤ r ∧ r ≤ t ∧ S.sample r ω = i) →
        S.yIterateOfProcess process t ω i =
          S.gradF i (S.blockIterateOfProcess process t ω i)) := by
  simpa [yIterateOfProcess, blockIterateOfProcess] using
    SOptLib.selectedCoordinateGradientMemory_characterization
      (sample := S.sample) (run := process)
      (y := fun s : State ι E => s.yCurr)
      (xmem := fun s : State ι E => s.blockX)
      (grad := S.gradF)
      (h_zero := by
        intro ω i
        have hzero := congrArg (fun s : State ι E => s.yCurr i) (hprocess.1 ω)
        simpa using hzero)
      (h_y_succ := by
        intro n ω
        have hstep := hprocess.2 (n + 1) (Nat.succ_pos n) ω
        simpa using hstep.2.2.2.2)
      (h_xmem_succ_of_ne := by
        intro n ω i hi
        have hstep := hprocess.2 (n + 1) (Nat.succ_pos n) ω
        have hb :
            (process (n + 1) ω).blockX =
              S.blockPointUpdate (n + 1) (S.sample (n + 1) ω)
                (process (n + 1) ω).x (process n ω).blockX := by
          simpa using hstep.2.2.1
        calc
          (process (n + 1) ω).blockX i =
              S.blockPointUpdate (n + 1) (S.sample (n + 1) ω)
                (process (n + 1) ω).x (process n ω).blockX i := by
            exact congrFun hb i
          _ = (process n ω).blockX i := by
            exact S.blockPointUpdate_other (t := n + 1) hi
              (process (n + 1) ω).x (process n ω).blockX)
      t ω i

/-- Corrected-domain generated-process specialization of Eq. (5.2.64). -/
theorem GradientStateCharacterization_Eq_5_2_64_positive_domain
    (hη : S.PositiveEtaDomain) (t : ℕ) (ω : BlockSamplePath ι) (i : ι) :
    ((¬ ∃ r, 1 ≤ r ∧ r ≤ t ∧ S.sample r ω = i) →
        S.positiveEtaYIterate hη t ω i = 0) ∧
      ((∃ r, 1 ≤ r ∧ r ≤ t ∧ S.sample r ω = i) →
        S.positiveEtaYIterate hη t ω i =
          S.gradF i (S.positiveEtaBlockIterate hη t ω i)) := by
  simpa [xIterateOfProcess, blockIterateOfProcess, yIterateOfProcess,
    positiveEtaGeneratedProcess, positiveEtaXIterate, positiveEtaBlockIterate, positiveEtaYIterate] using
    S.gradientStateCharacterization_of_process_equations
      (S.positiveEtaGeneratedProcess_equations hη) t ω i

/-- No-previous-update branch for the positive-eta component point table.

This is the point-table half of Lan Eq. (5.2.64)'s stale-gradient split:
if block `i` has not appeared in `i_1,...,i_t`, then its stored point is still
the initial point. The proof now delegates the history induction to the
paper-free selected-coordinate memory theorem, with RGEM only supplying the
initial state and nonselected block-update equation. -/
private theorem positiveEta_block_iterate_eq_x0_of_no_previous_update
    (hη : S.PositiveEtaDomain) {t : ℕ} {i : ι} {ω : BlockSamplePath ι}
    (hno : ¬ ∃ r, 1 ≤ r ∧ r ≤ t ∧ S.sample r ω = i) :
    S.positiveEtaBlockIterate hη t ω i = S.x0 := by
  simpa [positiveEtaBlockIterate] using
    SOptLib.selectedCoordinateMemory_eq_init_of_no_previous_hit
      (sample := S.sample) (run := S.positiveEtaGeneratedProcess hη)
      (mem := fun state i => state.blockX i) (init := S.x0)
      (h_init := by
        intro ω i
        simp [positiveEtaGeneratedProcess, positiveEtaProcess, initialState])
      (hmem_succ_of_ne := by
        intro n ω i hi
        have hstep := S.positiveEtaGeneratedProcess_succ_equations hη (Nat.succ_pos n) ω
        rcases hstep with ⟨_hxmem, _hmin, hblock, _hyprev, _hycurr⟩
        have hblock_i := congrFun hblock i
        calc
          (S.positiveEtaGeneratedProcess hη (n + 1) ω).blockX i =
              S.blockPointUpdate (n + 1) (S.sample (n + 1) ω)
                (S.positiveEtaGeneratedProcess hη (n + 1) ω).x
                (S.positiveEtaGeneratedProcess hη n ω).blockX i := by
                simpa using hblock_i
          _ = (S.positiveEtaGeneratedProcess hη n ω).blockX i := by
                exact S.blockPointUpdate_other (t := n + 1) hi
                  (S.positiveEtaGeneratedProcess hη (n + 1) ω).x
                  (S.positiveEtaGeneratedProcess hη n ω).blockX)
      (t := t) (ω := ω) (i := i) hno

/-- Formula of Lemma 5.9 over an externally supplied RGEM-equation process. -/
def ConditionalBlockExpectation59FormulaOfProcess
    (process : ℕ → BlockSamplePath ι → State ι E) (t : ℕ) (i : ι) : Prop :=
  let prevState : BlockSamplePath ι → State ι E :=
    fun ω => process (t - 1) ω
  let xNext : BlockSamplePath ι → E :=
    fun ω => S.xIterateOfProcess process t ω
  conditionalExpectationEq S.P (S.paperStrictPastSigma t)
      (fun ω => S.yIterateOfProcess process t ω i)
      (fun ω =>
        (Fintype.card ι : ℝ)⁻¹ •
            S.auxiliaryGradient t (xNext ω) (prevState ω).blockX i +
          (1 - (Fintype.card ι : ℝ)⁻¹) • (prevState ω).yCurr i) ∧
    conditionalExpectationEq S.P (S.paperStrictPastSigma t)
      (fun ω => S.blockIterateOfProcess process t ω i)
      (fun ω =>
        (Fintype.card ι : ℝ)⁻¹ •
            S.auxiliaryPoint t (xNext ω) ((prevState ω).blockX i) +
          (1 - (Fintype.card ι : ℝ)⁻¹) • (prevState ω).blockX i) ∧
    conditionalExpectationEq S.P (S.paperStrictPastSigma t)
      (fun ω => S.f i (S.blockIterateOfProcess process t ω i))
      (fun ω =>
        (Fintype.card ι : ℝ)⁻¹ *
            S.f i (S.auxiliaryPoint t (xNext ω) ((prevState ω).blockX i)) +
          (1 - (Fintype.card ι : ℝ)⁻¹) * S.f i ((prevState ω).blockX i)) ∧
    conditionalExpectationEq S.P (S.paperStrictPastSigma t)
      (fun ω =>
        S.dualNorm
          (S.gradF i (S.blockIterateOfProcess process t ω i) -
            S.gradF i ((prevState ω).blockX i)) ^ 2)
      (fun ω =>
        (Fintype.card ι : ℝ)⁻¹ *
          S.dualNorm
            (S.gradF i (S.auxiliaryPoint t (xNext ω) ((prevState ω).blockX i)) -
              S.gradF i ((prevState ω).blockX i)) ^ 2)

/-- Formula of Lemma 5.9 for the canonical generated deterministic RGEM process. -/
def ConditionalBlockExpectation59Formula
    (hη : S.PositiveEtaDomain) (t : ℕ) (i : ι) : Prop :=
  let prevState : BlockSamplePath ι → State ι E :=
    fun ω => S.positiveEtaGeneratedProcess hη (t - 1) ω
  let xNext : BlockSamplePath ι → E :=
    fun ω => S.positiveEtaXIterate hη t ω
  conditionalExpectationEq S.P (S.paperStrictPastSigma t)
      (fun ω => S.positiveEtaYIterate hη t ω i)
      (fun ω =>
        (Fintype.card ι : ℝ)⁻¹ •
            S.auxiliaryGradient t (xNext ω) (prevState ω).blockX i +
          (1 - (Fintype.card ι : ℝ)⁻¹) • (prevState ω).yCurr i) ∧
    conditionalExpectationEq S.P (S.paperStrictPastSigma t)
      (fun ω => S.positiveEtaBlockIterate hη t ω i)
      (fun ω =>
        (Fintype.card ι : ℝ)⁻¹ •
            S.auxiliaryPoint t (xNext ω) ((prevState ω).blockX i) +
          (1 - (Fintype.card ι : ℝ)⁻¹) • (prevState ω).blockX i) ∧
    conditionalExpectationEq S.P (S.paperStrictPastSigma t)
      (fun ω => S.f i (S.positiveEtaBlockIterate hη t ω i))
      (fun ω =>
        (Fintype.card ι : ℝ)⁻¹ *
            S.f i (S.auxiliaryPoint t (xNext ω) ((prevState ω).blockX i)) +
          (1 - (Fintype.card ι : ℝ)⁻¹) * S.f i ((prevState ω).blockX i)) ∧
    conditionalExpectationEq S.P (S.paperStrictPastSigma t)
      (fun ω =>
        S.dualNorm
          (S.gradF i (S.positiveEtaBlockIterate hη t ω i) -
            S.gradF i ((prevState ω).blockX i)) ^ 2)
      (fun ω =>
        (Fintype.card ι : ℝ)⁻¹ *
          S.dualNorm
            (S.gradF i (S.auxiliaryPoint t (xNext ω) ((prevState ω).blockX i)) -
              S.gradF i ((prevState ω).blockX i)) ^ 2)

/-- Integrability of a normed observable reconstructed from a finite sample window.

Search audit: the planner-named `integrable_of_finiteSampleWindow_factor` was
checked, but it requires `[MeasurableSpace F] [BorelSpace F]`, unavailable for
the abstract vector space in this file. This variant combines
`aestronglyMeasurable_of_countable_key_reconstruction` with
`integrable_of_finite_range`, preserving the same finite-window factor route
without adding theorem-head measurability assumptions. -/
private theorem integrable_of_finiteSampleWindow_factor_aestrongly
    {Ω Sample F : Type*} [MeasurableSpace Ω] [MeasurableSpace Sample]
    [Fintype Sample] [MeasurableSingletonClass Sample] [NormedAddCommGroup F]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (ξ : ℕ → Ω → Sample) (offset n : ℕ) {Z : Ω → F}
    (hξ_measurable : ∀ k, Measurable (ξ k))
    (hconst :
      ∀ ⦃ω ω' : Ω⦄,
        (fun r : Fin n => ξ (offset + r.1) ω) =
          (fun r : Fin n => ξ (offset + r.1) ω') →
        Z ω = Z ω') :
    Integrable Z μ := by
  exact _root_.integrable_of_finiteSampleWindow_factor_aestrongly
    (ξ := ξ) (offset := offset) (n := n) (Z := Z)
    hξ_measurable hconst

/-- The generated positive-eta process is determined by the sampled block window `i_1,...,i_n`.

Search audit: checked `recursive process finite prefix determinism`; the matching
SOptLib primitive is `recursive_process_eq_of_driver_prefix_eq`. The proof applies
it to the feasible-state subtype process so the successor step is definitionally
congruent in the previous subtype state and current sampled block. -/
private theorem positiveEtaGeneratedProcess_eq_of_sampleWindow_eq
    (hη : S.PositiveEtaDomain) (n : ℕ) :
    ∀ ⦃ω ω' : BlockSamplePath ι⦄,
      (fun r : Fin n => S.sample (1 + r.1) ω) =
        (fun r : Fin n => S.sample (1 + r.1) ω') →
      S.positiveEtaGeneratedProcess hη n ω =
        S.positiveEtaGeneratedProcess hη n ω' := by
  intro ω ω' hwin
  have hsub : S.positiveEtaProcess hη n ω = S.positiveEtaProcess hη n ω' := by
    exact SOptLib.recursive_process_eq_of_driver_prefix_eq
      (ξ := S.sample)
      (process := S.positiveEtaProcess hη)
      (offset := 1) (R := n) (t := n)
      (initial := S.initialState)
      (by intro ω; rfl)
      (by
        intro k _hk ω ω' hprev hsample
        have hsample' : S.sample (k + 1) ω = S.sample (k + 1) ω' := by
          simpa [Nat.add_comm] using hsample
        rw [S.positiveEtaProcess_succ hη k ω, S.positiveEtaProcess_succ hη k ω']
        rw [hprev, hsample'])
      (Nat.le_refl n) hwin
  exact congrArg Subtype.val hsub

/-- Finite-prefix payloads of the generated positive-eta state process are integrable.

This is route-local measure-theory infrastructure for Lan Proposition 5.6 proof
steps 8--9: the expected gradient-extrapolation telescope contains adjacent
state tables up to time `k`. Candidate audit: searched `generated process finite
prefix payload integrable`; the reusable SOptLib candidate
`recursive_process_measurable_finite_range_wrt_sample_prefix` proves
measurability/finite range for recursive processes, while the local
`integrable_of_finiteSampleWindow_factor_aestrongly` is the existing API that
directly yields integrability for arbitrary normed payloads without adding
codomain measurability assumptions. -/
private theorem positiveEta_prefix_payload_integrable
    (hη : S.PositiveEtaDomain) (n : ℕ)
    {F : Type*} [NormedAddCommGroup F]
    (G : (Fin (n + 1) → State ι E) → F) :
    Integrable
      (fun ω : BlockSamplePath ι =>
        G (fun r : Fin (n + 1) => S.positiveEtaGeneratedProcess hη r.1 ω)) S.P := by
  haveI : IsFiniteMeasure S.P := by
    unfold Setup.P uniformBlockStreamLaw
    infer_instance
  exact integrable_of_finiteSampleWindow_factor_aestrongly
    (ξ := S.sample) (offset := 1) (n := n)
    (Z := fun ω : BlockSamplePath ι =>
      G (fun r : Fin (n + 1) => S.positiveEtaGeneratedProcess hη r.1 ω))
    S.sample_measurable
    (by
      intro ω ω' hwin
      apply congrArg G
      funext r
      have hsubwin :
          (fun q : Fin (r.1) => S.sample (1 + q.1) ω) =
            (fun q : Fin (r.1) => S.sample (1 + q.1) ω') := by
        funext q
        exact congrFun hwin ⟨q.1, by omega⟩
      exact S.positiveEtaGeneratedProcess_eq_of_sampleWindow_eq hη r.1 hsubwin)

/-- Finite-prefix payloads depending on both sampled blocks and generated states are integrable.

This extends `positiveEta_prefix_payload_integrable` for the stochastic
sampled-block terms in Lan Proposition 5.6 proof steps 8--9, where the terminal
and lagged residuals use `i_k` and `i_{t-1}`. Candidate audit: searched
`generated process finite prefix payload integrable` and `expectation Finset
sum inner positiveEtaXIterate`; the available SOptLib/local primitives give
finite-window reconstruction, but no existing helper exposed both the sampled
prefix and the generated-state prefix in one integrable payload. -/
private theorem positiveEta_sample_state_prefix_payload_integrable
    (hη : S.PositiveEtaDomain) (n : ℕ)
    {F : Type*} [NormedAddCommGroup F]
    (G : (Fin n → ι) → (Fin (n + 1) → State ι E) → F) :
    Integrable
      (fun ω : BlockSamplePath ι =>
        G (fun r : Fin n => S.sample (1 + r.1) ω)
          (fun r : Fin (n + 1) => S.positiveEtaGeneratedProcess hη r.1 ω)) S.P := by
  haveI : IsFiniteMeasure S.P := by
    unfold Setup.P uniformBlockStreamLaw
    infer_instance
  exact integrable_of_finiteSampleWindow_factor_aestrongly
    (ξ := S.sample) (offset := 1) (n := n)
    (Z := fun ω : BlockSamplePath ι =>
      G (fun r : Fin n => S.sample (1 + r.1) ω)
        (fun r : Fin (n + 1) => S.positiveEtaGeneratedProcess hη r.1 ω))
    S.sample_measurable
    (by
      intro ω ω' hwin
      apply congrArg₂ G
      · funext r
        exact congrFun hwin r
      · funext r
        have hsubwin :
            (fun q : Fin (r.1) => S.sample (1 + q.1) ω) =
              (fun q : Fin (r.1) => S.sample (1 + q.1) ω') := by
          funext q
          exact congrFun hwin ⟨q.1, by omega⟩
        exact S.positiveEtaGeneratedProcess_eq_of_sampleWindow_eq hη r.1 hsubwin)

/-- The generated primal point `x^t` is determined by the strict sampled-block past.

Aligns with Algorithm 5.4 Eq. (5.2.50): the prox point uses the previous gradient
tables and not the freshly selected block. This sharpens
`positiveEtaGeneratedProcess_eq_of_sampleWindow_eq`, because the full state at
time `t` includes current-block table updates while its `x` component does not. -/
private theorem positiveEtaXIterate_eq_of_strictPastWindow_eq
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 1 ≤ t) :
    ∀ ⦃ω ω' : BlockSamplePath ι⦄,
      (fun r : Fin (t - 1) => S.sample (1 + r.1) ω) =
        (fun r : Fin (t - 1) => S.sample (1 + r.1) ω') →
      S.positiveEtaXIterate hη t ω = S.positiveEtaXIterate hη t ω' := by
  simpa [SOptLib.sampleWindow, positiveEtaXIterate, positiveEtaGeneratedProcess,
    positiveEtaProcess_succ, stateStep] using
    (SOptLib.pre_update_readout_eq_of_strict_driver_prefix_eq
      (driver := S.sample)
      (process := S.positiveEtaProcess hη)
      (current := S.positiveEtaXIterate hη)
      (readout := fun n ω prev =>
        if hn : 1 ≤ n then
          (S.stateStep n (hη n hn) (S.sample n ω) prev).1.x
        else
          prev.1.x)
      (offset := 1)
      (initial := S.initialState)
      (h_zero := by intro ω; rfl)
      (ht := ht)
      (h_succ_congr := by
        intro k _hk ω ω' hprev hsample
        have hsample' : S.sample (k + 1) ω = S.sample (k + 1) ω' := by
          simpa [Nat.add_comm] using hsample
        rw [S.positiveEtaProcess_succ hη k ω, S.positiveEtaProcess_succ hη k ω']
        rw [hprev, hsample'])
      (h_current_readout := by
        intro ω
        rcases t with _ | k
        · cases ht
        · simp [positiveEtaXIterate, positiveEtaGeneratedProcess,
            positiveEtaProcess_succ, stateStep])
      (h_readout_strict := by
        intro ω ω' prev _hwin
        simp [stateStep]))

/-- Strict-past payloads built from `(x^t, state^{t-1})` are integrable.

This is the generated-process well-definedness bridge for Lemma 5.9 payloads:
Eq. (5.2.50) makes `x^t` strict-past determined, and the previous state is also
strict-past determined. The proof uses the finite-window factor helper above,
not extra theorem-head measurability assumptions. -/
private theorem positiveEta_strictPast_payload_integrable
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 1 ≤ t)
    {F : Type*} [NormedAddCommGroup F] (G : E → State ι E → F) :
    Integrable
      (fun ω : BlockSamplePath ι =>
        G (S.positiveEtaXIterate hη t ω)
          (S.positiveEtaGeneratedProcess hη (t - 1) ω)) S.P := by
  haveI : IsFiniteMeasure S.P := by
    unfold Setup.P uniformBlockStreamLaw
    infer_instance
  exact integrable_of_finiteSampleWindow_factor_aestrongly
    (ξ := S.sample) (offset := 1) (n := t - 1)
    (Z := fun ω : BlockSamplePath ι =>
      G (S.positiveEtaXIterate hη t ω)
        (S.positiveEtaGeneratedProcess hη (t - 1) ω))
    S.sample_measurable
    (by
      intro ω ω' hwin
      have hx := S.positiveEtaXIterate_eq_of_strictPastWindow_eq hη ht hwin
      have hprev := S.positiveEtaGeneratedProcess_eq_of_sampleWindow_eq hη (t - 1) hwin
      simp [hx, hprev])

/-- Current/previous generated-state payloads are integrable from the finite sample window.

This supplies the left-hand-side integrability side condition for generated
Lemma 5.9 identities. Search audit: checked SOptLib
`integrable_of_finiteSampleWindow_factor` and
`recursive_process_measurable_finite_range_wrt_sample_prefix`; the former needs
codomain measurability not available here, while the latter proves measurability
for recursive processes but not this abstract normed payload integrability. -/
private theorem positiveEta_current_prev_payload_integrable
    (hη : S.PositiveEtaDomain) (t : ℕ)
    {F : Type*} [NormedAddCommGroup F] (G : State ι E → State ι E → F) :
    Integrable
      (fun ω : BlockSamplePath ι =>
        G (S.positiveEtaGeneratedProcess hη t ω)
          (S.positiveEtaGeneratedProcess hη (t - 1) ω)) S.P := by
  haveI : IsFiniteMeasure S.P := by
    unfold Setup.P uniformBlockStreamLaw
    infer_instance
  exact integrable_of_finiteSampleWindow_factor_aestrongly
    (ξ := S.sample) (offset := 1) (n := t)
    (Z := fun ω : BlockSamplePath ι =>
      G (S.positiveEtaGeneratedProcess hη t ω)
        (S.positiveEtaGeneratedProcess hη (t - 1) ω))
    S.sample_measurable
    (by
      intro ω ω' hwin
      have hcurr := S.positiveEtaGeneratedProcess_eq_of_sampleWindow_eq hη t hwin
      have hprev_win :
          (fun r : Fin (t - 1) => S.sample (1 + r.1) ω) =
            (fun r : Fin (t - 1) => S.sample (1 + r.1) ω') := by
        funext r
        exact congrFun hwin ⟨r.1, by omega⟩
      have hprev := S.positiveEtaGeneratedProcess_eq_of_sampleWindow_eq hη (t - 1) hprev_win
      simp [hcurr, hprev])

/-- Weighted-output observables are integrable from the finite sampled-block window.

This aligns with Lan Eq. (5.2.53): the output is the normalized finite weighted
average of `x^t`, `1 ≤ t ≤ k`. No direct SOptLib primitive matched this
paper-specific positive-eta output: searched `finite sample window integrable
factor` and `weighted average output finite sample window integrable`; the useful
matches were the local finite-window factor lemma and SOptLib's generic
`weightedAverageOutputValue`, which do not by themselves connect RGEM's strict
past iterate determinism across the whole output window. -/
private theorem positiveEta_weighted_output_payload_integrable
    (hη : S.PositiveEtaDomain) {k : ℕ} (hk : 1 ≤ k)
    (hθ : S.OutputWeightsPositive k)
    {F : Type*} [NormedAddCommGroup F] (G : E → F) :
    Integrable
      (fun ω : BlockSamplePath ι =>
        G (S.positiveEtaWeightedOutput hη k hk hθ ω)) S.P := by
  haveI : IsFiniteMeasure S.P := by
    unfold Setup.P uniformBlockStreamLaw
    infer_instance
  exact integrable_of_finiteSampleWindow_factor_aestrongly
    (ξ := S.sample) (offset := 1) (n := k)
    (Z := fun ω : BlockSamplePath ι =>
      G (S.positiveEtaWeightedOutput hη k hk hθ ω))
    S.sample_measurable
    (by
      intro ω ω' hwin
      have hx_eq : ∀ t ∈ outputWindow k,
          S.positiveEtaXIterate hη t ω = S.positiveEtaXIterate hη t ω' := by
        intro t ht
        have ht_bounds := Finset.mem_Icc.mp ht
        exact S.positiveEtaXIterate_eq_of_strictPastWindow_eq hη ht_bounds.1
          (by
            funext r
            exact congrFun hwin ⟨r.1, by omega⟩)
      have hout :
          S.positiveEtaWeightedOutput hη k hk hθ ω =
            S.positiveEtaWeightedOutput hη k hk hθ ω' := by
        rw [S.positiveEtaWeightedOutput_def hη k hk hθ ω,
          S.positiveEtaWeightedOutput_def hη k hk hθ ω']
        congr 1
        exact Finset.sum_congr rfl (by
          intro t ht
          rw [hx_eq t ht])
      simpa [hout])

/-- Theorem 5.4 weighted-output observables are integrable from the finite sample window.

This is the theorem-specific analogue of `positiveEta_weighted_output_payload_integrable`.
No SOptLib match applies: searched `finite sample window integrable weighted output`
and `theorem weighted output integrable expectation well defined`; the reusable
hits were `integrable_of_finiteSampleWindow_factor_aestrongly` and the local
positive-eta output helper, but the latter depends on `S.θ` while Theorem 5.4's
output uses the literal source proof weights `θ_t = α^{-t}`. -/
private theorem theorem54_weighted_output_payload_integrable
    (hμ_pos : 0 < S.μ)
    (hη_policy : ∀ t, 1 ≤ t → S.η t = S.constantEta hμ_pos)
    {k : ℕ} (hk : 1 ≤ k)
    (hθ : S.TheoremOutputWeightsPositive hμ_pos k)
    {F : Type*} [NormedAddCommGroup F] (G : E → F) :
    Integrable
      (fun ω : BlockSamplePath ι =>
        G (S.theoremWeightedOutput hμ_pos hη_policy k hk hθ ω)) S.P := by
  haveI : IsFiniteMeasure S.P := by
    unfold Setup.P uniformBlockStreamLaw
    infer_instance
  exact integrable_of_finiteSampleWindow_factor_aestrongly
    (ξ := S.sample) (offset := 1) (n := k)
    (Z := fun ω : BlockSamplePath ι =>
      G (S.theoremWeightedOutput hμ_pos hη_policy k hk hθ ω))
    S.sample_measurable
    (by
      intro ω ω' hwin
      have hx_eq : ∀ t ∈ outputWindow k,
          S.theoremXIterate hμ_pos hη_policy t ω =
            S.theoremXIterate hμ_pos hη_policy t ω' := by
        intro t ht
        have ht_bounds := Finset.mem_Icc.mp ht
        have hx :
            S.positiveEtaXIterate (S.theoremPositiveEtaDomain hμ_pos hη_policy) t ω =
              S.positiveEtaXIterate (S.theoremPositiveEtaDomain hμ_pos hη_policy) t ω' :=
          S.positiveEtaXIterate_eq_of_strictPastWindow_eq
            (S.theoremPositiveEtaDomain hμ_pos hη_policy) ht_bounds.1
            (by
              funext r
              exact congrFun hwin ⟨r.1, by omega⟩)
        simpa [theoremXIterate] using hx
      have hout :
          S.theoremWeightedOutput hμ_pos hη_policy k hk hθ ω =
            S.theoremWeightedOutput hμ_pos hη_policy k hk hθ ω' := by
        rw [S.theoremWeightedOutput_def hμ_pos hη_policy k hk hθ ω,
          S.theoremWeightedOutput_def hμ_pos hη_policy k hk hθ ω']
        congr 1
        exact Finset.sum_congr rfl (by
          intro t ht
          rw [hx_eq t ht])
      simpa [hout])

/-- Zero branch simplification for the RGEM dual norm.

This source-facing helper delegates to the paper-free affine-direction support
zero theorem needed for Lemma 5.9's nonselected branch. -/
private theorem dualNorm_zero :
    S.dualNorm (0 : E) = 0 := by
  simpa [dualNorm, affineDirectionDualNorm] using
    SOptLib.affineDirectionDualNorm_zero (X := S.X) (p := S.primalNorm)

/-- Pointwise stale-gradient split before the probability estimate.

This is the generated positive-eta form of Lan Proposition 5.6 proof step 20:
Eq. (5.2.64) makes the stale error zero after a previous update, while the
no-previous-update branch is reduced to the initial gradient by
`positiveEta_block_iterate_eq_x0_of_no_previous_update`. Search audit: checked
target/SOptLib for `stale gradient previous sample split`; the available exact
ingredients are the local Eq. (5.2.64) specialization and update invariant, and
no SOptLib probability or memory theorem states this paper-specific split. -/
private theorem stale_gradient_error_pointwise_split_positive_domain
    (hη : S.PositiveEtaDomain) (t : ℕ) (ω : BlockSamplePath ι) (i : ι) :
    S.dualNorm
        (S.gradF i (S.positiveEtaBlockIterate hη (t - 1) ω i) -
          S.positiveEtaYIterate hη (t - 1) ω i) ^ 2 =
      (by
        classical
        exact
          if ¬ ∃ r, 1 ≤ r ∧ r ≤ t - 1 ∧ S.sample r ω = i then
            S.dualNorm (S.gradF i S.x0) ^ 2
          else
            0) := by
  classical
  exact
    SOptLib.staleMemoryResidual_sq_eq_initial_or_zero
      (sample := S.sample) (target := S.gradF)
      (xmem := fun n ω i => S.positiveEtaBlockIterate hη n ω i)
      (ymem := fun n ω i => S.positiveEtaYIterate hη n ω i)
      (N := S.dualNorm) (x0 := S.x0)
      (t := t) (ω := ω) (i := i)
      (hN_zero := S.dualNorm_zero)
      (hx_no := by
        intro hno
        exact S.positiveEta_block_iterate_eq_x0_of_no_previous_update
          (hη := hη) (t := t - 1) (i := i) (ω := ω) hno)
      (hy_no := by
        intro hno
        exact (S.GradientStateCharacterization_Eq_5_2_64_positive_domain
          hη (t - 1) ω i).1 hno)
      (hy_hit := by
        intro hex
        exact (S.GradientStateCharacterization_Eq_5_2_64_positive_domain
          hη (t - 1) ω i).2 hex)

/-- Initial-gradient aggregation for the stale-gradient probability estimate.

This is the Eq. (5.2.56) scalar tail of Lan Proposition 5.6 proof step 21:
after expanding the selected-block/no-hit event into the uniform finite sum over
initial gradients, `InitialGradientBound` turns the sum into `sigma0^2`.
Candidate audit: searched target/SOptLib for `InitialGradientBound sigma0`,
`Finset product constant card probability no hit`, and finite-sum algebra; no
existing lemma specialized Eq. (5.2.56) to the geometric no-hit coefficient. -/
private theorem initial_gradient_geometric_sum_eq_positive_domain
    {sigma0 : ℝ} (hsigma : S.InitialGradientBound sigma0) (t : ℕ) :
    Finset.sum Finset.univ
        (fun i : ι =>
          (Fintype.card ι : ℝ)⁻¹ *
            (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) ^ (t - 1) *
            S.dualNorm (S.gradF i S.x0) ^ 2) =
      (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) ^ (t - 1) *
        sigma0 ^ 2 := by
  let q : ℝ := (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) ^ (t - 1)
  have hsum :
      (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ
            (fun i : ι => S.dualNorm (S.gradF i S.x0) ^ 2) =
        sigma0 ^ 2 := hsigma.1
  calc
    Finset.sum Finset.univ
        (fun i : ι =>
          (Fintype.card ι : ℝ)⁻¹ * q *
            S.dualNorm (S.gradF i S.x0) ^ 2)
        = q *
            ((Fintype.card ι : ℝ)⁻¹ *
              Finset.sum Finset.univ
                (fun i : ι => S.dualNorm (S.gradF i S.x0) ^ 2)) := by
          simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
    _ = q * sigma0 ^ 2 := by rw [hsum]
    _ = (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) ^ (t - 1) *
        sigma0 ^ 2 := by rfl

/-- The one-based no-hit event is measurable in the paper strict past.

Aligns with Lan Proposition 5.6's event `B_{i_t}` just before Eq. (5.2.75):
membership depends only on `i_1,\ldots,i_n`. Candidate audit: checked
`iIndepFun.indep_sampleBlock_singleton_of_not_mem`,
`iIndepFun.indepFun_finset_subtype_blocks`, and
`paperStrictPastSigma_eq_strictPastWindow_comap`; the independence lemmas factor
fresh coordinates, while this helper supplies the route-local measurability
bridge for the literal one-based no-hit event. -/
private theorem no_hit_prefix_measurable_paperStrictPast
    (n : ℕ) (i : ι) :
    @MeasurableSet (BlockSamplePath ι) (S.paperStrictPastSigma (n + 1))
      {ω : BlockSamplePath ι | ∀ r, 1 ≤ r → r ≤ n → S.sample r ω ≠ i} := by
  rw [S.paperStrictPastSigma_eq_strictPastWindow_comap (n + 1)]
  simpa [SOptLib.sampleWindow, Nat.lt_succ_iff] using
    (SOptLib.measurableSet_noHit_of_sampleWindow_comap
      (sample := S.sample) (offset := 1) (stop := n + 1) (a := i))

/-- The probability that a fixed block has not appeared in the one-based prefix.

This is the finite-prefix `B_{i_t}` probability used in Lan Proposition 5.6,
proof step after Eq. (5.2.75): `Prob(B_{i_t})=((m-1)/m)^(t-1)`.
Candidate audit: checked `SOptLib.iidStreamLaw_iIndepFun_eval`,
`SOptLib.iidStreamLaw_map_eval`, `iIndepFun.indep_sampleBlock_singleton_of_not_mem`,
and `iIndepFun.indepFun_finset_subtype_blocks`; they provide iid marginals and
finite-block freshness, but not this literal one-based no-previous-hit
probability, so this route-local helper specializes `S.currentBlock_fresh_uniform`
by induction over the prefix length. -/
private theorem no_hit_prefix_probability_uniform_block_stream
    (n : ℕ) (i : ι) :
    S.P.real {ω : BlockSamplePath ι |
        ∀ r, 1 ≤ r → r ≤ n → S.sample r ω ≠ i} =
      (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) ^ n := by
  classical
  haveI : IsProbabilityMeasure S.P := by
    unfold Setup.P uniformBlockStreamLaw
    infer_instance
  have hstage :=
    SOptLib.measureReal_no_hit_prefix_of_iid_uniform_finite
      (P := S.P) (sample := S.sample) (offset := 1) (n := n) (i := i)
      S.sample_measurable S.sample_iIndepFun S.sample_uniform
  have hset :
      {ω : BlockSamplePath ι | ∀ r, 1 ≤ r → r ≤ n → S.sample r ω ≠ i} =
        {ω : BlockSamplePath ι | ∀ r : Fin n, S.sample (1 + r.1) ω ≠ i} := by
    ext ω
    constructor
    · intro h r
      exact h (1 + r.1) (by omega) (by omega)
    · intro h r hr_one hr_le
      let a : Fin n := ⟨r - 1, by omega⟩
      have ha : 1 + (r - 1) = r := by omega
      simpa [a, ha] using h a
  rw [hset]
  exact hstage

/-- One-based no-previous-hit probability for the Proposition 5.6 stale-gradient event.

Aligns with Lan Proposition 5.6 proof step after Eq. (5.2.75), where
`B_{i_t}` is the event that `i` has not appeared among `i_1,\ldots,i_{t-1}`.
This is a direct corollary of `no_hit_prefix_probability_uniform_block_stream`,
which was needed because no SOptLib/Mathlib candidate states the literal
one-based finite-prefix probability. -/
private theorem no_previous_hit_probability_uniform_block_stream
    (t : ℕ) (i : ι) :
    S.P.real {ω : BlockSamplePath ι |
        ∀ r, 1 ≤ r → r ≤ t - 1 → S.sample r ω ≠ i} =
      (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) ^ (t - 1) := by
  simpa using S.no_hit_prefix_probability_uniform_block_stream (t - 1) i

/-- Ambient measurability of the one-based no-previous-hit event.

Aligns with the measurability side of Lan Proposition 5.6's event `B_{i_t}`.
Candidate audit: `no_hit_prefix_measurable_paperStrictPast` gives the adapted
sub-sigma form, while the expectation calculation below also needs the ambient
`MeasurableSet` required by `integral_indicator_const`; no SOptLib/Mathlib hit
states this literal RGEM event over the one-based prefix. -/
private theorem no_previous_hit_measurable_ambient
    (t : ℕ) (i : ι) :
    MeasurableSet {ω : BlockSamplePath ι |
        ∀ r, 1 ≤ r → r ≤ t - 1 → S.sample r ω ≠ i} := by
  classical
  by_cases ht : 1 ≤ t
  · have hsub : t - 1 + 1 = t := Nat.sub_add_cancel ht
    have hpast :
        @MeasurableSet (BlockSamplePath ι) (S.paperStrictPastSigma t)
          {ω : BlockSamplePath ι |
            ∀ r, 1 ≤ r → r ≤ t - 1 → S.sample r ω ≠ i} := by
      have hpast0 := S.no_hit_prefix_measurable_paperStrictPast (t - 1) i
      rw [hsub] at hpast0
      simpa using hpast0
    have hle : S.paperStrictPastSigma t ≤
        (inferInstance : MeasurableSpace (BlockSamplePath ι)) := by
      rw [S.paperStrictPastSigma_eq_strictPastWindow_comap t]
      change MeasurableSpace.comap
          (fun ω : BlockSamplePath ι => fun r : Fin (t - 1) => S.sample (1 + r.1) ω)
          (by infer_instance : MeasurableSpace (Fin (t - 1) → ι)) ≤
        (inferInstance : MeasurableSpace (BlockSamplePath ι))
      exact (show @Measurable (BlockSamplePath ι) (Fin (t - 1) → ι)
        (inferInstance : MeasurableSpace (BlockSamplePath ι))
        (by infer_instance : MeasurableSpace (Fin (t - 1) → ι))
        (fun ω : BlockSamplePath ι => fun r : Fin (t - 1) => S.sample (1 + r.1) ω) from
          @measurable_pi_lambda (BlockSamplePath ι) (Fin (t - 1)) (fun _ => ι)
            (inferInstance : MeasurableSpace (BlockSamplePath ι))
            (fun _ => by infer_instance)
            (fun ω : BlockSamplePath ι => fun r : Fin (t - 1) => S.sample (1 + r.1) ω)
            (fun r : Fin (t - 1) =>
              show @Measurable (BlockSamplePath ι) ι
                (inferInstance : MeasurableSpace (BlockSamplePath ι))
                (by infer_instance : MeasurableSpace ι)
                (fun ω : BlockSamplePath ι => S.sample (1 + r.1) ω) from
                  S.sample_measurable (1 + r.1))).comap_le
    exact hle _ hpast
  · have ht0 : t = 0 := by omega
    have hset :
        {ω : BlockSamplePath ι |
            ∀ r, 1 ≤ r → r ≤ t - 1 → S.sample r ω ≠ i} = Set.univ := by
      ext ω
      constructor
      · intro _; trivial
      · intro _ r hr_one hr_le
        omega
    rw [hset]
    exact MeasurableSet.univ

/-- Lemma 5.9 branch identities for the generated positive-eta process.

Aligns with Lan Lemma 5.9 proof step 1 and Algorithm 5.4 Eqs. (5.2.51)--(5.2.52):
conditioning on `i_t = i` gives the auxiliary point/gradient branch, while the
other branch preserves the previous stored point/gradient. Search audit:
checked target/SOptLib for "generated process branch identity block update
selected other"; the usable candidates are the local update equations,
`blockPointUpdate_*`, and Mathlib's `Function.update` coordinate API, not a
prepackaged Lemma 5.9 branch theorem. -/
private theorem positiveEtaGeneratedProcess_branch_identities
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 1 ≤ t) (i : ι) :
    (∀ ω : BlockSamplePath ι,
      S.positiveEtaYIterate hη t ω i =
        (if S.sample t ω = i then
          S.auxiliaryGradient t (S.positiveEtaXIterate hη t ω)
            (S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i
        else
          (S.positiveEtaGeneratedProcess hη (t - 1) ω).yCurr i)) ∧
    (∀ ω : BlockSamplePath ι,
      S.positiveEtaBlockIterate hη t ω i =
        (if S.sample t ω = i then
          S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
            ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)
        else
          (S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) ∧
    (∀ ω : BlockSamplePath ι,
      S.f i (S.positiveEtaBlockIterate hη t ω i) =
        (if S.sample t ω = i then
          S.f i (S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
            ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i))
        else
          S.f i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i))) ∧
    (∀ ω : BlockSamplePath ι,
      S.dualNorm
        (S.gradF i (S.positiveEtaBlockIterate hη t ω i) -
          S.gradF i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) ^ 2 =
        (if S.sample t ω = i then
          S.dualNorm
            (S.gradF i (S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
              ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) -
              S.gradF i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) ^ 2
        else 0)) := by
  classical
  exact
    SOptLib.selectedCoordinateRefresh_branch_identities
      (sample := fun ω : BlockSamplePath ι => S.sample t ω)
      (query := i)
      (valueStale := fun ω : BlockSamplePath ι =>
        (S.positiveEtaGeneratedProcess hη (t - 1) ω).yCurr i)
      (valueRefreshed := fun ω : BlockSamplePath ι =>
        S.auxiliaryGradient t (S.positiveEtaXIterate hη t ω)
          (S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)
      (valueAfter := fun ω : BlockSamplePath ι => S.positiveEtaYIterate hη t ω)
      (stale := fun ω : BlockSamplePath ι =>
        (S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)
      (refreshed := fun ω : BlockSamplePath ι =>
        S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
          ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i))
      (memAfter := fun ω : BlockSamplePath ι => S.positiveEtaBlockIterate hη t ω)
      (payload := S.f i)
      (residual := fun x z : E => S.dualNorm (S.gradF i x - S.gradF i z) ^ 2)
      (by
        intro ω
        have hstep := S.positiveEtaGeneratedProcess_succ_equations hη ht ω
        rcases hstep with ⟨_hxmem, _hmin, hblock, _hyprev, hycurr⟩
        dsimp [positiveEtaYIterate, positiveEtaXIterate] at *
        have hyi := congrFun hycurr i
        rw [hyi]
        by_cases hsel : S.sample t ω = i
        · subst hsel
          have hblocki := congrFun hblock (S.sample t ω)
          simp
          rw [hblocki]
          simp [blockPointUpdate, auxiliaryGradient]
        · have hnot : i ≠ S.sample t ω := fun hi => hsel hi.symm
          simp [hsel, hnot])
      (by
        intro ω
        have hstep := S.positiveEtaGeneratedProcess_succ_equations hη ht ω
        rcases hstep with ⟨_hxmem, _hmin, hblock, _hyprev, _hycurr⟩
        dsimp [positiveEtaBlockIterate, positiveEtaXIterate] at *
        have hxi := congrFun hblock i
        rw [hxi]
        by_cases hsel : S.sample t ω = i
        · subst hsel
          simp [blockPointUpdate]
        · have hnot : i ≠ S.sample t ω := fun hi => hsel hi.symm
          simp [hsel, hnot, blockPointUpdate])
      (by
        intro ω
        dsimp
        rw [sub_self, S.dualNorm_zero]
        norm_num)

/-- Strict-past finite-window constancy gives adaptedness to the paper strict-past sigma algebra.

Aligns with Lan Lemma 5.9's conditioning on `i_1,...,i_{t-1}`. Candidate audit:
`aestronglyMeasurable_of_countable_key_reconstruction` gives the ambient a.e.
variant, while this helper needs the stronger sub-sigma `StronglyMeasurable`
form required by `condExp_of_stronglyMeasurable`. -/
private theorem strictPast_stronglyMeasurable_of_window_const
    {F : Type*} [TopologicalSpace F] {t : ℕ}
    (Z : BlockSamplePath ι → F)
    (hZ_const :
      ∀ ⦃ω ω' : BlockSamplePath ι⦄,
        (fun r : Fin (t - 1) => S.sample (1 + r.1) ω) =
          (fun r : Fin (t - 1) => S.sample (1 + r.1) ω') →
        Z ω = Z ω') :
    StronglyMeasurable[S.paperStrictPastSigma t] Z := by
  classical
  exact stronglyMeasurable_of_countable_key_const
    (Y := fun ω : BlockSamplePath ι => fun r : Fin (t - 1) => S.sample (1 + r.1) ω)
    (Z := Z)
    (by
      rw [S.paperStrictPastSigma_eq_strictPastWindow_comap t]
      exact Measurable.of_comap_le le_rfl)
    hZ_const

/-- Conditional expectation of the current-block indicator given the strict past.

Aligns with Lan Lemma 5.9's `Prob_t {i_t=i}=1/m`. Candidate audit:
`condExp_indicator` applies only to conditioning-measurable events, while the
current event is fresh rather than strict-past measurable; Mathlib's
`condExp_indep_eq` matches after `S.currentBlock_fresh_uniform` supplies
independence and singleton mass. -/
private theorem condExp_currentBlock_indicator_of_fresh_uniform
    {t : ℕ} (i : ι) :
    @MeasureTheory.condExp (BlockSamplePath ι) ℝ (S.paperStrictPastSigma t)
        (m₀ := by infer_instance) _ _ _ S.P
        (fun ω => if S.sample t ω = i then (1 : ℝ) else 0) =ᵐ[S.P]
      fun _ => (Fintype.card ι : ℝ)⁻¹ := by
  classical
  let mΩ : MeasurableSpace (BlockSamplePath ι) := inferInstance
  let currentSigma : MeasurableSpace (BlockSamplePath ι) :=
    MeasurableSpace.comap (S.sample t) (by infer_instance : MeasurableSpace ι)
  let Evt : Set (BlockSamplePath ι) := (S.sample t) ⁻¹' ({i} : Set ι)
  let p : ℝ := (Fintype.card ι : ℝ)⁻¹
  have hfresh := S.currentBlock_fresh_uniform t i
  rcases hfresh with ⟨hIndep, hProb⟩
  have hcurrent_le : currentSigma ≤ mΩ := by
    change MeasurableSpace.comap (S.sample t)
        (by infer_instance : MeasurableSpace ι) ≤ mΩ
    exact (S.sample_measurable t).comap_le
  have hpast_le : S.paperStrictPastSigma t ≤ mΩ := by
    rw [S.paperStrictPastSigma_eq_strictPastWindow_comap t]
    change MeasurableSpace.comap
        (fun ω : BlockSamplePath ι => fun r : Fin (t - 1) => S.sample (1 + r.1) ω)
        (by infer_instance : MeasurableSpace (Fin (t - 1) → ι)) ≤ mΩ
    exact (show @Measurable (BlockSamplePath ι) (Fin (t - 1) → ι) mΩ
      (by infer_instance : MeasurableSpace (Fin (t - 1) → ι))
      (fun ω : BlockSamplePath ι => fun r : Fin (t - 1) => S.sample (1 + r.1) ω) from
        @measurable_pi_lambda (BlockSamplePath ι) (Fin (t - 1)) (fun _ => ι)
          mΩ (fun _ => by infer_instance)
          (fun ω : BlockSamplePath ι => fun r : Fin (t - 1) => S.sample (1 + r.1) ω)
          (fun r : Fin (t - 1) =>
            show @Measurable (BlockSamplePath ι) ι mΩ
              (by infer_instance : MeasurableSpace ι)
              (fun ω : BlockSamplePath ι => S.sample (1 + r.1) ω) from
                S.sample_measurable (1 + r.1))).comap_le
  haveI : IsFiniteMeasure S.P := by
    unfold Setup.P uniformBlockStreamLaw
    infer_instance
  haveI : SigmaFinite (S.P.trim hpast_le) := inferInstance
  have hEvt_current : MeasurableSet[currentSigma] Evt := by
    have hsample_current :
        Measurable[currentSigma] (S.sample t) := Measurable.of_comap_le le_rfl
    exact (measurableSet_singleton i).preimage hsample_current
  have hEvt_ambient : @MeasurableSet (BlockSamplePath ι) mΩ Evt := by
    exact (measurableSet_singleton i).preimage (S.sample_measurable t)
  have hf_indicator :
      (fun ω => if S.sample t ω = i then (1 : ℝ) else 0) =
        Evt.indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases hω : S.sample t ω = i <;> simp [Evt, Set.indicator, hω]
  have hf_current :
      StronglyMeasurable[currentSigma]
        (fun ω => if S.sample t ω = i then (1 : ℝ) else 0) := by
    rw [hf_indicator]
    exact stronglyMeasurable_const.indicator hEvt_current
  have hIntegral :
      (∫ ω, (if S.sample t ω = i then (1 : ℝ) else 0) ∂S.P) = p := by
    calc
      (∫ ω, (if S.sample t ω = i then (1 : ℝ) else 0) ∂S.P)
          = S.P.real Evt := by
            rw [hf_indicator]
            simpa using
              (integral_indicator_const (μ := S.P) (e := (1 : ℝ)) hEvt_ambient)
      _ = p := by
            have hp_nonneg : 0 ≤ p := by
              exact inv_nonneg.mpr (Nat.cast_nonneg _)
            rw [measureReal_def, hProb, ENNReal.toReal_ofReal hp_nonneg]
  have hce := MeasureTheory.condExp_indep_eq
    (μ := S.P) (m₁ := currentSigma) (m₂ := S.paperStrictPastSigma t)
    (m := mΩ) hcurrent_le hpast_le hf_current hIndep.symm
  simpa [p, hIntegral] using hce

/-- Indicator-payload conditional expectation for a strict-past-determined payload.

Aligns with the indicator branch of Lan Lemma 5.9. Candidate audit:
`condExp_currentBlock_indicator_of_fresh_uniform` proves the scalar fresh block
law, and `condExp_smul_of_aestronglyMeasurable_right` is the matching Mathlib
pull-out API for an adapted vector payload. -/
private theorem conditionalExpectationEq_indicator_current_of_fresh_uniform
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {t : ℕ} (i : ι) (C : BlockSamplePath ι → F)
    (hC_int : Integrable C S.P)
    (hC_past : StronglyMeasurable[S.paperStrictPastSigma t] C) :
    conditionalExpectationEq S.P (S.paperStrictPastSigma t)
      (fun ω => if S.sample t ω = i then C ω else 0)
      (fun ω => (Fintype.card ι : ℝ)⁻¹ • C ω) := by
  classical
  let mΩ : MeasurableSpace (BlockSamplePath ι) := inferInstance
  let Evt : Set (BlockSamplePath ι) := (S.sample t) ⁻¹' ({i} : Set ι)
  let scalar : BlockSamplePath ι → ℝ :=
    fun ω => if S.sample t ω = i then (1 : ℝ) else 0
  let p : ℝ := (Fintype.card ι : ℝ)⁻¹
  have hpast_le : S.paperStrictPastSigma t ≤ mΩ := by
    rw [S.paperStrictPastSigma_eq_strictPastWindow_comap t]
    change MeasurableSpace.comap
        (fun ω : BlockSamplePath ι => fun r : Fin (t - 1) => S.sample (1 + r.1) ω)
        (by infer_instance : MeasurableSpace (Fin (t - 1) → ι)) ≤ mΩ
    exact (show @Measurable (BlockSamplePath ι) (Fin (t - 1) → ι) mΩ
      (by infer_instance : MeasurableSpace (Fin (t - 1) → ι))
      (fun ω : BlockSamplePath ι => fun r : Fin (t - 1) => S.sample (1 + r.1) ω) from
        @measurable_pi_lambda (BlockSamplePath ι) (Fin (t - 1)) (fun _ => ι)
          mΩ (fun _ => by infer_instance)
          (fun ω : BlockSamplePath ι => fun r : Fin (t - 1) => S.sample (1 + r.1) ω)
          (fun r : Fin (t - 1) =>
            show @Measurable (BlockSamplePath ι) ι mΩ
              (by infer_instance : MeasurableSpace ι)
              (fun ω : BlockSamplePath ι => S.sample (1 + r.1) ω) from
                S.sample_measurable (1 + r.1))).comap_le
  haveI : IsFiniteMeasure S.P := by
    unfold Setup.P uniformBlockStreamLaw
    infer_instance
  haveI : SigmaFinite (S.P.trim hpast_le) := inferInstance
  have hEvt_ambient : @MeasurableSet (BlockSamplePath ι) mΩ Evt := by
    exact (measurableSet_singleton i).preimage (S.sample_measurable t)
  have hbranch_indicator :
      (fun ω => if S.sample t ω = i then C ω else 0) = Evt.indicator C := by
    funext ω
    by_cases hω : S.sample t ω = i <;> simp [Evt, Set.indicator, hω]
  have hscalar_indicator : scalar = Evt.indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases hω : S.sample t ω = i <;> simp [scalar, Evt, Set.indicator, hω]
  have hbranch_smul :
      (fun ω => if S.sample t ω = i then C ω else 0) =
        fun ω => scalar ω • C ω := by
    funext ω
    by_cases hω : S.sample t ω = i <;> simp [scalar, hω]
  have hscalar_int : Integrable scalar S.P := by
    rw [hscalar_indicator]
    exact (integrable_const (1 : ℝ)).indicator hEvt_ambient
  have hbranch_int : Integrable (fun ω => if S.sample t ω = i then C ω else 0) S.P := by
    rw [hbranch_indicator]
    exact hC_int.indicator hEvt_ambient
  have hsmul_int : Integrable (fun ω => scalar ω • C ω) S.P := by
    simpa [hbranch_smul] using hbranch_int
  unfold conditionalExpectationEq SOptLib.ConditionalExpectation.conditionalExpectationEq
    SOptLib.ConditionalExpectation.conditionalExpectationWellDefined
  refine ⟨⟨hpast_le, inferInstance, hbranch_int⟩, ?_⟩
  have hscalar_ce :
      @MeasureTheory.condExp (BlockSamplePath ι) ℝ (S.paperStrictPastSigma t)
          (m₀ := by infer_instance) _ _ _ S.P scalar =ᵐ[S.P] fun _ => p := by
    simpa [scalar, p] using S.condExp_currentBlock_indicator_of_fresh_uniform (t := t) i
  have hpull :
      @MeasureTheory.condExp (BlockSamplePath ι) F (S.paperStrictPastSigma t)
          (m₀ := by infer_instance) _ _ _ S.P (fun ω => scalar ω • C ω) =ᵐ[S.P]
        fun ω =>
          (@MeasureTheory.condExp (BlockSamplePath ι) ℝ (S.paperStrictPastSigma t)
            (m₀ := by infer_instance) _ _ _ S.P scalar ω) • C ω := by
    exact MeasureTheory.condExp_smul_of_aestronglyMeasurable_right
      (μ := S.P) (m := S.paperStrictPastSigma t)
      (f := scalar) (g := C) hscalar_int hsmul_int hC_past.aestronglyMeasurable
  calc
    @MeasureTheory.condExp (BlockSamplePath ι) F (S.paperStrictPastSigma t)
        (m₀ := by infer_instance) _ _ _ S.P
        (fun ω => if S.sample t ω = i then C ω else 0)
        =ᵐ[S.P]
      @MeasureTheory.condExp (BlockSamplePath ι) F (S.paperStrictPastSigma t)
        (m₀ := by infer_instance) _ _ _ S.P (fun ω => scalar ω • C ω) := by
          rw [hbranch_smul]
    _ =ᵐ[S.P] (fun ω =>
          (@MeasureTheory.condExp (BlockSamplePath ι) ℝ (S.paperStrictPastSigma t)
            (m₀ := by infer_instance) _ _ _ S.P scalar ω) • C ω) := hpull
    _ =ᵐ[S.P] fun ω => (Fintype.card ι : ℝ)⁻¹ • C ω := by
          filter_upwards [hscalar_ce] with ω hω
          simp [p, hω]

/-- Expectation of the selected no-previous-hit payload.

This is the scalar probability bridge for Lan Proposition 5.6 proof step after
Eq. (5.2.75): the current block contributes a factor `1/m`, while `B_{i_t}`
contributes `((m-1)/m)^(t-1)`. Candidate audit: checked
`conditionalExpectationEq_indicator_current_of_fresh_uniform`,
`expectation_sample_eq_expectation_weighted_fiber_sum_of_indepFun`, and
`integral_comp_indep_finite_uniform_eq_integral_inv_card_sum`; the local
conditional-expectation indicator bridge is the narrow match because the payload
is a strict-past no-hit indicator times a deterministic scalar. -/
private theorem selected_current_no_previous_hit_expectation_eq
    (t : ℕ) (i : ι) (c : ℝ) :
    SOptLib.expectation S.P
        (fun ω : BlockSamplePath ι =>
          if S.sample t ω = i then
            (by
              classical
              exact if ¬ ∃ r, 1 ≤ r ∧ r ≤ t - 1 ∧ S.sample r ω = i then c else 0)
          else 0) =
      (Fintype.card ι : ℝ)⁻¹ *
        (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) ^ (t - 1) * c := by
  classical
  haveI : IsProbabilityMeasure S.P := by
    unfold Setup.P uniformBlockStreamLaw
    infer_instance
  exact
    SOptLib.expectation_current_hit_no_previous_hit_const_eq
      (μ := S.P) (sample := S.sample) t i c
      S.sample_measurable S.sample_iIndepFun
      (by
        intro n j
        have hmap :
            (Measure.map (S.sample n) S.P).real ({j} : Set ι) =
              S.P.real ((S.sample n) ⁻¹' ({j} : Set ι)) := by
          exact MeasureTheory.map_measureReal_apply
            (μ := S.P) (f := S.sample n) (S.sample_measurable n)
            (s := ({j} : Set ι)) (measurableSet_singleton j)
        have hmass := S.sample_uniform n j
        have hp_nonneg : 0 ≤ (Fintype.card ι : ℝ)⁻¹ := by
          exact inv_nonneg.mpr (Nat.cast_nonneg _)
        rw [hmap, measureReal_def, hmass, ENNReal.toReal_ofReal hp_nonneg])

/-- Integrability of a selected no-previous-hit scalar summand.

This is the integrability side needed to sum the `B_{i_t}` contributions in
Lan Proposition 5.6. Candidate audit: `selected_current_no_previous_hit_expectation_eq`
computes the same summand's expectation, but `MeasureTheory.integral_finset_sum`
also needs a separate `Integrable` proof for each finite summand. -/
private theorem selected_current_no_previous_hit_integrable
    (t : ℕ) (i : ι) (c : ℝ) :
    Integrable
      (fun ω : BlockSamplePath ι =>
        if S.sample t ω = i then
          (by
            classical
            exact if ¬ ∃ r, 1 ≤ r ∧ r ≤ t - 1 ∧ S.sample r ω = i then c else (0 : ℝ))
        else (0 : ℝ)) S.P := by
  classical
  let Event : Set (BlockSamplePath ι) :=
    {ω | S.sample t ω = i ∧
      ∀ r, 1 ≤ r → r ≤ t - 1 → S.sample r ω ≠ i}
  have hsample_meas :
      MeasurableSet ((S.sample t) ⁻¹' ({i} : Set ι)) :=
    (measurableSet_singleton i).preimage (S.sample_measurable t)
  have hno_meas :
      MeasurableSet {ω : BlockSamplePath ι |
        ∀ r, 1 ≤ r → r ≤ t - 1 → S.sample r ω ≠ i} :=
    S.no_previous_hit_measurable_ambient t i
  have hEvent_meas : MeasurableSet Event := by
    simpa [Event, Set.setOf_and] using hsample_meas.inter hno_meas
  have hfun :
      (fun ω : BlockSamplePath ι =>
        if S.sample t ω = i then
          (by
            classical
            exact if ¬ ∃ r, 1 ≤ r ∧ r ≤ t - 1 ∧ S.sample r ω = i then c else (0 : ℝ))
        else (0 : ℝ)) =
        Event.indicator (fun _ : BlockSamplePath ι => c) := by
    funext ω
    have hiff :
        (¬ ∃ r, 1 ≤ r ∧ r ≤ t - 1 ∧ S.sample r ω = i) ↔
          (∀ r, 1 ≤ r → r ≤ t - 1 → S.sample r ω ≠ i) := by
      constructor
      · intro hno r hr_one hr_le heq
        exact hno ⟨r, hr_one, hr_le, heq⟩
      · intro hno hex
        rcases hex with ⟨r, hr_one, hr_le, heq⟩
        exact hno r hr_one hr_le heq
    by_cases hsel : S.sample t ω = i
    · by_cases hno : ¬ ∃ r, 1 ≤ r ∧ r ≤ t - 1 ∧ S.sample r ω = i
      · have hmem : ω ∈ Event := ⟨hsel, hiff.mp hno⟩
        simp [Event, Set.indicator, hsel, hno, hmem]
      · have hnotmem : ω ∉ Event := by
          intro hmem
          exact hno (hiff.mpr hmem.2)
        simp [Event, Set.indicator, hsel, hno, hnotmem]
    · have hnotmem : ω ∉ Event := by
        intro hmem
        exact hsel hmem.1
      simp [Event, Set.indicator, hsel, hnotmem]
  haveI : IsFiniteMeasure S.P := by
    unfold Setup.P uniformBlockStreamLaw
    infer_instance
  rw [hfun]
  exact (integrable_const c).indicator hEvent_meas

/-- Selected stale-gradient expectation computed by the `B_{i_t}` split.

Aligns with Lan Proposition 5.6 proof step after Eq. (5.2.75): the pointwise
Eq. (5.2.64) split reduces the selected stale-gradient error to no-hit events,
the scalar bridge contributes `(1/m)((m-1)/m)^(t-1)`, and Eq. (5.2.56) collapses
the finite sum to `sigma0^2`. Candidate audit: checked
`expectation_sample_eq_expectation_weighted_fiber_sum_of_indepFun`,
`integral_comp_indep_finite_uniform_eq_integral_inv_card_sum`, and the local
`selected_current_no_previous_hit_expectation_eq`; the local scalar bridge is
the direct match because the fixed-index payload is already reduced to a
deterministic initial-gradient square on `B_{i_t}`. -/
private theorem selected_stale_gradient_expectation_eq_positive_domain
    (hη : S.PositiveEtaDomain) {sigma0 : ℝ}
    (hsigma : S.InitialGradientBound sigma0) (t : ℕ) :
    SOptLib.expectation S.P
      (fun ω =>
        S.dualNorm
          (S.gradF (S.sample t ω)
            (S.positiveEtaBlockIterate hη (t - 1) ω (S.sample t ω)) -
           S.positiveEtaYIterate hη (t - 1) ω (S.sample t ω)) ^ 2) =
      (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) ^ (t - 1) *
        sigma0 ^ 2 := by
  classical
  haveI : IsProbabilityMeasure S.P := by
    unfold Setup.P uniformBlockStreamLaw
    infer_instance
  simpa using
    SOptLib.selectedStaleMemoryResidual_expectation_eq_geometric_initial
      (μ := S.P) (sample := S.sample)
      (residual := fun i _n ω =>
        S.dualNorm
          (S.gradF i (S.positiveEtaBlockIterate hη (t - 1) ω i) -
            S.positiveEtaYIterate hη (t - 1) ω i) ^ 2)
      (initialResidual := fun i => S.dualNorm (S.gradF i S.x0) ^ 2)
      (sigma0 := sigma0) (t := t)
      S.sample_measurable S.sample_iIndepFun
      (by
        intro n j
        have hmap :
            (Measure.map (S.sample n) S.P).real ({j} : Set ι) =
              S.P.real ((S.sample n) ⁻¹' ({j} : Set ι)) := by
          exact MeasureTheory.map_measureReal_apply
            (μ := S.P) (f := S.sample n) (S.sample_measurable n)
            (s := ({j} : Set ι)) (measurableSet_singleton j)
        have hmass := S.sample_uniform n j
        have hp_nonneg : 0 ≤ (Fintype.card ι : ℝ)⁻¹ := by
          exact inv_nonneg.mpr (Nat.cast_nonneg _)
        rw [hmap, measureReal_def, hmass, ENNReal.toReal_ofReal hp_nonneg])
      (by
        intro i ω
        exact S.stale_gradient_error_pointwise_split_positive_domain hη t ω i)
      (by
        exact hsigma.1)

/-- Two-branch conditional expectation for Lemma 5.9 under the canonical fresh block.

This is the paper proof step `Prob_t {i_t=i}=1/m`: if the two branch payloads are
strict-past determined, the conditional expectation of the selected/nonselected
branch is the finite-uniform average. The explicit strict-past premises are the
adaptedness facts that the former arbitrary-process helper could not derive from
`DeterministicRGEMProcessEquations` alone. -/
private theorem conditionalExpectationEq_two_branch_of_fresh_uniform
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {t : ℕ} (ht : 1 ≤ t) (i : ι)
    (A B : BlockSamplePath ι → F)
    (hA_int : Integrable A S.P) (hB_int : Integrable B S.P)
    (hA_strictPast :
      ∀ ⦃ω ω' : BlockSamplePath ι⦄,
        (fun r : Fin (t - 1) => S.sample (1 + r.1) ω) =
          (fun r : Fin (t - 1) => S.sample (1 + r.1) ω') →
        A ω = A ω')
    (hB_strictPast :
      ∀ ⦃ω ω' : BlockSamplePath ι⦄,
        (fun r : Fin (t - 1) => S.sample (1 + r.1) ω) =
          (fun r : Fin (t - 1) => S.sample (1 + r.1) ω') →
        B ω = B ω') :
    conditionalExpectationEq S.P (S.paperStrictPastSigma t)
      (fun ω => if S.sample t ω = i then A ω else B ω)
      (fun ω =>
        (Fintype.card ι : ℝ)⁻¹ • A ω +
          (1 - (Fintype.card ι : ℝ)⁻¹) • B ω) := by
  classical
  let p : ℝ := (Fintype.card ι : ℝ)⁻¹
  let C : BlockSamplePath ι → F := fun ω => A ω - B ω
  have hA_past : StronglyMeasurable[S.paperStrictPastSigma t] A :=
    S.strictPast_stronglyMeasurable_of_window_const A hA_strictPast
  have hB_past : StronglyMeasurable[S.paperStrictPastSigma t] B :=
    S.strictPast_stronglyMeasurable_of_window_const B hB_strictPast
  have hC_past : StronglyMeasurable[S.paperStrictPastSigma t] C := by
    exact hA_past.sub hB_past
  have hC_int : Integrable C S.P := by
    exact hA_int.sub hB_int
  have hIndicator :=
    S.conditionalExpectationEq_indicator_current_of_fresh_uniform
      (t := t) i C hC_int hC_past
  rcases hIndicator with ⟨⟨hpast_le, hsf, hInd_int⟩, hInd_ce⟩
  haveI : SigmaFinite (S.P.trim hpast_le) := hsf
  have hbranch_decomp :
      (fun ω => if S.sample t ω = i then A ω else B ω) =
        fun ω => B ω + (if S.sample t ω = i then C ω else 0) := by
    funext ω
    by_cases hω : S.sample t ω = i <;> simp [C, hω]
  have hmain_int :
      Integrable (fun ω => if S.sample t ω = i then A ω else B ω) S.P := by
    rw [hbranch_decomp]
    exact hB_int.add hInd_int
  unfold conditionalExpectationEq SOptLib.ConditionalExpectation.conditionalExpectationEq
    SOptLib.ConditionalExpectation.conditionalExpectationWellDefined
  refine ⟨⟨hpast_le, hsf, hmain_int⟩, ?_⟩
  have hB_ce :
      @MeasureTheory.condExp (BlockSamplePath ι) F (S.paperStrictPastSigma t)
          (m₀ := by infer_instance) _ _ _ S.P B =ᵐ[S.P] B := by
    rw [MeasureTheory.condExp_of_stronglyMeasurable hpast_le hB_past hB_int]
  have hadd :
      @MeasureTheory.condExp (BlockSamplePath ι) F (S.paperStrictPastSigma t)
          (m₀ := by infer_instance) _ _ _ S.P
          (fun ω => B ω + (if S.sample t ω = i then C ω else 0)) =ᵐ[S.P]
        fun ω =>
          @MeasureTheory.condExp (BlockSamplePath ι) F (S.paperStrictPastSigma t)
              (m₀ := by infer_instance) _ _ _ S.P B ω +
            @MeasureTheory.condExp (BlockSamplePath ι) F (S.paperStrictPastSigma t)
              (m₀ := by infer_instance) _ _ _ S.P
              (fun ω => if S.sample t ω = i then C ω else 0) ω := by
    exact MeasureTheory.condExp_add hB_int hInd_int (S.paperStrictPastSigma t)
  calc
    @MeasureTheory.condExp (BlockSamplePath ι) F (S.paperStrictPastSigma t)
        (m₀ := by infer_instance) _ _ _ S.P
        (fun ω => if S.sample t ω = i then A ω else B ω)
        =ᵐ[S.P]
      @MeasureTheory.condExp (BlockSamplePath ι) F (S.paperStrictPastSigma t)
        (m₀ := by infer_instance) _ _ _ S.P
        (fun ω => B ω + (if S.sample t ω = i then C ω else 0)) := by
          rw [hbranch_decomp]
    _ =ᵐ[S.P] (fun ω =>
          @MeasureTheory.condExp (BlockSamplePath ι) F (S.paperStrictPastSigma t)
              (m₀ := by infer_instance) _ _ _ S.P B ω +
            @MeasureTheory.condExp (BlockSamplePath ι) F (S.paperStrictPastSigma t)
              (m₀ := by infer_instance) _ _ _ S.P
              (fun ω => if S.sample t ω = i then C ω else 0) ω) := hadd
    _ =ᵐ[S.P] fun ω => B ω + p • C ω := by
          exact hB_ce.add hInd_ce
    _ =ᵐ[S.P] fun ω =>
        (Fintype.card ι : ℝ)⁻¹ • A ω +
          (1 - (Fintype.card ι : ℝ)⁻¹) • B ω := by
          filter_upwards with ω
          simp only [p, C]
          rw [smul_sub, sub_smul, one_smul]
          abel

/-- Formula of Lemma 5.9 for the corrected positive-eta generated process. -/
def ConditionalBlockExpectation59Formula_positive_domain
    (hη : S.PositiveEtaDomain) (t : ℕ) (i : ι) : Prop :=
  S.ConditionalBlockExpectation59Formula hη t i

/-- Corrected-domain generated-process specialization of Lemma 5.9. -/
theorem ConditionalBlockExpectation_Lemma_5_9_positive_domain
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 1 ≤ t) (i : ι) :
    S.ConditionalBlockExpectation59Formula_positive_domain hη t i := by
  classical
  rcases S.positiveEtaGeneratedProcess_branch_identities hη ht i with
    ⟨hy_branch, hx_branch, hf_branch, hnorm_branch⟩
  unfold ConditionalBlockExpectation59Formula_positive_domain
  unfold ConditionalBlockExpectation59Formula
  refine ⟨?_, ?_, ?_, ?_⟩
  · let A : BlockSamplePath ι → E := fun ω =>
      S.auxiliaryGradient t (S.positiveEtaXIterate hη t ω)
        (S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i
    let B : BlockSamplePath ι → E := fun ω =>
      (S.positiveEtaGeneratedProcess hη (t - 1) ω).yCurr i
    have hA_int : Integrable A S.P :=
      S.positiveEta_strictPast_payload_integrable hη ht
        (fun x prev => S.auxiliaryGradient t x prev.blockX i)
    have hB_int : Integrable B S.P :=
      S.positiveEta_strictPast_payload_integrable hη ht
        (fun _x prev => prev.yCurr i)
    have hA_past :
        ∀ ⦃ω ω' : BlockSamplePath ι⦄,
          (fun r : Fin (t - 1) => S.sample (1 + r.1) ω) =
            (fun r : Fin (t - 1) => S.sample (1 + r.1) ω') →
          A ω = A ω' := by
      intro ω ω' hwin
      have hx := S.positiveEtaXIterate_eq_of_strictPastWindow_eq hη ht hwin
      have hprev := S.positiveEtaGeneratedProcess_eq_of_sampleWindow_eq hη (t - 1) hwin
      simp [A, hx, hprev]
    have hB_past :
        ∀ ⦃ω ω' : BlockSamplePath ι⦄,
          (fun r : Fin (t - 1) => S.sample (1 + r.1) ω) =
            (fun r : Fin (t - 1) => S.sample (1 + r.1) ω') →
          B ω = B ω' := by
      intro ω ω' hwin
      have hprev := S.positiveEtaGeneratedProcess_eq_of_sampleWindow_eq hη (t - 1) hwin
      simp [B, hprev]
    simpa [A, B, hy_branch] using
      S.conditionalExpectationEq_two_branch_of_fresh_uniform ht i A B
        hA_int hB_int hA_past hB_past
  · let A : BlockSamplePath ι → E := fun ω =>
      S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
        ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)
    let B : BlockSamplePath ι → E := fun ω =>
      (S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i
    have hA_int : Integrable A S.P :=
      S.positiveEta_strictPast_payload_integrable hη ht
        (fun x prev => S.auxiliaryPoint t x (prev.blockX i))
    have hB_int : Integrable B S.P :=
      S.positiveEta_strictPast_payload_integrable hη ht
        (fun _x prev => prev.blockX i)
    have hA_past :
        ∀ ⦃ω ω' : BlockSamplePath ι⦄,
          (fun r : Fin (t - 1) => S.sample (1 + r.1) ω) =
            (fun r : Fin (t - 1) => S.sample (1 + r.1) ω') →
          A ω = A ω' := by
      intro ω ω' hwin
      have hx := S.positiveEtaXIterate_eq_of_strictPastWindow_eq hη ht hwin
      have hprev := S.positiveEtaGeneratedProcess_eq_of_sampleWindow_eq hη (t - 1) hwin
      simp [A, hx, hprev]
    have hB_past :
        ∀ ⦃ω ω' : BlockSamplePath ι⦄,
          (fun r : Fin (t - 1) => S.sample (1 + r.1) ω) =
            (fun r : Fin (t - 1) => S.sample (1 + r.1) ω') →
          B ω = B ω' := by
      intro ω ω' hwin
      have hprev := S.positiveEtaGeneratedProcess_eq_of_sampleWindow_eq hη (t - 1) hwin
      simp [B, hprev]
    simpa [A, B, hx_branch] using
      S.conditionalExpectationEq_two_branch_of_fresh_uniform ht i A B
        hA_int hB_int hA_past hB_past
  · let A : BlockSamplePath ι → ℝ := fun ω =>
      S.f i (S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
        ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i))
    let B : BlockSamplePath ι → ℝ := fun ω =>
      S.f i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)
    have hA_int : Integrable A S.P :=
      S.positiveEta_strictPast_payload_integrable hη ht
        (fun x prev => S.f i (S.auxiliaryPoint t x (prev.blockX i)))
    have hB_int : Integrable B S.P :=
      S.positiveEta_strictPast_payload_integrable hη ht
        (fun _x prev => S.f i (prev.blockX i))
    have hA_past :
        ∀ ⦃ω ω' : BlockSamplePath ι⦄,
          (fun r : Fin (t - 1) => S.sample (1 + r.1) ω) =
            (fun r : Fin (t - 1) => S.sample (1 + r.1) ω') →
          A ω = A ω' := by
      intro ω ω' hwin
      have hx := S.positiveEtaXIterate_eq_of_strictPastWindow_eq hη ht hwin
      have hprev := S.positiveEtaGeneratedProcess_eq_of_sampleWindow_eq hη (t - 1) hwin
      simp [A, hx, hprev]
    have hB_past :
        ∀ ⦃ω ω' : BlockSamplePath ι⦄,
          (fun r : Fin (t - 1) => S.sample (1 + r.1) ω) =
            (fun r : Fin (t - 1) => S.sample (1 + r.1) ω') →
          B ω = B ω' := by
      intro ω ω' hwin
      have hprev := S.positiveEtaGeneratedProcess_eq_of_sampleWindow_eq hη (t - 1) hwin
      simp [B, hprev]
    simpa [A, B, hf_branch, smul_eq_mul] using
      S.conditionalExpectationEq_two_branch_of_fresh_uniform ht i A B
        hA_int hB_int hA_past hB_past
  · let A : BlockSamplePath ι → ℝ := fun ω =>
      S.dualNorm
        (S.gradF i (S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
          ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) -
          S.gradF i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) ^ 2
    let B : BlockSamplePath ι → ℝ := fun _ω => 0
    have hA_int : Integrable A S.P :=
      S.positiveEta_strictPast_payload_integrable hη ht
        (fun x prev =>
          S.dualNorm
            (S.gradF i (S.auxiliaryPoint t x (prev.blockX i)) -
              S.gradF i (prev.blockX i)) ^ 2)
    have hB_int : Integrable B S.P := by
      simpa [B] using
        (integrable_zero (α := BlockSamplePath ι) (ε' := ℝ) (μ := S.P))
    have hA_past :
        ∀ ⦃ω ω' : BlockSamplePath ι⦄,
          (fun r : Fin (t - 1) => S.sample (1 + r.1) ω) =
            (fun r : Fin (t - 1) => S.sample (1 + r.1) ω') →
          A ω = A ω' := by
      intro ω ω' hwin
      have hx := S.positiveEtaXIterate_eq_of_strictPastWindow_eq hη ht hwin
      have hprev := S.positiveEtaGeneratedProcess_eq_of_sampleWindow_eq hη (t - 1) hwin
      simp [A, hx, hprev]
    have hB_past :
        ∀ ⦃ω ω' : BlockSamplePath ι⦄,
          (fun r : Fin (t - 1) => S.sample (1 + r.1) ω) =
            (fun r : Fin (t - 1) => S.sample (1 + r.1) ω') →
          B ω = B ω' := by
      intro ω ω' _hwin
      simp [B]
    have hsource :
        (fun ω : BlockSamplePath ι =>
          S.dualNorm
            (S.gradF i (S.positiveEtaBlockIterate hη t ω i) -
              S.gradF i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) ^ 2) =
          (fun ω => if S.sample t ω = i then A ω else B ω) := by
      funext ω
      simpa only [A, B] using hnorm_branch ω
    rw [hsource]
    simpa [A, B, smul_eq_mul] using
      S.conditionalExpectationEq_two_branch_of_fresh_uniform ht i A B
        hA_int hB_int hA_past hB_past

/-- Source theorem head for Eq. (5.2.85), the stochastic component-gradient update. -/
theorem StochasticComponentGradientUpdate_Eq_5_2_85 {Ξ : Type*}
    (B : ℕ → ℕ) (hB : S.StochasticBatchDomain B) (G : ι → E → Ξ → E)
    (ξ : ι → ℕ → ℕ → Ξ) (t : ℕ) (ht : 1 ≤ t) (selected i : ι)
    (blockNext yPrev : ι → E) :
    S.stochasticComponentGradientUpdate B hB G ξ t ht selected blockNext yPrev i =
      if i = selected then
        ((B t : ℝ)⁻¹) •
          Finset.sum (Finset.Icc 1 (B t)) (fun j => G i (blockNext i) (ξ i t j))
      else
        yPrev i := by
  by_cases hi : i = selected
  · subst hi
    simp [stochasticComponentGradientUpdate, stochasticBatchGradient]
  · simp [stochasticComponentGradientUpdate, hi]

/-- Source theorem head for Eq. (5.2.86), the stochastic auxiliary gradient. -/
theorem StochasticAuxiliaryGradientDefinition_Eq_5_2_86 {Ξ : Type*}
    (B : ℕ → ℕ) (hB : S.StochasticBatchDomain B) (G : ι → E → Ξ → E)
    (ξ : ι → ℕ → ℕ → Ξ) (t : ℕ) (ht : 1 ≤ t) (x : E)
    (blockPrev : ι → E) (i : ι) :
    S.stochasticAuxiliaryGradient B hB G ξ t ht x blockPrev i =
      ((B t : ℝ)⁻¹) •
        Finset.sum (Finset.Icc 1 (B t))
          (fun j => G i (S.auxiliaryPoint t x (blockPrev i)) (ξ i t j)) := by
  rfl

/-- Source-backed stochastic-oracle assumptions for Lemma 5.11.

The stochastic subsection states SFO assumptions (5.2.83)--(5.2.84) immediately
before Algorithm 5.5.  This record keeps only that source-literal fixed-query SFO
content: a finite oracle-table law and, for each component/time/batch coordinate,
an unbiased bounded-variance oracle on `X`.  It deliberately does not contain
generated-payload regularity fields: Lemma 5.11's source proof uses only the
selected/nonselected branch identities and the fresh uniform current-block law. -/
structure StochasticOracleAssumptions511 {Ξ : Type*} [MeasurableSpace Ξ] [MeasurableSpace E]
    (Pξ : Measure (StochasticSampleTable ι Ξ))
    (B : ℕ → ℕ) (hB : S.StochasticBatchDomain B) (G : ι → E → Ξ → E)
    (hη : S.PositiveEtaDomain) (σ : ℝ) : Prop where
  sample_table_finite : IsFiniteMeasure Pξ
  fixed_query_oracle :
    ∀ (i : ι) (t j : ℕ),
      SOptLib.BoundedVarianceUnbiasedOracleOn S.X
        (Measure.map (fun ξ : StochasticSampleTable ι Ξ => ξ i t j) Pξ)
        (fun x ξ => G i x ξ) (S.gradF i) S.dualNorm σ

/-- The product stochastic run law is finite once the SFO table law is finite. -/
private theorem stochasticRunLaw_finite_of_oracle_assumptions {Ξ : Type*}
    [MeasurableSpace Ξ] [MeasurableSpace E]
    (Pξ : Measure (StochasticSampleTable ι Ξ))
    (B : ℕ → ℕ) (hB : S.StochasticBatchDomain B) (G : ι → E → Ξ → E)
    (hη : S.PositiveEtaDomain) (σ : ℝ)
    (hSFO : S.StochasticOracleAssumptions511 Pξ B hB G hη σ) :
    IsFiniteMeasure (S.stochasticRunLaw Pξ) := by
  haveI : IsFiniteMeasure S.P := by
    unfold Setup.P uniformBlockStreamLaw
    infer_instance
  haveI : IsFiniteMeasure Pξ := hSFO.sample_table_finite
  unfold stochasticRunLaw
  infer_instance

/-- Finite measures are s-finite.

Mathlib's product rectangle identity is stated for an s-finite second factor;
Lemma 5.11's SFO assumptions give a finite oracle-table law, so this local
bridge exposes the required measure-theory instance without changing any
source-facing stochastic assumption. Candidate audit: searched `SFinite finite
measure instance finite measure is sfinite`; Mathlib provides
`sfinite_sum_of_countable` but no direct instance, so this specializes it to a
singleton countable sum. -/
private theorem sfinite_of_isFiniteMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] : SFinite μ := by
  refine ⟨fun n : ℕ => if n = 0 then μ else 0, ?_, ?_⟩
  · intro n
    by_cases hn : n = 0
    · subst n
      change IsFiniteMeasure μ
      infer_instance
    · simp [hn]
      change IsFiniteMeasure (0 : Measure Ω)
      infer_instance
  · ext s hs
    rw [Measure.sum_apply _ hs]
    symm
    calc
      (∑' n : ℕ, (if n = 0 then μ else 0) s) =
          (if (0 : ℕ) = 0 then μ else 0) s := by
        refine tsum_eq_single 0 ?_
        intro n hn
        simp [hn]
      _ = μ s := by simp

/-- Rectangle generator form of the stochastic current-block product-law normalization.

Aligns with Lan Lemma 5.11's `Prob_t {i_t=i}=1/m` on events that fix a
strict-past block event and an oracle-table event. This is the generator case
needed for extending the normalization to `paperStrictPastSigma ⊔ Prod.snd`.
Candidate audit: searched `product measure rectangle current block
independence` and checked `Measure.prod_prod`; the product rectangle API applies
exactly here, while the full joined-sigma statement still needs a monotone-class
extension. -/
private theorem stochastic_currentBlock_indicator_rectangle_measure_eq_of_fresh_uniform {Ξ : Type*}
    [MeasurableSpace Ξ]
    (Pξ : Measure (StochasticSampleTable ι Ξ))
    [SFinite Pξ]
    {t : ℕ} (_ht : 1 ≤ t) (i : ι)
    (A : Set (BlockSamplePath ι))
    (hA : @MeasurableSet (BlockSamplePath ι) (S.paperStrictPastSigma t) A)
    (B : Set (StochasticSampleTable ι Ξ)) :
    (S.stochasticRunLaw Pξ)
      (((Prod.fst ⁻¹' A) ∩ (Prod.snd ⁻¹' B)) ∩
        ((S.stochasticBlockSample (Ξ := Ξ) t) ⁻¹' ({i} : Set ι))) =
      ENNReal.ofReal ((Fintype.card ι : ℝ)⁻¹) *
        (S.stochasticRunLaw Pξ) ((Prod.fst ⁻¹' A) ∩ (Prod.snd ⁻¹' B)) := by
  classical
  let Evt : Set (BlockSamplePath ι) := (S.sample t) ⁻¹' ({i} : Set ι)
  let p : ℝ := (Fintype.card ι : ℝ)⁻¹
  rcases S.currentBlock_fresh_uniform t i with ⟨hIndep, hProb⟩
  have hEvt_current :
      @MeasurableSet (BlockSamplePath ι)
        (MeasurableSpace.comap (S.sample t) (by infer_instance : MeasurableSpace ι))
        Evt := by
    have hsample :
        @Measurable (BlockSamplePath ι) ι
          (MeasurableSpace.comap (S.sample t) (by infer_instance : MeasurableSpace ι))
          (by infer_instance : MeasurableSpace ι) (S.sample t) :=
      Measurable.of_comap_le le_rfl
    exact (measurableSet_singleton i).preimage hsample
  have hAevt :
      S.P (A ∩ Evt) = ENNReal.ofReal p * S.P A := by
    have h :=
      (Indep_iff (S.paperStrictPastSigma t)
        (MeasurableSpace.comap (S.sample t) (by infer_instance : MeasurableSpace ι))
        S.P).1 hIndep A Evt hA hEvt_current
    rw [h, hProb, mul_comm]
  have hleft_set :
      (((Prod.fst ⁻¹' A) ∩ (Prod.snd ⁻¹' B)) ∩
          ((S.stochasticBlockSample (Ξ := Ξ) t) ⁻¹' ({i} : Set ι))) =
        (A ∩ Evt) ×ˢ B := by
    ext ω
    simp [Evt, stochasticBlockSample]
    tauto
  have hright_set :
      ((Prod.fst ⁻¹' A) ∩ (Prod.snd ⁻¹' B) : Set (StochasticRunPath ι Ξ)) =
        A ×ˢ B := by
    ext ω
    simp
  calc
    (S.stochasticRunLaw Pξ)
        (((Prod.fst ⁻¹' A) ∩ (Prod.snd ⁻¹' B)) ∩
          ((S.stochasticBlockSample (Ξ := Ξ) t) ⁻¹' ({i} : Set ι)))
        = (S.P.prod Pξ) ((A ∩ Evt) ×ˢ B) := by
            rw [stochasticRunLaw, hleft_set]
    _ = S.P (A ∩ Evt) * Pξ B := by
            rw [Measure.prod_prod]
    _ = (ENNReal.ofReal p * S.P A) * Pξ B := by
            rw [hAevt]
    _ = ENNReal.ofReal p * (S.P A * Pξ B) := by
            rw [mul_assoc]
    _ = ENNReal.ofReal p * (S.P.prod Pξ) (A ×ˢ B) := by
            rw [Measure.prod_prod]
    _ = ENNReal.ofReal ((Fintype.card ι : ℝ)⁻¹) *
          (S.stochasticRunLaw Pξ) ((Prod.fst ⁻¹' A) ∩ (Prod.snd ⁻¹' B)) := by
            rw [stochasticRunLaw, hright_set]

/-- Measure form of the stochastic current-block product-law normalization.

Aligns with Lan Lemma 5.11's `Prob_t {i_t=i}=1/m` after fixing the strict
block past and the oracle table. Candidate audit: searched
`product measure independent first coordinate finite measure sigma algebra`,
`measurable set product sigma section measurable measure section`, and checked
`PMF.prod_measure_set_sigma_eq_sum`; those cover finite selector products or
raw product sections, but not the current `paperStrictPastSigma`-measurable
first-coordinate factor joined with a full second-coordinate sigma. -/
private theorem stochastic_currentBlock_indicator_measure_eq_of_fresh_uniform {Ξ : Type*}
    [MeasurableSpace Ξ]
    (Pξ : Measure (StochasticSampleTable ι Ξ))
    [SFinite Pξ]
    (hfinite : IsFiniteMeasure (S.stochasticRunLaw Pξ))
    {t : ℕ} (_ht : 1 ≤ t) (i : ι) :
    ∀ s : Set (StochasticRunPath ι Ξ),
      @MeasurableSet (StochasticRunPath ι Ξ)
        (S.stochasticConditioningSigma (Ξ := Ξ) t) s →
        (S.stochasticRunLaw Pξ)
          (s ∩ ((S.stochasticBlockSample (Ξ := Ξ) t) ⁻¹' ({i} : Set ι))) =
          ENNReal.ofReal ((Fintype.card ι : ℝ)⁻¹) * (S.stochasticRunLaw Pξ) s := by
  classical
  intro s hs
  let μ : Measure (StochasticRunPath ι Ξ) := S.stochasticRunLaw Pξ
  let mΩ : MeasurableSpace (StochasticRunPath ι Ξ) := inferInstance
  let pastSets : Set (Set (BlockSamplePath ι)) :=
    {A | @MeasurableSet (BlockSamplePath ι) (S.paperStrictPastSigma t) A}
  let tableSets : Set (Set (StochasticSampleTable ι Ξ)) :=
    {B | MeasurableSet B}
  let rects : Set (Set (StochasticRunPath ι Ξ)) :=
    Set.image2 (fun A B => A ×ˢ B) pastSets tableSets
  let Evt : Set (StochasticRunPath ι Ξ) :=
    (S.stochasticBlockSample (Ξ := Ξ) t) ⁻¹' ({i} : Set ι)
  let p : ℝ := (Fintype.card ι : ℝ)⁻¹
  let pENN : ENNReal := ENNReal.ofReal p
  haveI : IsFiniteMeasure μ := hfinite
  have hcond_le : S.stochasticConditioningSigma (Ξ := Ξ) t ≤ mΩ :=
    S.stochasticConditioningSigma_le (Ξ := Ξ) t
  have hblock_meas :
      @Measurable (StochasticRunPath ι Ξ) ι mΩ
        (by infer_instance : MeasurableSpace ι)
        (S.stochasticBlockSample (Ξ := Ξ) t) := by
    simpa [mΩ, stochasticBlockSample] using (S.sample_measurable t).comp measurable_fst
  have hEvt_ambient : @MeasurableSet (StochasticRunPath ι Ξ) mΩ Evt := by
    exact (measurableSet_singleton i).preimage hblock_meas
  have hcond_eq :
      S.stochasticConditioningSigma (Ξ := Ξ) t = MeasurableSpace.generateFrom rects := by
    change
      (@Prod.instMeasurableSpace (BlockSamplePath ι) (StochasticSampleTable ι Ξ)
          (S.paperStrictPastSigma t)
          (by infer_instance : MeasurableSpace (StochasticSampleTable ι Ξ))) =
        MeasurableSpace.generateFrom rects
    exact (@generateFrom_prod (BlockSamplePath ι) (StochasticSampleTable ι Ξ)
      (S.paperStrictPastSigma t)
      (by infer_instance : MeasurableSpace (StochasticSampleTable ι Ξ))).symm
  have hrects_pi : IsPiSystem rects := by
    change IsPiSystem
      (Set.image2 (fun A B => A ×ˢ B)
        {A : Set (BlockSamplePath ι) |
          @MeasurableSet (BlockSamplePath ι) (S.paperStrictPastSigma t) A}
        {B : Set (StochasticSampleTable ι Ξ) | MeasurableSet B})
    exact (@isPiSystem_prod (BlockSamplePath ι) (StochasticSampleTable ι Ξ)
      (S.paperStrictPastSigma t)
      (by infer_instance : MeasurableSpace (StochasticSampleTable ι Ξ)))
  have hbasic :
      ∀ r ∈ rects, (μ.restrict Evt) r = (pENN • μ) r := by
    intro r hr
    rcases hr with ⟨A, hA, B, _hB, rfl⟩
    have hprod_set :
        (A ×ˢ B : Set (StochasticRunPath ι Ξ)) =
        (Prod.fst ⁻¹' A) ∩ (Prod.snd ⁻¹' B) := by
      ext ω
      simp
    rw [Measure.restrict_apply' hEvt_ambient, Measure.smul_apply, smul_eq_mul]
    change μ ((A ×ˢ B : Set (StochasticRunPath ι Ξ)) ∩ Evt) =
      pENN * μ (A ×ˢ B : Set (StochasticRunPath ι Ξ))
    rw [hprod_set]
    simpa [μ, Evt, p, pENN] using
      S.stochastic_currentBlock_indicator_rectangle_measure_eq_of_fresh_uniform
        (Ξ := Ξ) Pξ (t := t) _ht i A hA B
  have huniv :
      (μ.restrict Evt) Set.univ = (pENN • μ) Set.univ := by
    rw [Measure.restrict_apply' hEvt_ambient, Measure.smul_apply, smul_eq_mul]
    have hrect :=
      S.stochastic_currentBlock_indicator_rectangle_measure_eq_of_fresh_uniform
        (Ξ := Ξ) Pξ (t := t) _ht i Set.univ
        (by exact MeasurableSet.univ) Set.univ
    simpa [μ, Evt, p, pENN] using hrect
  have hmeasure_eq :
      (μ.restrict Evt) s = (pENN • μ) s :=
    MeasureTheory.ext_on_measurableSpace_of_generate_finite
      mΩ rects hbasic hcond_le hcond_eq hrects_pi huniv hs
  rw [Measure.restrict_apply' hEvt_ambient, Measure.smul_apply, smul_eq_mul] at hmeasure_eq
  simpa [μ, Evt, p, pENN] using hmeasure_eq

/-- Set-integral form of the stochastic current-block freshness bridge.

Aligns with Lan Lemma 5.11's conditional step `Prob_t {i_t=i}=1/m`.
Candidate audit: `MeasureTheory.condExp_indep_eq` was considered but returns
the unnormalized integral under a finite measure, while this theorem needs the
normalized conditional probability for `S.P.prod Pξ`; searched
`integral_comp_indep_finite_uniform_eq_integral_inv_card_sum` and
`PMF.prod_measure_set_sigma_eq_sum`, which expose useful finite-uniform/product
integral patterns but do not directly handle the `paperStrictPastSigma ⊔
Prod.snd` conditioning sigma. -/
private theorem stochastic_currentBlock_indicator_setIntegral_eq_of_fresh_uniform {Ξ : Type*}
    [MeasurableSpace Ξ]
    (Pξ : Measure (StochasticSampleTable ι Ξ))
    [SFinite Pξ]
    (hfinite : IsFiniteMeasure (S.stochasticRunLaw Pξ))
    {t : ℕ} (_ht : 1 ≤ t) (i : ι) :
    ∀ s : Set (StochasticRunPath ι Ξ),
      @MeasurableSet (StochasticRunPath ι Ξ)
        (S.stochasticConditioningSigma (Ξ := Ξ) t) s →
      ((S.stochasticRunLaw Pξ) s < ⊤) →
        (∫ ω in s, ((Fintype.card ι : ℝ)⁻¹ : ℝ) ∂S.stochasticRunLaw Pξ) =
          ∫ ω in s,
            (if S.stochasticBlockSample t ω = i then (1 : ℝ) else 0)
              ∂S.stochasticRunLaw Pξ := by
  classical
  -- The remaining proof is the product-law normalization step: for every event
  -- measurable from the strict block past and oracle table, the current block
  -- singleton has conditional mass `1 / card ι` under `S.P.prod Pξ`.
  intro s hs hμs
  let mΩ : MeasurableSpace (StochasticRunPath ι Ξ) := inferInstance
  let μ : Measure (StochasticRunPath ι Ξ) := S.stochasticRunLaw Pξ
  let p : ℝ := (Fintype.card ι : ℝ)⁻¹
  let Evt : Set (StochasticRunPath ι Ξ) :=
    (S.stochasticBlockSample (Ξ := Ξ) t) ⁻¹' ({i} : Set ι)
  have hm :
      S.stochasticConditioningSigma (Ξ := Ξ) t ≤ mΩ :=
    S.stochasticConditioningSigma_le (Ξ := Ξ) t
  have hs_ambient : @MeasurableSet (StochasticRunPath ι Ξ) mΩ s := hm s hs
  have hblock_meas :
      @Measurable (StochasticRunPath ι Ξ) ι mΩ
        (by infer_instance : MeasurableSpace ι)
        (S.stochasticBlockSample (Ξ := Ξ) t) := by
    simpa [stochasticBlockSample] using (S.sample_measurable t).comp measurable_fst
  have hEvt_ambient : @MeasurableSet (StochasticRunPath ι Ξ) mΩ Evt := by
    exact (measurableSet_singleton i).preimage hblock_meas
  have hindicator :
      (fun ω : StochasticRunPath ι Ξ =>
          if S.stochasticBlockSample t ω = i then (1 : ℝ) else 0) =
        Evt.indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases hω : S.stochasticBlockSample t ω = i <;>
      simp [Evt, Set.indicator, hω]
  have hmass :
      μ (s ∩ Evt) = ENNReal.ofReal p * μ s := by
    simpa [μ, p, Evt] using
      S.stochastic_currentBlock_indicator_measure_eq_of_fresh_uniform
        (Ξ := Ξ) Pξ hfinite (t := t) _ht i s hs
  have hp_nonneg : 0 ≤ p := by
    exact inv_nonneg.mpr (Nat.cast_nonneg _)
  have hleft :
      (∫ ω in s, (p : ℝ) ∂μ) = μ.real s * p := by
    rw [setIntegral_const]
    simp [smul_eq_mul, mul_comm]
  have hright :
      (∫ ω in s,
          (if S.stochasticBlockSample t ω = i then (1 : ℝ) else 0) ∂μ) =
        μ.real (s ∩ Evt) := by
    rw [hindicator]
    calc
      (∫ ω in s, Evt.indicator (fun _ => (1 : ℝ)) ω ∂μ)
          = ∫ ω, Evt.indicator (fun _ => (1 : ℝ)) ω ∂(μ.restrict s) := rfl
      _ = (μ.restrict s).real Evt := by
          simpa using
            (integral_indicator_const (μ := μ.restrict s) (e := (1 : ℝ)) hEvt_ambient)
      _ = μ.real (Evt ∩ s) := by
          rw [measureReal_def, measureReal_def, Measure.restrict_apply hEvt_ambient]
      _ = μ.real (s ∩ Evt) := by
          congr 1
          exact Set.inter_comm Evt s
  have hreal_mass : μ.real (s ∩ Evt) = p * μ.real s := by
    rw [measureReal_def, hmass, ENNReal.toReal_mul]
    rw [ENNReal.toReal_ofReal hp_nonneg, measureReal_def]
  calc
    (∫ ω in s, ((Fintype.card ι : ℝ)⁻¹ : ℝ) ∂S.stochasticRunLaw Pξ)
        = μ.real s * p := by
          simpa [μ, p] using hleft
    _ = p * μ.real s := by ring
    _ = μ.real (s ∩ Evt) := hreal_mass.symm
    _ = ∫ ω in s,
          (if S.stochasticBlockSample t ω = i then (1 : ℝ) else 0)
            ∂S.stochasticRunLaw Pξ := by
          simpa [μ, Evt] using hright.symm

/-- Scalar current-block conditional expectation for stochastic Lemma 5.11.

This is the stochastic version of `condExp_currentBlock_indicator_of_fresh_uniform`:
under the product run law, the current block is fresh relative to the sigma
algebra generated by the strict block past and oracle table. This is a proof
obligation from Algorithm 5.4's uniform fresh block sampling, not a field of the
Lemma 5.11 payload regularity interface. -/
private theorem stochastic_currentBlock_indicator_ce_of_fresh_uniform {Ξ : Type*}
    [MeasurableSpace Ξ]
    (Pξ : Measure (StochasticSampleTable ι Ξ))
    [SFinite Pξ]
    (hfinite : IsFiniteMeasure (S.stochasticRunLaw Pξ))
    {t : ℕ} (_ht : 1 ≤ t) (i : ι) :
    @MeasureTheory.condExp (StochasticRunPath ι Ξ) ℝ
        (S.stochasticConditioningSigma (Ξ := Ξ) t)
        (m₀ := by infer_instance) _ _ _ (S.stochasticRunLaw Pξ)
        (fun ω => if S.stochasticBlockSample t ω = i then (1 : ℝ) else 0)
      =ᵐ[S.stochasticRunLaw Pξ] fun _ => (Fintype.card ι : ℝ)⁻¹ := by
  classical
  let mΩ : MeasurableSpace (StochasticRunPath ι Ξ) := inferInstance
  let μ : Measure (StochasticRunPath ι Ξ) := S.stochasticRunLaw Pξ
  let condSigma : MeasurableSpace (StochasticRunPath ι Ξ) :=
    S.stochasticConditioningSigma (Ξ := Ξ) t
  let scalar : StochasticRunPath ι Ξ → ℝ :=
    fun ω => if S.stochasticBlockSample t ω = i then (1 : ℝ) else 0
  let p : ℝ := (Fintype.card ι : ℝ)⁻¹
  let Evt : Set (StochasticRunPath ι Ξ) :=
    (S.stochasticBlockSample (Ξ := Ξ) t) ⁻¹' ({i} : Set ι)
  haveI : IsFiniteMeasure μ := hfinite
  have hm : condSigma ≤ mΩ := by
    change S.stochasticConditioningSigma (Ξ := Ξ) t ≤ mΩ
    exact S.stochasticConditioningSigma_le (Ξ := Ξ) t
  haveI : SigmaFinite (μ.trim hm) := by
    haveI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
    infer_instance
  have hblock_meas :
      @Measurable (StochasticRunPath ι Ξ) ι mΩ
        (by infer_instance : MeasurableSpace ι)
        (S.stochasticBlockSample (Ξ := Ξ) t) := by
    simpa [stochasticBlockSample] using (S.sample_measurable t).comp measurable_fst
  have hEvt_ambient : @MeasurableSet (StochasticRunPath ι Ξ) mΩ Evt := by
    exact (measurableSet_singleton i).preimage hblock_meas
  have hscalar_indicator : scalar = Evt.indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases hω : S.stochasticBlockSample t ω = i <;>
      simp [scalar, Evt, Set.indicator, hω]
  have hscalar_int : Integrable scalar μ := by
    rw [hscalar_indicator]
    exact (integrable_const (1 : ℝ)).indicator hEvt_ambient
  have hconst_int :
      ∀ s : Set (StochasticRunPath ι Ξ), @MeasurableSet (StochasticRunPath ι Ξ) condSigma s →
        (μ s < ⊤) →
        IntegrableOn (fun _ : StochasticRunPath ι Ξ => p) s μ := by
    intro s _hs hμs
    exact integrableOn_const hμs.ne
  have hset :
      ∀ s : Set (StochasticRunPath ι Ξ), @MeasurableSet (StochasticRunPath ι Ξ) condSigma s →
        (μ s < ⊤) →
        (∫ ω in s, (fun _ : StochasticRunPath ι Ξ => p) ω ∂μ) =
          ∫ ω in s, scalar ω ∂μ := by
    simpa [μ, condSigma, scalar, p] using
      S.stochastic_currentBlock_indicator_setIntegral_eq_of_fresh_uniform
        (Ξ := Ξ) Pξ hfinite (t := t) _ht i
  have hconst_meas :
      AEStronglyMeasurable[condSigma] (fun _ : StochasticRunPath ι Ξ => p) μ :=
    stronglyMeasurable_const.aestronglyMeasurable
  have hce :
      (fun _ : StochasticRunPath ι Ξ => p) =ᵐ[μ]
        @MeasureTheory.condExp (StochasticRunPath ι Ξ) ℝ condSigma
          (m₀ := mΩ) _ _ _ μ scalar :=
    MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hm hscalar_int
      hconst_int hset hconst_meas
  simpa [μ, condSigma, scalar, p] using hce.symm

/-- Finite-uniform current-block partial expectation used by Lemma 5.11.

Book JSON `#/key_lemmas[name=ConditionalBlockExpectation_Lemma_5_11]/proof/0`
states the proof as `Prob_t {i_t=i}=1/m`, with the selected branch taking the
hat value and the nonselected branch taking the previous value. This definition
uses the SOptLib finite-uniform selection primitive found by searching
`partial conditional expectation current coordinate finite uniform` and
`conditional expectation finite uniform branch indicator`; no separate Mathlib
conditional-expectation object is needed for this source proof step. -/
noncomputable def currentBlockTwoBranchExpectation
    (_S : RandomGradientExtrapolation.Setup ι E) {Ξ F : Type*}
    [AddCommGroup F] [Module ℝ F] (i : ι)
    (selected other : StochasticRunPath ι Ξ → F) : StochasticRunPath ι Ξ → F :=
  fun ω => SOptLib.finiteUniformAverage
    (fun j : ι => if j = i then selected ω else other ω)

private theorem currentBlockTwoBranchExpectation_eq_weighted {Ξ F : Type*}
    [AddCommGroup F] [Module ℝ F] (i : ι)
    (selected other : StochasticRunPath ι Ξ → F) :
    S.currentBlockTwoBranchExpectation i selected other =
      fun ω =>
        (Fintype.card ι : ℝ)⁻¹ • selected ω +
          (1 - (Fintype.card ι : ℝ)⁻¹) • other ω := by
  classical
  funext ω
  unfold currentBlockTwoBranchExpectation
  have hswap :
      (fun j : ι => if j = i then selected ω else other ω) =
        (fun j : ι => if i = j then selected ω else other ω) := by
    funext j
    by_cases hij : i = j
    · have hji : j = i := hij.symm
      rw [if_pos hji, if_pos hij]
    · have hji : j ≠ i := fun hji => hij hji.symm
      rw [if_neg hji, if_neg hij]
  rw [hswap]
  calc
    SOptLib.finiteUniformAverage
        (fun j : ι => if i = j then selected ω else other ω)
        = (Fintype.card ι : ℝ)⁻¹ • (selected ω - other ω) + other ω := by
          exact SOptLib.finiteUniformAverage_ite_eq_inv_card_smul_sub_add
            i (selected ω) (other ω)
    _ = (Fintype.card ι : ℝ)⁻¹ • selected ω +
          (1 - (Fintype.card ι : ℝ)⁻¹) • other ω := by
          rw [smul_sub, sub_smul, one_smul]
          abel

/-- Source-facing current-block partial expectation equality for Lemma 5.11.

This records exactly the source proof pattern: the sampled current block selects
one branch, and the paper's `E_t` averages that two-branch value over the fresh
uniform current block while holding the stated conditioning data fixed. -/
def currentBlockPartialExpectationEq {Ξ F : Type*}
    [AddCommGroup F] [Module ℝ F] (t : ℕ) (i : ι)
    (Z selected other target : StochasticRunPath ι Ξ → F) : Prop :=
  (∀ ω, Z ω = if S.stochasticBlockSample t ω = i then selected ω else other ω) ∧
    target = S.currentBlockTwoBranchExpectation i selected other

/-- Formula of Lemma 5.11 for the canonical generated stochastic RGEM process.

The paper defines `E_t` here as conditional expectation with respect to the
current block `i_t` after fixing the stated past and current stochastic batch.
The source proof immediately expands this to the two probabilities
`Prob_t{i_t=i}=1/m` and `1-1/m`; this formula represents that partial
current-block expectation directly instead of transporting a full-table
Mathlib `condExp` identity across sigma algebras. -/
def ConditionalBlockExpectation511Formula {Ξ : Type*} [MeasurableSpace Ξ]
    (Pξ : Measure (StochasticSampleTable ι Ξ))
    (B : ℕ → ℕ) (hB : S.StochasticBatchDomain B) (G : ι → E → Ξ → E)
    (hη : S.PositiveEtaDomain)
    (t : ℕ) (ht : 1 ≤ t) (i : ι) : Prop :=
  let prevState : StochasticRunPath ι Ξ → State ι E :=
    fun ω => S.positiveEtaGeneratedStochasticProcess B hB G hη (t - 1) ω
  let xNext : StochasticRunPath ι Ξ → E :=
    fun ω => S.positiveEtaStochasticXIterate B hB G hη t ω
  let sampleTable : StochasticRunPath ι Ξ → ι → ℕ → ℕ → Ξ :=
    fun ω i t j => S.stochasticOracleSample i t j ω
  S.currentBlockPartialExpectationEq t i
      (fun ω => S.positiveEtaStochasticYIterate B hB G hη t ω i)
      (fun ω =>
        S.stochasticAuxiliaryGradient B hB G (sampleTable ω) t ht
          (xNext ω) (prevState ω).blockX i)
      (fun ω => (prevState ω).yCurr i)
      (fun ω =>
        (Fintype.card ι : ℝ)⁻¹ •
            S.stochasticAuxiliaryGradient B hB G (sampleTable ω) t ht
              (xNext ω) (prevState ω).blockX i +
          (1 - (Fintype.card ι : ℝ)⁻¹) • (prevState ω).yCurr i) ∧
    S.currentBlockPartialExpectationEq t i
      (fun ω => S.positiveEtaStochasticBlockIterate B hB G hη t ω i)
      (fun ω => S.auxiliaryPoint t (xNext ω) ((prevState ω).blockX i))
      (fun ω => (prevState ω).blockX i)
      (fun ω =>
        (Fintype.card ι : ℝ)⁻¹ •
            S.auxiliaryPoint t (xNext ω) ((prevState ω).blockX i) +
          (1 - (Fintype.card ι : ℝ)⁻¹) • (prevState ω).blockX i) ∧
    S.currentBlockPartialExpectationEq t i
      (fun ω => S.f i (S.positiveEtaStochasticBlockIterate B hB G hη t ω i))
      (fun ω => S.f i (S.auxiliaryPoint t (xNext ω) ((prevState ω).blockX i)))
      (fun ω => S.f i ((prevState ω).blockX i))
      (fun ω =>
        (Fintype.card ι : ℝ)⁻¹ *
            S.f i (S.auxiliaryPoint t (xNext ω) ((prevState ω).blockX i)) +
          (1 - (Fintype.card ι : ℝ)⁻¹) * S.f i ((prevState ω).blockX i)) ∧
    S.currentBlockPartialExpectationEq t i
      (fun ω =>
        S.dualNorm
          (S.gradF i (S.positiveEtaStochasticBlockIterate B hB G hη t ω i) -
            S.gradF i ((prevState ω).blockX i)) ^ 2)
      (fun ω =>
        S.dualNorm
          (S.gradF i (S.auxiliaryPoint t (xNext ω) ((prevState ω).blockX i)) -
            S.gradF i ((prevState ω).blockX i)) ^ 2)
      (fun _ω => 0)
      (fun ω =>
        (Fintype.card ι : ℝ)⁻¹ *
          S.dualNorm
            (S.gradF i (S.auxiliaryPoint t (xNext ω) ((prevState ω).blockX i)) -
              S.gradF i ((prevState ω).blockX i)) ^ 2)

/-- Lemma 5.11 branch identities for the generated stochastic process.

This is the stochastic analogue of `positiveEtaGeneratedProcess_branch_identities`.
It uses the canonical process equations from Algorithm 5.5, so the branch payloads
are the actual `x^t`, `x_i^{t-1}`, and current stochastic batch objects that
Lemma 5.11 conditions on, not values from an arbitrary process relation. -/
private theorem positiveEtaGeneratedStochasticProcess_branch_identities {Ξ : Type*}
    (B : ℕ → ℕ) (hB : S.StochasticBatchDomain B) (G : ι → E → Ξ → E)
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 1 ≤ t) (i : ι) :
    (∀ ω : StochasticRunPath ι Ξ,
      S.positiveEtaStochasticYIterate B hB G hη t ω i =
        (if S.stochasticBlockSample t ω = i then
          S.stochasticAuxiliaryGradient B hB G
            (fun i n j => S.stochasticOracleSample i n j ω) t ht
            (S.positiveEtaStochasticXIterate B hB G hη t ω)
            (S.positiveEtaGeneratedStochasticProcess B hB G hη (t - 1) ω).blockX i
        else
          (S.positiveEtaGeneratedStochasticProcess B hB G hη (t - 1) ω).yCurr i)) ∧
    (∀ ω : StochasticRunPath ι Ξ,
      S.positiveEtaStochasticBlockIterate B hB G hη t ω i =
        (if S.stochasticBlockSample t ω = i then
          S.auxiliaryPoint t (S.positiveEtaStochasticXIterate B hB G hη t ω)
            ((S.positiveEtaGeneratedStochasticProcess B hB G hη (t - 1) ω).blockX i)
        else
          (S.positiveEtaGeneratedStochasticProcess B hB G hη (t - 1) ω).blockX i)) ∧
    (∀ ω : StochasticRunPath ι Ξ,
      S.f i (S.positiveEtaStochasticBlockIterate B hB G hη t ω i) =
        (if S.stochasticBlockSample t ω = i then
          S.f i (S.auxiliaryPoint t (S.positiveEtaStochasticXIterate B hB G hη t ω)
            ((S.positiveEtaGeneratedStochasticProcess B hB G hη (t - 1) ω).blockX i))
        else
          S.f i ((S.positiveEtaGeneratedStochasticProcess B hB G hη (t - 1) ω).blockX i))) ∧
    (∀ ω : StochasticRunPath ι Ξ,
      S.dualNorm
        (S.gradF i (S.positiveEtaStochasticBlockIterate B hB G hη t ω i) -
          S.gradF i ((S.positiveEtaGeneratedStochasticProcess B hB G hη (t - 1) ω).blockX i)) ^ 2 =
        (if S.stochasticBlockSample t ω = i then
          S.dualNorm
            (S.gradF i (S.auxiliaryPoint t (S.positiveEtaStochasticXIterate B hB G hη t ω)
              ((S.positiveEtaGeneratedStochasticProcess B hB G hη (t - 1) ω).blockX i)) -
              S.gradF i ((S.positiveEtaGeneratedStochasticProcess B hB G hη (t - 1) ω).blockX i)) ^ 2
        else 0)) := by
  classical
  have hy_branch : ∀ ω : StochasticRunPath ι Ξ,
      S.positiveEtaStochasticYIterate B hB G hη t ω i =
        (if S.stochasticBlockSample t ω = i then
          S.stochasticAuxiliaryGradient B hB G
            (fun i n j => S.stochasticOracleSample i n j ω) t ht
            (S.positiveEtaStochasticXIterate B hB G hη t ω)
            (S.positiveEtaGeneratedStochasticProcess B hB G hη (t - 1) ω).blockX i
        else
          (S.positiveEtaGeneratedStochasticProcess B hB G hη (t - 1) ω).yCurr i) := by
    intro ω
    have hstep := S.positiveEtaGeneratedStochasticProcess_succ_equations B hB G hη ht ω
    rcases hstep with ⟨_hxmem, _hmin, hblock, _hyprev, hycurr⟩
    dsimp [positiveEtaStochasticYIterate, positiveEtaStochasticXIterate] at *
    have hyi := congrFun hycurr i
    rw [hyi]
    by_cases hsel : S.stochasticBlockSample t ω = i
    · subst hsel
      have hblocki := congrFun hblock (S.stochasticBlockSample t ω)
      simp [stochasticComponentGradientUpdate]
      rw [hblocki]
      simp [blockPointUpdate, stochasticAuxiliaryGradient]
    · have hnot : i ≠ S.stochasticBlockSample t ω := fun hi => hsel hi.symm
      simp [hsel, hnot, stochasticComponentGradientUpdate]
  have hx_branch : ∀ ω : StochasticRunPath ι Ξ,
      S.positiveEtaStochasticBlockIterate B hB G hη t ω i =
        (if S.stochasticBlockSample t ω = i then
          S.auxiliaryPoint t (S.positiveEtaStochasticXIterate B hB G hη t ω)
            ((S.positiveEtaGeneratedStochasticProcess B hB G hη (t - 1) ω).blockX i)
        else
          (S.positiveEtaGeneratedStochasticProcess B hB G hη (t - 1) ω).blockX i) := by
    intro ω
    have hstep := S.positiveEtaGeneratedStochasticProcess_succ_equations B hB G hη ht ω
    rcases hstep with ⟨_hxmem, _hmin, hblock, _hyprev, _hycurr⟩
    dsimp [positiveEtaStochasticBlockIterate, positiveEtaStochasticXIterate] at *
    have hxi := congrFun hblock i
    rw [hxi]
    by_cases hsel : S.stochasticBlockSample t ω = i
    · subst hsel
      simp [blockPointUpdate]
    · have hnot : i ≠ S.stochasticBlockSample t ω := fun hi => hsel hi.symm
      simp [hsel, hnot, blockPointUpdate]
  have hf_branch : ∀ ω : StochasticRunPath ι Ξ,
      S.f i (S.positiveEtaStochasticBlockIterate B hB G hη t ω i) =
        (if S.stochasticBlockSample t ω = i then
          S.f i (S.auxiliaryPoint t (S.positiveEtaStochasticXIterate B hB G hη t ω)
            ((S.positiveEtaGeneratedStochasticProcess B hB G hη (t - 1) ω).blockX i))
        else
          S.f i ((S.positiveEtaGeneratedStochasticProcess B hB G hη (t - 1) ω).blockX i)) := by
    intro ω
    rw [hx_branch ω]
    by_cases hsel : S.stochasticBlockSample t ω = i <;> simp [hsel]
  have hnorm_branch : ∀ ω : StochasticRunPath ι Ξ,
      S.dualNorm
        (S.gradF i (S.positiveEtaStochasticBlockIterate B hB G hη t ω i) -
          S.gradF i ((S.positiveEtaGeneratedStochasticProcess B hB G hη (t - 1) ω).blockX i)) ^ 2 =
        (if S.stochasticBlockSample t ω = i then
          S.dualNorm
            (S.gradF i (S.auxiliaryPoint t (S.positiveEtaStochasticXIterate B hB G hη t ω)
              ((S.positiveEtaGeneratedStochasticProcess B hB G hη (t - 1) ω).blockX i)) -
              S.gradF i ((S.positiveEtaGeneratedStochasticProcess B hB G hη (t - 1) ω).blockX i)) ^ 2
        else 0) := by
    intro ω
    rw [hx_branch ω]
    by_cases hsel : S.stochasticBlockSample t ω = i
    · simp [hsel]
    · simp only [hsel, if_false]
      rw [sub_self, S.dualNorm_zero]
      norm_num
  exact ⟨hy_branch, hx_branch, hf_branch, hnorm_branch⟩

/-- Generated-process Lemma 5.11 route with the paper current-block expectation.

The proof follows the source proof of Lemma 5.11 directly: expand the generated
updates into selected/nonselected branches and then use the finite-uniform
current-block expectation formula. The retired full-oracle-history Mathlib
`condExp` route is intentionally not part of this source-facing cone. -/
theorem conditionalBlockExpectation_Lemma_5_11_generated {Ξ : Type*}
    [MeasurableSpace Ξ]
    (Pξ : Measure (StochasticSampleTable ι Ξ))
    (B : ℕ → ℕ) (hB : S.StochasticBatchDomain B) (G : ι → E → Ξ → E)
    (hη : S.PositiveEtaDomain)
    {t : ℕ} (ht : 1 ≤ t) (i : ι) :
    S.ConditionalBlockExpectation511Formula Pξ B hB G hη t ht i := by
  classical
  rcases S.positiveEtaGeneratedStochasticProcess_branch_identities B hB G hη ht i with
    ⟨hy_branch, hx_branch, hf_branch, hnorm_branch⟩
  unfold ConditionalBlockExpectation511Formula currentBlockPartialExpectationEq
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro ω
      simpa using hy_branch ω
    · exact (S.currentBlockTwoBranchExpectation_eq_weighted i
        (fun ω =>
          S.stochasticAuxiliaryGradient B hB G
            (fun i n j => S.stochasticOracleSample i n j ω) t ht
            (S.positiveEtaStochasticXIterate B hB G hη t ω)
            (S.positiveEtaGeneratedStochasticProcess B hB G hη (t - 1) ω).blockX i)
        (fun ω =>
          (S.positiveEtaGeneratedStochasticProcess B hB G hη (t - 1) ω).yCurr i)).symm
  · refine ⟨?_, ?_⟩
    · intro ω
      simpa using hx_branch ω
    · exact (S.currentBlockTwoBranchExpectation_eq_weighted i
        (fun ω =>
          S.auxiliaryPoint t (S.positiveEtaStochasticXIterate B hB G hη t ω)
            ((S.positiveEtaGeneratedStochasticProcess B hB G hη (t - 1) ω).blockX i))
        (fun ω =>
          (S.positiveEtaGeneratedStochasticProcess B hB G hη (t - 1) ω).blockX i)).symm
  · refine ⟨?_, ?_⟩
    · intro ω
      simpa using hf_branch ω
    · have hweighted := S.currentBlockTwoBranchExpectation_eq_weighted i
        (fun ω =>
          S.f i (S.auxiliaryPoint t (S.positiveEtaStochasticXIterate B hB G hη t ω)
            ((S.positiveEtaGeneratedStochasticProcess B hB G hη (t - 1) ω).blockX i)))
        (fun ω =>
          S.f i ((S.positiveEtaGeneratedStochasticProcess B hB G hη (t - 1) ω).blockX i))
      simpa [smul_eq_mul] using hweighted.symm
  · refine ⟨?_, ?_⟩
    · intro ω
      simpa using hnorm_branch ω
    · have hweighted := S.currentBlockTwoBranchExpectation_eq_weighted i
        (fun ω =>
          S.dualNorm
            (S.gradF i (S.auxiliaryPoint t (S.positiveEtaStochasticXIterate B hB G hη t ω)
              ((S.positiveEtaGeneratedStochasticProcess B hB G hη (t - 1) ω).blockX i)) -
              S.gradF i ((S.positiveEtaGeneratedStochasticProcess B hB G hη (t - 1) ω).blockX i)) ^ 2)
        (fun _ω : StochasticRunPath ι Ξ => 0)
      simpa [smul_eq_mul] using hweighted.symm

/-- Formula of Lemma 5.11 for the corrected positive-eta stochastic process. -/
def ConditionalBlockExpectation511Formula_positive_domain {Ξ : Type*} [MeasurableSpace Ξ]
    (Pξ : Measure (StochasticSampleTable ι Ξ))
    (B : ℕ → ℕ) (hB : S.StochasticBatchDomain B) (G : ι → E → Ξ → E)
    (hη : S.PositiveEtaDomain) (t : ℕ) (ht : 1 ≤ t) (i : ι) : Prop :=
  S.ConditionalBlockExpectation511Formula Pξ B hB G hη t ht i

/-- Corrected-domain generated-process specialization of Lemma 5.11. -/
theorem ConditionalBlockExpectation_Lemma_5_11_positive_domain {Ξ : Type*}
    [MeasurableSpace Ξ]
    (Pξ : Measure (StochasticSampleTable ι Ξ))
    (B : ℕ → ℕ) (hB : S.StochasticBatchDomain B) (G : ι → E → Ξ → E)
    (hη : S.PositiveEtaDomain)
    {t : ℕ} (ht : 1 ≤ t) (i : ι) :
    S.ConditionalBlockExpectation511Formula_positive_domain Pξ B hB G hη t ht i := by
  simpa [ConditionalBlockExpectation511Formula_positive_domain] using
    S.conditionalBlockExpectation_Lemma_5_11_generated Pξ B hB G hη ht i

/-- Lemma 5.9 block-iterate identity transported to an unconditional expectation.

Aligns with Lemma 5.10 proof step 2: the deterministic `E_t` identity from
Lemma 5.9 is integrated over the sampled block history. Candidate audit:
`ConditionalBlockExpectation_Lemma_5_9_positive_domain` gives the wrapped
conditional identity, and `conditionalExpectationEq_expectation_eq` is the
local bridge from that wrapper to `SOptLib.expectation`; no SOptLib theorem
already combines this paper-specific generated-process projection. -/
private theorem lemma59_block_iterate_expectation_relation
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 1 ≤ t) (i : ι) :
    SOptLib.expectation S.P (fun ω => S.positiveEtaBlockIterate hη t ω i) =
      SOptLib.expectation S.P
        (fun ω =>
          (Fintype.card ι : ℝ)⁻¹ •
              S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
                ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i) +
            (1 - (Fintype.card ι : ℝ)⁻¹) •
              (S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i) := by
  rcases S.ConditionalBlockExpectation_Lemma_5_9_positive_domain hη ht i with
    ⟨_hy, hx, _hf, _hnorm⟩
  exact conditionalExpectationEq_expectation_eq hx

/-- Lemma 5.9 component-value identity transported to an unconditional expectation.

Aligns with Lemma 5.10 proof step 2 for the component objective terms. This
projects the proved deterministic generated-process Lemma 5.9 identity and uses
the same `conditionalExpectationEq_expectation_eq` bridge; existing SOptLib
expectation equalities are paper-neutral and do not expose this generated RGEM
component formula. -/
private theorem lemma59_component_value_expectation_relation
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 1 ≤ t) (i : ι) :
    SOptLib.expectation S.P
        (fun ω => S.f i (S.positiveEtaBlockIterate hη t ω i)) =
      SOptLib.expectation S.P
        (fun ω =>
          (Fintype.card ι : ℝ)⁻¹ *
              S.f i (S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
                ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) +
            (1 - (Fintype.card ι : ℝ)⁻¹) *
              S.f i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) := by
  rcases S.ConditionalBlockExpectation_Lemma_5_9_positive_domain hη ht i with
    ⟨_hy, _hx, hf, _hnorm⟩
  exact conditionalExpectationEq_expectation_eq hf

/-- Lemma 5.9 component-value identity solved for the auxiliary value.

Aligns with Lan Proposition 5.6 proof step 6: after taking expectation, the
auxiliary component value in Eq. (5.2.72) is replaced by the sampled block value
and the previous block value. Candidate audit: checked
`lemma59_component_value_expectation_relation`,
`ConditionalBlockExpectation_Lemma_5_9_positive_domain`, and SOptLib
finite-sum expectation linearity; the existing local Lemma 5.9 projection gives
the exact RGEM formula, while no SOptLib theorem solves this paper-specific
`m⁻¹/(1-m⁻¹)` block mixture. -/
private theorem lemma59_component_value_auxiliary_expectation_relation
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 1 ≤ t) (i : ι) :
    SOptLib.expectation S.P
        (fun ω =>
          S.f i (S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
            ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i))) =
      (Fintype.card ι : ℝ) *
          SOptLib.expectation S.P
            (fun ω => S.f i (S.positiveEtaBlockIterate hη t ω i)) -
        ((Fintype.card ι : ℝ) - 1) *
          SOptLib.expectation S.P
            (fun ω => S.f i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) := by
  simpa [SOptLib.expectation_def, smul_eq_mul] using
    (expectation_eq_mul_sub_of_expectation_eq_inv_mul_add
      (μ := S.P)
      (A := fun ω =>
        S.f i (S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
          ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)))
      (B := fun ω =>
        S.f i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i))
      (C := fun ω => S.f i (S.positiveEtaBlockIterate hη t ω i))
      (m := (Fintype.card ι : ℝ))
      (by exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0))
      (S.positiveEta_strictPast_payload_integrable hη ht
        (fun xNext prev => S.f i (S.auxiliaryPoint t xNext (prev.blockX i))))
      (S.positiveEta_strictPast_payload_integrable hη ht
        (fun _xNext prev => S.f i (prev.blockX i)))
      (by
        simpa [SOptLib.expectation_def, smul_eq_mul] using
          (S.lemma59_component_value_expectation_relation hη ht i)))

/-- Lemma 5.9 squared-gradient-gap identity solved for the auxiliary gap.

Aligns with Lan Proposition 5.6 proof step 6: the auxiliary smoothness penalty
from Eq. (5.2.72) is converted to the sampled block-gradient gap. Candidate
audit: checked `ConditionalBlockExpectation_Lemma_5_9_positive_domain`,
`lemma59_component_value_expectation_relation`, and SOptLib expectation
linearity helpers; no existing theorem exposed this norm-square projection for
the generated RGEM process. -/
private theorem lemma59_auxiliary_gradient_gap_expectation_relation
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 1 ≤ t) (i : ι) :
    SOptLib.expectation S.P
        (fun ω =>
          S.dualNorm
            (S.gradF i
                (S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
                  ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) -
              S.gradF i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) ^ 2) =
      (Fintype.card ι : ℝ) *
        SOptLib.expectation S.P
          (fun ω =>
            S.dualNorm
              (S.gradF i (S.positiveEtaBlockIterate hη t ω i) -
                S.gradF i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) ^ 2) := by
  classical
  let m : ℝ := (Fintype.card ι : ℝ)
  let A : BlockSamplePath ι → ℝ := fun ω =>
    S.dualNorm
      (S.gradF i
          (S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
            ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) -
        S.gradF i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) ^ 2
  let C : BlockSamplePath ι → ℝ := fun ω =>
    S.dualNorm
      (S.gradF i (S.positiveEtaBlockIterate hη t ω i) -
        S.gradF i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) ^ 2
  have hm_ne : m ≠ 0 := by
    dsimp [m]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
  have hbase :
      SOptLib.expectation S.P C =
        SOptLib.expectation S.P (fun ω => m⁻¹ * A ω) := by
    rcases S.ConditionalBlockExpectation_Lemma_5_9_positive_domain hη ht i with
      ⟨_hy, _hx, _hf, hnorm⟩
    simpa [A, C, m] using conditionalExpectationEq_expectation_eq hnorm
  simpa [A, C, m, SOptLib.expectation_def] using
    (expectation_eq_mul_of_expectation_eq_inv_mul S.P A C hm_ne
      (by simpa [SOptLib.expectation_def] using hbase))

/-- Expected auxiliary smoothness gap from Eq. (5.2.72).

Aligns with Lan Proposition 5.6 proof steps 4--6 before the Lemma 5.9 block
substitution: integrate the generated auxiliary smoothness gap componentwise.
Candidate audit: checked
`proposition56_auxiliary_smoothness_gap_5_2_72_positive_domain`,
`expectation_le_sum_expectation_of_ae_le_finset_sum`, and
`integral_finset_sum_residual_lift_le`; the SOptLib candidates aggregate finite
sums, while this route-local helper is the single-component expectation lift
needed before the paper's block-mixture identities are applied. -/
private theorem proposition56_auxiliary_smoothness_gap_expectation_5_2_72_positive_domain
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 1 ≤ t) (i : ι) :
    (1 / (2 * S.Lcomp i)) *
        SOptLib.expectation S.P
          (fun ω =>
            S.dualNorm
              (S.gradF i
                  (S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
                    ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) -
                S.gradF i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) ^ 2) ≤
      SOptLib.expectation S.P
          (fun ω =>
            S.f i (S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
              ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i))) -
        SOptLib.expectation S.P
          (fun ω => S.f i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) -
        SOptLib.expectation S.P
          (fun ω =>
            ⟪S.gradF i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i),
              S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
                  ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i) -
                (S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i⟫_ℝ) := by
  exact
    expectation_const_smul_le_sub_sub_of_ae_le
      (P := S.P)
      (A := fun ω : BlockSamplePath ι =>
        S.dualNorm
          (S.gradF i
              (S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
                ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) -
            S.gradF i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) ^ 2)
      (F := fun ω : BlockSamplePath ι =>
        S.f i (S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
          ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)))
      (G := fun ω : BlockSamplePath ι =>
        S.f i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i))
      (H := fun ω : BlockSamplePath ι =>
        ⟪S.gradF i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i),
          S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
              ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i) -
            (S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i⟫_ℝ)
      (c := 1 / (2 * S.Lcomp i))
      (S.positiveEta_strictPast_payload_integrable hη ht
        (fun xNext prev =>
          S.dualNorm
            (S.gradF i (S.auxiliaryPoint t xNext (prev.blockX i)) -
              S.gradF i (prev.blockX i)) ^ 2))
      (S.positiveEta_strictPast_payload_integrable hη ht
        (fun xNext prev => S.f i (S.auxiliaryPoint t xNext (prev.blockX i))))
      (S.positiveEta_strictPast_payload_integrable hη ht
        (fun _xNext prev => S.f i (prev.blockX i)))
      (S.positiveEta_strictPast_payload_integrable hη ht
        (fun xNext prev =>
          ⟪S.gradF i (prev.blockX i),
            S.auxiliaryPoint t xNext (prev.blockX i) - prev.blockX i⟫_ℝ))
      (by
        filter_upwards with ω
        simpa using
          S.proposition56_auxiliary_smoothness_gap_5_2_72_positive_domain
            hη (t := t) ω i)

/-- Expected smoothness gap after the Lemma 5.9 sampled-block substitution.

Aligns with Lan Proposition 5.6 proof step 6, where auxiliary function and
gradient-gap expectations are rewritten in terms of the actual sampled block
table and the previous block table. Candidate audit: considered the local
`proposition56_auxiliary_smoothness_gap_expectation_5_2_72_positive_domain`,
`lemma59_component_value_auxiliary_expectation_relation`, and
`lemma59_auxiliary_gradient_gap_expectation_relation`; no target-file or SOptLib
candidate already stated this RGEM-specific substituted component inequality. -/
private theorem proposition56_sampled_smoothness_gap_expectation_5_2_73_positive_domain
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 1 ≤ t) (i : ι) :
    (1 / (2 * S.Lcomp i)) *
        ((Fintype.card ι : ℝ) *
          SOptLib.expectation S.P
            (fun ω =>
              S.dualNorm
                (S.gradF i (S.positiveEtaBlockIterate hη t ω i) -
                  S.gradF i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) ^ 2)) ≤
      ((Fintype.card ι : ℝ) *
          SOptLib.expectation S.P
            (fun ω => S.f i (S.positiveEtaBlockIterate hη t ω i)) -
        ((Fintype.card ι : ℝ) - 1) *
          SOptLib.expectation S.P
            (fun ω => S.f i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i))) -
        SOptLib.expectation S.P
          (fun ω => S.f i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) -
        SOptLib.expectation S.P
          (fun ω =>
            ⟪S.gradF i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i),
              S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
                  ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i) -
                (S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i⟫_ℝ) := by
  classical
  have haux :=
    S.proposition56_auxiliary_smoothness_gap_expectation_5_2_72_positive_domain
      hη (t := t) ht i
  have hnorm :=
    S.lemma59_auxiliary_gradient_gap_expectation_relation hη (t := t) ht i
  have hf :=
    S.lemma59_component_value_auxiliary_expectation_relation hη (t := t) ht i
  rw [hnorm, hf] at haux
  simpa using haux

/-- Expected generated prox inequality (5.2.71).

Aligns with Lan Proposition 5.6 proof steps 1 and 6: the pointwise prox
inequality is lifted to an unconditional expectation before being combined with
the expected smoothness gap. Candidate audit: checked
`proposition56_generated_prox_step_inequality_5_2_71_positive_domain`,
`proposition56_one_step_source_ingredients_5_2_73_positive_domain`, and SOptLib
finite-window expectation-lift helpers; no existing theorem stated this
single-step generated RGEM expectation inequality. -/
private theorem proposition56_prox_step_expectation_5_2_71_positive_domain
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 1 ≤ t) {x : E} (hx : x ∈ S.X) :
    SOptLib.expectation S.P
        (fun ω =>
          let prev : State ι E := S.positiveEtaGeneratedProcess hη (t - 1) ω
          let yTilde : ι → E := fun i => SOptLib.extrapolatedPoint (S.α t) ((prev).yCurr i) ((prev).yPrev i)
          let xNext : E := S.positiveEtaXIterate hη t ω
          ⟪xNext - x, tableAverage yTilde⟫_ℝ +
            S.μ * S.ν xNext - S.μ * S.ν x) ≤
      SOptLib.expectation S.P
        (fun ω =>
          let prev : State ι E := S.positiveEtaGeneratedProcess hη (t - 1) ω
          let xNext : E := S.positiveEtaXIterate hη t ω
          S.η t * S.V prev.x x - (S.μ + S.η t) * S.V xNext x -
            S.η t * S.V prev.x xNext) := by
  classical
  let L : BlockSamplePath ι → ℝ := fun ω =>
    let prev : State ι E := S.positiveEtaGeneratedProcess hη (t - 1) ω
    let yTilde : ι → E := fun i => SOptLib.extrapolatedPoint (S.α t) ((prev).yCurr i) ((prev).yPrev i)
    let xNext : E := S.positiveEtaXIterate hη t ω
    ⟪xNext - x, tableAverage yTilde⟫_ℝ + S.μ * S.ν xNext - S.μ * S.ν x
  let R : BlockSamplePath ι → ℝ := fun ω =>
    let prev : State ι E := S.positiveEtaGeneratedProcess hη (t - 1) ω
    let xNext : E := S.positiveEtaXIterate hη t ω
    S.η t * S.V prev.x x - (S.μ + S.η t) * S.V xNext x -
      S.η t * S.V prev.x xNext
  have hL_int : Integrable L S.P :=
    S.positiveEta_strictPast_payload_integrable hη ht
      (fun xNext prev =>
        let yTilde : ι → E := fun i => SOptLib.extrapolatedPoint (S.α t) ((prev).yCurr i) ((prev).yPrev i)
        ⟪xNext - x, tableAverage yTilde⟫_ℝ + S.μ * S.ν xNext - S.μ * S.ν x)
  have hR_int : Integrable R S.P :=
    S.positiveEta_strictPast_payload_integrable hη ht
      (fun xNext prev =>
        S.η t * S.V prev.x x - (S.μ + S.η t) * S.V xNext x -
          S.η t * S.V prev.x xNext)
  have hpoint : ∀ᵐ ω ∂S.P, L ω ≤ R ω := by
    filter_upwards with ω
    simpa [L, R] using
      S.proposition56_generated_prox_step_inequality_5_2_71_positive_domain
        hη (t := t) ht ω hx
  have hmono : (∫ ω, L ω ∂S.P) ≤ ∫ ω, R ω ∂S.P :=
    integral_mono_ae hL_int hR_int hpoint
  unfold SOptLib.expectation
  simpa [L, R] using hmono

/-- Lemma 5.9 scalar inner-product identity integrated over the sampled history.

This is the fixed-direction form needed by Lemma 5.10 proof step 2 after the
Q expansion. It consumes the same fresh-block route as Lemma 5.9, but states the
result for the scalar component `⟪x_i^t - x, ∇f_i(x)⟫`, avoiding a broader
conditional-expectation linear-map API. -/
private theorem lemma59_block_inner_expectation_relation
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 1 ≤ t) (i : ι) (x : E) :
    SOptLib.expectation S.P
        (fun ω =>
          ⟪S.positiveEtaBlockIterate hη t ω i - x, S.gradF i x⟫_ℝ) =
      SOptLib.expectation S.P
        (fun ω =>
          (Fintype.card ι : ℝ)⁻¹ *
              ⟪S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
                  ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i) - x,
                S.gradF i x⟫_ℝ +
            (1 - (Fintype.card ι : ℝ)⁻¹) *
              ⟪(S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i - x,
                S.gradF i x⟫_ℝ) := by
  let A : BlockSamplePath ι → ℝ := fun ω =>
    ⟪S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
        ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i) - x,
      S.gradF i x⟫_ℝ
  let B : BlockSamplePath ι → ℝ := fun ω =>
    ⟪(S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i - x, S.gradF i x⟫_ℝ
  have hA_int : Integrable A S.P :=
    S.positiveEta_strictPast_payload_integrable hη ht
      (fun xNext prev =>
        ⟪S.auxiliaryPoint t xNext (prev.blockX i) - x, S.gradF i x⟫_ℝ)
  have hB_int : Integrable B S.P :=
    S.positiveEta_strictPast_payload_integrable hη ht
      (fun _xNext prev => ⟪prev.blockX i - x, S.gradF i x⟫_ℝ)
  have hA_past :
      ∀ ⦃ω ω' : BlockSamplePath ι⦄,
        (fun r : Fin (t - 1) => S.sample (1 + r.1) ω) =
          (fun r : Fin (t - 1) => S.sample (1 + r.1) ω') →
        A ω = A ω' := by
    intro ω ω' hwin
    have hxNext := S.positiveEtaXIterate_eq_of_strictPastWindow_eq hη ht hwin
    have hprev := S.positiveEtaGeneratedProcess_eq_of_sampleWindow_eq hη (t - 1) hwin
    simp [A, hxNext, hprev]
  have hB_past :
      ∀ ⦃ω ω' : BlockSamplePath ι⦄,
        (fun r : Fin (t - 1) => S.sample (1 + r.1) ω) =
          (fun r : Fin (t - 1) => S.sample (1 + r.1) ω') →
        B ω = B ω' := by
    intro ω ω' hwin
    have hprev := S.positiveEtaGeneratedProcess_eq_of_sampleWindow_eq hη (t - 1) hwin
    simp [B, hprev]
  rcases S.positiveEtaGeneratedProcess_branch_identities hη ht i with
    ⟨_hy_branch, hx_branch, _hf_branch, _hnorm_branch⟩
  have hmain :
      (fun ω =>
        ⟪S.positiveEtaBlockIterate hη t ω i - x, S.gradF i x⟫_ℝ) =
        fun ω => if S.sample t ω = i then A ω else B ω := by
    funext ω
    rw [hx_branch ω]
    by_cases hsample : S.sample t ω = i <;> simp [A, B, hsample]
  have hce := S.conditionalExpectationEq_two_branch_of_fresh_uniform
    (t := t) ht i A B hA_int hB_int hA_past hB_past
  have hce' :
      conditionalExpectationEq S.P (S.paperStrictPastSigma t)
        (fun ω =>
          ⟪S.positiveEtaBlockIterate hη t ω i - x, S.gradF i x⟫_ℝ)
        (fun ω =>
          (Fintype.card ι : ℝ)⁻¹ *
              ⟪S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
                  ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i) - x,
                S.gradF i x⟫_ℝ +
            (1 - (Fintype.card ι : ℝ)⁻¹) *
              ⟪(S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i - x,
                S.gradF i x⟫_ℝ) := by
    simpa [hmain, A, B, smul_eq_mul] using hce
  exact conditionalExpectationEq_expectation_eq hce'

/-- Pathwise Q expansion through the auxiliary block points.

Aligns with Lemma 5.10 proof step 1. The SOptLib/target candidates considered
were `QDefinition_Eq_5_2_59`, `AuxiliaryPointIdentity_Eq_5_2_57`, and finite
inner-product sum lemmas such as `sum_inner`; none packages this paper-specific
combination of the RGEM Q definition with the solved auxiliary-point identity. -/
private theorem q_pathwise_auxiliary_decomposition
    (hη : S.PositiveEtaDomain) (t : ℕ) (x : E) (ω : BlockSamplePath ι) :
    S.Q (S.positiveEtaXIterate hη t ω) x =
      (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ
            (fun i =>
              (1 + S.τ t) *
                  ⟪S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
                      ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i) - x,
                    S.gradF i x⟫_ℝ -
                S.τ t *
                  ⟪(S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i - x,
                    S.gradF i x⟫_ℝ) +
        (S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.μ * S.ν x) := by
  classical
  let extra : ℝ := S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.μ * S.ν x
  have hinner :
      ⟪(Fintype.card ι : ℝ)⁻¹ •
          Finset.sum Finset.univ (fun i : ι => S.gradF i x),
        S.positiveEtaXIterate hη t ω - x⟫_ℝ =
        (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ
            (fun i =>
              (1 + S.τ t) *
                  ⟪S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
                      ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i) - x,
                    S.gradF i x⟫_ℝ +
                (-S.τ t) *
                  ⟪(S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i - x,
                    S.gradF i x⟫_ℝ) :=
    SOptLib.inner_smul_sum_affine_combination_sub_eq
      (ι := ι) (E := E)
      (s := Finset.univ)
      (g := fun i : ι => S.gradF i x)
      (a := fun i : ι =>
        S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
          ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i))
      (b := fun i : ι => (S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)
      (xNext := S.positiveEtaXIterate hη t ω)
      (x := x)
      (scale := (Fintype.card ι : ℝ)⁻¹)
      (ca := 1 + S.τ t)
      (cb := -S.τ t)
      (hcoeff := by ring)
      (haffine := fun i : ι => by
        intro _hi
        simpa [sub_eq_add_neg] using
          S.auxiliaryPoint_solve t (S.positiveEtaXIterate hη t ω)
            ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i))
  have hwithExtra :
      ⟪(Fintype.card ι : ℝ)⁻¹ •
          Finset.sum Finset.univ (fun i : ι => S.gradF i x),
        S.positiveEtaXIterate hη t ω - x⟫_ℝ + extra =
        (Fintype.card ι : ℝ)⁻¹ *
            Finset.sum Finset.univ
              (fun i =>
                (1 + S.τ t) *
                    ⟪S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
                        ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i) - x,
                      S.gradF i x⟫_ℝ +
                  (-S.τ t) *
                    ⟪(S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i - x,
                      S.gradF i x⟫_ℝ) +
          extra := by
    exact congrArg (fun r : ℝ => r + extra) hinner
  simpa [Q, SOptLib.finiteAverageGradientRegularizerGap, extra, sub_eq_add_neg,
    add_assoc] using hwithExtra

/-- One-step expected Q decomposition before applying the Lemma 5.9 block average.

This is the expectation-level form of Lemma 5.10 proof step 1. It is intentionally
narrower than the full weighted telescope: `q_pathwise_auxiliary_decomposition`
supplies the pointwise Eq. (5.2.57)/Q algebra, and the remaining source step is
to combine this with the Lemma 5.9 scalar block identity above. -/
private theorem weighted_q_one_step_expectation_relation
    (hη : S.PositiveEtaDomain) (t : ℕ) (x : E) :
    SOptLib.expectation S.P
        (fun ω => S.Q (S.positiveEtaXIterate hη t ω) x) =
      SOptLib.expectation S.P
        (fun ω =>
          (Fintype.card ι : ℝ)⁻¹ *
              Finset.sum Finset.univ
                (fun i =>
                  (1 + S.τ t) *
                      ⟪S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
                          ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i) - x,
                        S.gradF i x⟫_ℝ -
                    S.τ t *
                      ⟪(S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i - x,
                        S.gradF i x⟫_ℝ) +
            (S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.μ * S.ν x)) := by
  unfold SOptLib.expectation
  apply integral_congr_ae
  filter_upwards with ω
  exact S.q_pathwise_auxiliary_decomposition hη t x ω

/-- Lemma 5.10 proof step 2, converting the auxiliary-point expectation to block terms.

Aligns with Lan Lemma 5.10 proof lines applying Lemma 5.9 after the Q expansion.
Candidate audit: `expectation_finset_sum_const_smul_comp_eq_of_finite_range_key`
was checked but requires a finite-key reconstruction formulation; the local
`lemma59_block_inner_expectation_relation` is the paper-specific generated
process identity, and raw `integral_finset_sum`, `integral_const_mul`,
`integral_add`, and `integral_sub` give the needed expectation linearity. -/
private theorem weighted_q_auxiliary_expectation_to_block_inner
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 1 ≤ t) (x : E) :
    SOptLib.expectation S.P
        (fun ω =>
          (Fintype.card ι : ℝ)⁻¹ *
              Finset.sum Finset.univ
                (fun i =>
                  (1 + S.τ t) *
                      ⟪S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
                          ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i) - x,
                        S.gradF i x⟫_ℝ -
                    S.τ t *
                      ⟪(S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i - x,
                        S.gradF i x⟫_ℝ) +
            (S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.μ * S.ν x)) =
      Finset.sum Finset.univ
        (fun i =>
          (1 + S.τ t) *
              SOptLib.expectation S.P
                (fun ω =>
                  ⟪S.positiveEtaBlockIterate hη t ω i - x, S.gradF i x⟫_ℝ) -
            ((1 + S.τ t) - (Fintype.card ι : ℝ)⁻¹) *
              SOptLib.expectation S.P
                (fun ω =>
                  ⟪(S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i - x,
                    S.gradF i x⟫_ℝ)) +
        SOptLib.expectation S.P
          (fun ω => S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.μ * S.ν x) := by
  classical
  exact
    by
      simpa [SOptLib.expectation, smul_eq_mul] using
        (integral_finset_affine_regroup_of_integral_eq
          (μ := S.P)
          (s := Finset.univ)
          (A := fun i ω =>
            ⟪S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
                ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i) - x,
              S.gradF i x⟫_ℝ)
          (B := fun i ω =>
            ⟪(S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i - x,
              S.gradF i x⟫_ℝ)
          (C := fun i ω =>
            ⟪S.positiveEtaBlockIterate hη t ω i - x, S.gradF i x⟫_ℝ)
          (N := fun ω => S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.μ * S.ν x)
          (c := (Fintype.card ι : ℝ)⁻¹)
          (tau := S.τ t)
          (fun i _hi =>
            S.positiveEta_strictPast_payload_integrable hη ht
              (fun xNext prev =>
                ⟪S.auxiliaryPoint t xNext (prev.blockX i) - x, S.gradF i x⟫_ℝ))
          (fun i _hi =>
            S.positiveEta_strictPast_payload_integrable hη ht
              (fun _xNext prev => ⟪prev.blockX i - x, S.gradF i x⟫_ℝ))
          (S.positiveEta_strictPast_payload_integrable hη ht
            (fun xNext _prev => S.μ * S.ν xNext - S.μ * S.ν x))
          (by
            intro i _hi
            simpa [SOptLib.expectation, smul_eq_mul] using
              S.lemma59_block_inner_expectation_relation hη ht i x))

/-- Eq. (5.2.63), the scalar output-weight telescope used in Lemma 5.10.

Aligns with Lan Eq. (5.2.63). Candidate audit: searched `weighted recurrence
telescope finite window` and `sum Icc theta tau weight condition telescope`;
`finite_window_weighted_recurrence_telescope_with_tail_sums` and
`sum_Icc_two_coeff_telescope_le` were checked/read but encode different
inequality recurrences, so this local helper proves the literal algebraic
identity from `WeightCondition5261`. -/
private theorem weight_condition_5261_sum_identity
    {k : ℕ} (hk : 1 ≤ k) (hweight : S.WeightCondition5261 k) :
    Finset.sum (outputWindow k) S.θ =
      S.θ k * (Fintype.card ι : ℝ) * (1 + S.τ k) -
        S.θ 1 * ((Fintype.card ι : ℝ) * (1 + S.τ 1) - 1) := by
  classical
  let m : ℝ := (Fintype.card ι : ℝ)
  change Finset.sum (outputWindow k) S.θ =
      S.θ k * m * (1 + S.τ k) - S.θ 1 * (m * (1 + S.τ 1) - 1)
  revert hweight
  refine Nat.le_induction ?base ?step k hk
  · intro _hweight
    simp [outputWindow]
    ring
  · intro n hn ih hweight
    have hweight_n : S.WeightCondition5261 n := by
      intro t ht2 htle
      exact hweight t ht2 (Nat.le_trans htle (Nat.le_succ n))
    have ih' := ih hweight_n
    have hn1 : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
    rw [outputWindow, Finset.sum_Icc_succ_top hn1]
    have hrec :
        S.θ (n + 1) * (m * (1 + S.τ (n + 1)) - 1) =
          S.θ n * m * (1 + S.τ n) := by
      simpa [m] using hweight (n + 1) (Nat.succ_le_succ hn) le_rfl
    have ih'' :
        Finset.sum (outputWindow n) S.θ =
          S.θ n * m * (1 + S.τ n) - S.θ 1 * (m * (1 + S.τ 1) - 1) := ih'
    simp [outputWindow] at ih''
    rw [ih'']
    nlinarith [hrec]

/-- Adjacent coefficient form of (5.2.61), normalized by the component count.

Aligns with the coefficient cancellation used in Lan Lemma 5.10 proof step 5.
Candidate audit: searched `sum Icc theta tau weight condition telescope`; the
available SOptLib telescopes are inequality-oriented and do not expose this
paper-specific inverse-cardinality coefficient bridge. -/
private theorem weight_condition_5261_prev_coeff_eq
    {k t : ℕ} (hweight : S.WeightCondition5261 k) (ht : 2 ≤ t) (htle : t ≤ k) :
    S.θ (t - 1) * (1 + S.τ (t - 1)) =
      S.θ t * ((1 + S.τ t) - (Fintype.card ι : ℝ)⁻¹) := by
  classical
  let m : ℝ := (Fintype.card ι : ℝ)
  have hm_ne : m ≠ 0 := by
    dsimp [m]
    exact_mod_cast (Nat.ne_of_gt Fintype.card_pos)
  have hrec :
      S.θ t * (m * (1 + S.τ t) - 1) =
        S.θ (t - 1) * m * (1 + S.τ (t - 1)) := by
    simpa [m] using hweight t ht htle
  change S.θ (t - 1) * (1 + S.τ (t - 1)) =
      S.θ t * ((1 + S.τ t) - m⁻¹)
  field_simp [hm_ne]
  nlinarith [hrec]

/-- Scalar component telescope for Lemma 5.10's current/previous block terms.

This is the algebraic core of Lan Lemma 5.10 proof step 5. Candidate audit:
`finite_window_weighted_recurrence_telescope_with_tail_sums` and
`sum_Icc_two_coeff_telescope_le` were checked/read but have different
recurrence/inequality shapes; this helper is the literal one-based equality
driven by `WeightCondition5261`. -/
private theorem weight_condition_5261_component_scalar_telescope
    {k : ℕ} (hk : 1 ≤ k) (hweight : S.WeightCondition5261 k) (Z : ℕ → ℝ) :
    Finset.sum (outputWindow k)
        (fun t =>
          S.θ t *
            ((1 + S.τ t) * Z t -
              ((1 + S.τ t) - (Fintype.card ι : ℝ)⁻¹) * Z (t - 1))) =
      S.θ k * (1 + S.τ k) * Z k -
        S.θ 1 * ((1 + S.τ 1) - (Fintype.card ι : ℝ)⁻¹) * Z 0 := by
  classical
  revert hweight
  refine Nat.le_induction ?base ?step k hk
  · intro _hweight
    simp [outputWindow]
    ring
  · intro n hn ih hweight
    have hweight_n : S.WeightCondition5261 n := by
      intro t ht2 htle
      exact hweight t ht2 (Nat.le_trans htle (Nat.le_succ n))
    have ih' := ih hweight_n
    have hn1 : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
    rw [outputWindow, Finset.sum_Icc_succ_top hn1]
    have hcoef :
        S.θ n * (1 + S.τ n) =
          S.θ (n + 1) *
            ((1 + S.τ (n + 1)) - (Fintype.card ι : ℝ)⁻¹) := by
      exact S.weight_condition_5261_prev_coeff_eq hweight (Nat.succ_le_succ hn) le_rfl
    have ih'' :
        Finset.sum (Finset.Icc 1 n)
            (fun t =>
              S.θ t *
                ((1 + S.τ t) * Z t -
                  ((1 + S.τ t) - (Fintype.card ι : ℝ)⁻¹) * Z (t - 1))) =
          S.θ n * (1 + S.τ n) * Z n -
            S.θ 1 * ((1 + S.τ 1) - (Fintype.card ι : ℝ)⁻¹) * Z 0 := by
      simpa [outputWindow] using ih'
    rw [ih'']
    rw [Nat.succ_sub_one]
    have hcoef_mul :
        S.θ n * (1 + S.τ n) * Z n =
          S.θ (n + 1) *
            ((1 + S.τ (n + 1)) - (Fintype.card ι : ℝ)⁻¹) * Z n := by
      rw [hcoef]
    nlinarith [hcoef_mul]

/-- Lemma 5.10 proof step 5 for one component's block-inner expectations.

This consumes the scalar telescope above with
`Z t = E[<x_i^t - x, grad f_i(x)>]` and rewrites the initial state
`x_i^0 = x0`. It aligns with Lan Lemma 5.10 proof step 5; the searched
SOptLib telescopes are algebraically different, while this statement is the
paper's one-based block-memory cancellation. -/
private theorem weighted_block_inner_telescope_5261
    (hη : S.PositiveEtaDomain) {k : ℕ} (hk : 1 ≤ k)
    (hweight : S.WeightCondition5261 k) (i : ι) (x : E) :
    Finset.sum (outputWindow k)
        (fun t =>
          S.θ t *
            ((1 + S.τ t) *
                SOptLib.expectation S.P
                  (fun ω =>
                    ⟪S.positiveEtaBlockIterate hη t ω i - x, S.gradF i x⟫_ℝ) -
              ((1 + S.τ t) - (Fintype.card ι : ℝ)⁻¹) *
                SOptLib.expectation S.P
                  (fun ω =>
                    ⟪(S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i - x,
                      S.gradF i x⟫_ℝ))) =
      S.θ k * (1 + S.τ k) *
          SOptLib.expectation S.P
            (fun ω =>
              ⟪S.positiveEtaBlockIterate hη k ω i - x, S.gradF i x⟫_ℝ) -
        S.θ 1 * ((1 + S.τ 1) - (Fintype.card ι : ℝ)⁻¹) *
          ⟪S.x0 - x, S.gradF i x⟫_ℝ := by
  classical
  let Z : ℕ → ℝ := fun t =>
    SOptLib.expectation S.P
      (fun ω => ⟪S.positiveEtaBlockIterate hη t ω i - x, S.gradF i x⟫_ℝ)
  have htelescope :=
    S.weight_condition_5261_component_scalar_telescope hk hweight Z
  have hZ0 : Z 0 = ⟪S.x0 - x, S.gradF i x⟫_ℝ := by
    haveI : IsProbabilityMeasure S.P := by
      unfold Setup.P uniformBlockStreamLaw
      infer_instance
    unfold Z SOptLib.expectation
    simp [initialState, positiveEtaBlockIterate, positiveEtaGeneratedProcess_zero, integral_const,
      probReal_univ]
  rw [hZ0] at htelescope
  simpa [Z, positiveEtaBlockIterate] using htelescope

/-- Component-summed version of Lemma 5.10 proof step 5.

This immediately consumes `weighted_block_inner_telescope_5261`, commuting the
finite time and component sums so the downstream Lemma 5.10 proof no longer has
a window of previous-state inner products. -/
private theorem weighted_block_inner_window_telescope_5261
    (hη : S.PositiveEtaDomain) {k : ℕ} (hk : 1 ≤ k)
    (hweight : S.WeightCondition5261 k) (x : E) :
    Finset.sum (outputWindow k)
        (fun t =>
          S.θ t *
            Finset.sum Finset.univ
              (fun i =>
                (1 + S.τ t) *
                    SOptLib.expectation S.P
                      (fun ω =>
                        ⟪S.positiveEtaBlockIterate hη t ω i - x,
                          S.gradF i x⟫_ℝ) -
                  ((1 + S.τ t) - (Fintype.card ι : ℝ)⁻¹) *
                    SOptLib.expectation S.P
                      (fun ω =>
                        ⟪(S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i - x,
                          S.gradF i x⟫_ℝ))) =
      Finset.sum Finset.univ
        (fun i =>
          S.θ k * (1 + S.τ k) *
              SOptLib.expectation S.P
                (fun ω =>
                  ⟪S.positiveEtaBlockIterate hη k ω i - x, S.gradF i x⟫_ℝ) -
            S.θ 1 * ((1 + S.τ 1) - (Fintype.card ι : ℝ)⁻¹) *
              ⟪S.x0 - x, S.gradF i x⟫_ℝ) := by
  classical
  let F : ℕ → ι → ℝ := fun t i =>
    (1 + S.τ t) *
        SOptLib.expectation S.P
          (fun ω => ⟪S.positiveEtaBlockIterate hη t ω i - x, S.gradF i x⟫_ℝ) -
      ((1 + S.τ t) - (Fintype.card ι : ℝ)⁻¹) *
        SOptLib.expectation S.P
          (fun ω =>
            ⟪(S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i - x,
              S.gradF i x⟫_ℝ)
  calc
    Finset.sum (outputWindow k)
        (fun t =>
          S.θ t *
            Finset.sum Finset.univ
              (fun i =>
                (1 + S.τ t) *
                    SOptLib.expectation S.P
                      (fun ω =>
                        ⟪S.positiveEtaBlockIterate hη t ω i - x,
                          S.gradF i x⟫_ℝ) -
                  ((1 + S.τ t) - (Fintype.card ι : ℝ)⁻¹) *
                    SOptLib.expectation S.P
                      (fun ω =>
                        ⟪(S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i - x,
                          S.gradF i x⟫_ℝ))) =
      Finset.sum (outputWindow k)
        (fun t => Finset.sum Finset.univ (fun i => S.θ t * F t i)) := by
        simp [F, Finset.mul_sum, Finset.sum_sub_distrib, mul_sub]
    _ =
      Finset.sum Finset.univ
        (fun i => Finset.sum (outputWindow k) (fun t => S.θ t * F t i)) := by
        rw [Finset.sum_comm]
    _ =
      Finset.sum Finset.univ
        (fun i =>
          S.θ k * (1 + S.τ k) *
              SOptLib.expectation S.P
                (fun ω =>
                  ⟪S.positiveEtaBlockIterate hη k ω i - x, S.gradF i x⟫_ℝ) -
            S.θ 1 * ((1 + S.τ 1) - (Fintype.card ι : ℝ)⁻¹) *
              ⟪S.x0 - x, S.gradF i x⟫_ℝ) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        simpa [F] using S.weighted_block_inner_telescope_5261 hη hk hweight i x

/-- Component-function version of the (5.2.61) scalar telescope.

Aligns with Lan Proposition 5.6 proof step 11 for one component. Candidate
audit: searched `component function telescope weight condition outputWindow
expectation fAvg` and `weighted scalar telescope Icc theta tau fAvg`; the
usable local candidate is `weight_condition_5261_component_scalar_telescope`.
The SOptLib telescopes found (`sum_Icc_two_coeff_telescope_le` and
`finite_window_weighted_recurrence_telescope_with_tail_sums`) have different
inequality/recurrence shapes, so this specializes the literal Eq. (5.2.61)
scalar equality to `Z t = E[f_i(x_i^t)]`. -/
private theorem weighted_component_function_telescope_5261
    (hη : S.PositiveEtaDomain) {k : ℕ} (hk : 1 ≤ k)
    (hweight : S.WeightCondition5261 k) (i : ι) :
    Finset.sum (outputWindow k)
        (fun t =>
          S.θ t *
            ((1 + S.τ t) *
                SOptLib.expectation S.P
                  (fun ω => S.f i (S.positiveEtaBlockIterate hη t ω i)) -
              ((1 + S.τ t) - (Fintype.card ι : ℝ)⁻¹) *
                SOptLib.expectation S.P
                  (fun ω => S.f i (S.positiveEtaBlockIterate hη (t - 1) ω i)))) =
      S.θ k * (1 + S.τ k) *
          SOptLib.expectation S.P
            (fun ω => S.f i (S.positiveEtaBlockIterate hη k ω i)) -
        S.θ 1 * ((1 + S.τ 1) - (Fintype.card ι : ℝ)⁻¹) * S.f i S.x0 := by
  classical
  let Z : ℕ → ℝ := fun t =>
    SOptLib.expectation S.P
      (fun ω => S.f i (S.positiveEtaBlockIterate hη t ω i))
  have htelescope :=
    S.weight_condition_5261_component_scalar_telescope hk hweight Z
  have hZ0 : Z 0 = S.f i S.x0 := by
    haveI : IsProbabilityMeasure S.P := by
      unfold Setup.P uniformBlockStreamLaw
      infer_instance
    unfold Z SOptLib.expectation
    simp [initialState, positiveEtaBlockIterate, positiveEtaGeneratedProcess_zero, integral_const,
      probReal_univ]
  rw [hZ0] at htelescope
  simpa [Z] using htelescope

/-- Proposition 5.6 component-function telescope from (5.2.61).

Aligns with Lan Proposition 5.6 proof step 11: summing the componentwise
`WeightCondition5261` telescope and using Eq. (5.2.1)'s
`fAvg x0 = m⁻¹∑ᵢ f_i(x0)` converts the initial endpoint to
`θ₁(m(1+τ₁)-1) f(x0)`. Candidate audit: searched `component function
telescope weight condition outputWindow expectation fAvg`; the matching local
primitive was `weight_condition_5261_component_scalar_telescope`, while no
SOptLib theorem states this RGEM-specific function-value endpoint. -/
private theorem proposition56_component_function_telescope_5_2_61_positive_domain
    (hη : S.PositiveEtaDomain) {k : ℕ} (hk : 1 ≤ k)
    (hweight : S.WeightCondition5261 k) :
    Finset.sum (outputWindow k)
        (fun t =>
          S.θ t *
            ((1 + S.τ t) *
                Finset.sum Finset.univ
                  (fun i =>
                    SOptLib.expectation S.P
                      (fun ω => S.f i (S.positiveEtaBlockIterate hη t ω i))) -
              ((1 + S.τ t) - (Fintype.card ι : ℝ)⁻¹) *
                Finset.sum Finset.univ
                  (fun i =>
                    SOptLib.expectation S.P
                      (fun ω => S.f i (S.positiveEtaBlockIterate hη (t - 1) ω i))))) =
      S.θ k * (1 + S.τ k) *
          Finset.sum Finset.univ
            (fun i =>
              SOptLib.expectation S.P
                (fun ω => S.f i (S.positiveEtaBlockIterate hη k ω i))) -
        S.θ 1 * ((Fintype.card ι : ℝ) * (1 + S.τ 1) - 1) * S.fAvg S.x0 := by
  classical
  let F : ℕ → ι → ℝ := fun t i =>
    (1 + S.τ t) *
        SOptLib.expectation S.P
          (fun ω => S.f i (S.positiveEtaBlockIterate hη t ω i)) -
      ((1 + S.τ t) - (Fintype.card ι : ℝ)⁻¹) *
        SOptLib.expectation S.P
          (fun ω => S.f i (S.positiveEtaBlockIterate hη (t - 1) ω i))
  have hsum_components :
      Finset.sum (outputWindow k)
          (fun t =>
            S.θ t *
              ((1 + S.τ t) *
                  Finset.sum Finset.univ
                    (fun i =>
                      SOptLib.expectation S.P
                        (fun ω => S.f i (S.positiveEtaBlockIterate hη t ω i))) -
                ((1 + S.τ t) - (Fintype.card ι : ℝ)⁻¹) *
                  Finset.sum Finset.univ
                    (fun i =>
                      SOptLib.expectation S.P
                        (fun ω => S.f i (S.positiveEtaBlockIterate hη (t - 1) ω i))))) =
        Finset.sum Finset.univ
          (fun i =>
            S.θ k * (1 + S.τ k) *
                SOptLib.expectation S.P
                  (fun ω => S.f i (S.positiveEtaBlockIterate hη k ω i)) -
              S.θ 1 * ((1 + S.τ 1) - (Fintype.card ι : ℝ)⁻¹) * S.f i S.x0) := by
    calc
      Finset.sum (outputWindow k)
          (fun t =>
            S.θ t *
              ((1 + S.τ t) *
                  Finset.sum Finset.univ
                    (fun i =>
                      SOptLib.expectation S.P
                        (fun ω => S.f i (S.positiveEtaBlockIterate hη t ω i))) -
                ((1 + S.τ t) - (Fintype.card ι : ℝ)⁻¹) *
                  Finset.sum Finset.univ
                    (fun i =>
                      SOptLib.expectation S.P
                        (fun ω => S.f i (S.positiveEtaBlockIterate hη (t - 1) ω i))))) =
        Finset.sum (outputWindow k)
          (fun t => Finset.sum Finset.univ (fun i => S.θ t * F t i)) := by
          simp [F, Finset.mul_sum, Finset.sum_sub_distrib, mul_sub]
      _ =
        Finset.sum Finset.univ
          (fun i => Finset.sum (outputWindow k) (fun t => S.θ t * F t i)) := by
          rw [Finset.sum_comm]
      _ =
        Finset.sum Finset.univ
          (fun i =>
            S.θ k * (1 + S.τ k) *
                SOptLib.expectation S.P
                  (fun ω => S.f i (S.positiveEtaBlockIterate hη k ω i)) -
              S.θ 1 * ((1 + S.τ 1) - (Fintype.card ι : ℝ)⁻¹) * S.f i S.x0) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          simpa [F] using S.weighted_component_function_telescope_5261 hη hk hweight i
  let m : ℝ := (Fintype.card ι : ℝ)
  have hm_ne : m ≠ 0 := by
    dsimp [m]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
  have hinit :
      Finset.sum Finset.univ
          (fun i =>
            S.θ 1 * ((1 + S.τ 1) - (Fintype.card ι : ℝ)⁻¹) * S.f i S.x0) =
        S.θ 1 * ((Fintype.card ι : ℝ) * (1 + S.τ 1) - 1) * S.fAvg S.x0 := by
    dsimp [Setup.fAvg]
    change
      Finset.sum Finset.univ
          (fun i => S.θ 1 * ((1 + S.τ 1) - m⁻¹) * S.f i S.x0) =
        S.θ 1 * (m * (1 + S.τ 1) - 1) *
          (m⁻¹ * Finset.sum Finset.univ (fun i => S.f i S.x0))
    rw [← Finset.mul_sum]
    field_simp [hm_ne]
  calc
    Finset.sum (outputWindow k)
        (fun t =>
          S.θ t *
            ((1 + S.τ t) *
                Finset.sum Finset.univ
                  (fun i =>
                    SOptLib.expectation S.P
                      (fun ω => S.f i (S.positiveEtaBlockIterate hη t ω i))) -
              ((1 + S.τ t) - (Fintype.card ι : ℝ)⁻¹) *
                Finset.sum Finset.univ
                  (fun i =>
                    SOptLib.expectation S.P
                      (fun ω => S.f i (S.positiveEtaBlockIterate hη (t - 1) ω i))))) =
      Finset.sum Finset.univ
        (fun i =>
          S.θ k * (1 + S.τ k) *
              SOptLib.expectation S.P
                (fun ω => S.f i (S.positiveEtaBlockIterate hη k ω i)) -
            S.θ 1 * ((1 + S.τ 1) - (Fintype.card ι : ℝ)⁻¹) * S.f i S.x0) :=
        hsum_components
    _ =
      S.θ k * (1 + S.τ k) *
          Finset.sum Finset.univ
            (fun i =>
              SOptLib.expectation S.P
                (fun ω => S.f i (S.positiveEtaBlockIterate hη k ω i))) -
        Finset.sum Finset.univ
          (fun i =>
            S.θ 1 * ((1 + S.τ 1) - (Fintype.card ι : ℝ)⁻¹) * S.f i S.x0) := by
        rw [Finset.sum_sub_distrib]
        rw [← Finset.mul_sum]
    _ =
      S.θ k * (1 + S.τ k) *
          Finset.sum Finset.univ
            (fun i =>
              SOptLib.expectation S.P
                (fun ω => S.f i (S.positiveEtaBlockIterate hη k ω i))) -
        S.θ 1 * ((Fintype.card ι : ℝ) * (1 + S.τ 1) - 1) * S.fAvg S.x0 := by
        rw [hinit]

/-- Sampled-block support of the generated `y`-table update.

This is the pathwise component-change identity used inside Lan Proposition 5.6
proof step 8 before the gradient-extrapolation telescope. Candidate audit:
searched `gradient extrapolation telescope y current previous sampled block
theta alpha inner product`; no SOptLib or target-file theorem stated this
RGEM-specific sampled-update sum, while `positiveEtaGeneratedProcess_succ_equations`
and Mathlib's `Function.update_of_ne` provide the exact local update API. -/
private theorem positiveEta_y_update_sum_eq_sample_delta
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 1 ≤ t) (ω : BlockSamplePath ι) :
    Finset.sum Finset.univ
        (fun i =>
          S.positiveEtaYIterate hη t ω i -
            S.positiveEtaYIterate hη (t - 1) ω i) =
      S.positiveEtaYIterate hη t ω (S.sample t ω) -
        S.positiveEtaYIterate hη (t - 1) ω (S.sample t ω) := by
  classical
  have hstep := S.positiveEtaGeneratedProcess_succ_equations hη ht ω
  rcases hstep with ⟨_hxmem, _hmin, _hblock, _hyprev, hycurr⟩
  exact
    _root_.sum_update_sub_eq_sampled_sub_of_update_off
      (yPrev := fun i => S.positiveEtaYIterate hη (t - 1) ω i)
      (yNext := fun i => S.positiveEtaYIterate hη t ω i)
      (sampled := S.sample t ω)
      (by
        intro i hi_ne
        calc
          S.positiveEtaYIterate hη t ω i =
              Function.update (S.positiveEtaGeneratedProcess hη (t - 1) ω).yCurr
                (S.sample t ω)
                (S.gradF (S.sample t ω)
                  ((S.positiveEtaGeneratedProcess hη t ω).blockX (S.sample t ω))) i := by
                simpa [positiveEtaYIterate] using congrFun hycurr i
          _ = S.positiveEtaYIterate hη (t - 1) ω i := by
                simpa [positiveEtaYIterate] using
                  Function.update_of_ne hi_ne
                    (S.gradF (S.sample t ω)
                      ((S.positiveEtaGeneratedProcess hη t ω).blockX (S.sample t ω)))
                    (S.positiveEtaGeneratedProcess hη (t - 1) ω).yCurr)

/-- Inner-product form of the sampled-block `y`-table update.

Aligns with the first equality in Lan Proposition 5.6 proof step 8 after
pairing the sampled component-change identity with an arbitrary displacement.
Candidate audit: this consumes the proved local vector identity
`positiveEta_y_update_sum_eq_sample_delta`; generic SOptLib telescopes do not
know RGEM's sampled component table update. -/
private theorem positiveEta_y_update_inner_sum_eq_sample_delta
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 1 ≤ t)
    (ω : BlockSamplePath ι) (u : E) :
    Finset.sum Finset.univ
        (fun i =>
          ⟪u,
            S.positiveEtaYIterate hη t ω i -
              S.positiveEtaYIterate hη (t - 1) ω i⟫_ℝ) =
      ⟪u,
        S.positiveEtaYIterate hη t ω (S.sample t ω) -
          S.positiveEtaYIterate hη (t - 1) ω (S.sample t ω)⟫_ℝ := by
  classical
  have hvec := S.positiveEta_y_update_sum_eq_sample_delta hη ht ω
  calc
    Finset.sum Finset.univ
        (fun i =>
          ⟪u,
            S.positiveEtaYIterate hη t ω i -
              S.positiveEtaYIterate hη (t - 1) ω i⟫_ℝ) =
      ⟪u,
        Finset.sum Finset.univ
          (fun i =>
            S.positiveEtaYIterate hη t ω i -
              S.positiveEtaYIterate hη (t - 1) ω i)⟫_ℝ := by
        simpa [inner_sum, inner_sub_right, Finset.sum_sub_distrib]
    _ =
      ⟪u,
        S.positiveEtaYIterate hη t ω (S.sample t ω) -
          S.positiveEtaYIterate hη (t - 1) ω (S.sample t ω)⟫_ℝ := by
        rw [hvec]

/-- Lagged sampled-block support of the generated `y`-table update.

This is the `t-1` instance of the sampled update identity needed in Lan
Proposition 5.6 proof step 8 for the extrapolation term
`y_i^{t-1}-y_i^{t-2}`. Candidate audit: this is a direct specialization of
`positiveEta_y_update_inner_sum_eq_sample_delta`; no separate SOptLib candidate
matches the RGEM one-based lagged sample index. -/
private theorem positiveEta_y_lagged_update_inner_sum_eq_sample_delta
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 2 ≤ t)
    (ω : BlockSamplePath ι) (u : E) :
    Finset.sum Finset.univ
        (fun i =>
          ⟪u,
            S.positiveEtaYIterate hη (t - 1) ω i -
              S.positiveEtaYIterate hη (t - 2) ω i⟫_ℝ) =
      ⟪u,
        S.positiveEtaYIterate hη (t - 1) ω (S.sample (t - 1) ω) -
          S.positiveEtaYIterate hη (t - 2) ω (S.sample (t - 1) ω)⟫_ℝ := by
  classical
  have htprev : 1 ≤ t - 1 := by omega
  have h :=
    S.positiveEta_y_update_inner_sum_eq_sample_delta
      hη (t := t - 1) htprev ω u
  simpa [Nat.sub_sub] using h

/-- Uniform lagged update identity, including the `t = 1` boundary.

Lan Proposition 5.6 proof step 8 uses the convention `y_i^{-1}=y_i^0`.
In the generated Lean process this is represented by natural subtraction at
`t = 1`, where both lagged tables are the initial `y^0` table. This helper
keeps that boundary explicit while reusing the sampled lag identity for
`t ≥ 2`. -/
private theorem positiveEta_y_lagged_update_inner_sum_eq_delta_pred
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 1 ≤ t)
    (ω : BlockSamplePath ι) (u : E) :
    Finset.sum Finset.univ
        (fun i =>
          ⟪u,
            S.positiveEtaYIterate hη (t - 1) ω i -
              S.positiveEtaYIterate hη (t - 2) ω i⟫_ℝ) =
      ⟪u,
        S.positiveEtaYIterate hη (t - 1) ω (S.sample (t - 1) ω) -
          S.positiveEtaYIterate hη (t - 2) ω (S.sample (t - 1) ω)⟫_ℝ := by
  classical
  by_cases ht2 : 2 ≤ t
  · exact S.positiveEta_y_lagged_update_inner_sum_eq_sample_delta hη ht2 ω u
  · have ht_eq : t = 1 := by omega
    subst ht_eq
    simp

/-- One-step split of the gradient-extrapolation component sum.

This is the algebraic core of Lan Proposition 5.6 proof step 8 before summing
over time: the current component changes collapse to the sampled block, while
the lagged extrapolation changes remain as the previous table-change sum.
Candidate audit: searched `gradient extrapolation telescope y current previous
sampled block theta alpha inner product`; no existing target-file/SOptLib lemma
matched this RGEM expression, so this consumes the local sampled-update bridge
proved above. -/
private theorem proposition56_gradient_extrapolation_step_inner_sum_split_positive_domain
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 1 ≤ t)
    (ω : BlockSamplePath ι) (u : E) :
    Finset.sum Finset.univ
        (fun i =>
          ⟪u,
            (S.positiveEtaYIterate hη t ω i -
              S.positiveEtaYIterate hη (t - 1) ω i) -
              (S.α t / (Fintype.card ι : ℝ)) •
                (S.positiveEtaYIterate hη (t - 1) ω i -
                  S.positiveEtaYIterate hη (t - 2) ω i)⟫_ℝ) =
      ⟪u,
        S.positiveEtaYIterate hη t ω (S.sample t ω) -
          S.positiveEtaYIterate hη (t - 1) ω (S.sample t ω)⟫_ℝ -
        (S.α t / (Fintype.card ι : ℝ)) *
          Finset.sum Finset.univ
            (fun i =>
              ⟪u,
                S.positiveEtaYIterate hη (t - 1) ω i -
                  S.positiveEtaYIterate hη (t - 2) ω i⟫_ℝ) := by
  classical
  exact
    sum_inner_selected_extrapolation_split
      (yPrevPrev := fun i => S.positiveEtaYIterate hη (t - 2) ω i)
      (yPrev := fun i => S.positiveEtaYIterate hη (t - 1) ω i)
      (yNext := fun i => S.positiveEtaYIterate hη t ω i)
      (sampled := S.sample t ω) (u := u)
      (c := S.α t / (Fintype.card ι : ℝ))
      (S.positiveEta_y_update_inner_sum_eq_sample_delta hη ht ω u)

/-- Sampled lag form of the one-step gradient-extrapolation split for `t ≥ 2`.

Aligns with Lan Proposition 5.6 proof step 8 after using that only the sampled
component changed at the previous iteration. This is a direct consumer of the
current and lagged sampled-update helpers, still before the side-condition
(5.2.65) time telescope. -/
private theorem proposition56_gradient_extrapolation_step_inner_sum_sampled_positive_domain
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 2 ≤ t)
    (ω : BlockSamplePath ι) (u : E) :
    Finset.sum Finset.univ
        (fun i =>
          ⟪u,
            (S.positiveEtaYIterate hη t ω i -
              S.positiveEtaYIterate hη (t - 1) ω i) -
              (S.α t / (Fintype.card ι : ℝ)) •
                (S.positiveEtaYIterate hη (t - 1) ω i -
                  S.positiveEtaYIterate hη (t - 2) ω i)⟫_ℝ) =
      ⟪u,
        S.positiveEtaYIterate hη t ω (S.sample t ω) -
          S.positiveEtaYIterate hη (t - 1) ω (S.sample t ω)⟫_ℝ -
        (S.α t / (Fintype.card ι : ℝ)) *
          ⟪u,
            S.positiveEtaYIterate hη (t - 1) ω (S.sample (t - 1) ω) -
              S.positiveEtaYIterate hη (t - 2) ω (S.sample (t - 1) ω)⟫_ℝ := by
  classical
  have hsplit :=
    S.proposition56_gradient_extrapolation_step_inner_sum_split_positive_domain
      hη (t := t) (by omega) ω u
  have hlag :=
    S.positiveEta_y_lagged_update_inner_sum_eq_sample_delta hη ht ω u
  rw [hsplit, hlag]

/-- Terminal component convexity bridge for Lemma 5.10 proof step 6.

Aligns with Lan Lemma 5.10 step 6: component convexity at the fixed feasible
base point `x` bounds the terminal block inner product by the component value
gap, and monotonicity of the Bochner integral lifts this pointwise inequality
to `SOptLib.expectation`. Candidate audit: checked the target file for terminal
helpers and searched SOptLib/Mathlib for `convex first order support
HasGradientWithinAt` and expectation monotonicity. The matching support lemma
is `ConvexOn.firstOrderLinearModel_le_of_hasGradientWithinAt`; the proof uses
that theorem's Mathlib-level shape together with local integrability from
`positiveEta_current_prev_payload_integrable`. -/
private theorem terminal_component_inner_expectation_le_value_gap
    (hη : S.PositiveEtaDomain) (k : ℕ) (i : ι) {x : E} (hx : x ∈ S.X) :
    SOptLib.expectation S.P
        (fun ω => ⟪S.positiveEtaBlockIterate hη k ω i - x, S.gradF i x⟫_ℝ) ≤
    SOptLib.expectation S.P
        (fun ω => S.f i (S.positiveEtaBlockIterate hη k ω i)) - S.f i x := by
  classical
  haveI : IsProbabilityMeasure S.P := by
    unfold Setup.P uniformBlockStreamLaw
    infer_instance
  simpa [SOptLib.expectation_def] using
    ConvexOn.expectation_inner_sub_le_expectation_sub_of_hasGradientWithinAt
      (μ := S.P) (C := S.X) (f := S.f i) (grad := S.gradF i x) (x := x)
      (Y := fun ω => S.positiveEtaBlockIterate hη k ω i)
      (S.hcomponent_convex i) hx
      (by
        filter_upwards with ω
        simpa [positiveEtaBlockIterate, positiveEtaGeneratedProcess] using
          (S.positiveEtaProcess hη k ω).2.2 i)
      (S.hcomponent_hasGradient i x hx)
      (by
        exact S.positiveEta_current_prev_payload_integrable hη k
          (G := fun curr _prev => ⟪curr.blockX i - x, S.gradF i x⟫_ℝ))
      (by
        exact S.positiveEta_current_prev_payload_integrable hη k
          (G := fun curr _prev => S.f i (curr.blockX i)))

/-- Step-0 statement-correction artifact for Lemma 5.10.

The old hk-free Lemma 5.10 head admitted `k = 0`. At that index the two
weight premises are vacuous, while the endpoint term in the displayed RHS is
still unconstrained and can make the scalar inequality fail. This private lemma
records that obstruction without adding any source-facing premise or Setup
field. -/
private theorem weightedQRecursion_old_zero_domain_vacuous_and_endpoint_countermodel :
    S.OutputWeightsNonnegative 0 ∧
      S.WeightCondition5261 0 ∧
      ¬
        (0 ≤
          (0 : ℝ) * (1 + (0 : ℝ)) * (0 : ℝ) +
            (0 : ℝ) -
              (1 : ℝ) * ((Fintype.card ι : ℝ) * (1 + (1 : ℝ)) - 1) *
                (1 : ℝ)) := by
  refine ⟨?hθ, ?hweight, ?hcounter⟩
  · intro t ht
    have htIcc := Finset.mem_Icc.mp ht
    exact (Nat.not_succ_le_zero 0 (le_trans htIcc.1 htIcc.2)).elim
  · intro t ht2 htle
    exact (Nat.not_succ_le_zero 1 (le_trans ht2 htle)).elim
  · have hcard_nat : (1 : ℕ) ≤ Fintype.card ι :=
      Nat.succ_le_of_lt Fintype.card_pos
    have hcard : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by
      exact_mod_cast hcard_nat
    apply not_le_of_gt
    nlinarith

/-- Corrected-domain theorem head for Lemma 5.10, the weighted recursion for `Q`.

The expectation well-definedness obligations are conclusions of the theorem and
the displayed inequality uses `SOptLib.expectation`, matching the paper's `E[·]`
notation without exposing raw total Bochner integrals in the public statement. -/
theorem WeightedQRecursion_Lemma_5_10_positive_domain
    {k : ℕ} (hk : 1 ≤ k) (hη : S.PositiveEtaDomain) {x : E} (hx : x ∈ S.X)
    (hθ : S.OutputWeightsNonnegative k) (hweight : S.WeightCondition5261 k) :
    (∀ t, t ∈ outputWindow k →
        SOptLib.expectationWellDefined S.P
          (fun ω => S.Q (S.positiveEtaXIterate hη t ω) x)) ∧
      (∀ i, SOptLib.expectationWellDefined S.P
        (fun ω => S.f i (S.positiveEtaBlockIterate hη k ω i))) ∧
      (∀ t, t ∈ outputWindow k →
        SOptLib.expectationWellDefined S.P
          (fun ω => S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.psi x)) ∧
      Finset.sum (outputWindow k)
          (fun t => S.θ t *
            SOptLib.expectation S.P
              (fun ω => S.Q (S.positiveEtaXIterate hη t ω) x)) ≤
        S.θ k * (1 + S.τ k) *
            Finset.sum Finset.univ
              (fun i => SOptLib.expectation S.P
                (fun ω => S.f i (S.positiveEtaBlockIterate hη k ω i))) +
          Finset.sum (outputWindow k)
            (fun t => S.θ t *
              SOptLib.expectation S.P
                (fun ω => S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.psi x)) -
          S.θ 1 * ((Fintype.card ι : ℝ) * (1 + S.τ 1) - 1) *
            (⟪S.x0 - x, tableAverage (fun i => S.gradF i x)⟫_ℝ + S.fAvg x) := by
  refine And.intro ?hQwd ?rest
  · intro t _ht
    rw [SOptLib.expectationWellDefined_iff_integrable]
    simpa [positiveEtaXIterate] using
      (S.positiveEta_current_prev_payload_integrable hη t
        (G := fun curr _prev => S.Q curr.x x))
  · refine And.intro ?hfwd ?rest2
    · intro i
      rw [SOptLib.expectationWellDefined_iff_integrable]
      simpa [positiveEtaBlockIterate] using
        (S.positiveEta_current_prev_payload_integrable hη k
          (G := fun curr _prev => S.f i (curr.blockX i)))
    · refine And.intro ?hnuWd ?hineq
      · intro t _ht
        rw [SOptLib.expectationWellDefined_iff_integrable]
        simpa [positiveEtaXIterate] using
          (S.positiveEta_current_prev_payload_integrable hη t
            (G := fun curr _prev => S.μ * S.ν curr.x - S.psi x))
      · calc
          Finset.sum (outputWindow k)
              (fun t => S.θ t *
                SOptLib.expectation S.P
                  (fun ω => S.Q (S.positiveEtaXIterate hη t ω) x))
              =
            Finset.sum (outputWindow k)
              (fun t => S.θ t *
                SOptLib.expectation S.P
                  (fun ω =>
                    (Fintype.card ι : ℝ)⁻¹ *
                        Finset.sum Finset.univ
                          (fun i =>
                            (1 + S.τ t) *
                                ⟪S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
                                    ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i) - x,
                                  S.gradF i x⟫_ℝ -
                              S.τ t *
                                ⟪(S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i - x,
                                  S.gradF i x⟫_ℝ) +
                      (S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.μ * S.ν x))) := by
              apply Finset.sum_congr rfl
              intro t _ht
              rw [S.weighted_q_one_step_expectation_relation hη t x]
          _ =
            Finset.sum (outputWindow k)
              (fun t => S.θ t *
                (Finset.sum Finset.univ
                  (fun i =>
                    (1 + S.τ t) *
                        SOptLib.expectation S.P
                          (fun ω =>
                            ⟪S.positiveEtaBlockIterate hη t ω i - x,
                              S.gradF i x⟫_ℝ) -
                      ((1 + S.τ t) - (Fintype.card ι : ℝ)⁻¹) *
                        SOptLib.expectation S.P
                          (fun ω =>
                            ⟪(S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i - x,
                              S.gradF i x⟫_ℝ)) +
                  SOptLib.expectation S.P
                    (fun ω => S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.μ * S.ν x))) := by
              apply Finset.sum_congr rfl
              intro t htmem
              have ht : 1 ≤ t := by
                exact (Finset.mem_Icc.mp (by simpa [outputWindow] using htmem)).1
              rw [S.weighted_q_auxiliary_expectation_to_block_inner hη ht x]
          _ =
            Finset.sum Finset.univ
              (fun i =>
                S.θ k * (1 + S.τ k) *
                    SOptLib.expectation S.P
                      (fun ω =>
                        ⟪S.positiveEtaBlockIterate hη k ω i - x,
                          S.gradF i x⟫_ℝ) -
                  S.θ 1 * ((1 + S.τ 1) - (Fintype.card ι : ℝ)⁻¹) *
                    ⟪S.x0 - x, S.gradF i x⟫_ℝ) +
              Finset.sum (outputWindow k)
                (fun t => S.θ t *
                  SOptLib.expectation S.P
                    (fun ω => S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.μ * S.ν x)) := by
              let F : ℕ → ι → ℝ := fun t i =>
                (1 + S.τ t) *
                    SOptLib.expectation S.P
                      (fun ω =>
                        ⟪S.positiveEtaBlockIterate hη t ω i - x,
                          S.gradF i x⟫_ℝ) -
                  ((1 + S.τ t) - (Fintype.card ι : ℝ)⁻¹) *
                    SOptLib.expectation S.P
                      (fun ω =>
                        ⟪(S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i - x,
                          S.gradF i x⟫_ℝ)
              let N : ℕ → ℝ := fun t =>
                SOptLib.expectation S.P
                  (fun ω => S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.μ * S.ν x)
              have hsplit :
                  Finset.sum (outputWindow k)
                    (fun t => S.θ t * (Finset.sum Finset.univ (F t) + N t)) =
                    Finset.sum (outputWindow k)
                      (fun t => S.θ t * Finset.sum Finset.univ (F t)) +
                    Finset.sum (outputWindow k) (fun t => S.θ t * N t) := by
                simp [mul_add, Finset.sum_add_distrib]
              have htelescope :=
                S.weighted_block_inner_window_telescope_5261 hη hk hweight x
              calc
                Finset.sum (outputWindow k)
                    (fun t => S.θ t *
                      (Finset.sum Finset.univ (F t) + N t)) =
                  Finset.sum (outputWindow k)
                      (fun t => S.θ t * Finset.sum Finset.univ (F t)) +
                    Finset.sum (outputWindow k) (fun t => S.θ t * N t) := hsplit
                _ =
                  Finset.sum Finset.univ
                    (fun i =>
                      S.θ k * (1 + S.τ k) *
                          SOptLib.expectation S.P
                            (fun ω =>
                              ⟪S.positiveEtaBlockIterate hη k ω i - x,
                                S.gradF i x⟫_ℝ) -
                        S.θ 1 * ((1 + S.τ 1) - (Fintype.card ι : ℝ)⁻¹) *
                          ⟪S.x0 - x, S.gradF i x⟫_ℝ) +
                    Finset.sum (outputWindow k) (fun t => S.θ t * N t) := by
                    rw [htelescope]
              all_goals simp [F, N]
          _ ≤
              S.θ k * (1 + S.τ k) *
                  Finset.sum Finset.univ
                    (fun i => SOptLib.expectation S.P
                      (fun ω => S.f i (S.positiveEtaBlockIterate hη k ω i))) +
                Finset.sum (outputWindow k)
                  (fun t => S.θ t *
                    SOptLib.expectation S.P
                      (fun ω => S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.psi x)) -
                S.θ 1 * ((Fintype.card ι : ℝ) * (1 + S.τ 1) - 1) *
                  (⟪S.x0 - x, tableAverage (fun i => S.gradF i x)⟫_ℝ + S.fAvg x) := by
              classical
              let c : ℝ := S.θ k * (1 + S.τ k)
              let d : ℝ := S.θ 1 * ((1 + S.τ 1) - (Fintype.card ι : ℝ)⁻¹)
              let I : ι → ℝ := fun i =>
                SOptLib.expectation S.P
                  (fun ω =>
                    ⟪S.positiveEtaBlockIterate hη k ω i - x, S.gradF i x⟫_ℝ)
              let Fv : ι → ℝ := fun i =>
                SOptLib.expectation S.P
                  (fun ω => S.f i (S.positiveEtaBlockIterate hη k ω i))
              let G : ι → ℝ := fun i => ⟪S.x0 - x, S.gradF i x⟫_ℝ
              let Nμ : ℕ → ℝ := fun t =>
                SOptLib.expectation S.P
                  (fun ω => S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.μ * S.ν x)
              have hk_mem : k ∈ outputWindow k := by
                simp [outputWindow, hk]
              have hc_nonneg : 0 ≤ c := by
                have hθk : 0 ≤ S.θ k := hθ k hk_mem
                have hτk : 0 ≤ S.τ k := (S.hparam_nonneg k).2.2
                dsimp [c]
                nlinarith
              have hterm : ∀ i, I i ≤ Fv i - S.f i x := by
                intro i
                simpa [I, Fv] using
                  S.terminal_component_inner_expectation_le_value_gap hη k i hx
              have hsum_inner_le :
                  Finset.sum Finset.univ (fun i => c * I i - d * G i) ≤
                    Finset.sum Finset.univ (fun i => c * (Fv i - S.f i x) - d * G i) := by
                refine Finset.sum_le_sum ?_
                intro i _hi
                have hmul : c * I i ≤ c * (Fv i - S.f i x) :=
                  mul_le_mul_of_nonneg_left (hterm i) hc_nonneg
                linarith
              have hle_terminal :
                  (Finset.sum Finset.univ
                    (fun i =>
                      S.θ k * (1 + S.τ k) *
                          SOptLib.expectation S.P
                            (fun ω =>
                              ⟪S.positiveEtaBlockIterate hη k ω i - x,
                                S.gradF i x⟫_ℝ) -
                        S.θ 1 * ((1 + S.τ 1) - (Fintype.card ι : ℝ)⁻¹) *
                          ⟪S.x0 - x, S.gradF i x⟫_ℝ) +
                    Finset.sum (outputWindow k)
                      (fun t => S.θ t * Nμ t)) ≤
                  Finset.sum Finset.univ (fun i => c * (Fv i - S.f i x) - d * G i) +
                    Finset.sum (outputWindow k) (fun t => S.θ t * Nμ t) := by
                have h := add_le_add_right hsum_inner_le
                  (Finset.sum (outputWindow k) (fun t => S.θ t * Nμ t))
                simpa [c, d, I, Fv, G, Nμ, mul_assoc] using h
              have hscalar :
                  Finset.sum Finset.univ (fun i => c * (Fv i - S.f i x) - d * G i) +
                      Finset.sum (outputWindow k) (fun t => S.θ t * Nμ t) ≤
                    S.θ k * (1 + S.τ k) *
                        Finset.sum Finset.univ
                          (fun i => SOptLib.expectation S.P
                            (fun ω => S.f i (S.positiveEtaBlockIterate hη k ω i))) +
                      Finset.sum (outputWindow k)
                        (fun t => S.θ t *
                          SOptLib.expectation S.P
                            (fun ω => S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.psi x)) -
                      S.θ 1 * ((Fintype.card ι : ℝ) * (1 + S.τ 1) - 1) *
                        (⟪S.x0 - x, tableAverage (fun i => S.gradF i x)⟫_ℝ + S.fAvg x) := by
                haveI : IsProbabilityMeasure S.P := by
                  unfold Setup.P uniformBlockStreamLaw
                  infer_instance
                let SN : ℝ := Finset.sum (outputWindow k) (fun t => S.θ t * Nμ t)
                let W : ℝ := Finset.sum (outputWindow k) S.θ
                have hNshift :
                    Finset.sum (outputWindow k)
                        (fun t => S.θ t *
                          SOptLib.expectation S.P
                            (fun ω =>
                              S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.psi x)) =
                      SN - W * S.fAvg x := by
                  have hterm_eq : ∀ t ∈ outputWindow k,
                      SOptLib.expectation S.P
                          (fun ω =>
                            S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.psi x) =
                        Nμ t - S.fAvg x := by
                    intro t _ht
                    have hN_int : Integrable
                        (fun ω =>
                          S.μ * S.ν (S.positiveEtaXIterate hη t ω) -
                            S.μ * S.ν x) S.P := by
                      simpa [positiveEtaXIterate] using
                        (S.positiveEta_current_prev_payload_integrable hη t
                          (G := fun curr _prev => S.μ * S.ν curr.x - S.μ * S.ν x))
                    have hpsi_eq : S.psi x = S.fAvg x + S.μ * S.ν x := by
                      rfl
                    have hfun :
                        (fun ω =>
                          S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.psi x) =
                        (fun ω =>
                          (S.μ * S.ν (S.positiveEtaXIterate hη t ω) -
                            S.μ * S.ν x) - S.fAvg x) := by
                      funext ω
                      rw [hpsi_eq]
                      ring
                    rw [hfun]
                    unfold SOptLib.expectation
                    rw [integral_sub]
                    · rw [integral_const]
                      simp [probReal_univ]
                      dsimp [Nμ, SOptLib.expectation]
                    · exact hN_int
                    · exact integrable_const (S.fAvg x)
                  calc
                    Finset.sum (outputWindow k)
                        (fun t => S.θ t *
                          SOptLib.expectation S.P
                            (fun ω =>
                              S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.psi x)) =
                      Finset.sum (outputWindow k) (fun t => S.θ t * (Nμ t - S.fAvg x)) := by
                        refine Finset.sum_congr rfl ?_
                        intro t ht
                        rw [hterm_eq t ht]
                    _ = SN - W * S.fAvg x := by
                        dsimp [SN, W]
                        have hmul :
                            Finset.sum (outputWindow k)
                                (fun t => S.θ t * (Nμ t - S.fAvg x)) =
                              Finset.sum (outputWindow k)
                                (fun t => S.θ t * Nμ t - S.θ t * S.fAvg x) := by
                          refine Finset.sum_congr rfl ?_
                          intro t _ht
                          ring
                        rw [hmul, Finset.sum_sub_distrib]
                        congr 1
                        rw [← Finset.sum_mul]
                let m : ℝ := (Fintype.card ι : ℝ)
                let SF : ℝ := Finset.sum Finset.univ Fv
                let Sf : ℝ := Finset.sum Finset.univ (fun i => S.f i x)
                let SG : ℝ := Finset.sum Finset.univ G
                let e : ℝ := S.θ 1 * (m * (1 + S.τ 1) - 1)
                have hm_ne : m ≠ 0 := by
                  dsimp [m]
                  exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
                have hW : W = c * m - e := by
                  dsimp [W, e, c, m]
                  rw [S.weight_condition_5261_sum_identity hk hweight]
                  ring
                have hd : d = e * m⁻¹ := by
                  dsimp [d, e, m]
                  field_simp [hm_ne]
                have htable :
                    ⟪S.x0 - x, tableAverage (fun i => S.gradF i x)⟫_ℝ =
                      m⁻¹ * SG := by
                  dsimp [SG, G, m]
                  simp [tableAverage, inner_smul_right, inner_sum]
                have hfavg : S.fAvg x = m⁻¹ * Sf := by
                  dsimp [Sf, m]
                  rfl
                have hleft_expand :
                    Finset.sum Finset.univ
                        (fun i => c * (Fv i - S.f i x) - d * G i) + SN =
                      c * SF - c * Sf - d * SG + SN := by
                  dsimp [SF, Sf, SG]
                  rw [Finset.sum_sub_distrib]
                  have hsum₁ :
                      Finset.sum Finset.univ (fun i => c * (Fv i - S.f i x)) =
                        c * Finset.sum Finset.univ Fv -
                          c * Finset.sum Finset.univ (fun i => S.f i x) := by
                    rw [← Finset.mul_sum]
                    congr 1
                    rw [Finset.sum_sub_distrib]
                    ring
                  have hsum₂ :
                      Finset.sum Finset.univ (fun i => d * G i) =
                        d * Finset.sum Finset.univ G := by
                    rw [← Finset.mul_sum]
                  rw [hsum₁, hsum₂]
                have hright_expand :
                    S.θ k * (1 + S.τ k) *
                        Finset.sum Finset.univ
                          (fun i => SOptLib.expectation S.P
                            (fun ω => S.f i (S.positiveEtaBlockIterate hη k ω i))) +
                      Finset.sum (outputWindow k)
                        (fun t => S.θ t *
                          SOptLib.expectation S.P
                            (fun ω =>
                              S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.psi x)) -
                      S.θ 1 * ((Fintype.card ι : ℝ) * (1 + S.τ 1) - 1) *
                        (⟪S.x0 - x, tableAverage (fun i => S.gradF i x)⟫_ℝ + S.fAvg x) =
                    c * SF + (SN - W * S.fAvg x) -
                      e * (m⁻¹ * SG + S.fAvg x) := by
                  rw [hNshift, htable]
                have hscalar_eq :
                    Finset.sum Finset.univ
                        (fun i => c * (Fv i - S.f i x) - d * G i) + SN =
                      S.θ k * (1 + S.τ k) *
                          Finset.sum Finset.univ
                            (fun i => SOptLib.expectation S.P
                              (fun ω => S.f i (S.positiveEtaBlockIterate hη k ω i))) +
                        Finset.sum (outputWindow k)
                          (fun t => S.θ t *
                            SOptLib.expectation S.P
                              (fun ω =>
                                S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.psi x)) -
                        S.θ 1 * ((Fintype.card ι : ℝ) * (1 + S.τ 1) - 1) *
                          (⟪S.x0 - x, tableAverage (fun i => S.gradF i x)⟫_ℝ + S.fAvg x) := by
                  rw [hleft_expand, hright_expand, hW, hd, hfavg]
                  field_simp [hm_ne]
                  ring
                exact le_of_eq hscalar_eq
              exact hle_terminal.trans hscalar

/-- Proposition 5.6 one-step source ingredients before the Eq. (5.2.73) summation.

This is a strict bridge below Eq. (5.2.75): it packages the generated-run
instances of Eq. (5.2.71), Lemma 5.8, and Lemma 5.9 used in Lan Proposition
5.6 proof steps 1--6, but does not perform the finite-window summation or
residual discharge. Candidate audit: searched `Eq 5.2.73 residual inequality
telescope gradient`; the matching candidates were exactly
`S.ProxStepInequality_Eq_5_2_71`, `S.SmoothnessGradientGap_Lemma_5_8`, and
`S.ConditionalBlockExpectation_Lemma_5_9_positive_domain`, while no existing
target-file or SOptLib theorem already combines these generated-process
instances. -/
private theorem proposition56_one_step_source_ingredients_5_2_73_positive_domain
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 1 ≤ t) (ω : BlockSamplePath ι)
    {x : E} (hx : x ∈ S.X) :
    (let prev : State ι E := S.positiveEtaGeneratedProcess hη (t - 1) ω
     let yTilde : ι → E := fun i => SOptLib.extrapolatedPoint (S.α t) ((prev).yCurr i) ((prev).yPrev i)
     let xNext : E := S.positiveEtaXIterate hη t ω
     ⟪xNext - x, tableAverage yTilde⟫_ℝ + S.μ * S.ν xNext - S.μ * S.ν x ≤
      S.η t * S.V prev.x x - (S.μ + S.η t) * S.V xNext x -
         S.η t * S.V prev.x xNext) ∧
      (∀ i,
        (1 / (2 * S.Lcomp i)) *
            S.dualNorm
              (S.gradF i
                  (S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
                    ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) -
                S.gradF i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) ^ 2 ≤
          S.f i
              (S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
                ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) -
            S.f i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i) -
            ⟪S.gradF i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i),
              S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
                  ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i) -
                (S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i⟫_ℝ) ∧
      (∀ i, S.ConditionalBlockExpectation59Formula_positive_domain hη t i) := by
  classical
  refine ⟨?hprox, ?rest⟩
  · simpa using
      S.proposition56_generated_prox_step_inequality_5_2_71_positive_domain
        hη ht ω hx
  · refine ⟨?hsmooth, ?hcond⟩
    · intro i
      simpa using
        S.proposition56_auxiliary_smoothness_gap_5_2_72_positive_domain
          hη (t := t) ω i
    · intro i
      exact S.ConditionalBlockExpectation_Lemma_5_9_positive_domain hη ht i

/-- Proposition 5.6 side conditions (5.2.65)--(5.2.68), proposition-local.

Book citation: `book/FOML/RandomGradientExtrapolation.json#/assumptions/13`,
`#/assumptions/14`, `#/assumptions/15`, and `#/assumptions/16`.
Quote: the four displayed Proposition 5.6 side conditions (5.2.65)--(5.2.68). -/
def PropositionSideConditions (k : ℕ) : Prop :=
  (∀ t, 2 ≤ t → t ≤ k + 1 →
    (Fintype.card ι : ℝ) * S.θ (t - 1) = S.α t * S.θ t) ∧
  (∀ t, 2 ≤ t → t ≤ k + 1 →
    S.θ t * S.η t ≤ S.θ (t - 1) * (S.μ + S.η (t - 1))) ∧
  (∀ t i, 2 ≤ t → t ≤ k →
    2 * S.α t * S.Lcomp i ≤ (Fintype.card ι : ℝ) * S.τ (t - 1) * S.η t) ∧
  (∀ i, 4 * S.Lcomp i ≤ S.τ k * (S.μ + S.η k))

/-- Terminal scalar consequence used in Proposition 5.6 proof step 18.

PDF p. 265 states the last terminal-residual inequality follows from
`mη_{k+1} ≤ α_{k+1}(μ+η_k)`, induced by (5.2.65) and (5.2.66). The finite-horizon
`PropositionSideConditions k` exposes those two source conditions at `k + 1`,
so this bridge is derived rather than assumed. -/
private theorem propositionSideConditions_terminal_eta_bridge
    {k : ℕ}
    (hk : 1 ≤ k)
    (hθ_pos : S.OutputWeightsPositive k)
    (hside : S.PropositionSideConditions k) :
    (Fintype.card ι : ℝ) * S.η (k + 1) ≤
      S.α (k + 1) * (S.μ + S.η k) := by
  classical
  have hk_mem : k ∈ outputWindow k := Finset.mem_Icc.mpr ⟨hk, le_rfl⟩
  have hθk_pos : 0 < S.θ k := by
    simpa using hθ_pos k hk_mem
  have hk2 : 2 ≤ k + 1 := by omega
  exact
    mul_eta_le_alpha_mul_of_weighted_eta_le_and_coeff_eq
      (m := (Fintype.card ι : ℝ)) (alpha := S.α (k + 1)) (theta := S.θ k)
      (thetaNext := S.θ (k + 1)) (etaNext := S.η (k + 1))
      (M := S.μ + S.η k)
      hθk_pos
      (by simpa using (S.hparam_nonneg (k + 1)).1)
      (by
        have h := hside.1 (k + 1) hk2 le_rfl
        simpa using h)
      (by
        have h := hside.2.1 (k + 1) hk2 le_rfl
        simpa using h)

/-- Pointwise Young absorption of the lagged RGEM residual with the adjacent Bregman term.

Aligns with Lan Proposition 5.6 proof steps 14--15: `S.V_lower_bound` supplies
the squared primal displacement budget, while `dualNorm_inner_le_mul_primalNorm`
turns the lagged gradient-memory pairing into the paper primal/dual norm
product. Candidate audit: checked SOptLib's
`inner_sub_sub_bregman_le_half_dual_sq` and `young_absorb_inner_of_norm_sq_budget`;
the former is not in this file's imports and the latter is ambient-norm based,
so this helper specializes the already available RGEM dual support inequality
and leaves the paper coefficient in the exact residual form. -/
private theorem proposition56_lagged_inner_adj_young_pointwise_positive_domain
    (hη : S.PositiveEtaDomain) {k t : ℕ}
    (hθ_pos : S.OutputWeightsPositive k)
    (hside : S.PropositionSideConditions k)
    (ht2 : 2 ≤ t) (htk : t ≤ k)
    (ω : BlockSamplePath ι) :
    - (S.θ t * S.α t / (Fintype.card ι : ℝ)) *
        ⟪S.positiveEtaXIterate hη t ω -
            S.positiveEtaXIterate hη (t - 1) ω,
          S.positiveEtaYIterate hη (t - 1) ω (S.sample (t - 1) ω) -
            S.positiveEtaYIterate hη (t - 2) ω (S.sample (t - 1) ω)⟫_ℝ -
        S.θ t * (S.η t *
          S.V (S.positiveEtaXIterate hη (t - 1) ω)
            (S.positiveEtaXIterate hη t ω)) ≤
      S.θ (t - 1) * S.α t /
          (2 * (Fintype.card ι : ℝ) * S.η t) *
        S.dualNorm
          (S.positiveEtaYIterate hη (t - 1) ω (S.sample (t - 1) ω) -
            S.positiveEtaYIterate hη (t - 2) ω (S.sample (t - 1) ω)) ^ 2 := by
  classical
  let m : ℝ := (Fintype.card ι : ℝ)
  let d : E :=
    S.positiveEtaXIterate hη t ω -
      S.positiveEtaXIterate hη (t - 1) ω
  let ζ : E :=
    S.positiveEtaYIterate hη (t - 1) ω (S.sample (t - 1) ω) -
      S.positiveEtaYIterate hη (t - 2) ω (S.sample (t - 1) ω)
  let c : ℝ := S.θ t * S.α t / m
  let A : ℝ := S.θ t * S.η t
  have hm_pos : 0 < m := by
    dsimp [m]
    exact_mod_cast Fintype.card_pos
  have hηt_pos : 0 < S.η t := hη t (by omega)
  have ht_mem : t ∈ outputWindow k := by
    rw [outputWindow]
    exact Finset.mem_Icc.mpr ⟨by omega, htk⟩
  have hθt_pos : 0 < S.θ t := hθ_pos t ht_mem
  have hα_nonneg : 0 ≤ S.α t := (S.hparam_nonneg t).1
  have hc_nonneg : 0 ≤ c := by
    dsimp [c, m]
    positivity
  have hA_pos : 0 < A := by
    dsimp [A]
    exact mul_pos hθt_pos hηt_pos
  have hd_dir : d ∈ (affineSpan ℝ S.X).direction := by
    dsimp [d]
    exact AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ S.X (S.positiveEtaXIterate_mem hη t ω))
      (subset_affineSpan ℝ S.X (S.positiveEtaXIterate_mem hη (t - 1) ω))
  have hsupport_abs := dualNorm_inner_le_mul_primalNorm S ζ d hd_dir
  have hinner_support : -⟪d, ζ⟫_ℝ ≤ S.dualNorm ζ * S.primalNorm d := by
    have hneg_abs : -⟪d, ζ⟫_ℝ ≤ |⟪ζ, d⟫_ℝ| := by
      simpa [real_inner_comm] using (neg_le_abs ⟪ζ, d⟫_ℝ)
    exact hneg_abs.trans hsupport_abs
  have hV_lower :
      (1 / 2 : ℝ) * S.primalNorm d ^ 2 ≤
        S.V (S.positiveEtaXIterate hη (t - 1) ω)
          (S.positiveEtaXIterate hη t ω) := by
    simpa [d] using
      S.V_lower_bound
        (S.positiveEtaXIterate_mem hη (t - 1) ω)
        (S.positiveEtaXIterate_mem hη t ω)
  have htheta_mul : S.θ t * S.α t = S.θ (t - 1) * m := by
    have hraw : m * S.θ (t - 1) = S.α t * S.θ t := by
      simpa [m] using hside.1 t ht2 (Nat.le_trans htk (Nat.le_succ k))
    nlinarith [hraw]
  have hcoef_le :
      c ^ 2 / (2 * A) ≤
        S.θ (t - 1) * S.α t / (2 * m * S.η t) := by
    have hm_ne : m ≠ 0 := ne_of_gt hm_pos
    have hη_ne : S.η t ≠ 0 := ne_of_gt hηt_pos
    have hθ_ne : S.θ t ≠ 0 := ne_of_gt hθt_pos
    have hcoef :
        c ^ 2 / (2 * A) =
          S.θ (t - 1) * S.α t / (2 * m * S.η t) := by
      dsimp [c, A]
      field_simp [hm_ne, hη_ne, hθ_ne]
      nlinarith [htheta_mul]
    exact le_of_eq hcoef
  have hcall :=
    neg_inner_sub_bregman_young_le_scaled_dualNorm_sq
      (V := S.V) (primalNorm := S.primalNorm) (dualNorm := S.dualNorm)
      (c := c) (A := A)
      (coeffOut := S.θ (t - 1) * S.α t / (2 * m * S.η t))
      (x := S.positiveEtaXIterate hη (t - 1) ω)
      (y := S.positiveEtaXIterate hη t ω)
      (d := d) (zeta := ζ)
      hc_nonneg hA_pos hinner_support hV_lower hcoef_le
  dsimp [c, A, d, ζ, m] at hcall
  nlinarith [hcall]

/-- Cross-residual coefficient consequence of Proposition 5.6 side condition (5.2.67).

Aligns with Lan Proposition 5.6 proof step 17: condition (5.2.67) makes the
coefficient of the intermediate squared gradient-memory residual nonpositive.
Candidate audit: searched `residual Young inequality norm square side condition`;
SOptLib has generic Young/norm-square facts, but no RGEM-specific bridge from
`PropositionSideConditions` to this paper coefficient. -/
private theorem proposition56_cross_residual_coefficient_nonpos_positive_domain
    {k t : ℕ} (hη : S.PositiveEtaDomain)
    (hθ_pos : S.OutputWeightsPositive k)
    (hside : S.PropositionSideConditions k)
    (ht2 : 2 ≤ t) (htk : t ≤ k) (i : ι) (hLpos : 0 < S.Lcomp i) :
    S.θ (t - 1) * S.α t / ((Fintype.card ι : ℝ) * S.η t) -
        S.θ (t - 1) * S.τ (t - 1) / (2 * S.Lcomp i) ≤ 0 := by
  exact
    residual_coeff_nonpos_of_two_mul_alpha_mul_L_le
      (theta := S.θ (t - 1)) (alpha := S.α t) (tau := S.τ (t - 1))
      (L := S.Lcomp i) (m := (Fintype.card ι : ℝ)) (eta := S.η t)
      (mul_pos (by exact_mod_cast Fintype.card_pos) (hη t (by omega)))
      (mul_pos (by norm_num) hLpos)
      (le_of_lt (hθ_pos (t - 1) (by
        rw [outputWindow]
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩)))
      (by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hside.2.2.1 t i ht2 htk)

/-- Terminal stale-gradient coefficient consequence of side conditions (5.2.65)--(5.2.66).

Aligns with Lan Proposition 5.6 proof step 18, where
`m η_{k+1} ≤ α_{k+1}(μ+η_k)` converts the terminal residual coefficient into
the final stale-gradient coefficient. Candidate audit: the target-file helper
`S.propositionSideConditions_terminal_eta_bridge` is the exact scalar source
bridge; no SOptLib theorem packages this RGEM-specific terminal coefficient. -/
private theorem proposition56_terminal_stale_coefficient_le_positive_domain
    {k : ℕ} (hk : 1 ≤ k) (hη : S.PositiveEtaDomain)
    (hθ_pos : S.OutputWeightsPositive k)
    (hside : S.PropositionSideConditions k) :
    2 * S.θ k / (S.μ + S.η k) ≤
      2 * S.θ k * S.α (k + 1) / ((Fintype.card ι : ℝ) * S.η (k + 1)) := by
  classical
  exact div_le_mul_div_of_nonneg_of_pos_of_pos_of_le_mul
    (c := 2 * S.θ k) (M := S.μ + S.η k) (alpha := S.α (k + 1))
    (d := (Fintype.card ι : ℝ) * S.η (k + 1))
    (by
      have hk_mem : k ∈ outputWindow k := Finset.mem_Icc.mpr ⟨hk, le_rfl⟩
      have htheta_pos : 0 < S.θ k := hθ_pos k hk_mem
      nlinarith)
    (by
      have hηk_pos : 0 < S.η k := hη k hk
      nlinarith [S.hμ_nonneg]
    )
    (by
      exact mul_pos (by exact_mod_cast Fintype.card_pos) (hη (k + 1) (Nat.succ_pos k)))
    (by simpa using S.propositionSideConditions_terminal_eta_bridge hk hθ_pos hside)

/-- Pointwise dual-norm split of the gradient-memory difference through the
stored component gradient.

Aligns with Lan Proposition 5.6 proof step 16:
`‖y_i^t-y_i^{t-1}‖_*²` is split through
`∇f_i(x_i^{t-1})`. Candidate audit: searched `sample correction bregman
terminal norm split smoothness penalty` and `affineDirectionDualNorm add
subadditivity dual norm`; SOptLib's `norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq`
is ambient-norm only, so this consumes the local restricted dual-norm
subadditivity bridge. -/
private theorem proposition56_y_memory_dualNorm_split_positive_domain
    (hη : S.PositiveEtaDomain) (t : ℕ) (ω : BlockSamplePath ι) (i : ι) :
    S.dualNorm
        (S.positiveEtaYIterate hη t ω i -
          S.positiveEtaYIterate hη (t - 1) ω i) ^ 2 ≤
      2 *
          S.dualNorm
            (S.positiveEtaYIterate hη t ω i -
              S.gradF i (S.positiveEtaBlockIterate hη (t - 1) ω i)) ^ 2 +
        2 *
          S.dualNorm
            (S.gradF i (S.positiveEtaBlockIterate hη (t - 1) ω i) -
              S.positiveEtaYIterate hη (t - 1) ω i) ^ 2 := by
  exact
    size_sub_sq_le_two_mul_size_sub_sq_add_two_mul_size_sub_sq_of_add_sq
      S.dualNorm
      (S.positiveEtaYIterate hη t ω i)
      (S.gradF i (S.positiveEtaBlockIterate hη (t - 1) ω i))
      (S.positiveEtaYIterate hη (t - 1) ω i)
      (dualNorm_add_sq_le_two_mul_dualNorm_sq_add_two_mul_dualNorm_sq S)

/-- Division form of side condition (5.2.65).

Aligns with Lan Proposition 5.6 proof step 9, where
`m θ_{t-1} = α_t θ_t` is used to telescope the gradient-extrapolation sum.
Candidate audit: searched `gradient extrapolation telescope theta alpha card`;
the existing `PropositionSideConditions` field is the source condition but no
local or SOptLib helper exposed the divided coefficient form needed by the
finite-sum algebra. -/
private theorem propositionSideConditions_alpha_theta_div_card_eq
    {k t : ℕ} (hside : S.PropositionSideConditions k)
    (ht2 : 2 ≤ t) (htle : t ≤ k + 1) :
    S.θ t * S.α t / (Fintype.card ι : ℝ) = S.θ (t - 1) := by
  classical
  let m : ℝ := (Fintype.card ι : ℝ)
  have hm_ne : m ≠ 0 := by
    dsimp [m]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
  have hraw : m * S.θ (t - 1) = S.α t * S.θ t := by
    simpa [m] using hside.1 t ht2 htle
  change S.θ t * S.α t / m = S.θ (t - 1)
  field_simp [hm_ne]
  nlinarith [hraw]

/-- Scalar summation-by-parts form of the gradient-extrapolation telescope.

This is the finite-time algebra behind Lan Proposition 5.6 proof step 9:
after the sampled-update reduction, the coefficient identity
`θ_t α_t / m = θ_{t-1}` makes the current sampled terms telescope and leaves
only the terminal term plus the lagged displacement residuals. Candidate audit:
searched `finite sum telescope shifted coefficient theta alpha previous delta
terminal` and `sum Icc shifted previous coefficient telescope terminal minus
lagged residual`; SOptLib contains shifted Delta-drop and inequality telescopes,
but no equality for this RGEM inner-product lag pattern, so this local helper
proves the exact scalar algebra. -/
private theorem gradient_extrapolation_scalar_telescope_of_coeff
    {k : ℕ} (hk : 1 ≤ k)
    (halpha :
      ∀ t, 2 ≤ t → t ≤ k →
        S.θ t * S.α t / (Fintype.card ι : ℝ) = S.θ (t - 1))
    (x : E) (xseq δ : ℕ → E) (hδ0 : δ 0 = 0) :
    Finset.sum (outputWindow k)
        (fun t =>
          S.θ t *
            (⟪xseq t - x, δ t⟫_ℝ -
              (S.α t / (Fintype.card ι : ℝ)) *
                ⟪xseq t - x, δ (t - 1)⟫_ℝ)) =
      S.θ k * ⟪xseq k - x, δ k⟫_ℝ -
        Finset.sum (Finset.Icc 2 k)
          (fun t =>
            (S.θ t * S.α t / (Fintype.card ι : ℝ)) *
              ⟪xseq t - xseq (t - 1), δ (t - 1)⟫_ℝ) := by
  simpa [outputWindow] using
    (_root_.sum_Icc_weighted_lagged_inner_telescope_eq_terminal_sub
      (theta := S.θ) (alpha := S.α) (m := (Fintype.card ι : ℝ))
      (x := x) (xseq := xseq) (delta := δ) (k := k) hk halpha hδ0)

/-- Pathwise gradient-extrapolation telescope from side condition (5.2.65).

This is Lan Proposition 5.6 proof steps 8--9 before lifting through
expectation: sampled component updates reduce the component sum to stochastic
increments, and `(5.2.65)` telescopes those increments to the terminal sampled
block minus the accumulated lagged displacement residuals. Candidate audit:
searched `gradient extrapolation telescope y current previous sampled block
theta alpha inner product`; no existing SOptLib theorem captures this
RGEM-specific sampled memory telescope, so this consumes the local one-step
sampled-update helpers plus `gradient_extrapolation_scalar_telescope_of_coeff`.
-/
private theorem proposition56_gradient_extrapolation_telescope_pathwise_5_2_65_positive_domain
    (hη : S.PositiveEtaDomain) {k : ℕ} (hk : 1 ≤ k)
    (hside : S.PropositionSideConditions k)
    (ω : BlockSamplePath ι) (x : E) :
    Finset.sum (outputWindow k)
        (fun t =>
          S.θ t *
            Finset.sum Finset.univ
              (fun i =>
                ⟪S.positiveEtaXIterate hη t ω - x,
                  (S.positiveEtaYIterate hη t ω i -
                    S.positiveEtaYIterate hη (t - 1) ω i) -
                    (S.α t / (Fintype.card ι : ℝ)) •
                      (S.positiveEtaYIterate hη (t - 1) ω i -
                        S.positiveEtaYIterate hη (t - 2) ω i)⟫_ℝ)) =
      S.θ k *
          ⟪S.positiveEtaXIterate hη k ω - x,
            S.positiveEtaYIterate hη k ω (S.sample k ω) -
              S.positiveEtaYIterate hη (k - 1) ω (S.sample k ω)⟫_ℝ -
        Finset.sum (Finset.Icc 2 k)
          (fun t =>
            (S.θ t * S.α t / (Fintype.card ι : ℝ)) *
              ⟪S.positiveEtaXIterate hη t ω -
                    S.positiveEtaXIterate hη (t - 1) ω,
                S.positiveEtaYIterate hη (t - 1) ω (S.sample (t - 1) ω) -
                  S.positiveEtaYIterate hη (t - 2) ω (S.sample (t - 1) ω)⟫_ℝ) := by
  classical
  have halpha :
      ∀ t, 2 ≤ t → t ≤ k →
        S.θ t * S.α t / (Fintype.card ι : ℝ) = S.θ (t - 1) := by
    intro t ht2 htle
    simpa using
      S.propositionSideConditions_alpha_theta_div_card_eq
        hside ht2 (Nat.le_trans htle (Nat.le_succ k))
  have hcurrent :
      ∀ t, 1 ≤ t → t ≤ k →
        Finset.sum Finset.univ
            (fun i =>
              ⟪S.positiveEtaXIterate hη t ω - x,
                S.positiveEtaYIterate hη t ω i -
                  S.positiveEtaYIterate hη (t - 1) ω i⟫_ℝ) =
          ⟪S.positiveEtaXIterate hη t ω - x,
            S.positiveEtaYIterate hη t ω (S.sample t ω) -
              S.positiveEtaYIterate hη (t - 1) ω (S.sample t ω)⟫_ℝ := by
    intro t ht1 _htle
    exact
      S.positiveEta_y_update_inner_sum_eq_sample_delta
        hη (t := t) ht1 ω (S.positiveEtaXIterate hη t ω - x)
  have hlagged :
      ∀ t, 1 ≤ t → t ≤ k →
        Finset.sum Finset.univ
            (fun i =>
              ⟪S.positiveEtaXIterate hη t ω - x,
                S.positiveEtaYIterate hη (t - 1) ω i -
                  S.positiveEtaYIterate hη (t - 2) ω i⟫_ℝ) =
          ⟪S.positiveEtaXIterate hη t ω - x,
            S.positiveEtaYIterate hη (t - 1) ω (S.sample (t - 1) ω) -
              S.positiveEtaYIterate hη (t - 2) ω (S.sample (t - 1) ω)⟫_ℝ := by
    intro t ht1 _htle
    exact
      S.positiveEta_y_lagged_update_inner_sum_eq_delta_pred
        hη (t := t) ht1 ω (S.positiveEtaXIterate hη t ω - x)
  simpa [outputWindow] using
    (selectedMemory_gradientExtrapolation_telescope_pathwise
      (theta := S.θ) (alpha := S.α) (m := (Fintype.card ι : ℝ))
      (x := x)
      (xseq := fun t ω => S.positiveEtaXIterate hη t ω)
      (memory := fun t ω i => S.positiveEtaYIterate hη t ω i)
      (sample := fun t ω => S.sample t ω)
      (k := k) hk ω halpha hcurrent hlagged)

/-- Expected gradient-extrapolation telescope from side condition (5.2.65).

Aligns with Lan Proposition 5.6 proof steps 8--9 after taking expectation:
the pathwise RGEM sampled-memory telescope is lifted through the finite window
sum and deterministic scalar weights. Candidate audit: checked
`proposition56_gradient_extrapolation_telescope_pathwise_5_2_65_positive_domain`,
`integrable_finset_sum_const_mul`, `MeasureTheory.integral_finset_sum`, and
`MeasureTheory.integral_const_mul`; SOptLib has generic expectation-linearity
tools but no theorem with this RGEM-specific sampled table telescope shape. -/
private theorem proposition56_gradient_extrapolation_telescope_expectation_5_2_65_positive_domain
    (hη : S.PositiveEtaDomain) {k : ℕ} (hk : 1 ≤ k)
    (hside : S.PropositionSideConditions k) (x : E) :
    Finset.sum (outputWindow k)
        (fun t =>
          S.θ t *
            SOptLib.expectation S.P
              (fun ω =>
                Finset.sum Finset.univ
                  (fun i =>
                    ⟪S.positiveEtaXIterate hη t ω - x,
                      (S.positiveEtaYIterate hη t ω i -
                        S.positiveEtaYIterate hη (t - 1) ω i) -
                        (S.α t / (Fintype.card ι : ℝ)) •
                          (S.positiveEtaYIterate hη (t - 1) ω i -
                            S.positiveEtaYIterate hη (t - 2) ω i)⟫_ℝ))) =
      S.θ k *
          SOptLib.expectation S.P
            (fun ω =>
              ⟪S.positiveEtaXIterate hη k ω - x,
                S.positiveEtaYIterate hη k ω (S.sample k ω) -
                  S.positiveEtaYIterate hη (k - 1) ω (S.sample k ω)⟫_ℝ) -
        Finset.sum (Finset.Icc 2 k)
          (fun t =>
            (S.θ t * S.α t / (Fintype.card ι : ℝ)) *
              SOptLib.expectation S.P
                (fun ω =>
                  ⟪S.positiveEtaXIterate hη t ω -
                        S.positiveEtaXIterate hη (t - 1) ω,
                    S.positiveEtaYIterate hη (t - 1) ω (S.sample (t - 1) ω) -
                      S.positiveEtaYIterate hη (t - 2) ω (S.sample (t - 1) ω)⟫_ℝ)) := by
  classical
  let A : ℕ → BlockSamplePath ι → ℝ := fun t ω =>
    Finset.sum Finset.univ
      (fun i =>
        ⟪S.positiveEtaXIterate hη t ω - x,
          (S.positiveEtaYIterate hη t ω i -
            S.positiveEtaYIterate hη (t - 1) ω i) -
            (S.α t / (Fintype.card ι : ℝ)) •
              (S.positiveEtaYIterate hη (t - 1) ω i -
                S.positiveEtaYIterate hη (t - 2) ω i)⟫_ℝ)
  let B : BlockSamplePath ι → ℝ := fun ω =>
    ⟪S.positiveEtaXIterate hη k ω - x,
      S.positiveEtaYIterate hη k ω (S.sample k ω) -
        S.positiveEtaYIterate hη (k - 1) ω (S.sample k ω)⟫_ℝ
  let C : ℕ → BlockSamplePath ι → ℝ := fun t ω =>
    ⟪S.positiveEtaXIterate hη t ω -
          S.positiveEtaXIterate hη (t - 1) ω,
      S.positiveEtaYIterate hη (t - 1) ω (S.sample (t - 1) ω) -
        S.positiveEtaYIterate hη (t - 2) ω (S.sample (t - 1) ω)⟫_ℝ
  have hA_int : ∀ t ∈ outputWindow k, Integrable (A t) S.P := by
    intro t htmem
    have htk : t ≤ k := (Finset.mem_Icc.mp (by simpa [outputWindow] using htmem)).2
    let G : (Fin k → ι) → (Fin (k + 1) → State ι E) → ℝ := fun _samples states =>
      Finset.sum Finset.univ
        (fun i =>
          ⟪(states ⟨t, by omega⟩).x - x,
            ((states ⟨t, by omega⟩).yCurr i -
              (states ⟨t - 1, by omega⟩).yCurr i) -
              (S.α t / (Fintype.card ι : ℝ)) •
                ((states ⟨t - 1, by omega⟩).yCurr i -
                  (states ⟨t - 2, by omega⟩).yCurr i)⟫_ℝ)
    simpa [A, G, positiveEtaXIterate, positiveEtaYIterate] using
      (S.positiveEta_sample_state_prefix_payload_integrable hη k G)
  have hB_int : Integrable B S.P := by
    let G : (Fin k → ι) → (Fin (k + 1) → State ι E) → ℝ := fun samples states =>
      ⟪(states ⟨k, by omega⟩).x - x,
        (states ⟨k, by omega⟩).yCurr (samples ⟨k - 1, by omega⟩) -
          (states ⟨k - 1, by omega⟩).yCurr (samples ⟨k - 1, by omega⟩)⟫_ℝ
    have hidx : 1 + (k - 1) = k := by omega
    simpa [B, G, positiveEtaXIterate, positiveEtaYIterate, hidx] using
      (S.positiveEta_sample_state_prefix_payload_integrable hη k G)
  have hC_int : ∀ t ∈ Finset.Icc 2 k, Integrable (C t) S.P := by
    intro t htmem
    have ht2 : 2 ≤ t := (Finset.mem_Icc.mp htmem).1
    have htk : t ≤ k := (Finset.mem_Icc.mp htmem).2
    let G : (Fin k → ι) → (Fin (k + 1) → State ι E) → ℝ := fun samples states =>
      ⟪(states ⟨t, by omega⟩).x - (states ⟨t - 1, by omega⟩).x,
        (states ⟨t - 1, by omega⟩).yCurr (samples ⟨t - 2, by omega⟩) -
          (states ⟨t - 2, by omega⟩).yCurr (samples ⟨t - 2, by omega⟩)⟫_ℝ
    have hidx : 1 + (t - 2) = t - 1 := by omega
    simpa [C, G, positiveEtaXIterate, positiveEtaYIterate, hidx] using
      (S.positiveEta_sample_state_prefix_payload_integrable hη k G)
  have hpath : ∀ ω : BlockSamplePath ι,
      Finset.sum (outputWindow k) (fun t => S.θ t • A t ω) =
        S.θ k • B ω -
          Finset.sum (Finset.Icc 2 k)
            (fun t => (S.θ t * S.α t / (Fintype.card ι : ℝ)) • C t ω) := by
    intro ω
    simpa [A, B, C, smul_eq_mul] using
      S.proposition56_gradient_extrapolation_telescope_pathwise_5_2_65_positive_domain
        hη hk hside ω x
  simpa [A, B, C, SOptLib.expectation, smul_eq_mul] using
    (integral_weighted_telescope_of_ae_eq
      (μ := S.P) (s := outputWindow k) (r := Finset.Icc 2 k)
      (A := A) (C := C) (B := B) (a := S.θ) (β := S.θ k)
      (c := fun t => S.θ t * S.α t / (Fintype.card ι : ℝ))
      hA_int hB_int hC_int (Filter.Eventually.of_forall hpath))

/-- Proposition 5.6 Bregman telescope from side condition (5.2.66).

Aligns with Lan Proposition 5.6 proof step 10: the finite sum of
`θ_t[η_t V(x^{t-1},x*) - (μ+η_t)V(x^t,x*)]` telescopes to the initial
potential minus the terminal potential. Candidate audit: searched `Finset sum
Icc telescoping theta eta V inequality`; the matching reusable theorem is
`SOptLib.sum_Icc_two_coeff_telescope_le`, while no target-file helper already
specialized it to RGEM positive-eta iterates and the paper side condition
(5.2.66). -/
private theorem proposition56_bregman_telescope_5_2_66_positive_domain
    (hη : S.PositiveEtaDomain) {k : ℕ} (hk : 1 ≤ k) {xStar : E}
    (hxStar : xStar ∈ S.X) (hside : S.PropositionSideConditions k) :
    Finset.sum (outputWindow k)
        (fun t =>
          S.θ t *
            (S.η t *
                SOptLib.expectation S.P
                  (fun ω => S.V (S.positiveEtaXIterate hη (t - 1) ω) xStar) -
              (S.μ + S.η t) *
                SOptLib.expectation S.P
                  (fun ω => S.V (S.positiveEtaXIterate hη t ω) xStar))) ≤
      S.θ 1 * S.η 1 * S.V S.x0 xStar -
        S.θ k * (S.μ + S.η k) *
          SOptLib.expectation S.P
            (fun ω => S.V (S.positiveEtaXIterate hη k ω) xStar) := by
  classical
  let c : ℕ → ℝ := fun t => S.θ t * S.η t
  let d : ℕ → ℝ := fun t => S.θ t * (S.μ + S.η t)
  let Vseq : ℕ → ℝ := fun n =>
    SOptLib.expectation S.P
      (fun ω => S.V (S.positiveEtaXIterate hη n ω) xStar)
  have hV_nonneg : ∀ n, 1 ≤ n → n < k → 0 ≤ Vseq n := by
    intro n _hn1 _hnk
    have hpoint : ∀ ω : BlockSamplePath ι,
        0 ≤ S.V (S.positiveEtaXIterate hη n ω) xStar := by
      intro ω
      have hlow := S.V_lower_bound (S.positiveEtaXIterate_mem hη n ω) hxStar
      have hsq : 0 ≤ (1 / 2 : ℝ) *
          S.primalNorm (xStar - S.positiveEtaXIterate hη n ω) ^ 2 := by
        have hnormsq : 0 ≤ S.primalNorm (xStar - S.positiveEtaXIterate hη n ω) ^ 2 :=
          sq_nonneg _
        nlinarith
      nlinarith
    dsimp [Vseq, SOptLib.expectation]
    exact integral_nonneg hpoint
  have hbridge : ∀ n, 1 ≤ n → n < k → c (n + 1) ≤ d n := by
    intro n hn1 hnk
    have hn2 : 2 ≤ n + 1 := by omega
    have hnle : n + 1 ≤ k + 1 := by omega
    have h := hside.2.1 (n + 1) hn2 hnle
    simpa [c, d, Nat.add_sub_cancel] using h
  have htelescope :=
    SOptLib.sum_Icc_two_coeff_telescope_le c d Vseq k hk hV_nonneg hbridge
  have hV0 : Vseq 0 = S.V S.x0 xStar := by
    haveI : IsProbabilityMeasure S.P := by
      unfold Setup.P uniformBlockStreamLaw
      infer_instance
    dsimp [Vseq, SOptLib.expectation]
    simp [positiveEtaXIterate, positiveEtaGeneratedProcess_zero, initialState,
      integral_const, probReal_univ]
  have hsum_eq :
      Finset.sum (outputWindow k)
          (fun t =>
            S.θ t *
              (S.η t *
                  SOptLib.expectation S.P
                    (fun ω => S.V (S.positiveEtaXIterate hη (t - 1) ω) xStar) -
                (S.μ + S.η t) *
                  SOptLib.expectation S.P
                    (fun ω => S.V (S.positiveEtaXIterate hη t ω) xStar))) =
        Finset.sum (Finset.Icc 1 k) (fun t => c t * Vseq (t - 1) - d t * Vseq t) := by
    rw [outputWindow]
    refine Finset.sum_congr rfl ?_
    intro t _ht
    dsimp [c, d, Vseq]
    ring
  calc
    Finset.sum (outputWindow k)
        (fun t =>
          S.θ t *
            (S.η t *
                SOptLib.expectation S.P
                  (fun ω => S.V (S.positiveEtaXIterate hη (t - 1) ω) xStar) -
              (S.μ + S.η t) *
                SOptLib.expectation S.P
                  (fun ω => S.V (S.positiveEtaXIterate hη t ω) xStar)))
        = Finset.sum (Finset.Icc 1 k) (fun t => c t * Vseq (t - 1) - d t * Vseq t) :=
          hsum_eq
    _ ≤ c 1 * Vseq 0 - d k * Vseq k := htelescope
    _ =
      S.θ 1 * S.η 1 * S.V S.x0 xStar -
        S.θ k * (S.μ + S.η k) *
          SOptLib.expectation S.P
            (fun ω => S.V (S.positiveEtaXIterate hη k ω) xStar) := by
        rw [hV0]

/-- Selected smoothness penalty equals the component-summed branch penalty.

Aligns with Lan Proposition 5.6 proof step 6, where Lemma 5.9 turns the
componentwise smoothness gap into the sampled `i_t` penalty. Candidate audit:
searched selected finite-uniform expectation candidates
`expectation_sample_eq_expectation_weighted_fiber_sum_of_indepFun` and
`integral_comp_indep_finite_uniform_eq_integral_inv_card_sum`; they are generic
independence transports, while this RGEM branch identity follows directly from
the local Lemma 5.9 branch theorem because all nonselected component gaps are
zero. -/
private theorem positiveEta_sampled_smoothness_penalty_sum_eq
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 1 ≤ t) (ω : BlockSamplePath ι) :
    Finset.sum Finset.univ
        (fun i =>
          S.τ t / (2 * S.Lcomp i) *
            S.dualNorm
              (S.gradF i (S.positiveEtaBlockIterate hη t ω i) -
                S.gradF i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) ^ 2) =
      S.τ t / (2 * S.Lcomp (S.sample t ω)) *
        S.dualNorm
          (S.gradF (S.sample t ω)
              (S.positiveEtaBlockIterate hη t ω (S.sample t ω)) -
            S.gradF (S.sample t ω)
              (S.positiveEtaBlockIterate hη (t - 1) ω (S.sample t ω))) ^ 2 := by
  classical
  refine Finset.sum_eq_single (S.sample t ω) ?_ ?_
  · intro i _hi hne
    rcases S.positiveEtaGeneratedProcess_branch_identities hη ht i with
      ⟨_hy, _hx, _hf, hnorm⟩
    have hsel : S.sample t ω ≠ i := fun h => hne h.symm
    have hzero :
        S.dualNorm
          (S.gradF i (S.positiveEtaBlockIterate hη t ω i) -
            S.gradF i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) ^ 2 = 0 := by
      simpa [hsel] using hnorm ω
    rw [hzero]
    ring
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ _))

/-- Expectation form of the selected smoothness penalty branch identity.

This is the expectation-linear version of
`positiveEta_sampled_smoothness_penalty_sum_eq`, used to align the fixed
component smoothness helper with the sampled penalty printed in Eq. (5.2.73).
The general selected-index SOptLib transports were checked but are stronger
than needed here because the pathwise nonselected branch is already zero. -/
private theorem positiveEta_sampled_smoothness_penalty_expectation_sum_eq
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 1 ≤ t) :
    Finset.sum Finset.univ
        (fun i =>
          S.τ t / (2 * S.Lcomp i) *
            SOptLib.expectation S.P
              (fun ω =>
                S.dualNorm
                  (S.gradF i (S.positiveEtaBlockIterate hη t ω i) -
                    S.gradF i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) ^ 2)) =
      SOptLib.expectation S.P
        (fun ω =>
          S.τ t / (2 * S.Lcomp (S.sample t ω)) *
            S.dualNorm
              (S.gradF (S.sample t ω)
                  (S.positiveEtaBlockIterate hη t ω (S.sample t ω)) -
                S.gradF (S.sample t ω)
                  (S.positiveEtaBlockIterate hη (t - 1) ω (S.sample t ω))) ^ 2) := by
  classical
  let A : ι → BlockSamplePath ι → ℝ := fun i ω =>
    S.dualNorm
      (S.gradF i (S.positiveEtaBlockIterate hη t ω i) -
        S.gradF i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) ^ 2
  let c : ι → ℝ := fun i => S.τ t / (2 * S.Lcomp i)
  let selected : BlockSamplePath ι → ℝ := fun ω =>
    S.τ t / (2 * S.Lcomp (S.sample t ω)) *
      S.dualNorm
        (S.gradF (S.sample t ω)
            (S.positiveEtaBlockIterate hη t ω (S.sample t ω)) -
          S.gradF (S.sample t ω)
            (S.positiveEtaBlockIterate hη (t - 1) ω (S.sample t ω))) ^ 2
  have hA_int : ∀ i ∈ (Finset.univ : Finset ι), Integrable (fun ω => c i * A i ω) S.P := by
    intro i _hi
    exact (S.positiveEta_current_prev_payload_integrable hη t
      (G := fun curr prev =>
        S.dualNorm (S.gradF i (curr.blockX i) - S.gradF i (prev.blockX i)) ^ 2)).const_mul (c i)
  have hlin :
      SOptLib.expectation S.P
          (fun ω => Finset.sum Finset.univ (fun i => c i * A i ω)) =
        Finset.sum Finset.univ
          (fun i => c i * SOptLib.expectation S.P (A i)) := by
    unfold SOptLib.expectation
    rw [MeasureTheory.integral_finset_sum Finset.univ hA_int]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [MeasureTheory.integral_const_mul]
  have hpoint : ∀ ω : BlockSamplePath ι,
      Finset.sum Finset.univ (fun i => c i * A i ω) = selected ω := by
    intro ω
    simpa [A, c, selected, positiveEtaBlockIterate] using
      S.positiveEta_sampled_smoothness_penalty_sum_eq hη ht ω
  calc
    Finset.sum Finset.univ
        (fun i =>
          S.τ t / (2 * S.Lcomp i) *
            SOptLib.expectation S.P
              (fun ω =>
                S.dualNorm
                  (S.gradF i (S.positiveEtaBlockIterate hη t ω i) -
                    S.gradF i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) ^ 2))
        = Finset.sum Finset.univ
            (fun i => c i * SOptLib.expectation S.P (A i)) := by
            simp [A, c]
    _ = SOptLib.expectation S.P
          (fun ω => Finset.sum Finset.univ (fun i => c i * A i ω)) := hlin.symm
    _ = SOptLib.expectation S.P selected := by
          unfold SOptLib.expectation
          apply integral_congr_ae
          filter_upwards with ω
          exact hpoint ω
    _ =
      SOptLib.expectation S.P
        (fun ω =>
          S.τ t / (2 * S.Lcomp (S.sample t ω)) *
            S.dualNorm
              (S.gradF (S.sample t ω)
                  (S.positiveEtaBlockIterate hη t ω (S.sample t ω)) -
                S.gradF (S.sample t ω)
                  (S.positiveEtaBlockIterate hη (t - 1) ω (S.sample t ω))) ^ 2) := by
        simp [selected]

/-- Sampled current gradient-state identity from Eq. (5.2.64).

Aligns with Lan Proposition 5.6 proof step 13, where the selected smoothness
penalty is rewritten through the updated sampled `y` memory. Candidate audit:
searched `GradientStateCharacterization selected sampled y current gradient`
and `sampled_smoothness_penalty y state`; the existing source theorem is
`GradientStateCharacterization_Eq_5_2_64_positive_domain`, but no local theorem
had specialized its existential branch to the current sample. -/
private theorem positiveEta_selected_current_y_eq_grad_positive_domain
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 1 ≤ t)
    (ω : BlockSamplePath ι) :
    S.positiveEtaYIterate hη t ω (S.sample t ω) =
      S.gradF (S.sample t ω)
        (S.positiveEtaBlockIterate hη t ω (S.sample t ω)) := by
  exact
    (S.GradientStateCharacterization_Eq_5_2_64_positive_domain
      hη t ω (S.sample t ω)).2
      ⟨t, ht, le_rfl, rfl⟩

/-- Zero-`L_i` sampled residual branch for Proposition 5.6.

Aligns with Lan Proposition 5.6 proof steps 16--17 in the totalized
nonnegative-`L_i` branch: when the sampled component has `L_i = 0`, component
smoothness forces the gradient difference between the current and previous
stored block points to have zero paper dual norm, and Eq. (5.2.64) rewrites the
current sampled `y` table to that current gradient. Candidate audit: searched
target/SOptLib for `zero L component residual gradient table equals gradient`
and `positiveEta y iterate block iterate sample update equation`; the relevant
local ingredients are `S.hcomponent_smooth`,
`dualNorm_nonneg_for_component_smoothness`, and
`positiveEta_selected_current_y_eq_grad_positive_domain`, while no existing
helper stated this sampled zero-`L_i` residual directly. -/
private theorem proposition56_zero_L_sampled_current_residual_sq_eq_zero
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 1 ≤ t)
    (ω : BlockSamplePath ι)
    (hLzero : S.Lcomp (S.sample t ω) = 0) :
    S.dualNorm
        (S.positiveEtaYIterate hη t ω (S.sample t ω) -
          S.gradF (S.sample t ω)
            (S.positiveEtaBlockIterate hη (t - 1) ω (S.sample t ω))) ^ 2 = 0 := by
  exact
    SOptLib.zero_lipschitz_gradient_residual_dualNorm_sq_eq_zero
      (dualNorm := S.dualNorm) (grad := S.gradF (S.sample t ω))
      (y := S.positiveEtaYIterate hη t ω (S.sample t ω))
      (x := S.positiveEtaBlockIterate hη t ω (S.sample t ω))
      (z := S.positiveEtaBlockIterate hη (t - 1) ω (S.sample t ω))
      (L := S.Lcomp (S.sample t ω))
      (radius :=
        S.primalNorm
          (S.positiveEtaBlockIterate hη t ω (S.sample t ω) -
            S.positiveEtaBlockIterate hη (t - 1) ω (S.sample t ω)))
      (by
        simpa using
          S.positiveEta_selected_current_y_eq_grad_positive_domain hη ht ω)
      hLzero
      (by
        have hx :
            S.positiveEtaBlockIterate hη t ω (S.sample t ω) ∈ S.X := by
          simpa [positiveEtaBlockIterate, positiveEtaGeneratedProcess] using
            (S.positiveEtaProcess hη t ω).2.2 (S.sample t ω)
        have hz :
            S.positiveEtaBlockIterate hη (t - 1) ω (S.sample t ω) ∈ S.X := by
          simpa [positiveEtaBlockIterate, positiveEtaGeneratedProcess] using
            (S.positiveEtaProcess hη (t - 1) ω).2.2 (S.sample t ω)
        simpa [dualNorm] using
          S.hcomponent_smooth (S.sample t ω)
            (S.positiveEtaBlockIterate hη t ω (S.sample t ω))
            (S.positiveEtaBlockIterate hη (t - 1) ω (S.sample t ω))
            hx hz)
      (dualNorm_nonneg_for_component_smoothness S _)

/-- Pointwise terminal residual absorption for Proposition 5.6 step 18.

Aligns with Lan Proposition 5.6 proof step 18: the terminal inner product is
absorbed by the terminal Bregman budget using `V_lower_bound` and the paper
dual-norm support inequality, then the y-memory split and side condition
(5.2.68) cancel the current sampled residual. Candidate audit: searched
`terminal residual Young stale gradient dualNorm positiveEtaXIterate Lcomp
expectation`, `terminal condition tau mu eta Lcomp residual coefficient`, and
`Young inner product norm square budget dual norm`; existing hits were the
local y-memory split, zero-`L_i` sampled residual lemma, and generic ambient
Young/SOptLib norm helpers, but no theorem stated this RGEM terminal
sample-`k` residual with the totalized zero-`L_i` branch. -/
private theorem proposition56_terminal_residual_pointwise_positive_domain
    {k : ℕ} {xStar : E}
    (hk : 1 ≤ k)
    (hη : S.PositiveEtaDomain)
    (hopt : S.IsOptimalSolution xStar)
    (hθ_pos : S.OutputWeightsPositive k)
    (hside : S.PropositionSideConditions k)
    (ω : BlockSamplePath ι) :
    S.θ k *
        ⟪S.positiveEtaXIterate hη k ω - xStar,
          S.positiveEtaYIterate hη k ω (S.sample k ω) -
            S.positiveEtaYIterate hη (k - 1) ω (S.sample k ω)⟫_ℝ -
      (S.θ k * (S.μ + S.η k) / 2) *
        S.V (S.positiveEtaXIterate hη k ω) xStar -
      S.θ k *
        (S.τ k / (2 * S.Lcomp (S.sample k ω)) *
          S.dualNorm
            (S.positiveEtaYIterate hη k ω (S.sample k ω) -
              S.gradF (S.sample k ω)
                (S.positiveEtaBlockIterate hη (k - 1) ω (S.sample k ω))) ^ 2) ≤
      (2 * S.θ k / (S.μ + S.η k)) *
        S.dualNorm
          (S.gradF (S.sample k ω)
              (S.positiveEtaBlockIterate hη (k - 1) ω (S.sample k ω)) -
            S.positiveEtaYIterate hη (k - 1) ω (S.sample k ω)) ^ 2 := by
  classical
  refine
    terminal_residual_young_split_le_stale_residual
      (V := S.V) (primalNorm := S.primalNorm) (dualNorm := S.dualNorm)
      (theta := S.θ k) (M := S.μ + S.η k) (tau := S.τ k)
      (L := S.Lcomp (S.sample k ω))
      (Ecur :=
        S.dualNorm
          (S.positiveEtaYIterate hη k ω (S.sample k ω) -
            S.gradF (S.sample k ω)
              (S.positiveEtaBlockIterate hη (k - 1) ω (S.sample k ω))) ^ 2)
      (Estale :=
        S.dualNorm
          (S.gradF (S.sample k ω)
              (S.positiveEtaBlockIterate hη (k - 1) ω (S.sample k ω)) -
            S.positiveEtaYIterate hη (k - 1) ω (S.sample k ω)) ^ 2)
      (x := S.positiveEtaXIterate hη k ω) (y := xStar)
      (d := S.positiveEtaXIterate hη k ω - xStar)
      (zeta :=
        S.positiveEtaYIterate hη k ω (S.sample k ω) -
          S.positiveEtaYIterate hη (k - 1) ω (S.sample k ω))
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · have hk_mem : k ∈ outputWindow k := by
      rw [outputWindow]
      exact Finset.mem_Icc.mpr ⟨hk, le_rfl⟩
    exact le_of_lt (hθ_pos k hk_mem)
  · have hηk_pos : 0 < S.η k := hη k hk
    nlinarith [S.hμ_nonneg]
  · exact S.hLcomp_nonneg (S.sample k ω)
  · have hd_dir :
        S.positiveEtaXIterate hη k ω - xStar ∈ (affineSpan ℝ S.X).direction := by
      exact AffineSubspace.vsub_mem_direction
        (subset_affineSpan ℝ S.X (S.positiveEtaXIterate_mem hη k ω))
        (subset_affineSpan ℝ S.X hopt.1)
    exact dualNorm_inner_le_mul_primalNorm S _ _ hd_dir
  · have hraw := S.V_lower_bound
      (S.positiveEtaXIterate_mem hη k ω) hopt.1
    have hnorm :
        S.primalNorm (xStar - S.positiveEtaXIterate hη k ω) ^ 2 =
          S.primalNorm (S.positiveEtaXIterate hη k ω - xStar) ^ 2 := by
      have hsub :
          xStar - S.positiveEtaXIterate hη k ω =
            -(S.positiveEtaXIterate hη k ω - xStar) := by
        abel
      rw [hsub]
      rw [map_neg_eq_map]
    simpa [hnorm] using hraw
  · simpa using
      S.proposition56_y_memory_dualNorm_split_positive_domain
        hη k ω (S.sample k ω)
  · exact sq_nonneg _
  · exact hside.2.2.2 (S.sample k ω)
  · intro hLzero
    simpa using
      S.proposition56_zero_L_sampled_current_residual_sq_eq_zero
        hη (t := k) hk ω hLzero

/-- Expectation-level sampled smoothness penalty rewritten as a y-memory residual.

Aligns with Lan Proposition 5.6 proof step 13 before Eq. (5.2.74): Eq. (5.2.64)
turns the sampled gradient difference into the current table-memory residual.
Candidate audit: searched `sampled smoothness penalty y memory residual
expectation`; checked `positiveEta_sampled_smoothness_penalty_expectation_sum_eq`
and `GradientStateCharacterization_Eq_5_2_64_positive_domain`. The former only
selects the sampled component, while the latter is pointwise; this helper
combines them in the exact residual form used by the paper. -/
private theorem positiveEta_sampled_smoothness_penalty_y_residual_eq
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 1 ≤ t) :
    SOptLib.expectation S.P
        (fun ω =>
          S.τ t / (2 * S.Lcomp (S.sample t ω)) *
            S.dualNorm
              (S.gradF (S.sample t ω)
                  (S.positiveEtaBlockIterate hη t ω (S.sample t ω)) -
                S.gradF (S.sample t ω)
                  (S.positiveEtaBlockIterate hη (t - 1) ω (S.sample t ω))) ^ 2) =
      SOptLib.expectation S.P
        (fun ω =>
          S.τ t / (2 * S.Lcomp (S.sample t ω)) *
            S.dualNorm
              (S.positiveEtaYIterate hη t ω (S.sample t ω) -
                S.gradF (S.sample t ω)
                  (S.positiveEtaBlockIterate hη (t - 1) ω (S.sample t ω))) ^ 2) := by
  congr 1
  funext ω
  rw [positiveEta_selected_current_y_eq_grad_positive_domain (S := S) hη ht ω]

/-- Split the fixed comparator part of `ψ` out of the one-step expectation.

This is a bookkeeping bridge for Lan Proposition 5.6 proof step 6:
`ψ(x)=fAvg(x)+μν(x)` and `x` is deterministic, so the printed expectation
`E[μν(x^t)-ψ(x)]` is the prox-compatible term
`E[μν(x^t)-μν(x)]` minus `fAvg(x)`. Candidate audit: existing objective
helpers such as `WeightedQRecursion_Lemma_5_10_positive_domain` contain this
rewrite only inside a larger telescope, so this local helper exposes the exact
fixed-time form needed for Eq. (5.2.73). -/
private theorem positiveEta_nu_psi_expectation_shift
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 1 ≤ t) (x : E) :
    SOptLib.expectation S.P
        (fun ω => S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.psi x) =
      SOptLib.expectation S.P
        (fun ω => S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.μ * S.ν x) -
        S.fAvg x := by
  classical
  haveI : IsProbabilityMeasure S.P := by
    unfold Setup.P uniformBlockStreamLaw
    infer_instance
  let N : BlockSamplePath ι → ℝ := fun ω =>
    S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.μ * S.ν x
  have hN_int : Integrable N S.P :=
    S.positiveEta_strictPast_payload_integrable hη ht
      (fun xNext _prev => S.μ * S.ν xNext - S.μ * S.ν x)
  have hfun :
      (fun ω => S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.psi x) =
        (fun ω => N ω - S.fAvg x) := by
    funext ω
    simp [N, psi, fAvg]
    ring
  unfold SOptLib.expectation
  rw [hfun]
  rw [MeasureTheory.integral_sub]
  · rw [MeasureTheory.integral_const]
    simp [probReal_univ, N]
  · exact hN_int
  · exact integrable_const (S.fAvg x)

/-- Linearity of the three Bregman terms in the expected prox inequality.

Aligns with Lan Proposition 5.6 proof step 6, converting the expectation of the
prox RHS from Eq. (5.2.71) into the separated Bregman window used in
Eq. (5.2.73). Candidate audit: SOptLib has generic finite-sum and telescope
linearity lemmas, but no paper-specific RGEM triple containing
`V(x^{t-1},x)`, `V(x^t,x)`, and `V(x^{t-1},x^t)` with positive-eta generated
integrability. -/
private theorem positiveEta_bregman_prox_expectation_linear
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 1 ≤ t) (x : E) :
    SOptLib.expectation S.P
        (fun ω =>
          S.η t *
              S.V (S.positiveEtaXIterate hη (t - 1) ω) x -
            (S.μ + S.η t) * S.V (S.positiveEtaXIterate hη t ω) x -
            S.η t *
              S.V (S.positiveEtaXIterate hη (t - 1) ω)
                (S.positiveEtaXIterate hη t ω)) =
      S.η t *
          SOptLib.expectation S.P
            (fun ω => S.V (S.positiveEtaXIterate hη (t - 1) ω) x) -
        (S.μ + S.η t) *
          SOptLib.expectation S.P
            (fun ω => S.V (S.positiveEtaXIterate hη t ω) x) -
        S.η t *
          SOptLib.expectation S.P
            (fun ω =>
              S.V (S.positiveEtaXIterate hη (t - 1) ω)
                (S.positiveEtaXIterate hη t ω)) := by
  classical
  let A : BlockSamplePath ι → ℝ := fun ω =>
    S.V (S.positiveEtaXIterate hη (t - 1) ω) x
  let B : BlockSamplePath ι → ℝ := fun ω =>
    S.V (S.positiveEtaXIterate hη t ω) x
  let C : BlockSamplePath ι → ℝ := fun ω =>
    S.V (S.positiveEtaXIterate hη (t - 1) ω)
      (S.positiveEtaXIterate hη t ω)
  have hA_int : Integrable A S.P :=
    S.positiveEta_strictPast_payload_integrable hη ht
      (fun _xNext prev => S.V prev.x x)
  have hB_int : Integrable B S.P :=
    S.positiveEta_strictPast_payload_integrable hη ht
      (fun xNext _prev => S.V xNext x)
  have hC_int : Integrable C S.P :=
    S.positiveEta_strictPast_payload_integrable hη ht
      (fun xNext prev => S.V prev.x xNext)
  unfold SOptLib.expectation
  calc
    (∫ ω,
        S.η t * S.V (S.positiveEtaXIterate hη (t - 1) ω) x -
          (S.μ + S.η t) * S.V (S.positiveEtaXIterate hη t ω) x -
          S.η t *
            S.V (S.positiveEtaXIterate hη (t - 1) ω)
              (S.positiveEtaXIterate hη t ω) ∂S.P)
        = ∫ ω, (S.η t * A ω - (S.μ + S.η t) * B ω) - S.η t * C ω ∂S.P := by
          rfl
    _ =
        (∫ ω, S.η t * A ω - (S.μ + S.η t) * B ω ∂S.P) -
          ∫ ω, S.η t * C ω ∂S.P := by
          rw [MeasureTheory.integral_sub]
          · exact (hA_int.const_mul (S.η t)).sub
              (hB_int.const_mul (S.μ + S.η t))
          · exact hC_int.const_mul (S.η t)
    _ =
        ((∫ ω, S.η t * A ω ∂S.P) -
            ∫ ω, (S.μ + S.η t) * B ω ∂S.P) -
          ∫ ω, S.η t * C ω ∂S.P := by
          rw [MeasureTheory.integral_sub]
          · exact hA_int.const_mul (S.η t)
          · exact hB_int.const_mul (S.μ + S.η t)
    _ =
        S.η t * (∫ ω, A ω ∂S.P) -
          (S.μ + S.η t) * (∫ ω, B ω ∂S.P) -
          S.η t * (∫ ω, C ω ∂S.P) := by
          rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
            MeasureTheory.integral_const_mul]

/-- Linearity of the left side of the expected prox inequality.

This normalizes Eq. (5.2.71) after taking expectation into the separated
inner-product and regularizer-difference terms that are combined with the
smoothness relation in Eq. (5.2.73). Candidate audit: generic SOptLib
expectation-linearity lemmas were considered, but the local positive-eta
payload integrability hypotheses make the direct two-term bridge shorter and
paper-specific. -/
private theorem positiveEta_prox_left_expectation_linear
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 1 ≤ t) (x : E) :
    SOptLib.expectation S.P
        (fun ω =>
          let prev : State ι E := S.positiveEtaGeneratedProcess hη (t - 1) ω
          let yTilde : ι → E := fun i => SOptLib.extrapolatedPoint (S.α t) ((prev).yCurr i) ((prev).yPrev i)
          let xNext : E := S.positiveEtaXIterate hη t ω
          ⟪xNext - x, tableAverage yTilde⟫_ℝ +
            S.μ * S.ν xNext - S.μ * S.ν x) =
      SOptLib.expectation S.P
        (fun ω =>
          let prev : State ι E := S.positiveEtaGeneratedProcess hη (t - 1) ω
          let yTilde : ι → E := fun i => SOptLib.extrapolatedPoint (S.α t) ((prev).yCurr i) ((prev).yPrev i)
          let xNext : E := S.positiveEtaXIterate hη t ω
          ⟪xNext - x, tableAverage yTilde⟫_ℝ) +
        SOptLib.expectation S.P
          (fun ω => S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.μ * S.ν x) := by
  classical
  let A : BlockSamplePath ι → ℝ := fun ω =>
    let prev : State ι E := S.positiveEtaGeneratedProcess hη (t - 1) ω
    let yTilde : ι → E := fun i => SOptLib.extrapolatedPoint (S.α t) ((prev).yCurr i) ((prev).yPrev i)
    let xNext : E := S.positiveEtaXIterate hη t ω
    ⟪xNext - x, tableAverage yTilde⟫_ℝ
  let B : BlockSamplePath ι → ℝ := fun ω =>
    S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.μ * S.ν x
  have hA_int : Integrable A S.P :=
    S.positiveEta_strictPast_payload_integrable hη ht
      (fun xNext prev =>
        let yTilde : ι → E := fun i => SOptLib.extrapolatedPoint (S.α t) ((prev).yCurr i) ((prev).yPrev i)
        ⟪xNext - x, tableAverage yTilde⟫_ℝ)
  have hB_int : Integrable B S.P :=
    S.positiveEta_strictPast_payload_integrable hη ht
      (fun xNext _prev => S.μ * S.ν xNext - S.μ * S.ν x)
  unfold SOptLib.expectation
  calc
    (∫ ω,
        (let prev : State ι E := S.positiveEtaGeneratedProcess hη (t - 1) ω
         let yTilde : ι → E := fun i => SOptLib.extrapolatedPoint (S.α t) ((prev).yCurr i) ((prev).yPrev i)
         let xNext : E := S.positiveEtaXIterate hη t ω
         ⟪xNext - x, tableAverage yTilde⟫_ℝ +
           S.μ * S.ν xNext - S.μ * S.ν x) ∂S.P)
        = ∫ ω, A ω + B ω ∂S.P := by
          apply integral_congr_ae
          filter_upwards with ω
          dsimp [A, B]
          ring
    _ = (∫ ω, A ω ∂S.P) + ∫ ω, B ω ∂S.P := by
          rw [MeasureTheory.integral_add hA_int hB_int]

/-- Lemma 5.9 projected against the strict-past primal displacement.

This is the source-route replacement for the old scalar y-inner branch: the
vector conditional identity from `ConditionalBlockExpectation_Lemma_5_9_positive_domain`
is projected by the strict-past measurable payload `x^t - x` using Mathlib's
bilinear conditional-expectation pull-out. -/
private theorem lemma59_y_inner_auxiliary_expectation_relation
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 1 ≤ t) (i : ι) (x : E) :
    SOptLib.expectation S.P
        (fun ω =>
          ⟪S.positiveEtaXIterate hη t ω - x,
            S.positiveEtaYIterate hη t ω i⟫_ℝ) =
      SOptLib.expectation S.P
        (fun ω =>
          (Fintype.card ι : ℝ)⁻¹ *
              ⟪S.positiveEtaXIterate hη t ω - x,
                S.auxiliaryGradient t (S.positiveEtaXIterate hη t ω)
                  (S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i⟫_ℝ +
            (1 - (Fintype.card ι : ℝ)⁻¹) *
              ⟪S.positiveEtaXIterate hη t ω - x,
                (S.positiveEtaGeneratedProcess hη (t - 1) ω).yCurr i⟫_ℝ) := by
  classical
  let U : BlockSamplePath ι → E := fun ω => S.positiveEtaXIterate hη t ω - x
  let Y : BlockSamplePath ι → E := fun ω => S.positiveEtaYIterate hη t ω i
  let T : BlockSamplePath ι → E := fun ω =>
    (Fintype.card ι : ℝ)⁻¹ •
        S.auxiliaryGradient t (S.positiveEtaXIterate hη t ω)
          (S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i +
      (1 - (Fintype.card ι : ℝ)⁻¹) •
        (S.positiveEtaGeneratedProcess hη (t - 1) ω).yCurr i
  rcases S.ConditionalBlockExpectation_Lemma_5_9_positive_domain hη ht i with
    ⟨⟨⟨hm, hsf, hY_int_raw⟩, hce⟩, _hx, _hf, _hnorm⟩
  have hU_sm : StronglyMeasurable[S.paperStrictPastSigma t] U := by
    refine S.strictPast_stronglyMeasurable_of_window_const U ?_
    intro ω ω' hwin
    have hxNext := S.positiveEtaXIterate_eq_of_strictPastWindow_eq hη ht hwin
    simp [U, hxNext]
  have hY_int : Integrable Y S.P := by
    simpa [Y] using hY_int_raw
  have hinner_int : Integrable (fun ω => ⟪Y ω, U ω⟫_ℝ) S.P := by
    simpa [Y, U, positiveEtaXIterate, positiveEtaYIterate] using
      S.positiveEta_current_prev_payload_integrable hη t
        (G := fun curr _prev => ⟪curr.yCurr i, curr.x - x⟫_ℝ)
  have hY_ce : S.P[Y | S.paperStrictPastSigma t] =ᵐ[S.P] T := by
    filter_upwards [hce] with ω hω
    simpa [Y, T] using hω
  haveI : SigmaFinite (S.P.trim hm) := hsf
  simpa [U, Y, T, SOptLib.expectation_def, inner_add_right, inner_smul_right] using
    expectation_inner_eq_of_condExp_eq_and_aestronglyMeasurable_right
      (μ := S.P) (m := S.paperStrictPastSigma t)
      (Y := Y) (T := T) (U := U)
      hm hU_sm.aestronglyMeasurable hinner_int hY_int hY_ce

/-- Split scalar form of the Lemma 5.9 y-table projection.

This is the algebra-ready form of
`lemma59_y_inner_auxiliary_expectation_relation`, separating the two strict-past
terms by expectation linearity. -/
private theorem lemma59_y_inner_auxiliary_expectation_relation_split
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 1 ≤ t) (i : ι) (x : E) :
    SOptLib.expectation S.P
        (fun ω =>
          ⟪S.positiveEtaXIterate hη t ω - x,
            S.positiveEtaYIterate hη t ω i⟫_ℝ) =
      (Fintype.card ι : ℝ)⁻¹ *
          SOptLib.expectation S.P
            (fun ω =>
              ⟪S.positiveEtaXIterate hη t ω - x,
                S.auxiliaryGradient t (S.positiveEtaXIterate hη t ω)
                  (S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i⟫_ℝ) +
        (1 - (Fintype.card ι : ℝ)⁻¹) *
          SOptLib.expectation S.P
            (fun ω =>
              ⟪S.positiveEtaXIterate hη t ω - x,
                (S.positiveEtaGeneratedProcess hη (t - 1) ω).yCurr i⟫_ℝ) := by
  classical
  simpa [SOptLib.expectation_def, smul_eq_mul] using
    (expectation_two_branch_split_of_expectation_eq
      (μ := S.P) (p := (Fintype.card ι : ℝ)⁻¹)
      (Y := fun ω =>
        ⟪S.positiveEtaXIterate hη t ω - x,
          S.positiveEtaYIterate hη t ω i⟫_ℝ)
      (A := fun ω =>
        ⟪S.positiveEtaXIterate hη t ω - x,
          S.auxiliaryGradient t (S.positiveEtaXIterate hη t ω)
            (S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i⟫_ℝ)
      (B := fun ω =>
        ⟪S.positiveEtaXIterate hη t ω - x,
          (S.positiveEtaGeneratedProcess hη (t - 1) ω).yCurr i⟫_ℝ)
      (S.positiveEta_strictPast_payload_integrable hη ht
        (fun xNext prev => ⟪xNext - x, S.auxiliaryGradient t xNext prev.blockX i⟫_ℝ))
      (S.positiveEta_strictPast_payload_integrable hη ht
        (fun xNext prev => ⟪xNext - x, prev.yCurr i⟫_ℝ))
      (by
        simpa [SOptLib.expectation_def, smul_eq_mul] using
          (S.lemma59_y_inner_auxiliary_expectation_relation hη (t := t) ht i x)))

/-- Eq. (5.2.49) expanded inside the prox table-average inner product.

This separates the prox table-average term into the previous y-table and the
extrapolation difference table. -/
private theorem gradient_extrapolation_tableAverage_inner_expectation_split
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 1 ≤ t) (x : E) :
    SOptLib.expectation S.P
        (fun ω =>
          let prev : State ι E := S.positiveEtaGeneratedProcess hη (t - 1) ω
          let yTilde : ι → E := fun i => SOptLib.extrapolatedPoint (S.α t) ((prev).yCurr i) ((prev).yPrev i)
          let xNext : E := S.positiveEtaXIterate hη t ω
          ⟪xNext - x, tableAverage yTilde⟫_ℝ) =
      (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ
            (fun i =>
              SOptLib.expectation S.P
                (fun ω =>
                  ⟪S.positiveEtaXIterate hη t ω - x,
                    (S.positiveEtaGeneratedProcess hη (t - 1) ω).yCurr i⟫_ℝ)) +
        (S.α t * (Fintype.card ι : ℝ)⁻¹) *
          Finset.sum Finset.univ
            (fun i =>
              SOptLib.expectation S.P
                (fun ω =>
                  ⟪S.positiveEtaXIterate hη t ω - x,
                      (S.positiveEtaGeneratedProcess hη (t - 1) ω).yCurr i -
                      (S.positiveEtaGeneratedProcess hη (t - 1) ω).yPrev i⟫_ℝ)) := by
  classical
  simpa [tableAverage, SOptLib.expectation_def, SOptLib.extrapolatedPoint, add_comm] using
    (SOptLib.expectation_inner_finite_average_extrapolated_table_split
      (μ := S.P) (s := (Finset.univ : Finset ι)) (alpha := S.α t)
      (invCard := (Fintype.card ι : ℝ)⁻¹)
      (U := fun ω => S.positiveEtaXIterate hη t ω - x)
      (yCurr := fun i ω => (S.positiveEtaGeneratedProcess hη (t - 1) ω).yCurr i)
      (yPrev := fun i ω => (S.positiveEtaGeneratedProcess hη (t - 1) ω).yPrev i)
      (by
        intro i _hi
        exact S.positiveEta_strictPast_payload_integrable hη ht
          (fun xNext prev => ⟪xNext - x, prev.yCurr i⟫_ℝ))
      (by
        intro i _hi
        exact S.positiveEta_strictPast_payload_integrable hη ht
          (fun xNext prev => ⟪xNext - x, prev.yCurr i - prev.yPrev i⟫_ℝ)))

/-- Expected auxiliary form of the component inequality (5.2.72).

This is the first source-granularity transport step for Lan Proposition 5.6
proof step 6: the proved pointwise Eq. (5.2.72) bridge is integrated before the
Lemma 5.9 sampled-block substitutions are applied. It deliberately does not use
the tombstoned y-window/component route. -/
private theorem proposition56_auxiliary_component_expected_5_2_72_positive_domain
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 1 ≤ t) {x : E} (hx : x ∈ S.X) :
    SOptLib.expectation S.P
        (fun ω =>
          (1 + S.τ t) * (Fintype.card ι : ℝ)⁻¹ *
              Finset.sum Finset.univ
                (fun i =>
                  S.f i
                    (S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
                      ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i))) -
            S.fAvg x) ≤
      SOptLib.expectation S.P
        (fun ω =>
          S.τ t * (Fintype.card ι : ℝ)⁻¹ *
              Finset.sum Finset.univ
                (fun i => S.f i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) +
            (Fintype.card ι : ℝ)⁻¹ *
              Finset.sum Finset.univ
                (fun i =>
                  ⟪S.positiveEtaXIterate hη t ω - x,
                    S.auxiliaryGradient t (S.positiveEtaXIterate hη t ω)
                      (S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i⟫_ℝ) -
            S.τ t * (Fintype.card ι : ℝ)⁻¹ *
              Finset.sum Finset.univ
                (fun i =>
                  (1 / (2 * S.Lcomp i)) *
                    S.dualNorm
                      (S.gradF i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i) -
                        S.gradF i
                          (S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
                            ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i))) ^ 2)) := by
  classical
  let L : BlockSamplePath ι → ℝ := fun ω =>
    (1 + S.τ t) * (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ
          (fun i =>
            S.f i
              (S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
                ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i))) -
      S.fAvg x
  let R : BlockSamplePath ι → ℝ := fun ω =>
    S.τ t * (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ
          (fun i => S.f i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) +
      (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ
          (fun i =>
            ⟪S.positiveEtaXIterate hη t ω - x,
              S.auxiliaryGradient t (S.positiveEtaXIterate hη t ω)
                (S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i⟫_ℝ) -
      S.τ t * (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ
          (fun i =>
            (1 / (2 * S.Lcomp i)) *
              S.dualNorm
                (S.gradF i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i) -
                  S.gradF i
                    (S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
                      ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i))) ^ 2)
  have hL_int : Integrable L S.P :=
    S.positiveEta_strictPast_payload_integrable hη ht
      (fun xNext prev =>
        (1 + S.τ t) * (Fintype.card ι : ℝ)⁻¹ *
            Finset.sum Finset.univ
              (fun i => S.f i (S.auxiliaryPoint t xNext (prev.blockX i))) -
          S.fAvg x)
  have hR_int : Integrable R S.P :=
    S.positiveEta_strictPast_payload_integrable hη ht
      (fun xNext prev =>
        S.τ t * (Fintype.card ι : ℝ)⁻¹ *
            Finset.sum Finset.univ (fun i => S.f i (prev.blockX i)) +
          (Fintype.card ι : ℝ)⁻¹ *
            Finset.sum Finset.univ
              (fun i =>
                ⟪xNext - x, S.auxiliaryGradient t xNext prev.blockX i⟫_ℝ) -
          S.τ t * (Fintype.card ι : ℝ)⁻¹ *
            Finset.sum Finset.univ
              (fun i =>
                (1 / (2 * S.Lcomp i)) *
                  S.dualNorm
                    (S.gradF i (prev.blockX i) -
                      S.gradF i (S.auxiliaryPoint t xNext (prev.blockX i))) ^ 2))
  have hpoint : ∀ᵐ ω ∂S.P, L ω ≤ R ω := by
    filter_upwards with ω
    simpa [L, R] using
      S.proposition56_component_eq_5_2_72_pointwise_positive_domain
        hη (t := t) ω hx
  have hmono : (∫ ω, L ω ∂S.P) ≤ ∫ ω, R ω ∂S.P :=
    integral_mono_ae hL_int hR_int hpoint
  unfold SOptLib.expectation
  simpa [L, R] using hmono

/-- Fixed-time component/function-value assembly for the expected one-step route.

This is the named source-granularity replacement for the former local
`hcomponent_source` leaf in the fixed-time Eq. (5.2.73) proof. It consumes the
proved pointwise Eq. (5.2.72) expectation lift together with Lemma 5.9
projections, Eq. (5.2.49), and the sampled penalty identity; the remaining leaf
is the finite-sum/order rewrite aligning those source ingredients with the
printed y-window term. -/
private theorem proposition56_fixed_time_component_assembly_5_2_73_positive_domain
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 1 ≤ t) {x : E} (hx : x ∈ S.X) :
    (1 + S.τ t) *
        Finset.sum Finset.univ
          (fun i =>
            SOptLib.expectation S.P
              (fun ω => S.f i (S.positiveEtaBlockIterate hη t ω i))) -
      S.fAvg x ≤
      ((1 + S.τ t) - (Fintype.card ι : ℝ)⁻¹) *
          Finset.sum Finset.univ
            (fun i =>
              SOptLib.expectation S.P
                (fun ω => S.f i (S.positiveEtaBlockIterate hη (t - 1) ω i))) +
        SOptLib.expectation S.P
          (fun ω =>
            Finset.sum Finset.univ
              (fun i =>
                ⟪S.positiveEtaXIterate hη t ω - x,
                  (S.positiveEtaYIterate hη t ω i -
                    S.positiveEtaYIterate hη (t - 1) ω i) -
                    (S.α t / (Fintype.card ι : ℝ)) •
                      (S.positiveEtaYIterate hη (t - 1) ω i -
                        S.positiveEtaYIterate hη (t - 2) ω i)⟫_ℝ)) +
        SOptLib.expectation S.P
          (fun ω =>
            let prev : State ι E := S.positiveEtaGeneratedProcess hη (t - 1) ω
            let yTilde : ι → E := fun i => SOptLib.extrapolatedPoint (S.α t) ((prev).yCurr i) ((prev).yPrev i)
            let xNext : E := S.positiveEtaXIterate hη t ω
            ⟪xNext - x, tableAverage yTilde⟫_ℝ) -
        SOptLib.expectation S.P
          (fun ω =>
            S.τ t / (2 * S.Lcomp (S.sample t ω)) *
              S.dualNorm
                (S.gradF (S.sample t ω)
                    (S.positiveEtaBlockIterate hη t ω (S.sample t ω)) -
                  S.gradF (S.sample t ω)
                    (S.positiveEtaBlockIterate hη (t - 1) ω (S.sample t ω))) ^ 2) := by
  classical
  have haux_expected :=
    S.proposition56_auxiliary_component_expected_5_2_72_positive_domain
      hη (t := t) ht hx
  have hcomponent_value := fun i : ι =>
    S.lemma59_component_value_auxiliary_expectation_relation hη (t := t) ht i
  have hgap_value := fun i : ι =>
    S.lemma59_auxiliary_gradient_gap_expectation_relation hη (t := t) ht i
  have hcond_value := fun i : ι =>
    S.ConditionalBlockExpectation_Lemma_5_9_positive_domain hη ht i
  have hgrad_extrapolation_value :=
    S.GradientExtrapolationDefinition_Eq_5_2_49
  have hpenalty_value :=
    S.positiveEta_sampled_smoothness_penalty_expectation_sum_eq hη (t := t) ht
  have hyinner_source := fun i : ι =>
    S.lemma59_y_inner_auxiliary_expectation_relation_split
      hη (t := t) ht i x
  have htable_source :=
    S.gradient_extrapolation_tableAverage_inner_expectation_split
      hη (t := t) ht x
  have hpointwise_source := fun ω =>
    S.proposition56_component_eq_5_2_72_pointwise_positive_domain
      hη (t := t) ω hx
  have _source_attempt :
      SOptLib.expectation S.P
          (fun ω =>
            (1 + S.τ t) * (Fintype.card ι : ℝ)⁻¹ *
                Finset.sum Finset.univ
                  (fun i =>
                    S.f i
                      (S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
                        ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i))) -
              S.fAvg x) ≤
        SOptLib.expectation S.P
          (fun ω =>
            S.τ t * (Fintype.card ι : ℝ)⁻¹ *
                Finset.sum Finset.univ
                  (fun i => S.f i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) +
              (Fintype.card ι : ℝ)⁻¹ *
                Finset.sum Finset.univ
                  (fun i =>
                    ⟪S.positiveEtaXIterate hη t ω - x,
                      S.auxiliaryGradient t (S.positiveEtaXIterate hη t ω)
                        (S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i⟫_ℝ) -
              S.τ t * (Fintype.card ι : ℝ)⁻¹ *
                Finset.sum Finset.univ
                  (fun i =>
                    (1 / (2 * S.Lcomp i)) *
                      S.dualNorm
                        (S.gradF i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i) -
                          S.gradF i
                            (S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
                              ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i))) ^ 2)) :=
    haux_expected
  have _source_component_value := hcomponent_value
  have _source_gap_value := hgap_value
  have _source_cond_value := hcond_value
  have _source_grad_extrapolation_value := hgrad_extrapolation_value
  have _source_penalty_value := hpenalty_value
  have _source_y_inner_value := hyinner_source
  have _source_table_value := htable_source
  have _source_pointwise_value := hpointwise_source
  let m : ℝ := (Fintype.card ι : ℝ)
  let Curr : ℝ :=
    Finset.sum Finset.univ
      (fun i =>
        SOptLib.expectation S.P
          (fun ω => S.f i (S.positiveEtaBlockIterate hη t ω i)))
  let Prev : ℝ :=
    Finset.sum Finset.univ
      (fun i =>
        SOptLib.expectation S.P
          (fun ω => S.f i (S.positiveEtaBlockIterate hη (t - 1) ω i)))
  let YWindow : ℝ :=
    SOptLib.expectation S.P
      (fun ω =>
        Finset.sum Finset.univ
          (fun i =>
            ⟪S.positiveEtaXIterate hη t ω - x,
              (S.positiveEtaYIterate hη t ω i -
                S.positiveEtaYIterate hη (t - 1) ω i) -
                (S.α t / (Fintype.card ι : ℝ)) •
                  (S.positiveEtaYIterate hη (t - 1) ω i -
                    S.positiveEtaYIterate hη (t - 2) ω i)⟫_ℝ))
  let Table : ℝ :=
    SOptLib.expectation S.P
      (fun ω =>
        let prev : State ι E := S.positiveEtaGeneratedProcess hη (t - 1) ω
        let yTilde : ι → E := fun i => SOptLib.extrapolatedPoint (S.α t) ((prev).yCurr i) ((prev).yPrev i)
        let xNext : E := S.positiveEtaXIterate hη t ω
        ⟪xNext - x, tableAverage yTilde⟫_ℝ)
  let Penalty : ℝ :=
    SOptLib.expectation S.P
      (fun ω =>
        S.τ t / (2 * S.Lcomp (S.sample t ω)) *
          S.dualNorm
            (S.gradF (S.sample t ω)
                (S.positiveEtaBlockIterate hη t ω (S.sample t ω)) -
              S.gradF (S.sample t ω)
                (S.positiveEtaBlockIterate hη (t - 1) ω (S.sample t ω))) ^ 2)
  let AuxLeft : ℝ :=
    SOptLib.expectation S.P
      (fun ω =>
        (1 + S.τ t) * (Fintype.card ι : ℝ)⁻¹ *
            Finset.sum Finset.univ
              (fun i =>
                S.f i
                  (S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
                    ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i))) -
          S.fAvg x)
  let AuxRight : ℝ :=
    SOptLib.expectation S.P
      (fun ω =>
        S.τ t * (Fintype.card ι : ℝ)⁻¹ *
            Finset.sum Finset.univ
              (fun i => S.f i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) +
          (Fintype.card ι : ℝ)⁻¹ *
            Finset.sum Finset.univ
              (fun i =>
                ⟪S.positiveEtaXIterate hη t ω - x,
                  S.auxiliaryGradient t (S.positiveEtaXIterate hη t ω)
                    (S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i⟫_ℝ) -
          S.τ t * (Fintype.card ι : ℝ)⁻¹ *
            Finset.sum Finset.univ
              (fun i =>
                (1 / (2 * S.Lcomp i)) *
                  S.dualNorm
                    (S.gradF i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i) -
                      S.gradF i
                        (S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
                          ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i))) ^ 2))
  have haux_source : AuxLeft ≤ AuxRight := by
    simpa [AuxLeft, AuxRight] using haux_expected
  have hleft_transport :
      AuxLeft =
        (1 + S.τ t) * Curr -
          ((1 + S.τ t) * (m - 1) * m⁻¹) * Prev -
          S.fAvg x := by
    let AuxF : ι → BlockSamplePath ι → ℝ := fun i ω =>
      S.f i
        (S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
          ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i))
    let PrevF : ι → BlockSamplePath ι → ℝ := fun i ω =>
      S.f i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)
    have hAuxF_int :
        ∀ i ∈ (Finset.univ : Finset ι), Integrable (AuxF i) S.P := by
      intro i _hi
      exact S.positiveEta_strictPast_payload_integrable hη ht
        (fun xNext prev => S.f i (S.auxiliaryPoint t xNext (prev.blockX i)))
    have hAux_sum :
        SOptLib.expectation S.P
            (fun ω => Finset.sum Finset.univ (fun i => AuxF i ω)) =
          Finset.sum Finset.univ (fun i => SOptLib.expectation S.P (AuxF i)) := by
      unfold SOptLib.expectation
      rw [MeasureTheory.integral_finset_sum Finset.univ hAuxF_int]
    have hAux_components :
        Finset.sum Finset.univ (fun i => SOptLib.expectation S.P (AuxF i)) =
          m * Curr - (m - 1) * Prev := by
      calc
        Finset.sum Finset.univ (fun i => SOptLib.expectation S.P (AuxF i)) =
            Finset.sum Finset.univ
              (fun i =>
                (Fintype.card ι : ℝ) *
                    SOptLib.expectation S.P
                      (fun ω => S.f i (S.positiveEtaBlockIterate hη t ω i)) -
                  ((Fintype.card ι : ℝ) - 1) *
                    SOptLib.expectation S.P (PrevF i)) := by
                refine Finset.sum_congr rfl ?_
                intro i _hi
                have hi := hcomponent_value i
                simpa [AuxF, PrevF] using hi
          _ = m * Curr - (m - 1) * Prev := by
                rw [Finset.sum_sub_distrib]
                rw [← Finset.mul_sum, ← Finset.mul_sum]
                simp [Curr, Prev, PrevF, m, positiveEtaBlockIterate]
    have hleft_expectation :
        AuxLeft =
          (1 + S.τ t) * m⁻¹ *
              Finset.sum Finset.univ (fun i => SOptLib.expectation S.P (AuxF i)) -
            S.fAvg x := by
      haveI : IsProbabilityMeasure S.P := by
        unfold Setup.P uniformBlockStreamLaw
        infer_instance
      have hsum_int :
          Integrable (fun ω => Finset.sum Finset.univ (fun i => AuxF i ω)) S.P :=
        integrable_finset_sum Finset.univ hAuxF_int
      unfold AuxLeft SOptLib.expectation
      rw [MeasureTheory.integral_sub]
      · rw [MeasureTheory.integral_const_mul]
        rw [MeasureTheory.integral_finset_sum Finset.univ hAuxF_int]
        rw [MeasureTheory.integral_const]
        simp [probReal_univ, AuxF, m]
      · exact hsum_int.const_mul ((1 + S.τ t) * (Fintype.card ι : ℝ)⁻¹)
      · exact integrable_const (S.fAvg x)
    rw [hleft_expectation, hAux_components]
    have hm_ne : m ≠ 0 := by
      dsimp [m]
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
    field_simp [hm_ne]
  have hright_transport :
      AuxRight = S.τ t * m⁻¹ * Prev + (YWindow + Table) - Penalty := by
    let PrevF : ι → BlockSamplePath ι → ℝ := fun i ω =>
      S.f i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)
    let AuxInner : ι → BlockSamplePath ι → ℝ := fun i ω =>
      ⟪S.positiveEtaXIterate hη t ω - x,
        S.auxiliaryGradient t (S.positiveEtaXIterate hη t ω)
          (S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i⟫_ℝ
    let YNew : ι → BlockSamplePath ι → ℝ := fun i ω =>
      ⟪S.positiveEtaXIterate hη t ω - x,
        S.positiveEtaYIterate hη t ω i⟫_ℝ
    let YCurr : ι → BlockSamplePath ι → ℝ := fun i ω =>
      ⟪S.positiveEtaXIterate hη t ω - x,
        S.positiveEtaYIterate hη (t - 1) ω i⟫_ℝ
    let YDiff : ι → BlockSamplePath ι → ℝ := fun i ω =>
      ⟪S.positiveEtaXIterate hη t ω - x,
        S.positiveEtaYIterate hη (t - 1) ω i -
          S.positiveEtaYIterate hη (t - 2) ω i⟫_ℝ
    let AuxGapRev : ι → BlockSamplePath ι → ℝ := fun i ω =>
      S.dualNorm
        (S.gradF i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i) -
          S.gradF i
            (S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
              ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i))) ^ 2
    let AuxGap : ι → BlockSamplePath ι → ℝ := fun i ω =>
      S.dualNorm
        (S.gradF i
            (S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
              ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) -
          S.gradF i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) ^ 2
    let CurrGap : ι → BlockSamplePath ι → ℝ := fun i ω =>
      S.dualNorm
        (S.gradF i (S.positiveEtaBlockIterate hη t ω i) -
          S.gradF i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) ^ 2
    let c : ℝ := S.α t * m⁻¹
    have hPrevF_int : ∀ i ∈ (Finset.univ : Finset ι), Integrable (PrevF i) S.P := by
      intro i _hi
      exact S.positiveEta_strictPast_payload_integrable hη ht
        (fun _xNext prev => S.f i (prev.blockX i))
    have hAuxInner_int : ∀ i ∈ (Finset.univ : Finset ι), Integrable (AuxInner i) S.P := by
      intro i _hi
      exact S.positiveEta_strictPast_payload_integrable hη ht
        (fun xNext prev => ⟪xNext - x, S.auxiliaryGradient t xNext prev.blockX i⟫_ℝ)
    have hYNew_int : ∀ i ∈ (Finset.univ : Finset ι), Integrable (YNew i) S.P := by
      intro i _hi
      exact S.positiveEta_current_prev_payload_integrable hη t
        (G := fun curr _prev => ⟪curr.x - x, curr.yCurr i⟫_ℝ)
    have hYCurr_int : ∀ i ∈ (Finset.univ : Finset ι), Integrable (YCurr i) S.P := by
      intro i _hi
      exact S.positiveEta_strictPast_payload_integrable hη ht
        (fun xNext prev => ⟪xNext - x, prev.yCurr i⟫_ℝ)
    have hYDiff_int : ∀ i ∈ (Finset.univ : Finset ι), Integrable (YDiff i) S.P := by
      intro i _hi
      simpa [YDiff, positiveEtaYIterate,
        S.positiveEtaGeneratedProcess_yPrev_eq_yIterate_pred hη ht] using
        S.positiveEta_strictPast_payload_integrable hη ht
          (fun xNext prev => ⟪xNext - x, prev.yCurr i - prev.yPrev i⟫_ℝ)
    have hAuxGapRev_int :
        ∀ i ∈ (Finset.univ : Finset ι), Integrable (AuxGapRev i) S.P := by
      intro i _hi
      exact S.positiveEta_strictPast_payload_integrable hη ht
        (fun xNext prev =>
          S.dualNorm
            (S.gradF i (prev.blockX i) -
              S.gradF i (S.auxiliaryPoint t xNext (prev.blockX i))) ^ 2)
    have hAuxGap_int :
        ∀ i ∈ (Finset.univ : Finset ι), Integrable (AuxGap i) S.P := by
      intro i _hi
      exact S.positiveEta_strictPast_payload_integrable hη ht
        (fun xNext prev =>
          S.dualNorm
            (S.gradF i (S.auxiliaryPoint t xNext (prev.blockX i)) -
              S.gradF i (prev.blockX i)) ^ 2)
    have hCurrGap_int :
        ∀ i ∈ (Finset.univ : Finset ι), Integrable (CurrGap i) S.P := by
      intro i _hi
      exact S.positiveEta_current_prev_payload_integrable hη t
        (G := fun curr prev =>
          S.dualNorm (S.gradF i (curr.blockX i) - S.gradF i (prev.blockX i)) ^ 2)
    have hPrev_part :
        SOptLib.expectation S.P
            (fun ω => S.τ t * m⁻¹ * Finset.sum Finset.univ (fun i => PrevF i ω)) =
          S.τ t * m⁻¹ * Prev := by
      unfold SOptLib.expectation
      rw [MeasureTheory.integral_const_mul]
      rw [MeasureTheory.integral_finset_sum Finset.univ hPrevF_int]
      congr 1
    have hAux_part :
        SOptLib.expectation S.P
            (fun ω => m⁻¹ * Finset.sum Finset.univ (fun i => AuxInner i ω)) =
          m⁻¹ * Finset.sum Finset.univ
            (fun i => SOptLib.expectation S.P (AuxInner i)) := by
      unfold SOptLib.expectation
      rw [MeasureTheory.integral_const_mul]
      rw [MeasureTheory.integral_finset_sum Finset.univ hAuxInner_int]
    have hYnew_sum :
        Finset.sum Finset.univ (fun i => SOptLib.expectation S.P (YNew i)) =
          m⁻¹ *
              Finset.sum Finset.univ
                (fun i => SOptLib.expectation S.P (AuxInner i)) +
            (1 - m⁻¹) *
              Finset.sum Finset.univ
                (fun i => SOptLib.expectation S.P (YCurr i)) := by
      calc
        Finset.sum Finset.univ (fun i => SOptLib.expectation S.P (YNew i)) =
            Finset.sum Finset.univ
              (fun i =>
                m⁻¹ * SOptLib.expectation S.P (AuxInner i) +
                  (1 - m⁻¹) * SOptLib.expectation S.P (YCurr i)) := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              simpa [YNew, AuxInner, YCurr, m, positiveEtaYIterate] using
                hyinner_source i
        _ =
          m⁻¹ *
              Finset.sum Finset.univ
                (fun i => SOptLib.expectation S.P (AuxInner i)) +
            (1 - m⁻¹) *
              Finset.sum Finset.univ
                (fun i => SOptLib.expectation S.P (YCurr i)) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hYWindow_split :
        YWindow =
          Finset.sum Finset.univ (fun i => SOptLib.expectation S.P (YNew i)) -
            Finset.sum Finset.univ (fun i => SOptLib.expectation S.P (YCurr i)) -
            c * Finset.sum Finset.univ (fun i => SOptLib.expectation S.P (YDiff i)) := by
      let W : ι → BlockSamplePath ι → ℝ := fun i ω =>
        YNew i ω - YCurr i ω - c * YDiff i ω
      have hpoint :
          (fun ω =>
            Finset.sum Finset.univ
              (fun i =>
                ⟪S.positiveEtaXIterate hη t ω - x,
                  (S.positiveEtaYIterate hη t ω i -
                    S.positiveEtaYIterate hη (t - 1) ω i) -
                    (S.α t / (Fintype.card ι : ℝ)) •
                      (S.positiveEtaYIterate hη (t - 1) ω i -
                        S.positiveEtaYIterate hη (t - 2) ω i)⟫_ℝ)) =
            fun ω => Finset.sum Finset.univ (fun i => W i ω) := by
        funext ω
        refine Finset.sum_congr rfl ?_
        intro i _hi
        simp [W, YNew, YCurr, YDiff, c, m, div_eq_mul_inv,
          inner_sub_right, inner_smul_right]
      calc
        YWindow =
            SOptLib.expectation S.P
              (fun ω => Finset.sum Finset.univ (fun i => W i ω)) := by
              unfold YWindow
              rw [hpoint]
        _ =
          Finset.sum Finset.univ (fun i => SOptLib.expectation S.P (YNew i)) -
            Finset.sum Finset.univ (fun i => SOptLib.expectation S.P (YCurr i)) -
            c * Finset.sum Finset.univ (fun i => SOptLib.expectation S.P (YDiff i)) := by
              simpa [W, smul_eq_mul, SOptLib.expectation_def] using
                expectation_finset_sum_sub_sub_const_smul_eq
                  (μ := S.P) (s := (Finset.univ : Finset ι))
                  (YNew := YNew) (YCurr := YCurr) (YDiff := YDiff) (c := c)
                  hYNew_int hYCurr_int hYDiff_int
    have htable_final :
        Table =
          m⁻¹ *
              Finset.sum Finset.univ
                (fun i => SOptLib.expectation S.P (YCurr i)) +
            c *
              Finset.sum Finset.univ
                (fun i => SOptLib.expectation S.P (YDiff i)) := by
      simpa [Table, YCurr, YDiff, c, m, positiveEtaYIterate,
        S.positiveEtaGeneratedProcess_yPrev_eq_yIterate_pred hη ht] using
        htable_source
    have hYTable :
        m⁻¹ * Finset.sum Finset.univ
            (fun i => SOptLib.expectation S.P (AuxInner i)) =
          YWindow + Table := by
      rw [hYWindow_split, htable_final, hYnew_sum]
      ring
    have hgap_each : ∀ i,
        SOptLib.expectation S.P (AuxGapRev i) =
          m * SOptLib.expectation S.P (CurrGap i) := by
      intro i
      have hrev :
          SOptLib.expectation S.P (AuxGapRev i) =
            SOptLib.expectation S.P (AuxGap i) := by
        refine congrArg (SOptLib.expectation S.P) ?_
        funext ω
        simpa [AuxGapRev, AuxGap] using
          (S.dualNorm_sq_sub_comm
            (S.gradF i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i))
            (S.gradF i
              (S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
                ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i))))
      calc
        SOptLib.expectation S.P (AuxGapRev i) =
            SOptLib.expectation S.P (AuxGap i) := hrev
        _ = m * SOptLib.expectation S.P (CurrGap i) := by
            simpa [AuxGap, CurrGap, m, positiveEtaBlockIterate] using hgap_value i
    have hGap_part :
        SOptLib.expectation S.P
            (fun ω =>
              S.τ t * m⁻¹ *
                Finset.sum Finset.univ
                  (fun i => (1 / (2 * S.Lcomp i)) * AuxGapRev i ω)) =
          Penalty := by
      let GapWeighted : ι → BlockSamplePath ι → ℝ := fun i ω =>
        (1 / (2 * S.Lcomp i)) * AuxGapRev i ω
      have hGapWeighted_int :
          ∀ i ∈ (Finset.univ : Finset ι), Integrable (GapWeighted i) S.P := by
        intro i hi
        exact (hAuxGapRev_int i hi).const_mul (1 / (2 * S.Lcomp i))
      have hm_ne : m ≠ 0 := by
        dsimp [m]
        exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
      calc
        SOptLib.expectation S.P
            (fun ω =>
              S.τ t * m⁻¹ *
                Finset.sum Finset.univ
                  (fun i => (1 / (2 * S.Lcomp i)) * AuxGapRev i ω)) =
            S.τ t * m⁻¹ *
              Finset.sum Finset.univ
                (fun i => SOptLib.expectation S.P (GapWeighted i)) := by
              unfold SOptLib.expectation
              rw [MeasureTheory.integral_const_mul]
              rw [MeasureTheory.integral_finset_sum Finset.univ hGapWeighted_int]
        _ =
            S.τ t * m⁻¹ *
              Finset.sum Finset.univ
                (fun i =>
                  (1 / (2 * S.Lcomp i)) *
                    SOptLib.expectation S.P (AuxGapRev i)) := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro i hi
              unfold SOptLib.expectation GapWeighted
              rw [MeasureTheory.integral_const_mul]
        _ =
            S.τ t * m⁻¹ *
              Finset.sum Finset.univ
                (fun i =>
                  (1 / (2 * S.Lcomp i)) *
                    (m * SOptLib.expectation S.P (CurrGap i))) := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro i _hi
              rw [hgap_each i]
        _ =
            Finset.sum Finset.univ
              (fun i =>
                S.τ t / (2 * S.Lcomp i) *
                  SOptLib.expectation S.P (CurrGap i)) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro i _hi
              field_simp [hm_ne]
        _ = Penalty := by
              simpa [Penalty, CurrGap, positiveEtaBlockIterate] using hpenalty_value
    let PrevPart : BlockSamplePath ι → ℝ := fun ω =>
      S.τ t * m⁻¹ * Finset.sum Finset.univ (fun i => PrevF i ω)
    let AuxPart : BlockSamplePath ι → ℝ := fun ω =>
      m⁻¹ * Finset.sum Finset.univ (fun i => AuxInner i ω)
    let GapPart : BlockSamplePath ι → ℝ := fun ω =>
      S.τ t * m⁻¹ *
        Finset.sum Finset.univ
          (fun i => (1 / (2 * S.Lcomp i)) * AuxGapRev i ω)
    have hPrevPart_int : Integrable PrevPart S.P := by
      exact (integrable_finset_sum Finset.univ hPrevF_int).const_mul (S.τ t * m⁻¹)
    have hAuxPart_int : Integrable AuxPart S.P := by
      exact (integrable_finset_sum Finset.univ hAuxInner_int).const_mul m⁻¹
    have hGapPart_int : Integrable GapPart S.P := by
      exact (integrable_finset_sum Finset.univ
        (fun i hi => (hAuxGapRev_int i hi).const_mul (1 / (2 * S.Lcomp i)))).const_mul
          (S.τ t * m⁻¹)
    have hAuxRight_split :
        AuxRight =
          SOptLib.expectation S.P PrevPart +
            SOptLib.expectation S.P AuxPart -
            SOptLib.expectation S.P GapPart := by
      unfold AuxRight SOptLib.expectation
      calc
        (∫ ω,
          S.τ t * (Fintype.card ι : ℝ)⁻¹ *
              Finset.sum Finset.univ
                (fun i => S.f i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) +
            (Fintype.card ι : ℝ)⁻¹ *
              Finset.sum Finset.univ
                (fun i =>
                  ⟪S.positiveEtaXIterate hη t ω - x,
                    S.auxiliaryGradient t (S.positiveEtaXIterate hη t ω)
                      (S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i⟫_ℝ) -
            S.τ t * (Fintype.card ι : ℝ)⁻¹ *
              Finset.sum Finset.univ
                (fun i =>
                  (1 / (2 * S.Lcomp i)) *
                    S.dualNorm
                      (S.gradF i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i) -
                        S.gradF i
                          (S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
                            ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i))) ^ 2) ∂S.P)
            =
          ∫ ω, PrevPart ω + AuxPart ω - GapPart ω ∂S.P := by
            rfl
        _ =
          (∫ ω, PrevPart ω + AuxPart ω ∂S.P) -
            ∫ ω, GapPart ω ∂S.P := by
            rw [MeasureTheory.integral_sub]
            · exact hPrevPart_int.add hAuxPart_int
            · exact hGapPart_int
        _ =
          ((∫ ω, PrevPart ω ∂S.P) + ∫ ω, AuxPart ω ∂S.P) -
            ∫ ω, GapPart ω ∂S.P := by
            rw [MeasureTheory.integral_add hPrevPart_int hAuxPart_int]
    calc
      AuxRight =
          SOptLib.expectation S.P PrevPart +
            SOptLib.expectation S.P AuxPart -
            SOptLib.expectation S.P GapPart := hAuxRight_split
      _ =
          S.τ t * m⁻¹ * Prev +
            (m⁻¹ *
              Finset.sum Finset.univ
                (fun i => SOptLib.expectation S.P (AuxInner i))) -
            Penalty := by
          rw [hPrev_part, hAux_part, hGap_part]
      _ = S.τ t * m⁻¹ * Prev + (YWindow + Table) - Penalty := by
          rw [hYTable]
  have hm_ne : m ≠ 0 := by
    dsimp [m]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
  have hcoef :
      (1 + S.τ t) * (m - 1) * m⁻¹ + S.τ t * m⁻¹ =
        (1 + S.τ t) - m⁻¹ := by
    field_simp [hm_ne]
    ring
  have hcoef_mul :
      ((1 + S.τ t) * (m - 1) * m⁻¹) * Prev +
          (S.τ t * m⁻¹) * Prev =
        ((1 + S.τ t) - m⁻¹) * Prev := by
    rw [← add_mul, hcoef]
  have haux_normalized :
      (1 + S.τ t) * Curr -
          ((1 + S.τ t) * (m - 1) * m⁻¹) * Prev -
          S.fAvg x ≤
        S.τ t * m⁻¹ * Prev + (YWindow + Table) - Penalty := by
    simpa [hleft_transport, hright_transport] using haux_source
  have hscalar :
      (1 + S.τ t) * Curr - S.fAvg x ≤
        ((1 + S.τ t) - m⁻¹) * Prev + YWindow + Table - Penalty := by
    nlinarith [haux_normalized, hcoef_mul]
  simpa [Curr, Prev, YWindow, Table, Penalty, m, positiveEtaBlockIterate] using hscalar

private theorem component_and_prox_scalar_combine
    {A f C G T P N B : ℝ}
    (hcomp : A - f ≤ C + G + T - P) (hprox : T + N ≤ B) :
    A + (N - f) ≤ C + G + B - P := by
  exact add_sub_le_of_sub_le_add_add_sub_and_add_le hcomp hprox

/-- Scalar y-table form of Lemma 5.9 with the strict-past payload `x^t - x`.

Aligns with Lan Proposition 5.6 proof step 6: the current block update is
averaged conditionally while the payload is already determined before sampling
`i_t`. Candidate audit: checked local
`ConditionalBlockExpectation_Lemma_5_9_positive_domain`,
`conditionalExpectationEq_two_branch_of_fresh_uniform`, and
`lemma59_block_inner_expectation_relation`; the existing scalar helper fixes the
second argument to `∇f_i(x)`, so it does not cover this y-table payload. -/
private theorem positiveEta_y_inner_expectation_auxiliary_gradient_relation
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 1 ≤ t) (i : ι) (x : E) :
    SOptLib.expectation S.P
        (fun ω =>
          ⟪S.positiveEtaXIterate hη t ω - x,
            S.positiveEtaYIterate hη t ω i⟫_ℝ) =
      SOptLib.expectation S.P
        (fun ω =>
          (Fintype.card ι : ℝ)⁻¹ *
              ⟪S.positiveEtaXIterate hη t ω - x,
                S.auxiliaryGradient t (S.positiveEtaXIterate hη t ω)
                  (S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i⟫_ℝ +
            (1 - (Fintype.card ι : ℝ)⁻¹) *
              ⟪S.positiveEtaXIterate hη t ω - x,
                (S.positiveEtaGeneratedProcess hη (t - 1) ω).yCurr i⟫_ℝ) := by
  classical
  let A : BlockSamplePath ι → ℝ := fun ω =>
    ⟪S.positiveEtaXIterate hη t ω - x,
      S.auxiliaryGradient t (S.positiveEtaXIterate hη t ω)
        (S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i⟫_ℝ
  let B : BlockSamplePath ι → ℝ := fun ω =>
    ⟪S.positiveEtaXIterate hη t ω - x,
      (S.positiveEtaGeneratedProcess hη (t - 1) ω).yCurr i⟫_ℝ
  have hA_int : Integrable A S.P :=
    S.positiveEta_strictPast_payload_integrable hη ht
      (fun xNext prev =>
        ⟪xNext - x, S.auxiliaryGradient t xNext prev.blockX i⟫_ℝ)
  have hB_int : Integrable B S.P :=
    S.positiveEta_strictPast_payload_integrable hη ht
      (fun xNext prev => ⟪xNext - x, prev.yCurr i⟫_ℝ)
  have hA_past :
      ∀ ⦃ω ω' : BlockSamplePath ι⦄,
        (fun r : Fin (t - 1) => S.sample (1 + r.1) ω) =
          (fun r : Fin (t - 1) => S.sample (1 + r.1) ω') →
        A ω = A ω' := by
    intro ω ω' hwin
    have hxNext := S.positiveEtaXIterate_eq_of_strictPastWindow_eq hη ht hwin
    have hprev := S.positiveEtaGeneratedProcess_eq_of_sampleWindow_eq hη (t - 1) hwin
    simp [A, hxNext, hprev]
  have hB_past :
      ∀ ⦃ω ω' : BlockSamplePath ι⦄,
        (fun r : Fin (t - 1) => S.sample (1 + r.1) ω) =
          (fun r : Fin (t - 1) => S.sample (1 + r.1) ω') →
        B ω = B ω' := by
    intro ω ω' hwin
    have hxNext := S.positiveEtaXIterate_eq_of_strictPastWindow_eq hη ht hwin
    have hprev := S.positiveEtaGeneratedProcess_eq_of_sampleWindow_eq hη (t - 1) hwin
    simp [B, hxNext, hprev]
  rcases S.positiveEtaGeneratedProcess_branch_identities hη ht i with
    ⟨hy_branch, _hx_branch, _hf_branch, _hnorm_branch⟩
  have hmain :
      (fun ω =>
        ⟪S.positiveEtaXIterate hη t ω - x,
          S.positiveEtaYIterate hη t ω i⟫_ℝ) =
        fun ω => if S.sample t ω = i then A ω else B ω := by
    funext ω
    rw [hy_branch ω]
    by_cases hsample : S.sample t ω = i <;> simp [A, B, hsample]
  have hce := S.conditionalExpectationEq_two_branch_of_fresh_uniform
    (t := t) ht i A B hA_int hB_int hA_past hB_past
  have hce' :
      conditionalExpectationEq S.P (S.paperStrictPastSigma t)
        (fun ω =>
          ⟪S.positiveEtaXIterate hη t ω - x,
            S.positiveEtaYIterate hη t ω i⟫_ℝ)
        (fun ω =>
          (Fintype.card ι : ℝ)⁻¹ *
              ⟪S.positiveEtaXIterate hη t ω - x,
                S.auxiliaryGradient t (S.positiveEtaXIterate hη t ω)
                  (S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i⟫_ℝ +
            (1 - (Fintype.card ι : ℝ)⁻¹) *
              ⟪S.positiveEtaXIterate hη t ω - x,
                (S.positiveEtaGeneratedProcess hη (t - 1) ω).yCurr i⟫_ℝ) := by
    simpa [hmain, A, B, smul_eq_mul] using hce
  exact conditionalExpectationEq_expectation_eq hce'

/-- Fixed-time expected one-step RGEM inequality used in Eq. (5.2.73).

Aligns with Lan Proposition 5.6 proof step 6, immediately before multiplying
by `θ_t` and summing. Candidate audit: checked the local proved ingredients
`proposition56_prox_step_expectation_5_2_71_positive_domain`,
`proposition56_sampled_smoothness_gap_expectation_5_2_73_positive_domain`, and
`proposition56_one_step_source_ingredients_5_2_73_positive_domain`; SOptLib
searches for finite-sum expectation lifts (`expectation_le_sum_expectation_of_ae_le_finset_sum`,
`integral_finset_sum_le_of_pointwise_finset_sum_le`) do not state this
RGEM-specific auxiliary-point/prox algebra. -/
private theorem proposition56_fixed_time_expected_one_step_5_2_73_positive_domain
    (hη : S.PositiveEtaDomain) {t : ℕ} (ht : 1 ≤ t) {x : E} (hx : x ∈ S.X) :
    (1 + S.τ t) *
        Finset.sum Finset.univ
          (fun i =>
            SOptLib.expectation S.P
              (fun ω => S.f i (S.positiveEtaBlockIterate hη t ω i))) +
      SOptLib.expectation S.P
        (fun ω => S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.psi x) ≤
      ((1 + S.τ t) - (Fintype.card ι : ℝ)⁻¹) *
          Finset.sum Finset.univ
            (fun i =>
              SOptLib.expectation S.P
                (fun ω => S.f i (S.positiveEtaBlockIterate hη (t - 1) ω i))) +
        SOptLib.expectation S.P
          (fun ω =>
            Finset.sum Finset.univ
              (fun i =>
                ⟪S.positiveEtaXIterate hη t ω - x,
                  (S.positiveEtaYIterate hη t ω i -
                    S.positiveEtaYIterate hη (t - 1) ω i) -
                    (S.α t / (Fintype.card ι : ℝ)) •
                      (S.positiveEtaYIterate hη (t - 1) ω i -
                        S.positiveEtaYIterate hη (t - 2) ω i)⟫_ℝ)) +
        (S.η t *
            SOptLib.expectation S.P
              (fun ω => S.V (S.positiveEtaXIterate hη (t - 1) ω) x) -
          (S.μ + S.η t) *
            SOptLib.expectation S.P
              (fun ω => S.V (S.positiveEtaXIterate hη t ω) x) -
          S.η t *
            SOptLib.expectation S.P
              (fun ω =>
                S.V (S.positiveEtaXIterate hη (t - 1) ω)
                  (S.positiveEtaXIterate hη t ω))) -
        SOptLib.expectation S.P
          (fun ω =>
            S.τ t / (2 * S.Lcomp (S.sample t ω)) *
              S.dualNorm
                (S.gradF (S.sample t ω)
                    (S.positiveEtaBlockIterate hη t ω (S.sample t ω)) -
                  S.gradF (S.sample t ω)
                    (S.positiveEtaBlockIterate hη (t - 1) ω (S.sample t ω))) ^ 2) := by
  classical
  have hprox :=
    S.proposition56_prox_step_expectation_5_2_71_positive_domain
      hη (t := t) ht hx
  have hsmooth : ∀ i,
      (1 / (2 * S.Lcomp i)) *
          ((Fintype.card ι : ℝ) *
            SOptLib.expectation S.P
              (fun ω =>
                S.dualNorm
                  (S.gradF i (S.positiveEtaBlockIterate hη t ω i) -
                    S.gradF i
                      ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) ^ 2)) ≤
        ((Fintype.card ι : ℝ) *
            SOptLib.expectation S.P
              (fun ω => S.f i (S.positiveEtaBlockIterate hη t ω i)) -
          ((Fintype.card ι : ℝ) - 1) *
            SOptLib.expectation S.P
              (fun ω => S.f i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i))) -
          SOptLib.expectation S.P
            (fun ω => S.f i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i)) -
          SOptLib.expectation S.P
            (fun ω =>
              ⟪S.gradF i ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i),
                S.auxiliaryPoint t (S.positiveEtaXIterate hη t ω)
                    ((S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i) -
                  (S.positiveEtaGeneratedProcess hη (t - 1) ω).blockX i⟫_ℝ) := by
    intro i
    exact S.proposition56_sampled_smoothness_gap_expectation_5_2_73_positive_domain
      hη (t := t) ht i
  have hstep_source := fun ω =>
    S.proposition56_one_step_source_ingredients_5_2_73_positive_domain
      hη ht ω hx
  have hcond_source := fun i =>
    S.ConditionalBlockExpectation_Lemma_5_9_positive_domain hη ht i
  have hgrad_extrapolation_source :=
    S.GradientExtrapolationDefinition_Eq_5_2_49
  have hpenalty :=
    S.positiveEta_sampled_smoothness_penalty_expectation_sum_eq hη (t := t) ht
  have hnu_shift :=
    S.positiveEta_nu_psi_expectation_shift hη (t := t) ht x
  have hbreg_linear :=
    S.positiveEta_bregman_prox_expectation_linear hη (t := t) ht x
  have hprox_sep :
      SOptLib.expectation S.P
        (fun ω =>
          let prev : State ι E := S.positiveEtaGeneratedProcess hη (t - 1) ω
          let yTilde : ι → E := fun i => SOptLib.extrapolatedPoint (S.α t) ((prev).yCurr i) ((prev).yPrev i)
          let xNext : E := S.positiveEtaXIterate hη t ω
          ⟪xNext - x, tableAverage yTilde⟫_ℝ) +
        SOptLib.expectation S.P
          (fun ω => S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.μ * S.ν x) ≤
      S.η t *
          SOptLib.expectation S.P
            (fun ω => S.V (S.positiveEtaXIterate hη (t - 1) ω) x) -
        (S.μ + S.η t) *
          SOptLib.expectation S.P
            (fun ω => S.V (S.positiveEtaXIterate hη t ω) x) -
        S.η t *
          SOptLib.expectation S.P
            (fun ω =>
              S.V (S.positiveEtaXIterate hη (t - 1) ω)
                (S.positiveEtaXIterate hη t ω)) := by
    have hleft :=
      S.positiveEta_prox_left_expectation_linear hη (t := t) ht x
    have hbreg_linear' :
        SOptLib.expectation S.P
          (fun ω =>
            let prev : State ι E := S.positiveEtaGeneratedProcess hη (t - 1) ω
            let xNext : E := S.positiveEtaXIterate hη t ω
            S.η t * S.V prev.x x - (S.μ + S.η t) * S.V xNext x -
              S.η t * S.V prev.x xNext) =
        S.η t *
            SOptLib.expectation S.P
              (fun ω => S.V (S.positiveEtaXIterate hη (t - 1) ω) x) -
          (S.μ + S.η t) *
            SOptLib.expectation S.P
              (fun ω => S.V (S.positiveEtaXIterate hη t ω) x) -
          S.η t *
            SOptLib.expectation S.P
              (fun ω =>
                S.V (S.positiveEtaXIterate hη (t - 1) ω)
                  (S.positiveEtaXIterate hη t ω)) := by
      simpa [positiveEtaXIterate] using hbreg_linear
    rw [hleft, hbreg_linear'] at hprox
    exact hprox
  -- Remaining fixed-time blocker: combine `hprox` and `hsmooth` with the
  -- auxiliary-point identity, `ψ = fAvg + μν`, and the sampled-block
  -- expectation identities to obtain the printed expected one-step inequality.
  let A : ℝ :=
    (1 + S.τ t) *
      Finset.sum Finset.univ
        (fun i =>
          SOptLib.expectation S.P
            (fun ω => S.f i (S.positiveEtaBlockIterate hη t ω i)))
  let C : ℝ :=
    ((1 + S.τ t) - (Fintype.card ι : ℝ)⁻¹) *
      Finset.sum Finset.univ
        (fun i =>
          SOptLib.expectation S.P
            (fun ω => S.f i (S.positiveEtaBlockIterate hη (t - 1) ω i)))
  let G : ℝ :=
    SOptLib.expectation S.P
      (fun ω =>
        Finset.sum Finset.univ
          (fun i =>
            ⟪S.positiveEtaXIterate hη t ω - x,
              (S.positiveEtaYIterate hη t ω i -
                S.positiveEtaYIterate hη (t - 1) ω i) -
                (S.α t / (Fintype.card ι : ℝ)) •
                  (S.positiveEtaYIterate hη (t - 1) ω i -
                    S.positiveEtaYIterate hη (t - 2) ω i)⟫_ℝ))
  let T : ℝ :=
    SOptLib.expectation S.P
      (fun ω =>
        let prev : State ι E := S.positiveEtaGeneratedProcess hη (t - 1) ω
        let yTilde : ι → E := fun i => SOptLib.extrapolatedPoint (S.α t) ((prev).yCurr i) ((prev).yPrev i)
        let xNext : E := S.positiveEtaXIterate hη t ω
        ⟪xNext - x, tableAverage yTilde⟫_ℝ)
  let N : ℝ :=
    SOptLib.expectation S.P
      (fun ω => S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.μ * S.ν x)
  let B : ℝ :=
    S.η t *
        SOptLib.expectation S.P
          (fun ω => S.V (S.positiveEtaXIterate hη (t - 1) ω) x) -
      (S.μ + S.η t) *
        SOptLib.expectation S.P
          (fun ω => S.V (S.positiveEtaXIterate hη t ω) x) -
      S.η t *
        SOptLib.expectation S.P
          (fun ω =>
            S.V (S.positiveEtaXIterate hη (t - 1) ω)
              (S.positiveEtaXIterate hη t ω))
  let P : ℝ :=
    SOptLib.expectation S.P
      (fun ω =>
        S.τ t / (2 * S.Lcomp (S.sample t ω)) *
          S.dualNorm
            (S.gradF (S.sample t ω)
                (S.positiveEtaBlockIterate hη t ω (S.sample t ω)) -
              S.gradF (S.sample t ω)
                (S.positiveEtaBlockIterate hη (t - 1) ω (S.sample t ω))) ^ 2)
  have hcomponent_source :
      A - S.fAvg x ≤ C + G + T - P := by
    simpa [A, C, G, T, P] using
      S.proposition56_fixed_time_component_assembly_5_2_73_positive_domain
        hη (t := t) ht hx
  have hprox' : T + N ≤ B := by
    simpa [T, N, B] using hprox_sep
  have hnu' :
      SOptLib.expectation S.P
        (fun ω => S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.psi x) =
      N - S.fAvg x := by
    simpa [N] using hnu_shift
  rw [hnu']
  change A + (N - S.fAvg x) ≤ C + G + B - P
  exact component_and_prox_scalar_combine hcomponent_source hprox'

/-- Summed expected one-step inequality, Eq. (5.2.73).

Aligns with Lan Proposition 5.6 proof step 7: multiply the fixed-time expected
one-step inequality by the nonnegative output weight and sum over
`outputWindow k`. Candidate audit: the only SOptLib/Mathlib candidates were
generic finite-sum monotonicity tools (`Finset.sum_le_sum`,
`expectation_le_sum_expectation_of_ae_le_finset_sum`); no existing theorem
states this RGEM-specific finite-window bridge. -/
private theorem proposition56_summed_one_step_expectation_5_2_73_positive_domain
    (hη : S.PositiveEtaDomain) {k : ℕ} (hk : 1 ≤ k)
    {xStar : E} (hopt : S.IsOptimalSolution xStar)
    (hθ_pos : S.OutputWeightsPositive k) :
    Finset.sum (outputWindow k)
        (fun t =>
          S.θ t *
            ((1 + S.τ t) *
                Finset.sum Finset.univ
                  (fun i =>
                    SOptLib.expectation S.P
                      (fun ω => S.f i (S.positiveEtaBlockIterate hη t ω i))) +
              SOptLib.expectation S.P
                (fun ω => S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.psi xStar))) ≤
      Finset.sum (outputWindow k)
        (fun t =>
          S.θ t *
            (((1 + S.τ t) - (Fintype.card ι : ℝ)⁻¹) *
                Finset.sum Finset.univ
                  (fun i =>
                    SOptLib.expectation S.P
                      (fun ω => S.f i (S.positiveEtaBlockIterate hη (t - 1) ω i))) +
              SOptLib.expectation S.P
                (fun ω =>
                  Finset.sum Finset.univ
                    (fun i =>
                      ⟪S.positiveEtaXIterate hη t ω - xStar,
                        (S.positiveEtaYIterate hη t ω i -
                          S.positiveEtaYIterate hη (t - 1) ω i) -
                          (S.α t / (Fintype.card ι : ℝ)) •
                            (S.positiveEtaYIterate hη (t - 1) ω i -
                              S.positiveEtaYIterate hη (t - 2) ω i)⟫_ℝ)) +
              (S.η t *
                  SOptLib.expectation S.P
                    (fun ω => S.V (S.positiveEtaXIterate hη (t - 1) ω) xStar) -
                (S.μ + S.η t) *
                  SOptLib.expectation S.P
                    (fun ω => S.V (S.positiveEtaXIterate hη t ω) xStar) -
                S.η t *
                  SOptLib.expectation S.P
                    (fun ω =>
                      S.V (S.positiveEtaXIterate hη (t - 1) ω)
                        (S.positiveEtaXIterate hη t ω))) -
              SOptLib.expectation S.P
                (fun ω =>
                  S.τ t / (2 * S.Lcomp (S.sample t ω)) *
                    S.dualNorm
                      (S.gradF (S.sample t ω)
                          (S.positiveEtaBlockIterate hη t ω (S.sample t ω)) -
                        S.gradF (S.sample t ω)
                          (S.positiveEtaBlockIterate hη (t - 1) ω (S.sample t ω))) ^ 2))) := by
  classical
  refine Finset.sum_le_sum ?_
  intro t htmem
  have ht : 1 ≤ t :=
    (Finset.mem_Icc.mp (by simpa [outputWindow] using htmem)).1
  have hstep :=
    S.proposition56_fixed_time_expected_one_step_5_2_73_positive_domain
      hη (t := t) ht hopt.1
  exact mul_le_mul_of_nonneg_left hstep (le_of_lt (hθ_pos t htmem))

/-- Reindex the accumulated previous-time residuals plus the terminal residual
as the paper's `outputWindow` sum.

Aligns with Lan Proposition 5.6 proof step 19, where the `t = 2..k`
previous-sample residuals are shifted to output indices `1..k-1` and the
terminal `k` residual is appended. Candidate audit: searched `reindex
outputWindow Icc previous sample stale gradient`; checked
`SOptLib.sum_positiveTimeOutputWindowTimes_eq_Icc`, `Finset.sum_bij`, and
`Finset.sum_Icc_succ_top`. The SOptLib output-window theorem is subtype-shaped
and the telescope lemmas target differences, so this local helper records the
literal predecessor-plus-terminal finite-sum identity needed for Eq. (5.2.75). -/
private theorem proposition56_outputWindow_predecessor_sum_add_terminal_eq
    {k : ℕ} (hk : 1 ≤ k) (F : ℕ → ℝ) :
    Finset.sum (Finset.Icc 2 k) (fun t => F (t - 1)) + F k =
      Finset.sum (outputWindow k) F := by
  classical
  induction k with
  | zero =>
      omega
  | succ k ih =>
      by_cases hk0 : k = 0
      · subst k
        simp [outputWindow]
      · have hk_pos : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk0)
        have hleft :
            Finset.sum (Finset.Icc 2 (k + 1)) (fun t => F (t - 1)) =
              Finset.sum (Finset.Icc 2 k) (fun t => F (t - 1)) + F k := by
          rw [Finset.sum_Icc_succ_top]
          · simp
          · omega
        have hright :
            Finset.sum (outputWindow (k + 1)) F =
              Finset.sum (outputWindow k) F + F (k + 1) := by
          rw [outputWindow, outputWindow, Finset.sum_Icc_succ_top]
          omega
        calc
          Finset.sum (Finset.Icc 2 (k + 1)) (fun t => F (t - 1)) + F (k + 1)
              = (Finset.sum (Finset.Icc 2 k) (fun t => F (t - 1)) + F k) +
                  F (k + 1) := by rw [hleft]
          _ = Finset.sum (outputWindow k) F + F (k + 1) := by rw [ih hk_pos]
          _ = Finset.sum (outputWindow (k + 1)) F := hright.symm

/-- Window decomposition of the sampled smoothness penalty into residual terms.

Aligns with Lan Proposition 5.6 proof step 13/PDF Eq. (5.2.74): the sampled
smoothness penalties over `1..k` are rewritten as the predecessor residuals
over `2..k` plus the terminal sampled residual. Candidate audit: searched
`5.2.74 sampled penalty predecessor terminal reindex` and
`sampled smoothness penalty y residual outputWindow`; existing usable pieces are
`positiveEta_sampled_smoothness_penalty_y_residual_eq` and
`proposition56_outputWindow_predecessor_sum_add_terminal_eq`, but no SOptLib or
target-file theorem stated their RGEM-specific composition. -/
private theorem proposition56_sampled_penalty_y_residual_window_eq
    (hη : S.PositiveEtaDomain) {k : ℕ} (hk : 1 ≤ k) :
    Finset.sum (outputWindow k)
        (fun t =>
          S.θ t *
            SOptLib.expectation S.P
              (fun ω =>
                S.τ t / (2 * S.Lcomp (S.sample t ω)) *
                  S.dualNorm
                    (S.gradF (S.sample t ω)
                        (S.positiveEtaBlockIterate hη t ω (S.sample t ω)) -
                      S.gradF (S.sample t ω)
                        (S.positiveEtaBlockIterate hη (t - 1) ω (S.sample t ω))) ^ 2)) =
      Finset.sum (Finset.Icc 2 k)
          (fun t =>
            S.θ (t - 1) *
              SOptLib.expectation S.P
                (fun ω =>
                  S.τ (t - 1) / (2 * S.Lcomp (S.sample (t - 1) ω)) *
                    S.dualNorm
                      (S.positiveEtaYIterate hη (t - 1) ω (S.sample (t - 1) ω) -
                        S.gradF (S.sample (t - 1) ω)
                          (S.positiveEtaBlockIterate hη (t - 2) ω
                            (S.sample (t - 1) ω))) ^ 2)) +
        S.θ k *
          SOptLib.expectation S.P
            (fun ω =>
              S.τ k / (2 * S.Lcomp (S.sample k ω)) *
                S.dualNorm
                  (S.positiveEtaYIterate hη k ω (S.sample k ω) -
                    S.gradF (S.sample k ω)
                      (S.positiveEtaBlockIterate hη (k - 1) ω
                        (S.sample k ω))) ^ 2) := by
  classical
  let F : ℕ → ℝ := fun t =>
    S.θ t *
      SOptLib.expectation S.P
        (fun ω =>
          S.τ t / (2 * S.Lcomp (S.sample t ω)) *
            S.dualNorm
              (S.positiveEtaYIterate hη t ω (S.sample t ω) -
                S.gradF (S.sample t ω)
                  (S.positiveEtaBlockIterate hη (t - 1) ω (S.sample t ω))) ^ 2)
  have hleft :
      Finset.sum (outputWindow k)
          (fun t =>
            S.θ t *
              SOptLib.expectation S.P
                (fun ω =>
                  S.τ t / (2 * S.Lcomp (S.sample t ω)) *
                    S.dualNorm
                      (S.gradF (S.sample t ω)
                          (S.positiveEtaBlockIterate hη t ω (S.sample t ω)) -
                        S.gradF (S.sample t ω)
                          (S.positiveEtaBlockIterate hη (t - 1) ω (S.sample t ω))) ^ 2)) =
        Finset.sum (outputWindow k) F := by
    refine Finset.sum_congr rfl ?_
    intro t htmem
    have ht : 1 ≤ t :=
      (Finset.mem_Icc.mp (by simpa [outputWindow] using htmem)).1
    dsimp [F]
    rw [positiveEta_sampled_smoothness_penalty_y_residual_eq (S := S) hη ht]
  have hreindex :
      Finset.sum (Finset.Icc 2 k) (fun t => F (t - 1)) + F k =
        Finset.sum (outputWindow k) F :=
    proposition56_outputWindow_predecessor_sum_add_terminal_eq hk F
  rw [hleft, ← hreindex]
  dsimp [F]
  congr 1

/-- Scalar assembly pattern for Lan Proposition 5.6 Eq. (5.2.74).

This is the algebraic core after the source-specific telescopes have been
proved: the one-step window inequality, component endpoint equality, gradient
telescope, Bregman telescope, and sampled-penalty decomposition are combined
into the residual-plus-terminal form. Candidate audit: searched `scalar
residual telescope assembly component gradient bregman penalty`; SOptLib
contains generic recurrence telescopes such as
`finite_window_weighted_recurrence_telescope_with_tail_sums`, but none matches
this already-summed five-term rearrangement with a retained half-terminal
Bregman term. -/
private theorem proposition56_scalar_residual_5_2_74_assembly
    {α : Type*} [DecidableEq α] (s : Finset α)
    (A C G B Adj D N : α → ℝ)
    (terminalF initF initV terminalB gradTerminal gradAccum adjAccum penaltyAccum
      penaltyTerminal : ℝ)
    (hstep :
      Finset.sum s (fun t => A t + N t) ≤
        Finset.sum s (fun t => C t + G t + (B t - Adj t) - D t))
    (hcomponent :
      Finset.sum s (fun t => A t - C t) = terminalF - initF)
    (hgradient :
      Finset.sum s G = gradTerminal - gradAccum)
    (hbregman :
      Finset.sum s B ≤ initV - terminalB)
    (hpenalty :
      Finset.sum s D = penaltyAccum + penaltyTerminal)
    (hadj :
      Finset.sum s Adj = adjAccum) :
    terminalF + Finset.sum s N + terminalB / 2 ≤
      initF + initV +
        ((-gradAccum) - adjAccum - penaltyAccum) +
        (gradTerminal - terminalB / 2 - penaltyTerminal) := by
  exact
    finset_sum_add_half_le_of_aggregate_decompositions s A C G B Adj D N
      terminalF initF initV terminalB gradTerminal gradAccum adjAccum penaltyAccum
      penaltyTerminal hstep hcomponent hgradient hbregman hpenalty hadj

/-- Finite-sum algebra for the accumulated residual part of Lan Proposition 5.6.

This packages the mechanical passage from a per-time residual estimate to the
summed `2..k` residual estimate. Candidate audit: searched `Finset sum pointwise
inequality negative subtract` and `drop nonnegative subtracted term inequality`;
SOptLib hits such as `integral_finset_sum_residual_lift_le` and
`ae_finset_sum_residual_le_of_pointwise_balance` include probability residual
transport hypotheses, while this local helper is the pure scalar finite-sum
form needed after the expectations have already been formed. -/
private theorem proposition56_accumulated_residual_sum_le_of_pointwise
    {α : Type*} [DecidableEq α] (s : Finset α)
    (F P R : α → ℝ)
    (hpoint : ∀ t ∈ s, -F t - P t ≤ R t) :
    -Finset.sum s F - Finset.sum s P ≤ Finset.sum s R := by
  calc
    -Finset.sum s F - Finset.sum s P =
        Finset.sum s (fun t => -F t - P t) := by
          simp [Finset.sum_sub_distrib]
    _ ≤ Finset.sum s R :=
        Finset.sum_le_sum hpoint

/-- Nonnegativity of the accumulated adjacent Bregman residual in Proposition 5.6.

This is the source proof step that allows the extra `Adj` contribution from the
whole output window, including the `t = 1` term, to be discarded after it appears
with a minus sign. Candidate audit: searched `expected Bregman nonnegative V
lower bound integral nonnegative`; the closest SOptLib match was
`blockBregmanDivergence_nonneg_of_lower_bound`, while this helper specializes
the already-indexed positive-eta process and integrates the local
`S.V_lower_bound` statement. -/
private theorem proposition56_adj_window_nonneg_positive_domain
    {k : ℕ} (hη : S.PositiveEtaDomain)
    (hθ_pos : S.OutputWeightsPositive k) :
    0 ≤
      Finset.sum (outputWindow k)
        (fun t =>
          S.θ t *
            (S.η t *
              SOptLib.expectation S.P
                (fun ω =>
                  S.V (S.positiveEtaXIterate hη (t - 1) ω)
                    (S.positiveEtaXIterate hη t ω)))) := by
  classical
  refine Finset.sum_nonneg ?_
  intro t ht
  have ht_bounds : 1 ≤ t ∧ t ≤ k := by
    simpa [outputWindow] using (Finset.mem_Icc.mp ht)
  have hθt : 0 ≤ S.θ t := le_of_lt (hθ_pos t ht)
  have hηt : 0 ≤ S.η t := le_of_lt (hη t ht_bounds.1)
  have hVexp :
      0 ≤ SOptLib.expectation S.P
        (fun ω =>
          S.V (S.positiveEtaXIterate hη (t - 1) ω)
            (S.positiveEtaXIterate hη t ω)) := by
    dsimp [SOptLib.expectation]
    exact integral_nonneg (fun ω => by
      have hlow := S.V_lower_bound
        (S.positiveEtaXIterate_mem hη (t - 1) ω)
        (S.positiveEtaXIterate_mem hη t ω)
      have hsq : 0 ≤ (1 / 2 : ℝ) *
          S.primalNorm
            (S.positiveEtaXIterate hη t ω -
              S.positiveEtaXIterate hη (t - 1) ω) ^ 2 := by
        have hnormsq : 0 ≤ S.primalNorm
            (S.positiveEtaXIterate hη t ω -
              S.positiveEtaXIterate hη (t - 1) ω) ^ 2 :=
          sq_nonneg _
        nlinarith
      exact hsq.trans hlow)
  exact mul_nonneg hθt (mul_nonneg hηt hVexp)

/-- The adjacent-Bregman residual over `t = 2..k` is bounded by the full output window.

Aligns with Lan Proposition 5.6 proof steps 14--19: the residual absorption
uses only the `2..k` adjacent terms, while Eq. (5.2.74) carries the full
output-window `Adj` sum. Candidate audit: checked `Finset.sum_le_sum_of_subset_of_nonneg`
and the target helper `proposition56_adj_window_nonneg_positive_domain`; the
Mathlib lemma is the exact finite-sum order core, but this paper route needs
the RGEM `Adj` term's nonnegativity from `S.V_lower_bound` and positive output
weights. -/
private theorem proposition56_adj_Icc_le_outputWindow_positive_domain
    {k : ℕ} (hη : S.PositiveEtaDomain)
    (hθ_pos : S.OutputWeightsPositive k) :
    Finset.sum (Finset.Icc 2 k)
        (fun t =>
          S.θ t *
            (S.η t *
              SOptLib.expectation S.P
                (fun ω =>
                  S.V (S.positiveEtaXIterate hη (t - 1) ω)
                    (S.positiveEtaXIterate hη t ω)))) ≤
      Finset.sum (outputWindow k)
        (fun t =>
          S.θ t *
            (S.η t *
              SOptLib.expectation S.P
                (fun ω =>
                  S.V (S.positiveEtaXIterate hη (t - 1) ω)
                    (S.positiveEtaXIterate hη t ω)))) := by
  classical
  refine Finset.sum_le_sum_of_subset_of_nonneg ?hsubset ?hnonneg
  · intro t ht
    have ht_bounds := Finset.mem_Icc.mp ht
    rw [outputWindow]
    exact Finset.mem_Icc.mpr ⟨by omega, ht_bounds.2⟩
  · intro t ht _htnot
    have ht_bounds : 1 ≤ t ∧ t ≤ k := by
      simpa [outputWindow] using (Finset.mem_Icc.mp ht)
    have hθt : 0 ≤ S.θ t := le_of_lt (hθ_pos t ht)
    have hηt : 0 ≤ S.η t := le_of_lt (hη t ht_bounds.1)
    have hVexp :
        0 ≤ SOptLib.expectation S.P
          (fun ω =>
            S.V (S.positiveEtaXIterate hη (t - 1) ω)
              (S.positiveEtaXIterate hη t ω)) := by
      dsimp [SOptLib.expectation]
      exact integral_nonneg (fun ω => by
        have hlow := S.V_lower_bound
          (S.positiveEtaXIterate_mem hη (t - 1) ω)
          (S.positiveEtaXIterate_mem hη t ω)
        have hsq : 0 ≤ (1 / 2 : ℝ) *
            S.primalNorm
              (S.positiveEtaXIterate hη t ω -
                S.positiveEtaXIterate hη (t - 1) ω) ^ 2 := by
          have hnormsq : 0 ≤ S.primalNorm
              (S.positiveEtaXIterate hη t ω -
                S.positiveEtaXIterate hη (t - 1) ω) ^ 2 :=
            sq_nonneg _
          nlinarith
        exact hsq.trans hlow)
    exact mul_nonneg hθt (mul_nonneg hηt hVexp)

/-- Nonnegativity of the stale-gradient coefficient appearing in Eq. (5.2.75).

Aligns with Lan Proposition 5.6 proof step 19 after the residual terms have
been reindexed to the output window. Candidate audit: searched `stale RHS
coefficient nonnegative theta alpha eta outputWindow`; existing hits were the
generic output-weight nonnegativity predicate and the terminal coefficient
comparison, but no local theorem stated this exact `2 θ_t α_{t+1}/(mη_{t+1})`
coefficient positivity. -/
private theorem proposition56_stale_rhs_coefficient_nonneg_positive_domain
    {k t : ℕ} (hη : S.PositiveEtaDomain)
    (hθ_pos : S.OutputWeightsPositive k) (htmem : t ∈ outputWindow k) :
    0 ≤
      2 * S.θ t * S.α (t + 1) /
        ((Fintype.card ι : ℝ) * S.η (t + 1)) := by
  classical
  have hm_pos : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hη_pos : 0 < S.η (t + 1) :=
    hη (t + 1) (Nat.succ_pos t)
  have hθ_nonneg : 0 ≤ S.θ t := le_of_lt (hθ_pos t htmem)
  have hα_nonneg : 0 ≤ S.α (t + 1) :=
    (S.hparam_nonneg (t + 1)).1
  have hnum_nonneg : 0 ≤ 2 * S.θ t * S.α (t + 1) := by
    nlinarith
  have hden_nonneg : 0 ≤ (Fintype.card ι : ℝ) * S.η (t + 1) := by
    exact mul_nonneg (le_of_lt hm_pos) (le_of_lt hη_pos)
  exact div_nonneg hnum_nonneg hden_nonneg

set_option maxHeartbeats 800000

/-- Source-level residual inequality (5.2.75) for the positive-eta RGEM process.

This is Lan Proposition 5.6 proof steps 1--19, before inserting the stale-gradient
probability estimate. Candidate audit: searched `Proposition 5.6 residual
inequality Eq 5.2.75 positive eta Delta stale gradient`, checked the top hits
`S.ProxStepInequality_Eq_5_2_71`, `S.SmoothnessGradientGap_Lemma_5_8`, and
`S.ConditionalBlockExpectation_Lemma_5_9_positive_domain`, and scanned the
Lemma 5.10 helper block; no existing SOptLib or target-file theorem states this
RGEM-specific residual/telescope inequality, while the listed hits are exactly
the source ingredients for Eq. (5.2.75). -/
private theorem proposition56_residual_inequality_5_2_75_positive_domain
    {k : ℕ} {xStar : E}
    (hk : 1 ≤ k)
    (hη : S.PositiveEtaDomain)
    (hopt : S.IsOptimalSolution xStar)
    (hθ_pos : S.OutputWeightsPositive k)
    (hweight : S.WeightCondition5261 k)
    (hside : S.PropositionSideConditions k) :
    S.θ k * (1 + S.τ k) *
        Finset.sum Finset.univ
          (fun i => SOptLib.expectation S.P
            (fun ω => S.f i (S.positiveEtaBlockIterate hη k ω i))) +
      Finset.sum (outputWindow k)
        (fun t => S.θ t *
          SOptLib.expectation S.P
            (fun ω => S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.psi xStar)) +
      (S.θ k * (S.μ + S.η k) / 2) *
        SOptLib.expectation S.P
          (fun ω => S.V (S.positiveEtaXIterate hη k ω) xStar) ≤
      S.θ 1 * ((Fintype.card ι : ℝ) * (1 + S.τ 1) - 1) * S.fAvg S.x0 +
        S.θ 1 * S.η 1 * S.V S.x0 xStar +
        Finset.sum (outputWindow k)
          (fun t =>
            (2 * S.θ t * S.α (t + 1) /
                ((Fintype.card ι : ℝ) * S.η (t + 1))) *
              SOptLib.expectation S.P
                (fun ω =>
                  S.dualNorm
                    (S.gradF (S.sample t ω)
                      (S.positiveEtaBlockIterate hη (t - 1) ω (S.sample t ω)) -
                     S.positiveEtaYIterate hη (t - 1) ω (S.sample t ω)) ^ 2)) := by
  classical
  have _hprox_5271 := S.ProxStepInequality_Eq_5_2_71
  have _hsmooth_58 := S.SmoothnessGradientGap_Lemma_5_8
  have _hsmooth_nonnegL := S.component_smoothness_bound_of_nonnegative_L
  have _hcond_59 := S.ConditionalBlockExpectation_Lemma_5_9_positive_domain
  have _hterminal_eta_bridge :=
    S.propositionSideConditions_terminal_eta_bridge hk hθ_pos hside
  have _hstep_source := fun t (htmem : t ∈ outputWindow k) ω =>
    have ht : 1 ≤ t :=
      (Finset.mem_Icc.mp (by simpa [outputWindow] using htmem)).1
    S.proposition56_one_step_source_ingredients_5_2_73_positive_domain
      hη ht ω hopt.1
  have _hprox_expect := fun t (htmem : t ∈ outputWindow k) =>
    have ht : 1 ≤ t :=
      (Finset.mem_Icc.mp (by simpa [outputWindow] using htmem)).1
    S.proposition56_prox_step_expectation_5_2_71_positive_domain
      hη (t := t) ht hopt.1
  have _hsmooth_sampled_expect := fun t (htmem : t ∈ outputWindow k) i =>
    have ht : 1 ≤ t :=
      (Finset.mem_Icc.mp (by simpa [outputWindow] using htmem)).1
    S.proposition56_sampled_smoothness_gap_expectation_5_2_73_positive_domain
      hη (t := t) ht i
  have _hcross_coeff := fun (t : ℕ) (ht2 : 2 ≤ t) (htk : t ≤ k) i hLpos =>
    S.proposition56_cross_residual_coefficient_nonpos_positive_domain
      hη hθ_pos hside ht2 htk i hLpos
  have _hterminal_coeff :=
    S.proposition56_terminal_stale_coefficient_le_positive_domain hk hη hθ_pos hside
  have _hbregman_telescope :=
    S.proposition56_bregman_telescope_5_2_66_positive_domain
      hη hk hopt.1 hside
  have _hgradExp_expect :=
    S.proposition56_gradient_extrapolation_telescope_expectation_5_2_65_positive_domain
      hη hk hside xStar
  have _hcomponent_telescope :=
    S.proposition56_component_function_telescope_5_2_61_positive_domain
      hη hk hweight
  have _h73 :=
    S.proposition56_summed_one_step_expectation_5_2_73_positive_domain
      hη hk hopt hθ_pos
  let staleCoeff : ℕ → ℝ := fun t =>
    2 * S.θ t * S.α (t + 1) /
      ((Fintype.card ι : ℝ) * S.η (t + 1))
  let staleErr : ℕ → ℝ := fun t =>
    SOptLib.expectation S.P
      (fun ω =>
        S.dualNorm
          (S.gradF (S.sample t ω)
            (S.positiveEtaBlockIterate hη (t - 1) ω (S.sample t ω)) -
           S.positiveEtaYIterate hη (t - 1) ω (S.sample t ω)) ^ 2)
  have _hstale_coeff_nonneg :
      ∀ t, t ∈ outputWindow k → 0 ≤ staleCoeff t := by
    intro t htmem
    simpa [staleCoeff] using
      S.proposition56_stale_rhs_coefficient_nonneg_positive_domain
        hη hθ_pos htmem
  have _hstale_reindex :
      Finset.sum (Finset.Icc 2 k)
          (fun t => staleCoeff (t - 1) * staleErr (t - 1)) +
        staleCoeff k * staleErr k =
          Finset.sum (outputWindow k) (fun t => staleCoeff t * staleErr t) := by
    simpa using
      proposition56_outputWindow_predecessor_sum_add_terminal_eq
        hk (fun t => staleCoeff t * staleErr t)
  have _hy_memory_split := fun t ω i =>
    S.proposition56_y_memory_dualNorm_split_positive_domain hη t ω i
  let D : ℕ → ℝ := fun t =>
    S.θ t *
      SOptLib.expectation S.P
        (fun ω =>
          S.τ t / (2 * S.Lcomp (S.sample t ω)) *
            S.dualNorm
              (S.gradF (S.sample t ω)
                  (S.positiveEtaBlockIterate hη t ω (S.sample t ω)) -
                S.gradF (S.sample t ω)
                  (S.positiveEtaBlockIterate hη (t - 1) ω (S.sample t ω))) ^ 2)
  have _hpenalty_window :
      Finset.sum (outputWindow k) D =
        Finset.sum (Finset.Icc 2 k)
          (fun t =>
            S.θ (t - 1) *
              SOptLib.expectation S.P
                (fun ω =>
                  S.τ (t - 1) / (2 * S.Lcomp (S.sample (t - 1) ω)) *
                    S.dualNorm
                      (S.positiveEtaYIterate hη (t - 1) ω (S.sample (t - 1) ω) -
                        S.gradF (S.sample (t - 1) ω)
                          (S.positiveEtaBlockIterate hη (t - 2) ω
                            (S.sample (t - 1) ω))) ^ 2)) +
          S.θ k *
            SOptLib.expectation S.P
              (fun ω =>
                S.τ k / (2 * S.Lcomp (S.sample k ω)) *
                  S.dualNorm
                    (S.positiveEtaYIterate hη k ω (S.sample k ω) -
                      S.gradF (S.sample k ω)
                        (S.positiveEtaBlockIterate hη (k - 1) ω
                          (S.sample k ω))) ^ 2) := by
    simpa [D] using
      S.proposition56_sampled_penalty_y_residual_window_eq hη hk
  let A : ℕ → ℝ := fun t =>
    S.θ t *
      ((1 + S.τ t) *
        Finset.sum Finset.univ
          (fun i =>
            SOptLib.expectation S.P
              (fun ω => S.f i (S.positiveEtaBlockIterate hη t ω i))))
  let N : ℕ → ℝ := fun t =>
    S.θ t *
      SOptLib.expectation S.P
        (fun ω => S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.psi xStar)
  let C : ℕ → ℝ := fun t =>
    S.θ t *
      (((1 + S.τ t) - (Fintype.card ι : ℝ)⁻¹) *
        Finset.sum Finset.univ
          (fun i =>
            SOptLib.expectation S.P
              (fun ω => S.f i (S.positiveEtaBlockIterate hη (t - 1) ω i))))
  let G : ℕ → ℝ := fun t =>
    S.θ t *
      SOptLib.expectation S.P
        (fun ω =>
          Finset.sum Finset.univ
            (fun i =>
              ⟪S.positiveEtaXIterate hη t ω - xStar,
                (S.positiveEtaYIterate hη t ω i -
                  S.positiveEtaYIterate hη (t - 1) ω i) -
                  (S.α t / (Fintype.card ι : ℝ)) •
                    (S.positiveEtaYIterate hη (t - 1) ω i -
                      S.positiveEtaYIterate hη (t - 2) ω i)⟫_ℝ))
  let B : ℕ → ℝ := fun t =>
    S.θ t *
      (S.η t *
          SOptLib.expectation S.P
            (fun ω => S.V (S.positiveEtaXIterate hη (t - 1) ω) xStar) -
        (S.μ + S.η t) *
          SOptLib.expectation S.P
            (fun ω => S.V (S.positiveEtaXIterate hη t ω) xStar))
  let Adj : ℕ → ℝ := fun t =>
    S.θ t *
      (S.η t *
        SOptLib.expectation S.P
          (fun ω =>
            S.V (S.positiveEtaXIterate hη (t - 1) ω)
              (S.positiveEtaXIterate hη t ω)))
  let terminalF : ℝ :=
    S.θ k * (1 + S.τ k) *
      Finset.sum Finset.univ
        (fun i =>
          SOptLib.expectation S.P
            (fun ω => S.f i (S.positiveEtaBlockIterate hη k ω i)))
  let initF : ℝ :=
    S.θ 1 * ((Fintype.card ι : ℝ) * (1 + S.τ 1) - 1) * S.fAvg S.x0
  let initV : ℝ := S.θ 1 * S.η 1 * S.V S.x0 xStar
  let terminalB : ℝ :=
    S.θ k * (S.μ + S.η k) *
      SOptLib.expectation S.P
        (fun ω => S.V (S.positiveEtaXIterate hη k ω) xStar)
  let gradTerminal : ℝ :=
    S.θ k *
      SOptLib.expectation S.P
        (fun ω =>
          ⟪S.positiveEtaXIterate hη k ω - xStar,
            S.positiveEtaYIterate hη k ω (S.sample k ω) -
              S.positiveEtaYIterate hη (k - 1) ω (S.sample k ω)⟫_ℝ)
  let gradAccum : ℝ :=
    Finset.sum (Finset.Icc 2 k)
      (fun t =>
        S.θ t * S.α t / (Fintype.card ι : ℝ) *
          SOptLib.expectation S.P
            (fun ω =>
              ⟪S.positiveEtaXIterate hη t ω -
                  S.positiveEtaXIterate hη (t - 1) ω,
                S.positiveEtaYIterate hη (t - 1) ω (S.sample (t - 1) ω) -
                  S.positiveEtaYIterate hη (t - 2) ω (S.sample (t - 1) ω)⟫_ℝ))
  let adjAccum : ℝ := Finset.sum (outputWindow k) Adj
  let penaltyAccum : ℝ :=
    Finset.sum (Finset.Icc 2 k)
      (fun t =>
        S.θ (t - 1) *
          SOptLib.expectation S.P
            (fun ω =>
              S.τ (t - 1) / (2 * S.Lcomp (S.sample (t - 1) ω)) *
                S.dualNorm
                  (S.positiveEtaYIterate hη (t - 1) ω (S.sample (t - 1) ω) -
                    S.gradF (S.sample (t - 1) ω)
                      (S.positiveEtaBlockIterate hη (t - 2) ω
                        (S.sample (t - 1) ω))) ^ 2))
  let penaltyTerminal : ℝ :=
    S.θ k *
      SOptLib.expectation S.P
        (fun ω =>
          S.τ k / (2 * S.Lcomp (S.sample k ω)) *
            S.dualNorm
              (S.positiveEtaYIterate hη k ω (S.sample k ω) -
                S.gradF (S.sample k ω)
                  (S.positiveEtaBlockIterate hη (k - 1) ω
                    (S.sample k ω))) ^ 2)
  have hstep :
      Finset.sum (outputWindow k) (fun t => A t + N t) ≤
        Finset.sum (outputWindow k) (fun t => C t + G t + (B t - Adj t) - D t) := by
    simpa [A, N, C, G, B, Adj, D, mul_add, mul_sub, add_assoc, sub_eq_add_neg]
      using _h73
  have hcomponent :
      Finset.sum (outputWindow k) (fun t => A t - C t) = terminalF - initF := by
    convert _hcomponent_telescope using 1
    · refine Finset.sum_congr rfl ?_
      intro t _ht
      simp [A, C]
      ring
  have hgradient :
      Finset.sum (outputWindow k) G = gradTerminal - gradAccum := by
    simpa [G, gradTerminal, gradAccum] using _hgradExp_expect
  have hbregman :
      Finset.sum (outputWindow k) B ≤ initV - terminalB := by
    simpa [B, initV, terminalB] using _hbregman_telescope
  have hpenalty :
      Finset.sum (outputWindow k) D = penaltyAccum + penaltyTerminal := by
    simpa [penaltyAccum, penaltyTerminal] using _hpenalty_window
  have hadj :
      Finset.sum (outputWindow k) Adj = adjAccum := by
    rfl
  have h74 :
      terminalF + Finset.sum (outputWindow k) N + terminalB / 2 ≤
        initF + initV +
          ((-gradAccum) - adjAccum - penaltyAccum) +
          (gradTerminal - terminalB / 2 - penaltyTerminal) :=
    proposition56_scalar_residual_5_2_74_assembly
      (outputWindow k) A C G B Adj D N
      terminalF initF initV terminalB gradTerminal gradAccum adjAccum
      penaltyAccum penaltyTerminal
      hstep hcomponent hgradient hbregman hpenalty hadj
  have haccum :
      ((-gradAccum) - adjAccum - penaltyAccum) ≤
        Finset.sum (Finset.Icc 2 k)
          (fun t => staleCoeff (t - 1) * staleErr (t - 1)) := by
    let F : ℕ → ℝ := fun t =>
      S.θ t * S.α t / (Fintype.card ι : ℝ) *
        SOptLib.expectation S.P
          (fun ω =>
            ⟪S.positiveEtaXIterate hη t ω -
                S.positiveEtaXIterate hη (t - 1) ω,
              S.positiveEtaYIterate hη (t - 1) ω (S.sample (t - 1) ω) -
                S.positiveEtaYIterate hη (t - 2) ω (S.sample (t - 1) ω)⟫_ℝ)
    let P : ℕ → ℝ := fun t =>
      S.θ (t - 1) *
        SOptLib.expectation S.P
          (fun ω =>
            S.τ (t - 1) / (2 * S.Lcomp (S.sample (t - 1) ω)) *
              S.dualNorm
                (S.positiveEtaYIterate hη (t - 1) ω (S.sample (t - 1) ω) -
                  S.gradF (S.sample (t - 1) ω)
                    (S.positiveEtaBlockIterate hη (t - 2) ω
                      (S.sample (t - 1) ω))) ^ 2)
    let R : ℕ → ℝ := fun t => staleCoeff (t - 1) * staleErr (t - 1)
    have hadj_icc_le : Finset.sum (Finset.Icc 2 k) Adj ≤ adjAccum := by
      simpa [adjAccum, Adj] using
        S.proposition56_adj_Icc_le_outputWindow_positive_domain hη hθ_pos
    have hper :
        ∀ t ∈ Finset.Icc 2 k, -F t - Adj t - P t ≤ R t := by
      intro t ht
      have ht_bounds := Finset.mem_Icc.mp ht
      have ht2 : 2 ≤ t := ht_bounds.1
      have htk : t ≤ k := ht_bounds.2
      have hyoung_pointwise :
          ∀ ω : BlockSamplePath ι,
            - (S.θ t * S.α t / (Fintype.card ι : ℝ)) *
                ⟪S.positiveEtaXIterate hη t ω -
                    S.positiveEtaXIterate hη (t - 1) ω,
                  S.positiveEtaYIterate hη (t - 1) ω (S.sample (t - 1) ω) -
                    S.positiveEtaYIterate hη (t - 2) ω
                      (S.sample (t - 1) ω)⟫_ℝ -
                S.θ t * (S.η t *
                  S.V (S.positiveEtaXIterate hη (t - 1) ω)
                    (S.positiveEtaXIterate hη t ω)) ≤
              S.θ (t - 1) * S.α t /
                  (2 * (Fintype.card ι : ℝ) * S.η t) *
                S.dualNorm
                  (S.positiveEtaYIterate hη (t - 1) ω
                      (S.sample (t - 1) ω) -
                    S.positiveEtaYIterate hη (t - 2) ω
                      (S.sample (t - 1) ω)) ^ 2 := by
        intro ω
        exact
          S.proposition56_lagged_inner_adj_young_pointwise_positive_domain
            hη hθ_pos hside ht2 htk ω
      have hy_split_pointwise :
          ∀ ω : BlockSamplePath ι,
            S.dualNorm
                (S.positiveEtaYIterate hη (t - 1) ω
                    (S.sample (t - 1) ω) -
                  S.positiveEtaYIterate hη (t - 2) ω
                    (S.sample (t - 1) ω)) ^ 2 ≤
              2 *
                  S.dualNorm
                    (S.positiveEtaYIterate hη (t - 1) ω
                        (S.sample (t - 1) ω) -
                      S.gradF (S.sample (t - 1) ω)
                        (S.positiveEtaBlockIterate hη (t - 2) ω
                          (S.sample (t - 1) ω))) ^ 2 +
                2 *
                  S.dualNorm
                    (S.gradF (S.sample (t - 1) ω)
                        (S.positiveEtaBlockIterate hη (t - 2) ω
                          (S.sample (t - 1) ω)) -
                      S.positiveEtaYIterate hη (t - 2) ω
                        (S.sample (t - 1) ω)) ^ 2 := by
        intro ω
        simpa using
          _hy_memory_split (t - 1) ω (S.sample (t - 1) ω)
      have hcross_coeff_pos_branch :
          ∀ ω : BlockSamplePath ι,
            0 < S.Lcomp (S.sample (t - 1) ω) →
              S.θ (t - 1) * S.α t /
                    ((Fintype.card ι : ℝ) * S.η t) -
                  S.θ (t - 1) * S.τ (t - 1) /
                    (2 * S.Lcomp (S.sample (t - 1) ω)) ≤ 0 := by
        intro ω hLpos
        exact _hcross_coeff t ht2 htk (S.sample (t - 1) ω) hLpos
      -- Remaining source steps 16--17: integrate `hyoung_pointwise`, apply
      -- `hy_split_pointwise`, and discharge the current residual coefficient
      -- using `hcross_coeff_pos_branch` plus the zero-`L_i` branch.
      let m : ℝ := (Fintype.card ι : ℝ)
      let cF : ℝ := S.θ t * S.α t / m
      let cY : ℝ := S.θ (t - 1) * S.α t / (2 * m * S.η t)
      let coeff : ℝ := S.θ (t - 1) * S.α t / (m * S.η t)
      let staleC : ℝ := staleCoeff (t - 1)
      let I : BlockSamplePath ι → ℝ := fun ω =>
        ⟪S.positiveEtaXIterate hη t ω -
            S.positiveEtaXIterate hη (t - 1) ω,
          S.positiveEtaYIterate hη (t - 1) ω (S.sample (t - 1) ω) -
            S.positiveEtaYIterate hη (t - 2) ω (S.sample (t - 1) ω)⟫_ℝ
      let Vv : BlockSamplePath ι → ℝ := fun ω =>
        S.V (S.positiveEtaXIterate hη (t - 1) ω)
          (S.positiveEtaXIterate hη t ω)
      let Ydiff : BlockSamplePath ι → ℝ := fun ω =>
        S.dualNorm
          (S.positiveEtaYIterate hη (t - 1) ω (S.sample (t - 1) ω) -
            S.positiveEtaYIterate hη (t - 2) ω (S.sample (t - 1) ω)) ^ 2
      let Ecur : BlockSamplePath ι → ℝ := fun ω =>
        S.dualNorm
          (S.positiveEtaYIterate hη (t - 1) ω (S.sample (t - 1) ω) -
            S.gradF (S.sample (t - 1) ω)
              (S.positiveEtaBlockIterate hη (t - 2) ω (S.sample (t - 1) ω))) ^ 2
      let Estale : BlockSamplePath ι → ℝ := fun ω =>
        S.dualNorm
          (S.gradF (S.sample (t - 1) ω)
              (S.positiveEtaBlockIterate hη (t - 2) ω (S.sample (t - 1) ω)) -
            S.positiveEtaYIterate hη (t - 2) ω (S.sample (t - 1) ω)) ^ 2
      let Pen : BlockSamplePath ι → ℝ := fun ω =>
        S.τ (t - 1) / (2 * S.Lcomp (S.sample (t - 1) ω)) * Ecur ω
      let leftFun : BlockSamplePath ι → ℝ := fun ω =>
        -(cF * I ω) - S.θ t * (S.η t * Vv ω) - S.θ (t - 1) * Pen ω
      let rightFun : BlockSamplePath ι → ℝ := fun ω =>
        staleC * Estale ω
      have ht_pred : 1 + (t - 2) = t - 1 := by omega
      have htm1 : 1 ≤ t - 1 := by omega
      have hm_pos : 0 < m := by
        dsimp [m]
        exact_mod_cast Fintype.card_pos
      have hm_ne : m ≠ 0 := ne_of_gt hm_pos
      have hηt_pos : 0 < S.η t := hη t (by omega)
      have hηt_ne : S.η t ≠ 0 := ne_of_gt hηt_pos
      have htminus_mem : t - 1 ∈ outputWindow k := by
        rw [outputWindow]
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hθprev_pos : 0 < S.θ (t - 1) := hθ_pos (t - 1) htminus_mem
      have hαt_nonneg : 0 ≤ S.α t := (S.hparam_nonneg t).1
      have hcY_nonneg : 0 ≤ cY := by
        dsimp [cY, m]
        positivity
      have hcoeff_nonneg : 0 ≤ coeff := by
        dsimp [coeff, m]
        positivity
      have hstale_eq : staleC = 2 * coeff := by
        dsimp [staleC, staleCoeff, coeff, m]
        have hsucc : t - 1 + 1 = t := by omega
        rw [hsucc]
        ring
      have hcoeff_le_stale : coeff ≤ staleC := by
        rw [hstale_eq]
        nlinarith
      have hI_int : Integrable I S.P := by
        simpa [I, positiveEtaXIterate, positiveEtaYIterate,
          positiveEtaGeneratedProcess, ht_pred] using
          (S.positiveEta_sample_state_prefix_payload_integrable hη t
            (G := fun samples states =>
              ⟪(states ⟨t, by omega⟩).x - (states ⟨t - 1, by omega⟩).x,
                (states ⟨t - 1, by omega⟩).yCurr (samples ⟨t - 2, by omega⟩) -
                  (states ⟨t - 2, by omega⟩).yCurr
                    (samples ⟨t - 2, by omega⟩)⟫_ℝ))
      have hV_int : Integrable Vv S.P := by
        simpa [Vv, positiveEtaXIterate, positiveEtaGeneratedProcess] using
          (S.positiveEta_prefix_payload_integrable hη t
            (G := fun states =>
              S.V (states ⟨t - 1, by omega⟩).x (states ⟨t, by omega⟩).x))
      have hEcur_int : Integrable Ecur S.P := by
        simpa [Ecur, positiveEtaYIterate, positiveEtaBlockIterate,
          positiveEtaGeneratedProcess, ht_pred] using
          (S.positiveEta_sample_state_prefix_payload_integrable hη t
            (G := fun samples states =>
              S.dualNorm
                ((states ⟨t - 1, by omega⟩).yCurr (samples ⟨t - 2, by omega⟩) -
                  S.gradF (samples ⟨t - 2, by omega⟩)
                    ((states ⟨t - 2, by omega⟩).blockX
                      (samples ⟨t - 2, by omega⟩))) ^ 2))
      have hEstale_int : Integrable Estale S.P := by
        simpa [Estale, positiveEtaYIterate, positiveEtaBlockIterate,
          positiveEtaGeneratedProcess, ht_pred] using
          (S.positiveEta_sample_state_prefix_payload_integrable hη t
            (G := fun samples states =>
              S.dualNorm
                (S.gradF (samples ⟨t - 2, by omega⟩)
                    ((states ⟨t - 2, by omega⟩).blockX
                      (samples ⟨t - 2, by omega⟩)) -
                  (states ⟨t - 2, by omega⟩).yCurr
                    (samples ⟨t - 2, by omega⟩)) ^ 2))
      have hPen_int : Integrable Pen S.P := by
        simpa [Pen, Ecur, positiveEtaYIterate, positiveEtaBlockIterate,
          positiveEtaGeneratedProcess, ht_pred] using
          (S.positiveEta_sample_state_prefix_payload_integrable hη t
            (G := fun samples states =>
              S.τ (t - 1) / (2 * S.Lcomp (samples ⟨t - 2, by omega⟩)) *
                S.dualNorm
                  ((states ⟨t - 1, by omega⟩).yCurr (samples ⟨t - 2, by omega⟩) -
                    S.gradF (samples ⟨t - 2, by omega⟩)
                      ((states ⟨t - 2, by omega⟩).blockX
                        (samples ⟨t - 2, by omega⟩))) ^ 2))
      have hleft_int : Integrable leftFun S.P := by
        exact (((hI_int.const_mul cF).neg.sub
          ((hV_int.const_mul (S.η t)).const_mul (S.θ t))).sub
          (hPen_int.const_mul (S.θ (t - 1))))
      have hright_int : Integrable rightFun S.P := by
        exact hEstale_int.const_mul staleC
      have hpoint : ∀ᵐ ω ∂S.P, leftFun ω ≤ rightFun ω := by
        filter_upwards with ω
        let penCoeff : ℝ :=
          S.θ (t - 1) * S.τ (t - 1) /
            (2 * S.Lcomp (S.sample (t - 1) ω))
        have hY :
            -(cF * I ω) - S.θ t * (S.η t * Vv ω) ≤ cY * Ydiff ω := by
          simpa [cF, I, Vv, Ydiff, cY, m] using hyoung_pointwise ω
        have hsplit :
            cY * Ydiff ω ≤ coeff * Ecur ω + coeff * Estale ω := by
          have hs := hy_split_pointwise ω
          have hmul := mul_le_mul_of_nonneg_left hs hcY_nonneg
          have hcoeff_two : 2 * cY = coeff := by
            dsimp [cY, coeff, m]
            field_simp [hm_ne, hηt_ne]
          calc
            cY * Ydiff ω ≤ cY * (2 * Ecur ω + 2 * Estale ω) := hmul
            _ = (2 * cY) * Ecur ω + (2 * cY) * Estale ω := by ring
            _ = coeff * Ecur ω + coeff * Estale ω := by rw [hcoeff_two]
        have hbase :
            -(cF * I ω) - S.θ t * (S.η t * Vv ω) ≤
              coeff * Ecur ω + coeff * Estale ω :=
          hY.trans hsplit
        have hEcur_nonneg : 0 ≤ Ecur ω := by
          dsimp [Ecur]
          exact sq_nonneg _
        have hEstale_nonneg : 0 ≤ Estale ω := by
          dsimp [Estale]
          exact sq_nonneg _
        have hpen :
            S.θ (t - 1) * Pen ω = penCoeff * Ecur ω := by
          dsimp [Pen, penCoeff]
          ring
        have hright_coeff :
            coeff * Estale ω ≤ staleC * Estale ω :=
          mul_le_mul_of_nonneg_right hcoeff_le_stale hEstale_nonneg
        by_cases hLpos : 0 < S.Lcomp (S.sample (t - 1) ω)
        · have hcoeff_pen : coeff - penCoeff ≤ 0 := by
            simpa [coeff, penCoeff, m] using
              hcross_coeff_pos_branch ω hLpos
          have hcancel : (coeff - penCoeff) * Ecur ω ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg hcoeff_pen hEcur_nonneg
          calc
            leftFun ω =
                (-(cF * I ω) - S.θ t * (S.η t * Vv ω)) -
                  penCoeff * Ecur ω := by
                  dsimp [leftFun]
                  rw [hpen]
            _ ≤ (coeff * Ecur ω + coeff * Estale ω) -
                  penCoeff * Ecur ω :=
                  sub_le_sub_right hbase _
            _ = (coeff - penCoeff) * Ecur ω + coeff * Estale ω := by ring
            _ ≤ 0 + staleC * Estale ω :=
                  add_le_add hcancel hright_coeff
            _ = rightFun ω := by
                  dsimp [rightFun]
                  ring
        · have hLzero :
              S.Lcomp (S.sample (t - 1) ω) = 0 :=
            le_antisymm (le_of_not_gt hLpos)
              (S.hLcomp_nonneg (S.sample (t - 1) ω))
          have hEcur_zero : Ecur ω = 0 := by
            simpa [Ecur] using
              S.proposition56_zero_L_sampled_current_residual_sq_eq_zero
                hη (t := t - 1) htm1 ω hLzero
          have hbase_zero :
              -(cF * I ω) - S.θ t * (S.η t * Vv ω) ≤
                coeff * Estale ω := by
            rw [hEcur_zero] at hbase
            simpa using hbase
          calc
            leftFun ω =
                (-(cF * I ω) - S.θ t * (S.η t * Vv ω)) -
                  penCoeff * Ecur ω := by
                  dsimp [leftFun]
                  rw [hpen]
            _ = -(cF * I ω) - S.θ t * (S.η t * Vv ω) := by
                  rw [hEcur_zero]
                  ring
            _ ≤ coeff * Estale ω := hbase_zero
            _ ≤ staleC * Estale ω := hright_coeff
            _ = rightFun ω := by
                  dsimp [rightFun]
      have hmono :
          (∫ ω, leftFun ω ∂S.P) ≤ ∫ ω, rightFun ω ∂S.P :=
        integral_mono_ae hleft_int hright_int hpoint
      have hleft_eq :
          (∫ ω, leftFun ω ∂S.P) = -F t - Adj t - P t := by
        have htermF_int : Integrable (fun ω => -(cF * I ω)) S.P :=
          (hI_int.const_mul cF).neg
        have htermV_int :
            Integrable (fun ω => S.θ t * (S.η t * Vv ω)) S.P :=
          (hV_int.const_mul (S.η t)).const_mul (S.θ t)
        have htermP_int :
            Integrable (fun ω => S.θ (t - 1) * Pen ω) S.P :=
          hPen_int.const_mul (S.θ (t - 1))
        have hneg_pull :
            (∫ ω, -(cF * I ω) ∂S.P) =
              -(cF * ∫ ω, I ω ∂S.P) := by
          rw [integral_neg]
          rw [integral_const_mul]
        have hV_pull :
            (∫ ω, S.θ t * (S.η t * Vv ω) ∂S.P) =
              S.θ t * (S.η t * ∫ ω, Vv ω ∂S.P) := by
          rw [integral_const_mul]
          rw [integral_const_mul]
        have hPen_pull :
            (∫ ω, S.θ (t - 1) * Pen ω ∂S.P) =
              S.θ (t - 1) * ∫ ω, Pen ω ∂S.P := by
          rw [integral_const_mul]
        have hraw :
            (∫ ω, leftFun ω ∂S.P) =
              -(cF * ∫ ω, I ω ∂S.P) -
                S.θ t * (S.η t * ∫ ω, Vv ω ∂S.P) -
                  S.θ (t - 1) * ∫ ω, Pen ω ∂S.P := by
          calc
            (∫ ω, leftFun ω ∂S.P) =
                ∫ ω,
                  (-(cF * I ω) - S.θ t * (S.η t * Vv ω)) -
                    S.θ (t - 1) * Pen ω ∂S.P := by
                  rfl
            _ =
                (∫ ω, -(cF * I ω) - S.θ t * (S.η t * Vv ω) ∂S.P) -
                  ∫ ω, S.θ (t - 1) * Pen ω ∂S.P := by
                  exact integral_sub
                    (f := fun ω => -(cF * I ω) - S.θ t * (S.η t * Vv ω))
                    (g := fun ω => S.θ (t - 1) * Pen ω)
                    (μ := S.P) (htermF_int.sub htermV_int) htermP_int
            _ =
                ((∫ ω, -(cF * I ω) ∂S.P) -
                    ∫ ω, S.θ t * (S.η t * Vv ω) ∂S.P) -
                  ∫ ω, S.θ (t - 1) * Pen ω ∂S.P := by
                  rw [integral_sub
                    (f := fun ω => -(cF * I ω))
                    (g := fun ω => S.θ t * (S.η t * Vv ω))
                    (μ := S.P) htermF_int htermV_int]
            _ =
                -(cF * ∫ ω, I ω ∂S.P) -
                  S.θ t * (S.η t * ∫ ω, Vv ω ∂S.P) -
                    S.θ (t - 1) * ∫ ω, Pen ω ∂S.P := by
                  rw [hneg_pull, hV_pull, hPen_pull]
        have hfold :
            -(cF * ∫ ω, I ω ∂S.P) -
                S.θ t * (S.η t * ∫ ω, Vv ω ∂S.P) -
                  S.θ (t - 1) * ∫ ω, Pen ω ∂S.P =
              -F t - Adj t - P t := by
          change
            -(cF * ∫ ω, I ω ∂S.P) -
                S.θ t * (S.η t * ∫ ω, Vv ω ∂S.P) -
                  S.θ (t - 1) * ∫ ω, Pen ω ∂S.P =
              -(cF * ∫ ω, I ω ∂S.P) -
                S.θ t * (S.η t * ∫ ω, Vv ω ∂S.P) -
                  S.θ (t - 1) * ∫ ω, Pen ω ∂S.P
          rfl
        exact hraw.trans hfold
      have hright_eq :
          (∫ ω, rightFun ω ∂S.P) = R t := by
        have hraw :
            (∫ ω, rightFun ω ∂S.P) =
              staleC * ∫ ω, Estale ω ∂S.P := by
          unfold rightFun
          rw [integral_const_mul]
        have hpred2 : t - 1 - 1 = t - 2 := by omega
        have hEstale_fold :
            (∫ ω, Estale ω ∂S.P) = staleErr (t - 1) := by
          unfold staleErr SOptLib.expectation Estale
          apply integral_congr_ae
          filter_upwards with ω
          rw [hpred2]
        calc
          (∫ ω, rightFun ω ∂S.P) = staleC * ∫ ω, Estale ω ∂S.P := hraw
          _ = staleCoeff (t - 1) * staleErr (t - 1) := by
                rw [hEstale_fold]
          _ = R t := by rfl
      rw [hleft_eq, hright_eq] at hmono
      exact hmono
    have hsum_bound :
        -gradAccum - Finset.sum (Finset.Icc 2 k) Adj - penaltyAccum ≤
          Finset.sum (Finset.Icc 2 k) R := by
      calc
        -gradAccum - Finset.sum (Finset.Icc 2 k) Adj - penaltyAccum =
            Finset.sum (Finset.Icc 2 k) (fun t => -F t - Adj t - P t) := by
              simp [F, Adj, P, gradAccum, penaltyAccum, Finset.sum_sub_distrib]
        _ ≤ Finset.sum (Finset.Icc 2 k) R :=
            Finset.sum_le_sum hper
    nlinarith [hadj_icc_le, hsum_bound]
  have hterminal :
      gradTerminal - terminalB / 2 - penaltyTerminal ≤ staleCoeff k * staleErr k := by
    have hterminal_base :
        gradTerminal - terminalB / 2 - penaltyTerminal ≤
          (2 * S.θ k / (S.μ + S.η k)) * staleErr k := by
      -- Terminal Young/V-lower-bound estimate from Lan Proposition 5.6 proof step 18.
      let M : ℝ := S.μ + S.η k
      let I : BlockSamplePath ι → ℝ := fun ω =>
        ⟪S.positiveEtaXIterate hη k ω - xStar,
          S.positiveEtaYIterate hη k ω (S.sample k ω) -
            S.positiveEtaYIterate hη (k - 1) ω (S.sample k ω)⟫_ℝ
      let Vv : BlockSamplePath ι → ℝ := fun ω =>
        S.V (S.positiveEtaXIterate hη k ω) xStar
      let Ecur : BlockSamplePath ι → ℝ := fun ω =>
        S.dualNorm
          (S.positiveEtaYIterate hη k ω (S.sample k ω) -
            S.gradF (S.sample k ω)
              (S.positiveEtaBlockIterate hη (k - 1) ω (S.sample k ω))) ^ 2
      let Estale : BlockSamplePath ι → ℝ := fun ω =>
        S.dualNorm
          (S.gradF (S.sample k ω)
              (S.positiveEtaBlockIterate hη (k - 1) ω (S.sample k ω)) -
            S.positiveEtaYIterate hη (k - 1) ω (S.sample k ω)) ^ 2
      let Pen : BlockSamplePath ι → ℝ := fun ω =>
        S.τ k / (2 * S.Lcomp (S.sample k ω)) * Ecur ω
      let leftFun : BlockSamplePath ι → ℝ := fun ω =>
        S.θ k * I ω - (S.θ k * M / 2) * Vv ω - S.θ k * Pen ω
      let rightFun : BlockSamplePath ι → ℝ := fun ω =>
        (2 * S.θ k / M) * Estale ω
      have hidx : 1 + (k - 1) = k := by omega
      have hI_int : Integrable I S.P := by
        let G : (Fin k → ι) → (Fin (k + 1) → State ι E) → ℝ :=
          fun samples states =>
            ⟪(states ⟨k, by omega⟩).x - xStar,
              (states ⟨k, by omega⟩).yCurr (samples ⟨k - 1, by omega⟩) -
                (states ⟨k - 1, by omega⟩).yCurr
                  (samples ⟨k - 1, by omega⟩)⟫_ℝ
        simpa [I, G, positiveEtaXIterate, positiveEtaYIterate, hidx] using
          (S.positiveEta_sample_state_prefix_payload_integrable hη k G)
      have hV_int : Integrable Vv S.P := by
        let G : (Fin (k + 1) → State ι E) → ℝ := fun states =>
          S.V (states ⟨k, by omega⟩).x xStar
        simpa [Vv, G, positiveEtaXIterate, positiveEtaGeneratedProcess] using
          (S.positiveEta_prefix_payload_integrable hη k G)
      have hEcur_int : Integrable Ecur S.P := by
        let G : (Fin k → ι) → (Fin (k + 1) → State ι E) → ℝ :=
          fun samples states =>
            S.dualNorm
              ((states ⟨k, by omega⟩).yCurr (samples ⟨k - 1, by omega⟩) -
                S.gradF (samples ⟨k - 1, by omega⟩)
                  ((states ⟨k - 1, by omega⟩).blockX
                    (samples ⟨k - 1, by omega⟩))) ^ 2
        simpa [Ecur, G, positiveEtaYIterate, positiveEtaBlockIterate,
          positiveEtaGeneratedProcess, hidx] using
          (S.positiveEta_sample_state_prefix_payload_integrable hη k G)
      have hEstale_int : Integrable Estale S.P := by
        let G : (Fin k → ι) → (Fin (k + 1) → State ι E) → ℝ :=
          fun samples states =>
            S.dualNorm
              (S.gradF (samples ⟨k - 1, by omega⟩)
                  ((states ⟨k - 1, by omega⟩).blockX
                    (samples ⟨k - 1, by omega⟩)) -
                (states ⟨k - 1, by omega⟩).yCurr
                  (samples ⟨k - 1, by omega⟩)) ^ 2
        simpa [Estale, G, positiveEtaYIterate, positiveEtaBlockIterate,
          positiveEtaGeneratedProcess, hidx] using
          (S.positiveEta_sample_state_prefix_payload_integrable hη k G)
      have hPen_int : Integrable Pen S.P := by
        let G : (Fin k → ι) → (Fin (k + 1) → State ι E) → ℝ :=
          fun samples states =>
            S.τ k / (2 * S.Lcomp (samples ⟨k - 1, by omega⟩)) *
              S.dualNorm
                ((states ⟨k, by omega⟩).yCurr (samples ⟨k - 1, by omega⟩) -
                  S.gradF (samples ⟨k - 1, by omega⟩)
                    ((states ⟨k - 1, by omega⟩).blockX
                      (samples ⟨k - 1, by omega⟩))) ^ 2
        simpa [Pen, Ecur, G, positiveEtaYIterate, positiveEtaBlockIterate,
          positiveEtaGeneratedProcess, hidx] using
          (S.positiveEta_sample_state_prefix_payload_integrable hη k G)
      have hleft_int : Integrable leftFun S.P := by
        exact (((hI_int.const_mul (S.θ k)).sub
          (hV_int.const_mul (S.θ k * M / 2))).sub
          (hPen_int.const_mul (S.θ k)))
      have hright_int : Integrable rightFun S.P := by
        exact hEstale_int.const_mul (2 * S.θ k / M)
      have hpoint : ∀ᵐ ω ∂S.P, leftFun ω ≤ rightFun ω := by
        filter_upwards with ω
        simpa [leftFun, rightFun, I, Vv, Pen, Ecur, Estale, M] using
          S.proposition56_terminal_residual_pointwise_positive_domain
            hk hη hopt hθ_pos hside ω
      have hmono :
          (∫ ω, leftFun ω ∂S.P) ≤ ∫ ω, rightFun ω ∂S.P :=
        integral_mono_ae hleft_int hright_int hpoint
      have hleft_eq :
          (∫ ω, leftFun ω ∂S.P) =
            gradTerminal - terminalB / 2 - penaltyTerminal := by
        have htermI_int : Integrable (fun ω => S.θ k * I ω) S.P :=
          hI_int.const_mul (S.θ k)
        have htermV_int :
            Integrable (fun ω => (S.θ k * M / 2) * Vv ω) S.P :=
          hV_int.const_mul (S.θ k * M / 2)
        have htermP_int : Integrable (fun ω => S.θ k * Pen ω) S.P :=
          hPen_int.const_mul (S.θ k)
        have hI_pull :
            (∫ ω, S.θ k * I ω ∂S.P) =
              S.θ k * ∫ ω, I ω ∂S.P := by
          rw [integral_const_mul]
        have hV_pull :
            (∫ ω, (S.θ k * M / 2) * Vv ω ∂S.P) =
              (S.θ k * M / 2) * ∫ ω, Vv ω ∂S.P := by
          rw [integral_const_mul]
        have hPen_pull :
            (∫ ω, S.θ k * Pen ω ∂S.P) =
              S.θ k * ∫ ω, Pen ω ∂S.P := by
          rw [integral_const_mul]
        have hraw :
            (∫ ω, leftFun ω ∂S.P) =
              S.θ k * ∫ ω, I ω ∂S.P -
                (S.θ k * M / 2) * ∫ ω, Vv ω ∂S.P -
                  S.θ k * ∫ ω, Pen ω ∂S.P := by
          calc
            (∫ ω, leftFun ω ∂S.P) =
                ∫ ω,
                  (S.θ k * I ω - (S.θ k * M / 2) * Vv ω) -
                    S.θ k * Pen ω ∂S.P := by
                  rfl
            _ =
                (∫ ω, S.θ k * I ω - (S.θ k * M / 2) * Vv ω ∂S.P) -
                  ∫ ω, S.θ k * Pen ω ∂S.P := by
                  exact integral_sub
                    (f := fun ω => S.θ k * I ω - (S.θ k * M / 2) * Vv ω)
                    (g := fun ω => S.θ k * Pen ω)
                    (μ := S.P) (htermI_int.sub htermV_int) htermP_int
            _ =
                ((∫ ω, S.θ k * I ω ∂S.P) -
                  ∫ ω, (S.θ k * M / 2) * Vv ω ∂S.P) -
                  ∫ ω, S.θ k * Pen ω ∂S.P := by
                  rw [integral_sub
                    (f := fun ω => S.θ k * I ω)
                    (g := fun ω => (S.θ k * M / 2) * Vv ω)
                    (μ := S.P) htermI_int htermV_int]
            _ =
                S.θ k * ∫ ω, I ω ∂S.P -
                  (S.θ k * M / 2) * ∫ ω, Vv ω ∂S.P -
                    S.θ k * ∫ ω, Pen ω ∂S.P := by
                  rw [hI_pull, hV_pull, hPen_pull]
        have hfold :
            S.θ k * ∫ ω, I ω ∂S.P -
                (S.θ k * M / 2) * ∫ ω, Vv ω ∂S.P -
                  S.θ k * ∫ ω, Pen ω ∂S.P =
              gradTerminal - terminalB / 2 - penaltyTerminal := by
          dsimp [gradTerminal, terminalB, penaltyTerminal,
            SOptLib.expectation, I, Vv, Pen, M]
          ring
        exact hraw.trans hfold
      have hright_eq :
          (∫ ω, rightFun ω ∂S.P) =
            (2 * S.θ k / (S.μ + S.η k)) * staleErr k := by
        have hraw :
            (∫ ω, rightFun ω ∂S.P) =
              (2 * S.θ k / M) * ∫ ω, Estale ω ∂S.P := by
          unfold rightFun
          rw [integral_const_mul]
        have hEstale_fold :
            (∫ ω, Estale ω ∂S.P) = staleErr k := by
          rfl
        calc
          (∫ ω, rightFun ω ∂S.P) =
              (2 * S.θ k / M) * ∫ ω, Estale ω ∂S.P := hraw
          _ = (2 * S.θ k / M) * staleErr k := by rw [hEstale_fold]
          _ = (2 * S.θ k / (S.μ + S.η k)) * staleErr k := by
              simp [M]
      rw [hleft_eq, hright_eq] at hmono
      exact hmono
    have hstaleErr_nonneg : 0 ≤ staleErr k := by
      dsimp [staleErr, SOptLib.expectation]
      exact integral_nonneg (fun ω => sq_nonneg _)
    have hcoeff_scaled :
        (2 * S.θ k / (S.μ + S.η k)) * staleErr k ≤
          staleCoeff k * staleErr k := by
      have hmul := mul_le_mul_of_nonneg_right _hterminal_coeff hstaleErr_nonneg
      simpa [staleCoeff] using hmul
    exact hterminal_base.trans hcoeff_scaled
  have hresid :
      terminalF + Finset.sum (outputWindow k) N + terminalB / 2 ≤
        initF + initV +
          (Finset.sum (Finset.Icc 2 k)
            (fun t => staleCoeff (t - 1) * staleErr (t - 1)) +
            staleCoeff k * staleErr k) := by
    linarith [h74, haccum, hterminal]
  rw [_hstale_reindex] at hresid
  convert hresid using 1 <;>
    simp [terminalF, initF, initV, terminalB, N, staleCoeff, staleErr] <;>
    ring_nf

set_option maxHeartbeats 200000

/-- Eq. (5.2.75) plus Lemma 5.10 and the stale-gradient estimate give the pre-Delta bound.

This packages Lan Proposition 5.6 proof steps 22--23 in the exact shape consumed
by `proposition56_pre_delta_to_v_bound_positive_domain`. Candidate audit:
searched `Proposition56 pre delta outputWeightSum DeltaTilde expectationLe
positive domain`; the only existing consumer was the V rearrangement helper,
so this local bridge is the missing algebraic connection from Eq. (5.2.75) to
`DeltaTilde0Sigma0`. -/
private theorem proposition56_pre_delta_inequality_positive_domain
    {k : ℕ} {xStar : E} {sigma0 : ℝ}
    (hk : 1 ≤ k)
    (hη : S.PositiveEtaDomain)
    (hopt : S.IsOptimalSolution xStar)
    (hθ_pos : S.OutputWeightsPositive k)
    (hweight : S.WeightCondition5261 k)
    (hside : S.PropositionSideConditions k)
    (hq_rec :
      Finset.sum (outputWindow k)
          (fun t => S.θ t *
            SOptLib.expectation S.P
              (fun ω => S.Q (S.positiveEtaXIterate hη t ω) xStar)) ≤
        S.θ k * (1 + S.τ k) *
            Finset.sum Finset.univ
              (fun i => SOptLib.expectation S.P
                (fun ω => S.f i (S.positiveEtaBlockIterate hη k ω i))) +
          Finset.sum (outputWindow k)
            (fun t => S.θ t *
              SOptLib.expectation S.P
                (fun ω => S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.psi xStar)) -
          S.θ 1 * ((Fintype.card ι : ℝ) * (1 + S.τ 1) - 1) *
            (⟪S.x0 - xStar, tableAverage (fun i => S.gradF i xStar)⟫_ℝ +
              S.fAvg xStar))
    (h75 :
      S.θ k * (1 + S.τ k) *
          Finset.sum Finset.univ
            (fun i => SOptLib.expectation S.P
              (fun ω => S.f i (S.positiveEtaBlockIterate hη k ω i))) +
        Finset.sum (outputWindow k)
          (fun t => S.θ t *
            SOptLib.expectation S.P
              (fun ω => S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.psi xStar)) +
        (S.θ k * (S.μ + S.η k) / 2) *
          SOptLib.expectation S.P
            (fun ω => S.V (S.positiveEtaXIterate hη k ω) xStar) ≤
        S.θ 1 * ((Fintype.card ι : ℝ) * (1 + S.τ 1) - 1) * S.fAvg S.x0 +
          S.θ 1 * S.η 1 * S.V S.x0 xStar +
          Finset.sum (outputWindow k)
            (fun t =>
              (2 * S.θ t * S.α (t + 1) /
                  ((Fintype.card ι : ℝ) * S.η (t + 1))) *
                SOptLib.expectation S.P
                  (fun ω =>
                    S.dualNorm
                      (S.gradF (S.sample t ω)
                        (S.positiveEtaBlockIterate hη (t - 1) ω (S.sample t ω)) -
                       S.positiveEtaYIterate hη (t - 1) ω (S.sample t ω)) ^ 2)))
    (hstale_bound :
      ∀ t, t ∈ outputWindow k →
        SOptLib.expectation S.P
          (fun ω =>
            S.dualNorm
              (S.gradF (S.sample t ω)
                (S.positiveEtaBlockIterate hη (t - 1) ω (S.sample t ω)) -
               S.positiveEtaYIterate hη (t - 1) ω (S.sample t ω)) ^ 2) ≤
          (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) ^ (t - 1) *
            sigma0 ^ 2) :
    Finset.sum (outputWindow k)
        (fun t => S.θ t *
          SOptLib.expectation S.P
            (fun ω => S.Q (S.positiveEtaXIterate hη t ω) xStar)) +
      (S.θ k * (S.μ + S.η k) / 2) *
        SOptLib.expectation S.P
          (fun ω => S.V (S.positiveEtaXIterate hη k ω) xStar) ≤
      S.DeltaTilde0Sigma0 hη k xStar sigma0 := by
  classical
  let m : ℝ := (Fintype.card ι : ℝ)
  let qSum : ℝ :=
    Finset.sum (outputWindow k)
      (fun t => S.θ t *
        SOptLib.expectation S.P
          (fun ω => S.Q (S.positiveEtaXIterate hη t ω) xStar))
  let terminal : ℝ :=
    S.θ k * (1 + S.τ k) *
      Finset.sum Finset.univ
        (fun i => SOptLib.expectation S.P
          (fun ω => S.f i (S.positiveEtaBlockIterate hη k ω i)))
  let nuSum : ℝ :=
    Finset.sum (outputWindow k)
      (fun t => S.θ t *
        SOptLib.expectation S.P
          (fun ω => S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.psi xStar))
  let vTerm : ℝ :=
    (S.θ k * (S.μ + S.η k) / 2) *
      SOptLib.expectation S.P
        (fun ω => S.V (S.positiveEtaXIterate hη k ω) xStar)
  let e : ℝ := S.θ 1 * (m * (1 + S.τ 1) - 1)
  let D : ℝ :=
    e * (⟪S.x0 - xStar, tableAverage (fun i => S.gradF i xStar)⟫_ℝ +
      S.fAvg xStar)
  let staleSum : ℝ :=
    Finset.sum (outputWindow k)
      (fun t =>
        (2 * S.θ t * S.α (t + 1) /
            (m * S.η (t + 1))) *
          SOptLib.expectation S.P
            (fun ω =>
              S.dualNorm
                (S.gradF (S.sample t ω)
                  (S.positiveEtaBlockIterate hη (t - 1) ω (S.sample t ω)) -
                 S.positiveEtaYIterate hη (t - 1) ω (S.sample t ω)) ^ 2))
  let noiseBound : ℝ :=
    Finset.sum (outputWindow k)
      (fun t =>
        (((m - 1) / m) ^ (t - 1)) *
          (2 * S.θ t * S.α (t + 1) / (m * S.η (t + 1))) * sigma0 ^ 2)
  have hq_rec' : qSum ≤ terminal + nuSum - D := by
    simpa [qSum, terminal, nuSum, D, e, m] using hq_rec
  have h75' :
      terminal + nuSum + vTerm ≤ e * S.fAvg S.x0 + S.θ 1 * S.η 1 * S.V S.x0 xStar +
        staleSum := by
    simpa [terminal, nuSum, vTerm, staleSum, e, m] using h75
  have hm_nat : (1 : ℕ) ≤ Fintype.card ι := Nat.succ_le_of_lt Fintype.card_pos
  have hm_pos : 0 < m := by
    dsimp [m]
    exact_mod_cast Fintype.card_pos
  have hm_ge_one : 1 ≤ m := by
    dsimp [m]
    exact_mod_cast hm_nat
  have he_nonneg : 0 ≤ e := by
    have hθ1 : 0 < S.θ 1 := hθ_pos 1 (Finset.mem_Icc.mpr ⟨le_rfl, hk⟩)
    have hτ1 : 0 ≤ S.τ 1 := (S.hparam_nonneg 1).2.2
    have hcoef : 0 ≤ m * (1 + S.τ 1) - 1 := by
      nlinarith
    exact mul_nonneg hθ1.le hcoef
  have hinit_gap := S.proposition56_initial_linearized_gap_le_psi_gap hopt
  have hinitial :
      e * S.fAvg S.x0 - D ≤ e * (S.psi S.x0 - S.psi xStar) := by
    have hmul := mul_le_mul_of_nonneg_left hinit_gap he_nonneg
    nlinarith [hmul]
  have hnoise : staleSum ≤ noiseBound := by
    refine Finset.sum_le_sum ?_
    intro t ht
    let coeff : ℝ := 2 * S.θ t * S.α (t + 1) / (m * S.η (t + 1))
    have hθt : 0 ≤ S.θ t := (hθ_pos t ht).le
    have hαt : 0 ≤ S.α (t + 1) := (S.hparam_nonneg (t + 1)).1
    have hηnext : 0 < S.η (t + 1) := hη (t + 1) (Nat.succ_pos t)
    have hden_pos : 0 < m * S.η (t + 1) := mul_pos hm_pos hηnext
    have hcoeff_nonneg : 0 ≤ coeff := by
      exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hθt) hαt) hden_pos.le
    have hmul :=
      mul_le_mul_of_nonneg_left (hstale_bound t ht) hcoeff_nonneg
    simpa [staleSum, noiseBound, coeff, m, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hmain :
      qSum + vTerm ≤ e * (S.psi S.x0 - S.psi xStar) +
        S.θ 1 * S.η 1 * S.V S.x0 xStar + noiseBound := by
    have hqv : qSum + vTerm ≤ e * S.fAvg S.x0 + S.θ 1 * S.η 1 * S.V S.x0 xStar +
        staleSum - D := by
      nlinarith [hq_rec', h75']
    nlinarith [hqv, hinitial, hnoise]
  simpa [DeltaTilde0Sigma0, qSum, vTerm, noiseBound, e, m] using hmain

/-- Corrected positive-domain version of the general RGEM bound.

This is not exported under the original Proposition 5.6 name: it adds the
positive output-weight and positive-eta well-definedness domains required by
Eq. (5.2.53) and Eq. (5.2.9), respectively. The fresh conditional sampling law
used by Lemma 5.9 is consumed as a derived fact from the canonical sampled-block
stream; Bochner expectation well-definedness is consumed as a proof obligation
inside the proof, not as a theorem-head assumption. -/
theorem proposition_5_6_positive_domain
    {k : ℕ} {xStar : E} {sigma0 : ℝ}
    (hk : 1 ≤ k)
    (hη : S.PositiveEtaDomain)
    (hopt : S.IsOptimalSolution xStar)
    (hsigma : S.InitialGradientBound sigma0)
    (hθ_pos : S.OutputWeightsPositive k)
    (hweight : S.WeightCondition5261 k)
    (hside : S.PropositionSideConditions k) :
    expectationLe S.P
        (fun ω => S.Q (S.positiveEtaWeightedOutput hη k hk hθ_pos ω) xStar)
        ((S.outputWeightSum k)⁻¹ * S.DeltaTilde0Sigma0 hη k xStar sigma0) ∧
      expectationLe S.P
        (fun ω => S.V (S.positiveEtaXIterate hη k ω) xStar)
        (2 * S.DeltaTilde0Sigma0 hη k xStar sigma0 / (S.θ k * (S.μ + S.η k))) := by
  have hfresh : S.FreshConditionalBlockSampling := S.freshConditionalBlockSampling
  have hlemma510 :
      (∀ t, t ∈ outputWindow k →
          SOptLib.expectationWellDefined S.P
            (fun ω => S.Q (S.positiveEtaXIterate hη t ω) xStar)) ∧
        (∀ i, SOptLib.expectationWellDefined S.P
          (fun ω => S.f i (S.positiveEtaBlockIterate hη k ω i))) ∧
        (∀ t, t ∈ outputWindow k →
          SOptLib.expectationWellDefined S.P
            (fun ω => S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.psi xStar)) ∧
        Finset.sum (outputWindow k)
            (fun t => S.θ t *
              SOptLib.expectation S.P
                (fun ω => S.Q (S.positiveEtaXIterate hη t ω) xStar)) ≤
          S.θ k * (1 + S.τ k) *
              Finset.sum Finset.univ
                (fun i => SOptLib.expectation S.P
                  (fun ω => S.f i (S.positiveEtaBlockIterate hη k ω i))) +
            Finset.sum (outputWindow k)
              (fun t => S.θ t *
                SOptLib.expectation S.P
                  (fun ω => S.μ * S.ν (S.positiveEtaXIterate hη t ω) - S.psi xStar)) -
            S.θ 1 * ((Fintype.card ι : ℝ) * (1 + S.τ 1) - 1) *
              (⟪S.x0 - xStar, tableAverage (fun i => S.gradF i xStar)⟫_ℝ +
                S.fAvg xStar) :=
    S.WeightedQRecursion_Lemma_5_10_positive_domain hk hη hopt.1
      (S.outputWeightsNonnegative_of_positive hθ_pos) hweight
  have hwd :
      SOptLib.expectationWellDefined S.P
          (fun ω => S.Q (S.positiveEtaWeightedOutput hη k hk hθ_pos ω) xStar) ∧
        SOptLib.expectationWellDefined S.P
          (fun ω => S.V (S.positiveEtaXIterate hη k ω) xStar) :=
    by
      constructor
      · simpa [SOptLib.expectationWellDefined] using
          (S.positiveEta_weighted_output_payload_integrable hη hk hθ_pos
            (fun x => S.Q x xStar))
      · simpa [SOptLib.expectationWellDefined] using
          (S.positiveEta_strictPast_payload_integrable hη hk
            (G := fun x _prev => S.V x xStar))
  have hstale_bound :
      ∀ t, t ∈ outputWindow k →
        SOptLib.expectation S.P
          (fun ω =>
            S.dualNorm
              (S.gradF (S.sample t ω)
                (S.positiveEtaBlockIterate hη (t - 1) ω (S.sample t ω)) -
               S.positiveEtaYIterate hη (t - 1) ω (S.sample t ω)) ^ 2) ≤
          (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) ^ (t - 1) *
            sigma0 ^ 2 := by
    intro t _ht
    exact le_of_eq
      (selected_stale_gradient_expectation_eq_positive_domain (S := S) hη hsigma t)
  have h75 :=
    S.proposition56_residual_inequality_5_2_75_positive_domain
      hk hη hopt hθ_pos hweight hside
  have hpre :
      Finset.sum (outputWindow k)
          (fun t => S.θ t *
            SOptLib.expectation S.P
              (fun ω => S.Q (S.positiveEtaXIterate hη t ω) xStar)) +
        (S.θ k * (S.μ + S.η k) / 2) *
          SOptLib.expectation S.P
            (fun ω => S.V (S.positiveEtaXIterate hη k ω) xStar) ≤
        S.DeltaTilde0Sigma0 hη k xStar sigma0 :=
    S.proposition56_pre_delta_inequality_positive_domain
      hk hη hopt hθ_pos hweight hside hlemma510.2.2.2 h75 hstale_bound
  have hV :
      expectationLe S.P
        (fun ω => S.V (S.positiveEtaXIterate hη k ω) xStar)
        (2 * S.DeltaTilde0Sigma0 hη k xStar sigma0 /
          (S.θ k * (S.μ + S.η k))) :=
    S.proposition56_pre_delta_to_v_bound_positive_domain
      hk hη hopt hθ_pos hwd.2 hpre
  refine And.intro ?hQ hV
  let W : ℝ := S.outputWeightSum k
  let qSum : ℝ :=
    Finset.sum (outputWindow k)
      (fun t => S.θ t *
        SOptLib.expectation S.P
          (fun ω => S.Q (S.positiveEtaXIterate hη t ω) xStar))
  let vTerm : ℝ :=
    (S.θ k * (S.μ + S.η k) / 2) *
      SOptLib.expectation S.P
        (fun ω => S.V (S.positiveEtaXIterate hη k ω) xStar)
  have hW_pos : 0 < W := by
    simpa [W] using S.outputWeightSum_pos hk hθ_pos
  have hVexp_nonneg :
      0 ≤ SOptLib.expectation S.P
        (fun ω => S.V (S.positiveEtaXIterate hη k ω) xStar) := by
    unfold SOptLib.expectation
    exact integral_nonneg (fun ω => by
      have hxk := S.PrimalUpdateFeasibility_Eq_5_2_50_positive_domain hη k ω
      have hv :=
        S.ProxLowerBound_Eq_5_2_8 hxk hopt.1
      have hhalf_nonneg :
          0 ≤ (1 / 2 : ℝ) *
            S.primalNorm (xStar - S.positiveEtaXIterate hη k ω) ^ 2 := by
        nlinarith [sq_nonneg (S.primalNorm (xStar - S.positiveEtaXIterate hη k ω))]
      exact le_trans hhalf_nonneg hv)
  have hvTerm_nonneg : 0 ≤ vTerm := by
    have hk_mem : k ∈ outputWindow k := Finset.mem_Icc.mpr ⟨hk, le_rfl⟩
    have hθk : 0 ≤ S.θ k := (hθ_pos k hk_mem).le
    have hηk : 0 < S.η k := hη k hk
    have hmu_eta : 0 ≤ S.μ + S.η k :=
      (add_pos_of_nonneg_of_pos S.hμ_nonneg hηk).le
    have hcoeff : 0 ≤ S.θ k * (S.μ + S.η k) / 2 := by
      exact div_nonneg (mul_nonneg hθk hmu_eta) (by norm_num)
    exact mul_nonneg hcoeff hVexp_nonneg
  have hqSum_le_delta : qSum ≤ S.DeltaTilde0Sigma0 hη k xStar sigma0 := by
    have hpre' : qSum + vTerm ≤ S.DeltaTilde0Sigma0 hη k xStar sigma0 := by
      simpa [qSum, vTerm] using hpre
    nlinarith [hpre', hvTerm_nonneg]
  let rhsFun : BlockSamplePath ι → ℝ := fun ω =>
    W⁻¹ *
      Finset.sum (outputWindow k)
        (fun t => S.θ t * S.Q (S.positiveEtaXIterate hη t ω) xStar)
  have hrhs_int : Integrable rhsFun S.P := by
    refine (integrable_finset_sum (outputWindow k) ?_).const_mul W⁻¹
    intro t ht
    have htwd := hlemma510.1 t ht
    exact (show Integrable (fun ω => S.Q (S.positiveEtaXIterate hη t ω) xStar) S.P from htwd).const_mul (S.θ t)
  have hpoint : ∀ᵐ ω ∂S.P,
      S.Q (S.positiveEtaWeightedOutput hη k hk hθ_pos ω) xStar ≤ rhsFun ω := by
    filter_upwards with ω
    have hweights_sum : Finset.sum (outputWindow k) (fun t => W⁻¹ * S.θ t) = 1 := by
      calc
        Finset.sum (outputWindow k) (fun t => W⁻¹ * S.θ t) =
            W⁻¹ * Finset.sum (outputWindow k) S.θ := by
          rw [Finset.mul_sum]
        _ = W⁻¹ * W := by
          simp [W, outputWeightSum]
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hW_pos)
    have hweights_nonneg :
        ∀ t ∈ outputWindow k, 0 ≤ W⁻¹ * S.θ t := by
      intro t ht
      exact mul_nonneg (inv_nonneg.mpr hW_pos.le) (hθ_pos t ht).le
    have hp_mem :
        ∀ t ∈ outputWindow k, S.positiveEtaXIterate hη t ω ∈ S.X := by
      intro t _ht
      exact S.PrimalUpdateFeasibility_Eq_5_2_50_positive_domain hη t ω
    have haverage :
        S.positiveEtaWeightedOutput hη k hk hθ_pos ω =
          Finset.sum (outputWindow k)
            (fun t => (W⁻¹ * S.θ t) • S.positiveEtaXIterate hη t ω) := by
      calc
        S.positiveEtaWeightedOutput hη k hk hθ_pos ω =
            W⁻¹ •
              Finset.sum (outputWindow k)
                (fun t => S.θ t • S.positiveEtaXIterate hη t ω) := by
          simpa [W] using S.WeightedOutputDefinition_Eq_5_2_53_positive_domain hη k hk hθ_pos ω
        _ =
            Finset.sum (outputWindow k)
              (fun t => (W⁻¹ * S.θ t) • S.positiveEtaXIterate hη t ω) := by
          simp [Finset.smul_sum, smul_smul, mul_assoc]
    have hJ :=
      (S.q_convexOn_positive_domain xStar).map_sum_le
        (t := outputWindow k) (w := fun t => W⁻¹ * S.θ t)
        (p := fun t => S.positiveEtaXIterate hη t ω)
        hweights_nonneg hweights_sum hp_mem
    rw [← haverage] at hJ
    have hright :
        Finset.sum (outputWindow k)
            (fun t => (W⁻¹ * S.θ t) •
              S.Q (S.positiveEtaXIterate hη t ω) xStar) =
          rhsFun ω := by
      calc
        Finset.sum (outputWindow k)
            (fun t => (W⁻¹ * S.θ t) •
              S.Q (S.positiveEtaXIterate hη t ω) xStar)
            =
          Finset.sum (outputWindow k)
            (fun t => W⁻¹ * (S.θ t *
              S.Q (S.positiveEtaXIterate hη t ω) xStar)) := by
            refine Finset.sum_congr rfl ?_
            intro t _ht
            simp [smul_eq_mul, mul_assoc]
        _ = rhsFun ω := by
            simp [rhsFun, Finset.mul_sum]
    have hright_expanded :
        Finset.sum (outputWindow k)
            (fun t => W⁻¹ * S.θ t *
              S.Q (S.positiveEtaXIterate hη t ω) xStar) =
          rhsFun ω := by
      calc
        Finset.sum (outputWindow k)
            (fun t => W⁻¹ * S.θ t *
              S.Q (S.positiveEtaXIterate hη t ω) xStar)
            =
          Finset.sum (outputWindow k)
            (fun t => W⁻¹ * (S.θ t *
              S.Q (S.positiveEtaXIterate hη t ω) xStar)) := by
            refine Finset.sum_congr rfl ?_
            intro t _ht
            ring
        _ = rhsFun ω := by
            simp [rhsFun, Finset.mul_sum]
    exact hJ.trans (le_of_eq hright_expanded)
  have hJensen_expect :
      SOptLib.expectation S.P
          (fun ω => S.Q (S.positiveEtaWeightedOutput hη k hk hθ_pos ω) xStar) ≤
        W⁻¹ * qSum := by
    have hmono :
        (∫ ω, S.Q (S.positiveEtaWeightedOutput hη k hk hθ_pos ω) xStar ∂S.P) ≤
          ∫ ω, rhsFun ω ∂S.P := by
      exact integral_mono_ae hwd.1 hrhs_int hpoint
    have hrhs_eq :
        SOptLib.expectation S.P rhsFun = W⁻¹ * qSum := by
      have hsum_int :
          ∀ t ∈ outputWindow k,
            Integrable
              (fun ω => S.θ t * S.Q (S.positiveEtaXIterate hη t ω) xStar) S.P := by
        intro t ht
        exact (show Integrable (fun ω => S.Q (S.positiveEtaXIterate hη t ω) xStar) S.P from
          hlemma510.1 t ht).const_mul (S.θ t)
      unfold SOptLib.expectation rhsFun qSum
      rw [integral_const_mul]
      · congr 1
        rw [integral_finset_sum (s := outputWindow k)
          (f := fun t ω => S.θ t * S.Q (S.positiveEtaXIterate hη t ω) xStar)
          hsum_int]
        refine Finset.sum_congr rfl ?_
        intro t ht
        simp [SOptLib.expectation, integral_const_mul]
    simpa [SOptLib.expectation] using hmono.trans (le_of_eq hrhs_eq)
  refine And.intro hwd.1 ?_
  calc
    SOptLib.expectation S.P
        (fun ω => S.Q (S.positiveEtaWeightedOutput hη k hk hθ_pos ω) xStar)
        ≤ W⁻¹ * qSum := hJensen_expect
    _ ≤ W⁻¹ * S.DeltaTilde0Sigma0 hη k xStar sigma0 := by
      exact mul_le_mul_of_nonneg_left hqSum_le_delta (inv_nonneg.mpr hW_pos.le)
    _ = (S.outputWeightSum k)⁻¹ * S.DeltaTilde0Sigma0 hη k xStar sigma0 := by
      simp [W]

/-- Finite geometric sums with ratio in `[0,1)` are bounded by the infinite
geometric denominator.

This is route-local scalar infrastructure for Lan Theorem 5.4 proof step 8.
Candidate audit: checked Mathlib `geom_sum_mul`, `geom_sum_mul_neg`,
`geom_sum_eq`, and searched SOptLib for `finite geometric sum ratio less one
bound`; no imported theorem exposed this exact inequality over finite real
ranges, so this helper packages the standard ordered-field consequence. -/
private theorem geom_sum_range_le_inv_one_sub
    {r : ℝ} {n : ℕ} (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1) :
    (Finset.range n).sum (fun j => r ^ j) ≤ (1 - r)⁻¹ := by
  have hden_pos : 0 < 1 - r := sub_pos.mpr hr_lt_one
  have hden_nonneg : 0 ≤ 1 - r := hden_pos.le
  have hpow_nonneg : 0 ≤ r ^ n := pow_nonneg hr_nonneg n
  have hgeom :
      ((Finset.range n).sum (fun j => r ^ j)) * (1 - r) = 1 - r ^ n := by
    simpa using (geom_sum_mul_neg r n)
  have hmul_le :
      ((Finset.range n).sum (fun j => r ^ j)) * (1 - r) ≤ 1 := by
    rw [hgeom]
    nlinarith [hpow_nonneg]
  calc
    (Finset.range n).sum (fun j => r ^ j)
        = ((Finset.range n).sum (fun j => r ^ j)) * (1 - r) / (1 - r) := by
          field_simp [ne_of_gt hden_pos]
    _ ≤ 1 / (1 - r) := div_le_div_of_nonneg_right hmul_le hden_nonneg
    _ = (1 - r)⁻¹ := by rw [one_div]

/-- Scalar sqrt budget behind Theorem 5.4 side conditions (5.2.67)--(5.2.68).

No SOptLib match: searched `sqrt budget cross terminal scalar alpha theorem`,
`Real sqrt squared nonnegative inequality budget`, and `divide inequality by
positive right real`; scanned `SOptLib/Model/ParameterChoices.lean` and
`SOptLib/Layer1/Telescope.lean`. The hits cover other schedules or aggregate
budgets, while Lan Eq. (5.2.77) requires the literal
`sqrt (m^2 + 16*m*Lhat/μ)` closed form used here. -/
private theorem theorem54_sqrt_budget_cross_terminal_scalar
    {m μ L a : ℝ}
    (hm_pos : 0 < m) (hμ_pos : 0 < μ) (hL_nonneg : 0 ≤ L)
    (ha_pos : 0 < a)
    (ha_def : a = 1 - (m + Real.sqrt (m ^ 2 + 16 * m * L / μ))⁻¹) :
    2 * (m * a) * L ≤
        m * (((m * (1 - a))⁻¹ - 1)) * (a / (1 - a) * μ) ∧
      4 * L ≤
        (((m * (1 - a))⁻¹ - 1)) * (μ + a / (1 - a) * μ) :=
  _root_.sqrt_schedule_cross_terminal_bounds hm_pos hμ_pos hL_nonneg ha_pos ha_def

/-- The Theorem 5.4 square-root choice implies `m(1-α) ≤ 1/2`.

Aligns with Lan Theorem 5.4 proof step 9 after Eq. (5.2.77). Candidate audit:
searched `alpha greater (2*m-1)/(2*m) one minus alpha card`,
`geometric series alpha one minus power finite sum`, and checked
`SOptLib.sqrt_alpha_schedule_pos_lt_one_log_neg`; that SOptLib theorem has a
different closed form, so the staged Glue lemma packages the literal RGEM
`m+sqrt(m^2+16m Lhat/μ)` half-budget schedule. -/
private theorem theorem54_card_mul_one_minus_alpha_le_half
    (hμ_pos : 0 < S.μ) :
    (Fintype.card ι : ℝ) * (1 - S.theoremAlpha hμ_pos) ≤ 1 / 2 := by
  have hm_pos : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  simpa [theoremAlpha, SOptLib.sqrtDenominatorContractionAlpha_def] using
    _root_.mul_one_sub_sqrt_schedule_alpha_le_half
      (m := (Fintype.card ι : ℝ)) (mu := S.μ) (L := S.Lhat)
      hm_pos hμ_pos S.Lhat_nonneg

/-- Lower-bound form of Lan's observation `α ≥ (2m-1)/(2m)`.

Aligns with Theorem 5.4 proof step 8. This is derived from
`theorem54_card_mul_one_minus_alpha_le_half`, whose proof now specializes the
staged square-root half-budget lemma. -/
private theorem theorem54_alpha_ge_two_card_minus_one_div_two_card
    (hμ_pos : 0 < S.μ) :
    ((2 * (Fintype.card ι : ℝ) - 1) / (2 * (Fintype.card ι : ℝ))) ≤
      S.theoremAlpha hμ_pos := by
  classical
  let m : ℝ := (Fintype.card ι : ℝ)
  have hm_pos : 0 < m := by
    dsimp [m]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hm_ne : m ≠ 0 := ne_of_gt hm_pos
  have hhalf := S.theorem54_card_mul_one_minus_alpha_le_half hμ_pos
  have hone_minus_le : 1 - S.theoremAlpha hμ_pos ≤ 1 / (2 * m) := by
    have hdiv :
        m * (1 - S.theoremAlpha hμ_pos) / m ≤ (1 / 2) / m :=
      div_le_div_of_nonneg_right (by simpa [m] using hhalf) hm_pos.le
    calc
      1 - S.theoremAlpha hμ_pos =
          m * (1 - S.theoremAlpha hμ_pos) / m := by field_simp [hm_ne]
      _ ≤ (1 / 2) / m := hdiv
      _ = 1 / (2 * m) := by field_simp [hm_ne]
  have htarget_eq : (2 * m - 1) / (2 * m) = 1 - 1 / (2 * m) := by
    field_simp [hm_ne]
  rw [show (2 * (Fintype.card ι : ℝ) - 1) /
      (2 * (Fintype.card ι : ℝ)) = (2 * m - 1) / (2 * m) by rfl,
    htarget_eq]
  linarith

/-- Geometric stale-gradient mass bound used in the Theorem 5.4 Delta reduction.

This is the reindexed scalar core of Lan Theorem 5.4 proof step 8:
`α ≥ (2m-1)/(2m)` implies
`α⁻¹ ∑_{j=0}^{k-1} ((m-1)/(mα))^j ≤ 2m`. Candidate audit: searched
`finite geometric sum ratio less one bound` and checked Mathlib
`geom_sum_mul_neg`; the staged Glue lemma now packages the RGEM ratio comparison
with the finite real geometric denominator. -/
private theorem theorem54_scaled_stale_geometric_sum_le_two_card
    {m a : ℝ} {k : ℕ}
    (hm_ge_one : 1 ≤ m)
    (ha_pos : 0 < a)
    (ha_lower : (2 * m - 1) / (2 * m) ≤ a) :
    a⁻¹ * (Finset.range k).sum (fun j => ((m - 1) / (m * a)) ^ j) ≤ 2 * m := by
  exact inv_mul_sum_range_sub_one_div_mul_le_two_mul_of_lower_bound
    (m := m) (a := a) (k := k) hm_ge_one ha_pos ha_lower

/-- Scalar stale-gradient noise budget after the Theorem 5.4 geometric reduction.

Aligns with Lan Theorem 5.4 proof step 9: after reindexing the stale-gradient
sum and applying `theorem54_scaled_stale_geometric_sum_le_two_card`, the fact
`m(1-α) ≤ 1/2` makes the remaining noise term fit inside the
`(1-α)⁻¹ * σ₀²/(mμ)` part of `Δ_{0,σ₀}`. Candidate audit: searched
`DeltaTilde Delta0 stale geometric sigma budget`, `geometric sum outputWindow
theoremTheta outputWeightSum alpha`, and checked the local candidates
`theorem54_scaled_stale_geometric_sum_le_two_card`,
`theorem54_card_mul_one_minus_alpha_le_half`, and
`theorem54_alpha_ge_two_card_minus_one_div_two_card`; no SOptLib/Mathlib theorem
combined this RGEM-specific alpha schedule with the final noise-budget
comparison. -/
private theorem theorem54_stale_noise_budget_le_delta_noise
    {m μ a sigma0 : ℝ} {k : ℕ}
    (hm_ge_one : 1 ≤ m)
    (hμ_pos : 0 < μ)
    (ha_pos : 0 < a)
    (ha_lt_one : a < 1)
    (ha_lower : (2 * m - 1) / (2 * m) ≤ a)
    (hm_one_minus : m * (1 - a) ≤ 1 / 2) :
    (2 * (1 - a) / μ) *
        (a⁻¹ * (Finset.range k).sum (fun j => ((m - 1) / (m * a)) ^ j)) *
        sigma0 ^ 2 ≤
      (1 - a)⁻¹ * (sigma0 ^ 2 / (m * μ)) := by
  exact _root_.stale_geometric_noise_budget_le_inverse_contraction_variance_budget
    (m := m) (mu := μ) (a := a) (sigma0 := sigma0) (k := k)
    hm_ge_one hμ_pos ha_pos ha_lt_one ha_lower hm_one_minus

/-- Reindex the RGEM one-based output window as a zero-based range.

This is the finite-sum bridge needed by Lan Theorem 5.4 proof step 8 when the
stale-gradient sum over `t = 1, ..., k` is rewritten with `j = t - 1`. Candidate
audit: searched `sum Icc one to k reindex range predecessor`, checked local
`proposition56_outputWindow_predecessor_sum_add_terminal_eq` and SOptLib
one-based telescope helpers; none states this direct shifted-range identity. -/
private theorem outputWindow_sum_eq_range_succ (k : ℕ) (F : ℕ → ℝ) :
    Finset.sum (outputWindow k) F =
      (Finset.range k).sum (fun j => F (j + 1)) := by
  simpa [outputWindow] using sum_Icc_one_eq_sum_range_succ (M := ℝ) k F

/-- Constant-policy expansion of Proposition 5.6's `Δ̃_{0,σ₀}` for Theorem 5.4.

This is the exact reindexing/normalization step behind Lan Eq. (5.2.81): after
substituting `θ_t = α⁻ᵗ`, `τ_t = (m(1-α))⁻¹-1`, `η_t = αμ/(1-α)`, and
`α_t = mα`, the deterministic part of `Δ̃` becomes
`(1-α)⁻¹(μV(x⁰,x*) + ψ(x⁰)-ψ(x*))`, while the stale-gradient sum is bounded by
the normalized range geometric mass below. Candidate audit: searched
`DeltaTilde Delta0 stale geometric sigma budget`, `geometric sum outputWindow
theoremTheta outputWeightSum alpha`, scanned `SOptLib/Model/Budget.lean`,
`SOptLib/Model/ParameterChoices.lean`, and checked the target-file candidates
`DeltaTilde0Sigma0`, `Delta0Sigma0_nonneg`,
`theorem54_scaled_stale_geometric_sum_le_two_card`; none states this
RGEM-specific Eq. (5.2.81) expansion. -/
private theorem theorem54_delta_tilde_constant_policy_le_expanded
    {k : ℕ} {xStar : E} {sigma0 : ℝ}
    (hμ_pos : 0 < S.μ)
    (hηθ :
      ({ S with θ := S.theoremTheta hμ_pos } : Setup ι E).PositiveEtaDomain)
    (hτ_policy : ∀ t, 1 ≤ t → S.τ t = S.constantTau hμ_pos)
    (hη_policy : ∀ t, 1 ≤ t → S.η t = S.constantEta hμ_pos)
    (hα_policy : ∀ t, 1 ≤ t → S.α t = S.constantAlphaStep hμ_pos) :
    ({ S with θ := S.theoremTheta hμ_pos } : Setup ι E).DeltaTilde0Sigma0
        hηθ k xStar sigma0 ≤
      (1 - S.theoremAlpha hμ_pos)⁻¹ *
          (S.μ * S.V S.x0 xStar + S.psi S.x0 - S.psi xStar) +
        (2 * (1 - S.theoremAlpha hμ_pos) / S.μ) *
          ((S.theoremAlpha hμ_pos)⁻¹ *
            (Finset.range k).sum (fun j =>
              (((Fintype.card ι : ℝ) - 1) /
                ((Fintype.card ι : ℝ) * S.theoremAlpha hμ_pos)) ^ j)) *
          sigma0 ^ 2 := by
  classical
  let Sθ : Setup ι E := { S with θ := S.theoremTheta hμ_pos }
  let a : ℝ := S.theoremAlpha hμ_pos
  let m : ℝ := (Fintype.card ι : ℝ)
  rcases S.theoremAlpha_pos_lt_one hμ_pos with ⟨ha_pos_raw, ha_lt_raw⟩
  have ha_pos : 0 < a := by simpa [a] using ha_pos_raw
  have ha_lt_one : a < 1 := by simpa [a] using ha_lt_raw
  have h1ma_pos : 0 < 1 - a := sub_pos.mpr ha_lt_one
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have h1ma_ne : 1 - a ≠ 0 := ne_of_gt h1ma_pos
  have hμ_ne : S.μ ≠ 0 := ne_of_gt hμ_pos
  have hm_pos : 0 < m := by
    dsimp [m]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hm_ne : m ≠ 0 := ne_of_gt hm_pos
  have hma_ne : m * a ≠ 0 := mul_ne_zero hm_ne ha_ne
  have hm1ma_ne : m * (1 - a) ≠ 0 := mul_ne_zero hm_ne h1ma_ne
  have hmul_inv_m_one_minus :
      m * (m * (1 - a))⁻¹ = (1 - a)⁻¹ := by
    calc
      m * (m * (1 - a))⁻¹ = m * ((1 - a)⁻¹ * m⁻¹) := by
        rw [mul_inv_rev]
      _ = (m * m⁻¹) * (1 - a)⁻¹ := by ring
      _ = (1 - a)⁻¹ := by
        rw [mul_inv_cancel₀ hm_ne, one_mul]
  have htau_coeff_inner :
      m * (1 + ((m * (1 - a))⁻¹ - 1)) - 1 = a / (1 - a) := by
    calc
      m * (1 + ((m * (1 - a))⁻¹ - 1)) - 1
          = m * (m * (1 - a))⁻¹ - 1 := by ring
      _ = (1 - a)⁻¹ - 1 := by rw [hmul_inv_m_one_minus]
      _ = a / (1 - a) := by
        have hone_as_mul : 1 = (1 - a) * (1 - a)⁻¹ := by
          rw [mul_inv_cancel₀ h1ma_ne]
        calc
          (1 - a)⁻¹ - 1 = (1 - a)⁻¹ - (1 - a) * (1 - a)⁻¹ := by
            congr 1
          _ = a / (1 - a) := by
            rw [div_eq_mul_inv]
            ring
  have htau_coeff :
      a⁻¹ * (m * (1 + ((m * (1 - a))⁻¹ - 1)) - 1) = (1 - a)⁻¹ := by
    calc
      a⁻¹ * (m * (1 + ((m * (1 - a))⁻¹ - 1)) - 1)
          = a⁻¹ * (a / (1 - a)) := by rw [htau_coeff_inner]
      _ = (a⁻¹ * a) * (1 - a)⁻¹ := by
        rw [div_eq_mul_inv]
        ring
      _ = (1 - a)⁻¹ := by
        rw [inv_mul_cancel₀ ha_ne, one_mul]
  have heta_coeff :
      a⁻¹ * (a / (1 - a) * S.μ) = (1 - a)⁻¹ * S.μ := by
    calc
      a⁻¹ * (a / (1 - a) * S.μ)
          = (a⁻¹ * a) * (1 - a)⁻¹ * S.μ := by
        rw [div_eq_mul_inv]
        ring
      _ = (1 - a)⁻¹ * S.μ := by
        rw [inv_mul_cancel₀ ha_ne, one_mul]
  have hdet :
      Sθ.θ 1 * (m * (1 + Sθ.τ 1) - 1) *
          (S.psi S.x0 - S.psi xStar) +
        Sθ.θ 1 * Sθ.η 1 * S.V S.x0 xStar =
      (1 - a)⁻¹ *
        (S.μ * S.V S.x0 xStar + S.psi S.x0 - S.psi xStar) := by
    have hτ1 : Sθ.τ 1 = (m * (1 - a))⁻¹ - 1 := by
      change S.τ 1 = (m * (1 - a))⁻¹ - 1
      simpa [constantTau, a, m] using hτ_policy 1 (by norm_num)
    have hη1 : Sθ.η 1 = a / (1 - a) * S.μ := by
      change S.η 1 = a / (1 - a) * S.μ
      simpa [constantEta, a] using hη_policy 1 (by norm_num)
    have hθ1 : Sθ.θ 1 = a⁻¹ := by
      change S.theoremTheta hμ_pos 1 = a⁻¹
      simp [theoremTheta, a]
    rw [hτ1, hη1, hθ1]
    calc
      a⁻¹ * (m * (1 + ((m * (1 - a))⁻¹ - 1)) - 1) *
            (S.psi S.x0 - S.psi xStar) +
          a⁻¹ * (a / (1 - a) * S.μ) * S.V S.x0 xStar
          =
        (1 - a)⁻¹ * (S.psi S.x0 - S.psi xStar) +
          ((1 - a)⁻¹ * S.μ) * S.V S.x0 xStar := by
            rw [htau_coeff, heta_coeff]
      _ = (1 - a)⁻¹ *
          (S.μ * S.V S.x0 xStar + S.psi S.x0 - S.psi xStar) := by
            ring
  have hden_cancel :
      (m * a) / (m * (a / (1 - a) * S.μ)) = (1 - a) / S.μ := by
    simp [div_eq_mul_inv, mul_inv_rev, hm_ne, ha_ne, h1ma_ne, hμ_ne,
      mul_assoc, mul_left_comm, mul_comm]
    calc
      a * ((1 - a) * a⁻¹) = (a * a⁻¹) * (1 - a) := by ring
      _ = 1 - a := by rw [mul_inv_cancel₀ ha_ne, one_mul]
  have hratio_base :
      (m - 1) / (m * a) = ((m - 1) / m) * a⁻¹ := by
    simp [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm]
  have hstale :
      Finset.sum (outputWindow k) (fun t =>
        ((((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) ^ (t - 1)) *
          (2 * Sθ.θ t * Sθ.α (t + 1) /
            ((Fintype.card ι : ℝ) * Sθ.η (t + 1))) * sigma0 ^ 2) =
        (2 * (1 - a) / S.μ) *
          (a⁻¹ * (Finset.range k).sum (fun j => ((m - 1) / (m * a)) ^ j)) *
            sigma0 ^ 2 := by
    rw [outputWindow_sum_eq_range_succ]
    calc
      (Finset.range k).sum (fun j =>
          (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) ^ ((j + 1) - 1) *
            (2 * Sθ.θ (j + 1) * Sθ.α ((j + 1) + 1) /
              ((Fintype.card ι : ℝ) * Sθ.η ((j + 1) + 1))) * sigma0 ^ 2)
          =
        (Finset.range k).sum (fun j =>
          (2 * (1 - a) / S.μ) *
            (a⁻¹ * ((m - 1) / (m * a)) ^ j) * sigma0 ^ 2) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hαj : Sθ.α ((j + 1) + 1) = m * a := by
              change S.α ((j + 1) + 1) = m * a
              simpa [constantAlphaStep, a, m] using
                hα_policy ((j + 1) + 1) (by omega)
            have hηj : Sθ.η ((j + 1) + 1) = a / (1 - a) * S.μ := by
              change S.η ((j + 1) + 1) = a / (1 - a) * S.μ
              simpa [constantEta, a] using hη_policy ((j + 1) + 1) (by omega)
            have hθj : Sθ.θ (j + 1) = (a ^ (j + 1))⁻¹ := by
              change S.theoremTheta hμ_pos (j + 1) = (a ^ (j + 1))⁻¹
              simp [theoremTheta, a]
            rw [hαj, hηj, hθj]
            have hpred : (j + 1) - 1 = j := by omega
            rw [hpred]
            change
              ((m - 1) / m) ^ j *
                  (2 * (a ^ (j + 1))⁻¹ * (m * a) /
                    (m * (a / (1 - a) * S.μ))) * sigma0 ^ 2 =
                2 * (1 - a) / S.μ *
                  (a⁻¹ * ((m - 1) / (m * a)) ^ j) * sigma0 ^ 2
            have hden_cancel_j :
                2 * (a ^ (j + 1))⁻¹ * (m * a) /
                    (m * (a / (1 - a) * S.μ)) =
                  2 * (a ^ (j + 1))⁻¹ * ((1 - a) / S.μ) := by
              rw [mul_div_assoc, hden_cancel]
            rw [hden_cancel_j, hratio_base, mul_pow]
            rw [← inv_pow]
            rw [pow_succ]
            ring
      _ = (2 * (1 - a) / S.μ) *
          (a⁻¹ * (Finset.range k).sum (fun j => ((m - 1) / (m * a)) ^ j)) *
            sigma0 ^ 2 := by
            calc
              (Finset.range k).sum (fun j =>
                  (2 * (1 - a) / S.μ) *
                    (a⁻¹ * ((m - 1) / (m * a)) ^ j) * sigma0 ^ 2)
                  =
                (Finset.range k).sum (fun j =>
                  ((2 * (1 - a) / S.μ) * a⁻¹ * sigma0 ^ 2) *
                    ((m - 1) / (m * a)) ^ j) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    ring
              _ =
                ((2 * (1 - a) / S.μ) * a⁻¹ * sigma0 ^ 2) *
                  (Finset.range k).sum (fun j => ((m - 1) / (m * a)) ^ j) := by
                    rw [Finset.mul_sum]
              _ = (2 * (1 - a) / S.μ) *
                  (a⁻¹ * (Finset.range k).sum
                    (fun j => ((m - 1) / (m * a)) ^ j)) * sigma0 ^ 2 := by
                    ring
  change Sθ.DeltaTilde0Sigma0 hηθ k xStar sigma0 ≤
    (1 - a)⁻¹ * (S.μ * S.V S.x0 xStar + S.psi S.x0 - S.psi xStar) +
      (2 * (1 - a) / S.μ) *
        (a⁻¹ * (Finset.range k).sum (fun j => ((m - 1) / (m * a)) ^ j)) *
          sigma0 ^ 2
  apply le_of_eq
  unfold DeltaTilde0Sigma0
  change
      Sθ.θ 1 * (m * (1 + Sθ.τ 1) - 1) *
          (S.psi S.x0 - S.psi xStar) +
        Sθ.θ 1 * Sθ.η 1 * S.V S.x0 xStar +
        Finset.sum (outputWindow k) (fun t =>
          ((((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) ^ (t - 1)) *
            (2 * Sθ.θ t * Sθ.α (t + 1) /
              ((Fintype.card ι : ℝ) * Sθ.η (t + 1))) * sigma0 ^ 2) =
      (1 - a)⁻¹ *
          (S.μ * S.V S.x0 xStar + S.psi S.x0 - S.psi xStar) +
        (2 * (1 - a) / S.μ) *
          (a⁻¹ * (Finset.range k).sum (fun j => ((m - 1) / (m * a)) ^ j)) *
            sigma0 ^ 2
  calc
    Sθ.θ 1 * (m * (1 + Sθ.τ 1) - 1) *
          (S.psi S.x0 - S.psi xStar) +
        Sθ.θ 1 * Sθ.η 1 * S.V S.x0 xStar +
        Finset.sum (outputWindow k) (fun t =>
          ((((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) ^ (t - 1)) *
            (2 * Sθ.θ t * Sθ.α (t + 1) /
              ((Fintype.card ι : ℝ) * Sθ.η (t + 1))) * sigma0 ^ 2)
        =
      (Sθ.θ 1 * (m * (1 + Sθ.τ 1) - 1) *
          (S.psi S.x0 - S.psi xStar) +
        Sθ.θ 1 * Sθ.η 1 * S.V S.x0 xStar) +
        Finset.sum (outputWindow k) (fun t =>
          ((((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) ^ (t - 1)) *
            (2 * Sθ.θ t * Sθ.α (t + 1) /
              ((Fintype.card ι : ℝ) * Sθ.η (t + 1))) * sigma0 ^ 2) := by
          ring
    _ =
      (1 - a)⁻¹ *
          (S.μ * S.V S.x0 xStar + S.psi S.x0 - S.psi xStar) +
        (2 * (1 - a) / S.μ) *
          (a⁻¹ * (Finset.range k).sum (fun j => ((m - 1) / (m * a)) ^ j)) *
            sigma0 ^ 2 := by
          rw [hdet, hstale]

/-- The Theorem 5.4 policy reduces `Δ̃_{0,σ₀}` to `(1-α)⁻¹ Δ_{0,σ₀}`.

Aligns with Lan Eq. (5.2.81). This consumes the constant-policy expansion,
`theorem54_scaled_stale_geometric_sum_le_two_card`,
`theorem54_card_mul_one_minus_alpha_le_half`,
`theorem54_alpha_ge_two_card_minus_one_div_two_card`, and
`theoremAlpha_pos_lt_one`; the only paper-specific exact step is isolated in
`theorem54_delta_tilde_constant_policy_le_expanded`. -/
private theorem theorem54_delta_tilde_le_delta0_over_one_minus_alpha
    {k : ℕ} {xStar : E} {sigma0 : ℝ}
    (hμ_pos : 0 < S.μ)
    (hηθ :
      ({ S with θ := S.theoremTheta hμ_pos } : Setup ι E).PositiveEtaDomain)
    (hτ_policy : ∀ t, 1 ≤ t → S.τ t = S.constantTau hμ_pos)
    (hη_policy : ∀ t, 1 ≤ t → S.η t = S.constantEta hμ_pos)
    (hα_policy : ∀ t, 1 ≤ t → S.α t = S.constantAlphaStep hμ_pos) :
    ({ S with θ := S.theoremTheta hμ_pos } : Setup ι E).DeltaTilde0Sigma0
        hηθ k xStar sigma0 ≤
      (1 - S.theoremAlpha hμ_pos)⁻¹ *
        S.Delta0Sigma0 hμ_pos xStar sigma0 := by
  classical
  let a : ℝ := S.theoremAlpha hμ_pos
  let m : ℝ := (Fintype.card ι : ℝ)
  have hm_ge_one : 1 ≤ m := by
    dsimp [m]
    exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos : 0 < Fintype.card ι))
  rcases S.theoremAlpha_pos_lt_one hμ_pos with ⟨ha_pos_raw, ha_lt_raw⟩
  have ha_pos : 0 < a := by simpa [a] using ha_pos_raw
  have ha_lt_one : a < 1 := by simpa [a] using ha_lt_raw
  have ha_lower : (2 * m - 1) / (2 * m) ≤ a := by
    simpa [a, m] using S.theorem54_alpha_ge_two_card_minus_one_div_two_card hμ_pos
  have hm_one_minus : m * (1 - a) ≤ 1 / 2 := by
    simpa [a, m] using S.theorem54_card_mul_one_minus_alpha_le_half hμ_pos
  have hnoise :
      (2 * (1 - a) / S.μ) *
          (a⁻¹ * (Finset.range k).sum (fun j => ((m - 1) / (m * a)) ^ j)) *
          sigma0 ^ 2 ≤
        (1 - a)⁻¹ * (sigma0 ^ 2 / (m * S.μ)) :=
    theorem54_stale_noise_budget_le_delta_noise
      (m := m) (μ := S.μ) (a := a) (sigma0 := sigma0) (k := k)
      hm_ge_one hμ_pos ha_pos ha_lt_one ha_lower hm_one_minus
  have hexpand :=
    S.theorem54_delta_tilde_constant_policy_le_expanded
      (k := k) (xStar := xStar) (sigma0 := sigma0)
      hμ_pos hηθ hτ_policy hη_policy hα_policy
  have hmain :
      (1 - S.theoremAlpha hμ_pos)⁻¹ *
          (S.μ * S.V S.x0 xStar + S.psi S.x0 - S.psi xStar) +
        (2 * (1 - S.theoremAlpha hμ_pos) / S.μ) *
          ((S.theoremAlpha hμ_pos)⁻¹ *
            (Finset.range k).sum (fun j =>
              (((Fintype.card ι : ℝ) - 1) /
                ((Fintype.card ι : ℝ) * S.theoremAlpha hμ_pos)) ^ j)) *
          sigma0 ^ 2 ≤
        (1 - S.theoremAlpha hμ_pos)⁻¹ *
          S.Delta0Sigma0 hμ_pos xStar sigma0 := by
    have hnoise' :
        (2 * (1 - S.theoremAlpha hμ_pos) / S.μ) *
            ((S.theoremAlpha hμ_pos)⁻¹ *
              (Finset.range k).sum (fun j =>
                (((Fintype.card ι : ℝ) - 1) /
                  ((Fintype.card ι : ℝ) * S.theoremAlpha hμ_pos)) ^ j)) *
            sigma0 ^ 2 ≤
          (1 - S.theoremAlpha hμ_pos)⁻¹ *
            (sigma0 ^ 2 / ((Fintype.card ι : ℝ) * S.μ)) := by
      simpa [a, m] using hnoise
    have hadd :=
      add_le_add_left hnoise'
        ((1 - S.theoremAlpha hμ_pos)⁻¹ *
          (S.μ * S.V S.x0 xStar + S.psi S.x0 - S.psi xStar))
    calc
      (1 - S.theoremAlpha hμ_pos)⁻¹ *
          (S.μ * S.V S.x0 xStar + S.psi S.x0 - S.psi xStar) +
        (2 * (1 - S.theoremAlpha hμ_pos) / S.μ) *
          ((S.theoremAlpha hμ_pos)⁻¹ *
            (Finset.range k).sum (fun j =>
              (((Fintype.card ι : ℝ) - 1) /
                ((Fintype.card ι : ℝ) * S.theoremAlpha hμ_pos)) ^ j)) *
          sigma0 ^ 2
          ≤ (1 - S.theoremAlpha hμ_pos)⁻¹ *
              (S.μ * S.V S.x0 xStar + S.psi S.x0 - S.psi xStar) +
            (1 - S.theoremAlpha hμ_pos)⁻¹ *
              (sigma0 ^ 2 / ((Fintype.card ι : ℝ) * S.μ)) := by
            simpa [add_comm, add_left_comm, add_assoc] using hadd
      _ = (1 - S.theoremAlpha hμ_pos)⁻¹ *
          S.Delta0Sigma0 hμ_pos xStar sigma0 := by
        unfold Delta0Sigma0 strongConvexInitialVarianceBudget
        ring_nf
  exact le_trans hexpand hmain

/-- Inverse geometric output-mass identity for Theorem 5.4.

Aligns with Lan Eq. (5.2.81), where `θ_t = α⁻ᵗ` turns the normalized
Proposition 5.6 `Q` bound into `α^k / (1 - α^k)`. Candidate audit: searched
`geometric sum inverse denominator alpha pow one minus pow`,
`finite geometric sum inverse powers`, and checked local
`outputWindow_sum_eq_range_succ` plus Mathlib `geom_sum_mul`/`geom_sum_mul_neg`;
no existing helper stated this one-based inverse-power denominator in the RGEM
output-window form. -/
private theorem theorem54_inverse_geometric_output_mass
    {a : ℝ} {k : ℕ} (hk : 1 ≤ k) (ha_pos : 0 < a) (ha_lt_one : a < 1) :
    (Finset.sum (outputWindow k) (fun t => (a ^ t)⁻¹))⁻¹ * (1 - a)⁻¹ =
      a ^ k / (1 - a ^ k) := by
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have hpow_ne_one : a ^ k ≠ 1 := by
    exact ne_of_lt (pow_lt_one₀ ha_pos.le ha_lt_one (by omega : k ≠ 0))
  simpa [outputWindow] using
    inv_sum_Icc_one_pow_inv_mul_one_sub_inv (a := a) (k := k) ha_ne hpow_ne_one

/-- V-bound scalar postprocessing from Proposition 5.6 to Theorem 5.4.

Aligns with the distance part of Lan Eq. (5.2.81): after
`Δ̃_{0,σ₀} ≤ (1-α)⁻¹ Δ_{0,σ₀}`, the Theorem 5.4 policy gives
`θ_k(μ+η_k)=α^{-k} μ/(1-α)`, hence the Proposition 5.6 RHS reduces to
`2 Δ_{0,σ₀} α^k/μ`. -/
private theorem theorem54_v_rhs_bound_from_delta_tilde
    {k : ℕ} {xStar : E} {sigma0 : ℝ}
    (hk : 1 ≤ k)
    (hμ_pos : 0 < S.μ)
    (hηθ :
      ({ S with θ := S.theoremTheta hμ_pos } : Setup ι E).PositiveEtaDomain)
    (hτ_policy : ∀ t, 1 ≤ t → S.τ t = S.constantTau hμ_pos)
    (hη_policy : ∀ t, 1 ≤ t → S.η t = S.constantEta hμ_pos)
    (hα_policy : ∀ t, 1 ≤ t → S.α t = S.constantAlphaStep hμ_pos) :
    2 *
        ({ S with θ := S.theoremTheta hμ_pos } : Setup ι E).DeltaTilde0Sigma0
          hηθ k xStar sigma0 /
        ((({ S with θ := S.theoremTheta hμ_pos } : Setup ι E).θ k) *
          ((({ S with θ := S.theoremTheta hμ_pos } : Setup ι E).μ) +
            (({ S with θ := S.theoremTheta hμ_pos } : Setup ι E).η k))) ≤
      2 * S.Delta0Sigma0 hμ_pos xStar sigma0 *
        S.theoremAlpha hμ_pos ^ k / S.μ := by
  classical
  let Sθ : Setup ι E := { S with θ := S.theoremTheta hμ_pos }
  let a : ℝ := S.theoremAlpha hμ_pos
  change
    2 * Sθ.DeltaTilde0Sigma0 hηθ k xStar sigma0 /
        (Sθ.θ k * (Sθ.μ + Sθ.η k)) ≤
      2 * S.Delta0Sigma0 hμ_pos xStar sigma0 *
        S.theoremAlpha hμ_pos ^ k / S.μ
  rcases S.theoremAlpha_pos_lt_one hμ_pos with ⟨ha_pos_raw, ha_lt_raw⟩
  have ha_pos : 0 < a := by simpa [a] using ha_pos_raw
  have ha_lt_one : a < 1 := by simpa [a] using ha_lt_raw
  have h1ma_pos : 0 < 1 - a := sub_pos.mpr ha_lt_one
  have h1ma_ne : 1 - a ≠ 0 := ne_of_gt h1ma_pos
  have hμ_ne : S.μ ≠ 0 := ne_of_gt hμ_pos
  have ha_pow_ne : a ^ k ≠ 0 := pow_ne_zero k (ne_of_gt ha_pos)
  have hηk_eq : Sθ.η k = a / (1 - a) * S.μ := by
    change S.η k = a / (1 - a) * S.μ
    simpa [a, constantEta] using hη_policy k hk
  have hsum_eq : Sθ.μ + Sθ.η k = S.μ / (1 - a) := by
    change S.μ + Sθ.η k = S.μ / (1 - a)
    rw [hηk_eq]
    field_simp [h1ma_ne]
    ring
  have htheta_eq : Sθ.θ k = (a ^ k)⁻¹ := by
    change S.theoremTheta hμ_pos k = (a ^ k)⁻¹
    simp [theoremTheta, a]
  have hden_eq :
      Sθ.θ k * (Sθ.μ + Sθ.η k) =
        (a ^ k)⁻¹ * (S.μ / (1 - a)) := by
    rw [htheta_eq, hsum_eq]
  have hden_pos : 0 < Sθ.θ k * (Sθ.μ + Sθ.η k) := by
    rw [hden_eq]
    exact mul_pos (inv_pos.mpr (pow_pos ha_pos k)) (div_pos hμ_pos h1ma_pos)
  have hDelta :
      Sθ.DeltaTilde0Sigma0 hηθ k xStar sigma0 ≤
        (1 - S.theoremAlpha hμ_pos)⁻¹ *
          S.Delta0Sigma0 hμ_pos xStar sigma0 := by
    change ({ S with θ := S.theoremTheta hμ_pos } : Setup ι E).DeltaTilde0Sigma0
        hηθ k xStar sigma0 ≤
      (1 - S.theoremAlpha hμ_pos)⁻¹ *
        S.Delta0Sigma0 hμ_pos xStar sigma0
    exact
      S.theorem54_delta_tilde_le_delta0_over_one_minus_alpha
        (k := k) (xStar := xStar) (sigma0 := sigma0)
        hμ_pos hηθ hτ_policy hη_policy hα_policy
  have hnum :
      2 * Sθ.DeltaTilde0Sigma0 hηθ k xStar sigma0 ≤
        2 * ((1 - S.theoremAlpha hμ_pos)⁻¹ *
          S.Delta0Sigma0 hμ_pos xStar sigma0) :=
    mul_le_mul_of_nonneg_left hDelta (by norm_num)
  have hdiv :=
    div_le_div_of_nonneg_right hnum hden_pos.le
  calc
    2 * Sθ.DeltaTilde0Sigma0 hηθ k xStar sigma0 /
        (Sθ.θ k * (Sθ.μ + Sθ.η k))
        ≤ 2 * ((1 - S.theoremAlpha hμ_pos)⁻¹ *
          S.Delta0Sigma0 hμ_pos xStar sigma0) /
            (Sθ.θ k * (Sθ.μ + Sθ.η k)) := hdiv
    _ = 2 * S.Delta0Sigma0 hμ_pos xStar sigma0 *
        S.theoremAlpha hμ_pos ^ k / S.μ := by
      rw [hden_eq]
      change
        2 * ((1 - a)⁻¹ * S.Delta0Sigma0 hμ_pos xStar sigma0) /
            ((a ^ k)⁻¹ * (S.μ / (1 - a))) =
          2 * S.Delta0Sigma0 hμ_pos xStar sigma0 * a ^ k / S.μ
      field_simp [hμ_ne, h1ma_ne, ha_pow_ne]

/-- The Theorem 5.4 choice `θ_t = α^{-t}` satisfies Proposition 5.6's
weight recurrence and scalar side conditions.

Aligns with Lan Theorem 5.4 proof sentence "we can easily check" after
Eqs. (5.2.76)--(5.2.77), covering Eq. (5.2.61) and Eqs. (5.2.65)--(5.2.68).
Candidate audit: pre-searched digest had no theorem-5.4 candidate; searched
`parameter choice weight condition side conditions theorem theta` and
`geometric theta alpha constant tau eta side condition`, checked local
`PropositionSideConditions` consequences and SOptLib `ParameterChoices` geometric
epoch schedules, and scanned `SOptLib/Model`, `SOptLib/Layer0`, and
`SOptLib/Layer1`; none proves RGEM's literal constant-policy side conditions. -/
private theorem theorem54_theta_policy_weight_and_side_conditions
    {k : ℕ}
    (hk : 1 ≤ k)
    (hμ_pos : 0 < S.μ)
    (hτ_policy : ∀ t, 1 ≤ t → S.τ t = S.constantTau hμ_pos)
    (hη_policy : ∀ t, 1 ≤ t → S.η t = S.constantEta hμ_pos)
    (hα_policy : ∀ t, 1 ≤ t → S.α t = S.constantAlphaStep hμ_pos) :
    ({ S with θ := S.theoremTheta hμ_pos } : Setup ι E).WeightCondition5261 k ∧
      ({ S with θ := S.theoremTheta hμ_pos } : Setup ι E).PropositionSideConditions k := by
  classical
  let Sθ : Setup ι E := { S with θ := S.theoremTheta hμ_pos }
  change Sθ.WeightCondition5261 k ∧ Sθ.PropositionSideConditions k
  have hμθ : 0 < Sθ.μ := by
    simpa [Sθ] using hμ_pos
  have hτθ_policy : ∀ t, 1 ≤ t → Sθ.τ t = Sθ.constantTau hμθ := by
    intro t ht
    simpa [Sθ, constantTau, theoremAlpha] using hτ_policy t ht
  have hηθ_policy : ∀ t, 1 ≤ t → Sθ.η t = Sθ.constantEta hμθ := by
    intro t ht
    simpa [Sθ, constantEta, theoremAlpha] using hη_policy t ht
  have hαθ_policy : ∀ t, 1 ≤ t → Sθ.α t = Sθ.constantAlphaStep hμθ := by
    intro t ht
    simpa [Sθ, constantAlphaStep, theoremAlpha] using hα_policy t ht
  rcases Sθ.theoremAlpha_pos_lt_one hμθ with ⟨ha_pos_raw, ha_lt_raw⟩
  let a : ℝ := Sθ.theoremAlpha hμθ
  let m : ℝ := (Fintype.card ι : ℝ)
  have ha_pos : 0 < a := by simpa [a] using ha_pos_raw
  have ha_lt : a < 1 := by simpa [a] using ha_lt_raw
  have hden_ne : 1 - a ≠ 0 := by linarith
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have hm_pos : 0 < m := by
    dsimp [m]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hm_ne : m ≠ 0 := ne_of_gt hm_pos
  have htau_coeff :
      m * (1 + ((m * (1 - a))⁻¹ - 1)) = 1 / (1 - a) := by
    calc
      m * (1 + ((m * (1 - a))⁻¹ - 1)) = m * ((m * (1 - a))⁻¹) := by ring
      _ = 1 / (1 - a) := by
        field_simp [hm_ne, hden_ne]
  have htau_coeff_minus :
      m * (1 + ((m * (1 - a))⁻¹ - 1)) - 1 = a / (1 - a) := by
    calc
      m * (1 + ((m * (1 - a))⁻¹ - 1)) - 1 = (1 / (1 - a)) - 1 := by
        rw [htau_coeff]
      _ = a / (1 - a) := by
        field_simp [hden_ne]
        ring
  have htheta_adj {t : ℕ} (ht2 : 2 ≤ t) :
      (a ^ t)⁻¹ * a = (a ^ (t - 1))⁻¹ := by
    have ht_eq : t = (t - 1) + 1 := by omega
    rw [ht_eq, pow_succ]
    field_simp [ha_ne]
    have hsub : t - 1 + 1 - 1 = t - 1 := by omega
    rw [hsub]
  have hLcomp_le_Lhat : ∀ i, Sθ.Lcomp i ≤ Sθ.Lhat := by
    intro i
    have hnonempty : (Finset.univ.image Sθ.Lcomp).Nonempty :=
      Finset.image_nonempty.mpr
        (Finset.univ_nonempty : (Finset.univ : Finset ι).Nonempty)
    simpa [Sθ, Lhat] using
      SOptLib.le_finite_image_max (f := Sθ.Lcomp) i hnonempty
  refine ⟨?hweight, ?hside⟩
  ·
    -- Eq. (5.2.61) after substituting `θ_t = a^{-t}` and
    -- `τ = (m(1-a))^{-1}-1`.
    intro t ht2 _htle
    have ht1 : 1 ≤ t := by omega
    have htm1 : 1 ≤ t - 1 := by omega
    have ha_eq : Sθ.theoremAlpha hμθ = S.theoremAlpha hμ_pos := by
      simp [Sθ, theoremAlpha, Lhat]
    have hθt : Sθ.θ t = (a ^ t)⁻¹ := by
      change S.theoremTheta hμ_pos t = (a ^ t)⁻¹
      simp [theoremTheta, a, ha_eq]
    have hθtm1 : Sθ.θ (t - 1) = (a ^ (t - 1))⁻¹ := by
      change S.theoremTheta hμ_pos (t - 1) = (a ^ (t - 1))⁻¹
      simp [theoremTheta, a, ha_eq]
    have hτconst : Sθ.constantTau hμθ = ((m * (1 - a))⁻¹ - 1) := by
      simp [constantTau, a, m]
    have hm_card : (Fintype.card ι : ℝ) = m := rfl
    rw [hθt, hθtm1, hτθ_policy t ht1, hτθ_policy (t - 1) htm1,
      hτconst, hm_card]
    rw [htau_coeff_minus]
    calc
      (a ^ t)⁻¹ * (a / (1 - a))
          = ((a ^ t)⁻¹ * a) * (1 / (1 - a)) := by ring
      _ = (a ^ (t - 1))⁻¹ * (1 / (1 - a)) := by rw [htheta_adj ht2]
      _ = (a ^ (t - 1))⁻¹ * m * (1 + ((m * (1 - a))⁻¹ - 1)) := by
            rw [← htau_coeff]
            ring
  · refine ⟨?h65, ?hrest⟩
    · intro t ht2 _htle
      have ht1 : 1 ≤ t := by omega
      rw [hαθ_policy t ht1]
      change m * (a ^ (t - 1))⁻¹ = (m * a) * (a ^ t)⁻¹
      rw [← htheta_adj ht2]
      ring
    · refine ⟨?h66, ?hcross_terminal⟩
      · intro t ht2 _htle
        have ht1 : 1 ≤ t := by omega
        have htm1 : 1 ≤ t - 1 := by omega
        rw [hηθ_policy t ht1, hηθ_policy (t - 1) htm1]
        apply le_of_eq
        change (a ^ t)⁻¹ * (a / (1 - a) * Sθ.μ) =
          (a ^ (t - 1))⁻¹ * (Sθ.μ + a / (1 - a) * Sθ.μ)
        have heta_sum : Sθ.μ + a / (1 - a) * Sθ.μ = Sθ.μ / (1 - a) := by
          field_simp [hden_ne]
          ring
        rw [heta_sum]
        calc
          (a ^ t)⁻¹ * (a / (1 - a) * Sθ.μ)
              = ((a ^ t)⁻¹ * a) * (Sθ.μ / (1 - a)) := by ring
          _ = (a ^ (t - 1))⁻¹ * (Sθ.μ / (1 - a)) := by
                rw [htheta_adj ht2]
      ·
        have ha_def :
            a = 1 -
              (m + Real.sqrt (m ^ 2 + 16 * m * Sθ.Lhat / Sθ.μ))⁻¹ := by
          simp [a, theoremAlpha, m]
        have hbudget :
            2 * (m * a) * Sθ.Lhat ≤
                m * (((m * (1 - a))⁻¹ - 1)) *
                  (a / (1 - a) * Sθ.μ) ∧
              4 * Sθ.Lhat ≤
                (((m * (1 - a))⁻¹ - 1)) *
                  (Sθ.μ + a / (1 - a) * Sθ.μ) :=
          theorem54_sqrt_budget_cross_terminal_scalar
            (m := m) (μ := Sθ.μ) (L := Sθ.Lhat) (a := a)
            hm_pos hμθ Sθ.Lhat_nonneg ha_pos ha_def
        have hαconst : Sθ.constantAlphaStep hμθ = m * a := by
          simp [constantAlphaStep, a, m]
        have hτconst : Sθ.constantTau hμθ = ((m * (1 - a))⁻¹ - 1) := by
          simp [constantTau, a, m]
        have hηconst : Sθ.constantEta hμθ = a / (1 - a) * Sθ.μ := by
          simp [constantEta, a]
        have hm_card : (Fintype.card ι : ℝ) = m := rfl
        refine ⟨?hcross, ?hterminal⟩
        · intro t i ht2 _htk
          have ht1 : 1 ≤ t := by omega
          have htm1 : 1 ≤ t - 1 := by omega
          rw [hαθ_policy t ht1, hτθ_policy (t - 1) htm1, hηθ_policy t ht1,
            hαconst, hτconst, hηconst, hm_card]
          exact le_trans
            (mul_le_mul_of_nonneg_left (hLcomp_le_Lhat i) (by nlinarith [hm_pos, ha_pos]))
            hbudget.1
        · intro i
          rw [hτθ_policy k hk, hηθ_policy k hk, hτconst, hηconst]
          exact le_trans
            (mul_le_mul_of_nonneg_left (hLcomp_le_Lhat i) (by norm_num : (0 : ℝ) ≤ 4))
            hbudget.2

/-- The average component smoothness is bounded by the largest component
smoothness.

Aligns with Lan Eq. (5.2.4), where `L = m⁻¹∑ᵢ Lᵢ` and `Lhat = maxᵢ Lᵢ`.
Candidate audit: considered `SOptLib.le_finite_image_max` and the finite-average
smoothness transfer lemmas returned by the `Lavg Lhat finite image max` search;
the transfer lemmas prove objective smoothness rather than this scalar bound, so
this helper specializes `SOptLib.le_finite_image_max` and sums over `Finset.univ`. -/
private theorem theorem54_Lavg_le_Lhat :
    S.Lavg ≤ S.Lhat := by
  classical
  have hnonempty : (Finset.univ.image S.Lcomp).Nonempty :=
    Finset.image_nonempty.mpr
      (Finset.univ_nonempty : (Finset.univ : Finset ι).Nonempty)
  have hcard_pos : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hsum_le :
      Finset.sum Finset.univ S.Lcomp ≤
        Finset.sum Finset.univ (fun _ : ι => S.Lhat) := by
    refine Finset.sum_le_sum ?_
    intro i _hi
    simpa [Lhat] using SOptLib.le_finite_image_max (f := S.Lcomp) i hnonempty
  calc
    S.Lavg = (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ S.Lcomp := by
      rfl
    _ ≤ (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ (fun _ : ι => S.Lhat) := by
      exact mul_le_mul_of_nonneg_left hsum_le (inv_nonneg.mpr hcard_pos.le)
    _ = S.Lhat := by
      rw [Finset.sum_const]
      simp [nsmul_eq_mul]

/-- Pointwise conversion of the `Lf` quadratic remainder to the theorem's
`Lhat` quadratic remainder.

Aligns with Lan Theorem 5.4 proof step using Eq. (5.2.4), not a global
assumption `Lf ≤ Lhat`. Candidate audit: considered the local `average_smooth`
API and `SOptLib.le_finite_image_max`; no existing helper states this
coefficient bridge at a feasible point, so this combines `S.average_smooth`,
`theorem54_Lavg_le_Lhat`, and seminorm nonnegativity. -/
private theorem theorem54_lf_remainder_le_lhat_remainder
    {x xStar : E} (hx : x ∈ S.X) (hxStar : xStar ∈ S.X) :
    (S.Lf / 2) * S.primalNorm (x - xStar) ^ 2 ≤
      (S.Lhat / 2) * S.primalNorm (x - xStar) ^ 2 := by
  have hsmooth := (S.average_smooth hx hxStar).2
  have hnorm_nonneg : 0 ≤ S.primalNorm (x - xStar) := by
    exact apply_nonneg S.primalNorm (x - xStar)
  have hsquare_nonneg : 0 ≤ S.primalNorm (x - xStar) ^ 2 := by
    exact sq_nonneg (S.primalNorm (x - xStar))
  have hLfLavg_sq :
      S.Lf * S.primalNorm (x - xStar) ^ 2 ≤
        S.Lavg * S.primalNorm (x - xStar) ^ 2 := by
    calc
      S.Lf * S.primalNorm (x - xStar) ^ 2 =
          (S.Lf * S.primalNorm (x - xStar)) *
            S.primalNorm (x - xStar) := by ring
      _ ≤ (S.Lavg * S.primalNorm (x - xStar)) *
            S.primalNorm (x - xStar) := by
        exact mul_le_mul_of_nonneg_right hsmooth hnorm_nonneg
      _ = S.Lavg * S.primalNorm (x - xStar) ^ 2 := by ring
  have hLavgLhat_sq :
      S.Lavg * S.primalNorm (x - xStar) ^ 2 ≤
        S.Lhat * S.primalNorm (x - xStar) ^ 2 := by
    exact mul_le_mul_of_nonneg_right S.theorem54_Lavg_le_Lhat hsquare_nonneg
  have hmain :
      S.Lf * S.primalNorm (x - xStar) ^ 2 ≤
        S.Lhat * S.primalNorm (x - xStar) ^ 2 :=
    le_trans hLfLavg_sq hLavgLhat_sq
  calc
    (S.Lf / 2) * S.primalNorm (x - xStar) ^ 2 =
        (S.Lf * S.primalNorm (x - xStar) ^ 2) / 2 := by ring
    _ ≤ (S.Lhat * S.primalNorm (x - xStar) ^ 2) / 2 := by
      exact div_le_div_of_nonneg_right hmain (by norm_num : (0 : ℝ) ≤ 2)
    _ = (S.Lhat / 2) * S.primalNorm (x - xStar) ^ 2 := by ring

/-- Per-time `V` expectation bound for the Theorem 5.4 output window.

Aligns with Lan Theorem 5.4 proof steps 9--10, replaying Proposition 5.6 at a
fixed time `t` under the theorem's `θ_s = α⁻ˢ` policy. Candidate audit:
searched `V bound each output time proposition 5.6 positiveEtaXIterate
theoremAlpha Delta0`; the matching existing theorem is
`proposition_5_6_positive_domain`, while no local helper already packaged the
Sθ-to-S transport and Eq. (5.2.81) scalar postprocessing for arbitrary `t`. -/
private theorem theorem54_v_bound_each_output_time
    {t : ℕ} {xStar : E} {sigma0 : ℝ}
    (ht : 1 ≤ t)
    (hμ_pos : 0 < S.μ)
    (hopt : S.IsOptimalSolution xStar)
    (hsigma : S.InitialGradientBound sigma0)
    (hτ_policy : ∀ s, 1 ≤ s → S.τ s = S.constantTau hμ_pos)
    (hη_policy : ∀ s, 1 ≤ s → S.η s = S.constantEta hμ_pos)
    (hα_policy : ∀ s, 1 ≤ s → S.α s = S.constantAlphaStep hμ_pos) :
    expectationLe S.P
      (fun ω =>
        S.V (S.positiveEtaXIterate
          (S.theoremPositiveEtaDomain hμ_pos hη_policy) t ω) xStar)
      (2 * S.Delta0Sigma0 hμ_pos xStar sigma0 *
        S.theoremAlpha hμ_pos ^ t / S.μ) := by
  let Sθ : Setup ι E := { S with θ := S.theoremTheta hμ_pos }
  have hμθ : 0 < Sθ.μ := by
    simpa [Sθ] using hμ_pos
  have hηθ : Sθ.PositiveEtaDomain := by
    simpa [Sθ, constantEta, theoremAlpha] using
      (S.theoremPositiveEtaDomain hμ_pos hη_policy)
  have hoptθ : Sθ.IsOptimalSolution xStar := by
    simpa [Sθ, IsOptimalSolution, psi] using hopt
  have hsigmaθ : Sθ.InitialGradientBound sigma0 := by
    simpa [Sθ, InitialGradientBound] using hsigma
  have hθposθ : Sθ.OutputWeightsPositive t := by
    intro s hs
    simpa [Sθ, theoremTheta, theoremAlpha] using
      (S.theoremTheta_outputWeightsPositive ht hμ_pos s hs)
  have hθ_side :
      ({ S with θ := S.theoremTheta hμ_pos } : Setup ι E).WeightCondition5261 t ∧
        ({ S with θ := S.theoremTheta hμ_pos } : Setup ι E).PropositionSideConditions t :=
    S.theorem54_theta_policy_weight_and_side_conditions ht hμ_pos
      hτ_policy hη_policy hα_policy
  have hweightθ : Sθ.WeightCondition5261 t := by
    simpa [Sθ] using hθ_side.1
  have hsideθ : Sθ.PropositionSideConditions t := by
    simpa [Sθ] using hθ_side.2
  have hprop :=
    Sθ.proposition_5_6_positive_domain ht hηθ hoptθ hsigmaθ hθposθ hweightθ hsideθ
  have hV_prop :
      expectationLe Sθ.P
        (fun ω => Sθ.V (Sθ.positiveEtaXIterate hηθ t ω) xStar)
        (2 * Sθ.DeltaTilde0Sigma0 hηθ t xStar sigma0 /
          (Sθ.θ t * (Sθ.μ + Sθ.η t))) :=
    hprop.2
  have hVRhs :
      2 * Sθ.DeltaTilde0Sigma0 hηθ t xStar sigma0 /
          (Sθ.θ t * (Sθ.μ + Sθ.η t)) ≤
        2 * S.Delta0Sigma0 hμ_pos xStar sigma0 *
          S.theoremAlpha hμ_pos ^ t / S.μ := by
    change
      2 *
          ({ S with θ := S.theoremTheta hμ_pos } : Setup ι E).DeltaTilde0Sigma0
            hηθ t xStar sigma0 /
          ((({ S with θ := S.theoremTheta hμ_pos } : Setup ι E).θ t) *
            ((({ S with θ := S.theoremTheta hμ_pos } : Setup ι E).μ) +
              (({ S with θ := S.theoremTheta hμ_pos } : Setup ι E).η t))) ≤
        2 * S.Delta0Sigma0 hμ_pos xStar sigma0 *
          S.theoremAlpha hμ_pos ^ t / S.μ
    exact S.theorem54_v_rhs_bound_from_delta_tilde
      (k := t) (xStar := xStar) (sigma0 := sigma0)
      ht hμ_pos hηθ hτ_policy hη_policy hα_policy
  rcases hV_prop with ⟨hV_wd, hV_le⟩
  have hfun_eq :
      (fun ω => Sθ.V (Sθ.positiveEtaXIterate hηθ t ω) xStar) =
        (fun ω =>
          S.V
            (S.positiveEtaXIterate
              (S.theoremPositiveEtaDomain hμ_pos hη_policy) t ω)
            xStar) := by
    funext ω
    have hx :=
      S.positiveEtaXIterate_theta_update_eq
        (S.theoremTheta hμ_pos) hηθ
        (S.theoremPositiveEtaDomain hμ_pos hη_policy) t ω
    exact congrArg (fun y => S.V y xStar) hx
  refine ⟨?_, ?_⟩
  · simpa [Sθ, hfun_eq] using hV_wd
  · exact le_trans (by simpa [Sθ, hfun_eq] using hV_le) hVRhs

/-- Convexity of the squared paper-seminorm distance to a fixed center.

Aligns with Lan Theorem 5.4 proof step 11, the Jensen step for the weighted
output. Candidate audit: checked `Seminorm.convexOn`, `ConvexOn.map_sum_le`,
`weighted_sq_norm_sub_center_le`, and sister-paper
`primalNorm_sq_weighted_average_sub_le_sum`; the available SOptLib norm-square
lemmas use ambient normed-group structure or two-point centers, while this route
needs the arbitrary RGEM paper seminorm with a fixed center. -/
private theorem theorem54_sq_primalNorm_convexOn (xStar : E) :
    ConvexOn ℝ Set.univ (fun x => S.primalNorm (x - xStar) ^ 2) := by
  refine ⟨convex_univ, ?_⟩
  intro y _hy z _hz α η hα hη hsum
  let py : ℝ := S.primalNorm (y - xStar)
  let pz : ℝ := S.primalNorm (z - xStar)
  have hvec :
      (α • y + η • z) - xStar =
        α • (y - xStar) + η • (z - xStar) := by
    calc
      (α • y + η • z) - xStar =
          (α • y + η • z) - (α + η) • xStar := by
            rw [hsum, one_smul]
      _ = α • (y - xStar) + η • (z - xStar) := by
            module
  have hnorm :
      S.primalNorm ((α • y + η • z) - xStar) ≤ α * py + η * pz := by
    calc
      S.primalNorm ((α • y + η • z) - xStar)
          = S.primalNorm (α • (y - xStar) + η • (z - xStar)) := by rw [hvec]
      _ ≤ S.primalNorm (α • (y - xStar)) +
            S.primalNorm (η • (z - xStar)) :=
          map_add_le_add S.primalNorm _ _
      _ = |α| * py + |η| * pz := by
          simp [py, pz, map_smul_eq_mul]
      _ = α * py + η * pz := by
          rw [abs_of_nonneg hα, abs_of_nonneg hη]
  have hleft_nonneg :
      0 ≤ S.primalNorm ((α • y + η • z) - xStar) :=
    apply_nonneg S.primalNorm _
  have hright_nonneg : 0 ≤ α * py + η * pz := by
    have hpy : 0 ≤ py := by dsimp [py]; exact apply_nonneg S.primalNorm _
    have hpz : 0 ≤ pz := by dsimp [pz]; exact apply_nonneg S.primalNorm _
    nlinarith
  have hsquare :
      S.primalNorm ((α • y + η • z) - xStar) ^ 2 ≤
        (α * py + η * pz) ^ 2 := by
    nlinarith [hnorm, hleft_nonneg, hright_nonneg,
      sq_nonneg ((α * py + η * pz) -
        S.primalNorm ((α • y + η • z) - xStar))]
  have hweighted_square :
      (α * py + η * pz) ^ 2 ≤ α * py ^ 2 + η * pz ^ 2 := by
    have hpy : 0 ≤ py := by dsimp [py]; exact apply_nonneg S.primalNorm _
    have hpz : 0 ≤ pz := by dsimp [pz]; exact apply_nonneg S.primalNorm _
    have hsq : 0 ≤ α * η * (py - pz) ^ 2 :=
      mul_nonneg (mul_nonneg hα hη) (sq_nonneg _)
    nlinarith
  exact hsquare.trans hweighted_square

/-- Jensen bound for the squared distance of the Theorem 5.4 weighted output.

Aligns with Lan Theorem 5.4 proof step 11. Candidate audit: checked
`ConvexOn.map_sum_le`, SOptLib
`convexOn_weighted_average_le_weighted_sum`, and weighted squared-norm lemmas;
the generic weighted Jensen bridge matches after specializing the local convexity
helper `theorem54_sq_primalNorm_convexOn` to the theorem output definition. -/
private theorem theorem54_weighted_output_sq_primalNorm_pointwise
    {k : ℕ} (hk : 1 ≤ k)
    (hμ_pos : 0 < S.μ)
    (hη_policy : ∀ t, 1 ≤ t → S.η t = S.constantEta hμ_pos)
    (hθ : S.TheoremOutputWeightsPositive hμ_pos k)
    (xStar : E) (ω : BlockSamplePath ι) :
    S.primalNorm
        (S.theoremWeightedOutput hμ_pos hη_policy k hk hθ ω - xStar) ^ 2 ≤
      (S.theoremOutputWeightSum hμ_pos k)⁻¹ *
        Finset.sum (outputWindow k) (fun t =>
          S.theoremTheta hμ_pos t *
            S.primalNorm
              (S.theoremXIterate hμ_pos hη_policy t ω - xStar) ^ 2) := by
  classical
  let W : ℝ := S.theoremOutputWeightSum hμ_pos k
  have hW_pos : 0 < W := by
    dsimp [W, theoremOutputWeightSum]
    exact Finset.sum_pos (fun t ht => hθ t ht)
      ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hk⟩⟩
  have hW_eq : W = Finset.sum (outputWindow k) (S.theoremTheta hμ_pos) := by
    rfl
  have hxbar :
      S.theoremWeightedOutput hμ_pos hη_policy k hk hθ ω =
        W⁻¹ • Finset.sum (outputWindow k) (fun t =>
          S.theoremTheta hμ_pos t • S.theoremXIterate hμ_pos hη_policy t ω) := by
    simpa [W] using
      S.theoremWeightedOutput_def hμ_pos hη_policy k hk hθ ω
  have hweights_sum :
      Finset.sum (outputWindow k) (fun t => W⁻¹ * S.theoremTheta hμ_pos t) = 1 := by
    calc
      Finset.sum (outputWindow k) (fun t => W⁻¹ * S.theoremTheta hμ_pos t)
          = W⁻¹ * Finset.sum (outputWindow k) (S.theoremTheta hμ_pos) := by
            rw [Finset.mul_sum]
      _ = W⁻¹ * W := by rw [← hW_eq]
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hW_pos)
  have hweights_nonneg :
      ∀ t ∈ outputWindow k, 0 ≤ W⁻¹ * S.theoremTheta hμ_pos t := by
    intro t ht
    exact mul_nonneg (inv_nonneg.mpr hW_pos.le) (hθ t ht).le
  have haverage :
      S.theoremWeightedOutput hμ_pos hη_policy k hk hθ ω =
        Finset.sum (outputWindow k) (fun t =>
          (W⁻¹ * S.theoremTheta hμ_pos t) •
            S.theoremXIterate hμ_pos hη_policy t ω) := by
    calc
      S.theoremWeightedOutput hμ_pos hη_policy k hk hθ ω =
          W⁻¹ • Finset.sum (outputWindow k) (fun t =>
            S.theoremTheta hμ_pos t • S.theoremXIterate hμ_pos hη_policy t ω) := hxbar
      _ = Finset.sum (outputWindow k) (fun t =>
          (W⁻¹ * S.theoremTheta hμ_pos t) •
            S.theoremXIterate hμ_pos hη_policy t ω) := by
        simp [Finset.smul_sum, smul_smul, mul_assoc]
  have hJ :=
    (S.theorem54_sq_primalNorm_convexOn xStar).map_sum_le
      (t := outputWindow k)
      (w := fun t => W⁻¹ * S.theoremTheta hμ_pos t)
      (p := fun t => S.theoremXIterate hμ_pos hη_policy t ω)
      hweights_nonneg hweights_sum (by intro t ht; trivial)
  rw [← haverage] at hJ
  have hright :
      Finset.sum (outputWindow k) (fun t =>
          (W⁻¹ * S.theoremTheta hμ_pos t) •
            S.primalNorm (S.theoremXIterate hμ_pos hη_policy t ω - xStar) ^ 2) =
        W⁻¹ * Finset.sum (outputWindow k) (fun t =>
          S.theoremTheta hμ_pos t *
            S.primalNorm (S.theoremXIterate hμ_pos hη_policy t ω - xStar) ^ 2) := by
    calc
      Finset.sum (outputWindow k) (fun t =>
          (W⁻¹ * S.theoremTheta hμ_pos t) •
            S.primalNorm (S.theoremXIterate hμ_pos hη_policy t ω - xStar) ^ 2)
          =
        Finset.sum (outputWindow k) (fun t =>
          W⁻¹ * (S.theoremTheta hμ_pos t *
            S.primalNorm (S.theoremXIterate hμ_pos hη_policy t ω - xStar) ^ 2)) := by
          refine Finset.sum_congr rfl ?_
          intro t _ht
          simp [smul_eq_mul, mul_assoc]
      _ = W⁻¹ * Finset.sum (outputWindow k) (fun t =>
          S.theoremTheta hμ_pos t *
            S.primalNorm (S.theoremXIterate hμ_pos hη_policy t ω - xStar) ^ 2) := by
          rw [Finset.mul_sum]
  rw [hright] at hJ
  simpa [W] using hJ

/-- Eq. (5.2.8) converts theorem-iterate squared distance into the directed
Bregman term used by Proposition 5.6.

Aligns with Lan Theorem 5.4 proof step 12. Candidate audit: checked local
`ProxLowerBound_Eq_5_2_8`, `theoremXIterate_eq_positiveEtaXIterate`, and
Mathlib/SOptLib seminorm symmetry via `map_neg_eq_map`; no existing helper had
the theorem-iterate orientation `‖xᵗ-x*‖² ≤ 2 V(xᵗ,x*)`. -/
private theorem theorem54_sq_primalNorm_iterate_le_two_V
    {xStar : E}
    (hμ_pos : 0 < S.μ)
    (hη_policy : ∀ t, 1 ≤ t → S.η t = S.constantEta hμ_pos)
    (hopt : S.IsOptimalSolution xStar)
    (t : ℕ) (ω : BlockSamplePath ι) :
    S.primalNorm (S.theoremXIterate hμ_pos hη_policy t ω - xStar) ^ 2 ≤
      2 * S.V (S.theoremXIterate hμ_pos hη_policy t ω) xStar := by
  let hη := S.theoremPositiveEtaDomain hμ_pos hη_policy
  have hx :
      S.theoremXIterate hμ_pos hη_policy t ω ∈ S.X := by
    simpa [S.theoremXIterate_eq_positiveEtaXIterate hμ_pos hη_policy t ω] using
      S.PrimalUpdateFeasibility_Eq_5_2_50_positive_domain hη t ω
  have hprox :=
    S.ProxLowerBound_Eq_5_2_8 hx hopt.1
  have hsym :
      S.primalNorm (xStar - S.theoremXIterate hμ_pos hη_policy t ω) =
        S.primalNorm (S.theoremXIterate hμ_pos hη_policy t ω - xStar) := by
    have hneg :
        xStar - S.theoremXIterate hμ_pos hη_policy t ω =
          -(S.theoremXIterate hμ_pos hη_policy t ω - xStar) := by
      abel
    rw [hneg, map_neg_eq_map]
  rw [hsym] at hprox
  nlinarith

/-- Pointwise weighted-output squared-distance bound by the weighted Bregman
distances of the generated iterates.

Aligns with Lan Theorem 5.4 proof steps 11--12: finite Jensen for the weighted
output, followed by Eq. (5.2.8) at every output-window iterate. Candidate audit:
searched for `weighted squared seminorm sub center Jensen finite sum`; the
available SOptLib/Mathlib pieces were generic Jensen or ambient-norm lemmas, so
this helper consumes the local squared-seminorm Jensen and Eq. (5.2.8)
orientation helpers. -/
private theorem theorem54_weighted_output_sq_primalNorm_le_weighted_V_pointwise
    {k : ℕ} (hk : 1 ≤ k)
    {xStar : E}
    (hμ_pos : 0 < S.μ)
    (hη_policy : ∀ t, 1 ≤ t → S.η t = S.constantEta hμ_pos)
    (hθ : S.TheoremOutputWeightsPositive hμ_pos k)
    (hopt : S.IsOptimalSolution xStar)
    (ω : BlockSamplePath ι) :
    S.primalNorm
        (S.theoremWeightedOutput hμ_pos hη_policy k hk hθ ω - xStar) ^ 2 ≤
      (S.theoremOutputWeightSum hμ_pos k)⁻¹ *
        Finset.sum (outputWindow k) (fun t =>
          S.theoremTheta hμ_pos t *
            (2 * S.V (S.theoremXIterate hμ_pos hη_policy t ω) xStar)) := by
  have hJ :=
    S.theorem54_weighted_output_sq_primalNorm_pointwise
      hk hμ_pos hη_policy hθ xStar ω
  have hW_pos : 0 < S.theoremOutputWeightSum hμ_pos k := by
    dsimp [theoremOutputWeightSum]
    exact Finset.sum_pos (fun t ht => hθ t ht)
      ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hk⟩⟩
  have hsum_le :
      Finset.sum (outputWindow k) (fun t =>
          S.theoremTheta hμ_pos t *
            S.primalNorm
              (S.theoremXIterate hμ_pos hη_policy t ω - xStar) ^ 2) ≤
        Finset.sum (outputWindow k) (fun t =>
          S.theoremTheta hμ_pos t *
            (2 * S.V (S.theoremXIterate hμ_pos hη_policy t ω) xStar)) := by
    refine Finset.sum_le_sum ?_
    intro t ht
    exact mul_le_mul_of_nonneg_left
      (S.theorem54_sq_primalNorm_iterate_le_two_V hμ_pos hη_policy hopt t ω)
      (hθ t ht).le
  exact le_trans hJ
    (mul_le_mul_of_nonneg_left hsum_le (inv_nonneg.mpr hW_pos.le))

/-- Finite-window expectation aggregation for the weighted `V` term in
Theorem 5.4.

Aligns with Lan Theorem 5.4 proof steps 11--13: after the pointwise Jensen/Eq.
(5.2.8) reduction, integrate the finite output-window sum and apply the
per-time Proposition 5.6 bound. Candidate audit: checked the SOptLib/Mathlib
candidate `integral_scaled_finset_sum_le_scaled_sum_of_integral_bounds`, plus
`MeasureTheory.integral_finset_sum` and `Finset.sum_le_sum`; the SOptLib helper
is present in source but not exported through the active target name surface, so
this local theorem uses the Mathlib finite-sum integral APIs directly. -/
private theorem theorem54_weighted_V_sum_expectation_bound_raw
    {k : ℕ} {xStar : E} {sigma0 : ℝ}
    (hk : 1 ≤ k)
    (hμ_pos : 0 < S.μ)
    (hopt : S.IsOptimalSolution xStar)
    (hsigma : S.InitialGradientBound sigma0)
    (hτ_policy : ∀ t, 1 ≤ t → S.τ t = S.constantTau hμ_pos)
    (hη_policy : ∀ t, 1 ≤ t → S.η t = S.constantEta hμ_pos)
    (hα_policy : ∀ t, 1 ≤ t → S.α t = S.constantAlphaStep hμ_pos) :
    expectationLe S.P
      (fun ω =>
        (S.Lhat / 2) *
          ((S.theoremOutputWeightSum hμ_pos k)⁻¹ *
            Finset.sum (outputWindow k) (fun t =>
              S.theoremTheta hμ_pos t *
                (2 * S.V (S.theoremXIterate hμ_pos hη_policy t ω) xStar))))
      ((S.Lhat / 2) * (S.theoremOutputWeightSum hμ_pos k)⁻¹ *
        Finset.sum (outputWindow k) (fun _t => 4 * S.Delta0Sigma0 hμ_pos xStar sigma0 / S.μ)) := by
  classical
  let a : ℝ := S.theoremAlpha hμ_pos
  let Δ : ℝ := S.Delta0Sigma0 hμ_pos xStar sigma0
  let W : ℝ := S.theoremOutputWeightSum hμ_pos k
  let scale : ℝ := (S.Lhat / 2) * W⁻¹
  let summand : ℕ → BlockSamplePath ι → ℝ := fun t ω =>
    S.theoremTheta hμ_pos t *
      (2 * S.V (S.theoremXIterate hμ_pos hη_policy t ω) xStar)
  have ha_pos : 0 < a := by
    simpa [a] using (S.theoremAlpha_pos_lt_one hμ_pos).1
  have hW_pos : 0 < W := by
    dsimp [W, theoremOutputWeightSum]
    exact Finset.sum_pos
      (fun t ht => S.theoremTheta_outputWeightsPositive hk hμ_pos t ht)
      ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hk⟩⟩
  have hsummand_int :
      ∀ t, t ∈ outputWindow k → Integrable (summand t) S.P := by
    intro t ht
    have ht1 : 1 ≤ t := (Finset.mem_Icc.mp (by simpa [outputWindow] using ht)).1
    have hV :=
      S.theorem54_v_bound_each_output_time
        (t := t) (xStar := xStar) (sigma0 := sigma0)
        ht1 hμ_pos hopt hsigma hτ_policy hη_policy hα_policy
    rcases hV with ⟨hV_int, _hV_le⟩
    have hscaled :
        Integrable
          (fun ω =>
            (S.theoremTheta hμ_pos t * 2) *
              S.V (S.theoremXIterate hμ_pos hη_policy t ω) xStar) S.P :=
      hV_int.const_mul (S.theoremTheta hμ_pos t * 2)
    simpa [summand, mul_assoc, mul_left_comm, mul_comm] using hscaled
  have hsummand_bound :
      ∀ t, t ∈ outputWindow k →
        ∫ ω, summand t ω ∂S.P ≤ 4 * Δ / S.μ := by
    intro t ht
    have ht1 : 1 ≤ t := (Finset.mem_Icc.mp (by simpa [outputWindow] using ht)).1
    have hV :=
      S.theorem54_v_bound_each_output_time
        (t := t) (xStar := xStar) (sigma0 := sigma0)
        ht1 hμ_pos hopt hsigma hτ_policy hη_policy hα_policy
    rcases hV with ⟨hV_int, hV_le⟩
    have htheta_nonneg : 0 ≤ S.theoremTheta hμ_pos t :=
      (S.theoremTheta_outputWeightsPositive hk hμ_pos t ht).le
    have hcoef_nonneg : 0 ≤ S.theoremTheta hμ_pos t * 2 := by
      nlinarith
    have hint_eq :
        ∫ ω, summand t ω ∂S.P =
          (S.theoremTheta hμ_pos t * 2) *
            ∫ ω, S.V (S.theoremXIterate hμ_pos hη_policy t ω) xStar ∂S.P := by
      have hfun :
          (fun ω => summand t ω) =
            (fun ω =>
              (S.theoremTheta hμ_pos t * 2) *
                S.V (S.theoremXIterate hμ_pos hη_policy t ω) xStar) := by
        funext ω
        simp [summand, mul_assoc, mul_left_comm, mul_comm]
      rw [hfun]
      rw [integral_const_mul]
    have hscaled_bound :
        (S.theoremTheta hμ_pos t * 2) *
            ∫ ω, S.V (S.theoremXIterate hμ_pos hη_policy t ω) xStar ∂S.P ≤
          (S.theoremTheta hμ_pos t * 2) *
            (2 * Δ * a ^ t / S.μ) := by
      simpa [SOptLib.expectation, a, Δ] using
        mul_le_mul_of_nonneg_left hV_le hcoef_nonneg
    have hsimplify :
        (S.theoremTheta hμ_pos t * 2) *
            (2 * Δ * a ^ t / S.μ) = 4 * Δ / S.μ := by
      have htheta_eq : S.theoremTheta hμ_pos t = (a ^ t)⁻¹ := by
        simp [theoremTheta, a]
      have hpow_ne : a ^ t ≠ 0 := ne_of_gt (pow_pos ha_pos t)
      rw [htheta_eq]
      field_simp [hpow_ne, ne_of_gt hμ_pos]
      ring
    calc
      ∫ ω, summand t ω ∂S.P
          = (S.theoremTheta hμ_pos t * 2) *
              ∫ ω, S.V (S.theoremXIterate hμ_pos hη_policy t ω) xStar ∂S.P := hint_eq
      _ ≤ (S.theoremTheta hμ_pos t * 2) *
            (2 * Δ * a ^ t / S.μ) := hscaled_bound
      _ = 4 * Δ / S.μ := hsimplify
  have hsum_int :
      Integrable (fun ω => Finset.sum (outputWindow k) (fun t => summand t ω)) S.P :=
    MeasureTheory.integrable_finset_sum (s := outputWindow k) (μ := S.P) hsummand_int
  have hterm_eq :
      (fun ω =>
        (S.Lhat / 2) *
          ((S.theoremOutputWeightSum hμ_pos k)⁻¹ *
            Finset.sum (outputWindow k) (fun t =>
              S.theoremTheta hμ_pos t *
                (2 * S.V (S.theoremXIterate hμ_pos hη_policy t ω) xStar)))) =
        (fun ω => scale * Finset.sum (outputWindow k) (fun t => summand t ω)) := by
    funext ω
    simp [scale, W, summand, mul_assoc, mul_left_comm, mul_comm]
  have hterm_int :
      Integrable
        (fun ω =>
          (S.Lhat / 2) *
            ((S.theoremOutputWeightSum hμ_pos k)⁻¹ *
              Finset.sum (outputWindow k) (fun t =>
                S.theoremTheta hμ_pos t *
                  (2 * S.V (S.theoremXIterate hμ_pos hη_policy t ω) xStar)))) S.P := by
    rw [hterm_eq]
    exact hsum_int.const_mul scale
  have hscale_nonneg : 0 ≤ scale := by
    dsimp [scale, W]
    exact mul_nonneg (by nlinarith [S.Lhat_nonneg]) (inv_nonneg.mpr hW_pos.le)
  have hsum_bound :
      ∫ ω, scale * Finset.sum (outputWindow k) (fun t => summand t ω) ∂S.P ≤
        scale * Finset.sum (outputWindow k)
          (fun _t => 4 * S.Delta0Sigma0 hμ_pos xStar sigma0 / S.μ) := by
    calc
      ∫ ω, scale * Finset.sum (outputWindow k) (fun t => summand t ω) ∂S.P
          = scale *
              ∫ ω, Finset.sum (outputWindow k) (fun t => summand t ω) ∂S.P := by
            rw [integral_const_mul]
      _ = scale *
            Finset.sum (outputWindow k) (fun t => ∫ ω, summand t ω ∂S.P) := by
            rw [MeasureTheory.integral_finset_sum (outputWindow k) hsummand_int]
      _ ≤ scale * Finset.sum (outputWindow k)
            (fun _t => 4 * S.Delta0Sigma0 hμ_pos xStar sigma0 / S.μ) := by
            exact mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum hsummand_bound) hscale_nonneg
  refine ⟨hterm_int, ?_⟩
  unfold SOptLib.expectation
  rw [hterm_eq]
  simpa [scale, W, Δ, mul_assoc, mul_left_comm, mul_comm] using hsum_bound

/-- Source step-16 max bound for the reciprocal alpha gap.

Aligns with Lan Theorem 5.4 proof step 16. Candidate audit: searched the
target file for `theoremAlpha`, alpha-chain, geometric-output, and max-bound
helpers, and searched SOptLib/Mathlib for square-root schedule max bounds; the
hits (`theoremAlpha_pos_lt_one`, `theorem54_card_mul_one_minus_alpha_le_half`,
`sqrt_alpha_schedule_pos_lt_one_log_neg`) support signs or a different
schedule, but none states the printed
`1/(1-alpha) <= (16/3) max {m, Lhat/mu}` bound. -/
private theorem theorem54_one_div_one_minus_alpha_le_sixteen_thirds_max
    (hμ_pos : 0 < S.μ) :
    1 / (1 - S.theoremAlpha hμ_pos) ≤
      (16 / 3) * max (Fintype.card ι : ℝ) (S.Lhat / S.μ) := by
  classical
  let m : ℝ := (Fintype.card ι : ℝ)
  let q : ℝ := S.Lhat / S.μ
  let M : ℝ := max m q
  let B : ℝ := Real.sqrt (m ^ 2 + 16 * m * q)
  let D : ℝ := m + B
  have hm_pos : 0 < m := by
    dsimp [m]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg S.Lhat_nonneg hμ_pos.le
  have hM_nonneg : 0 ≤ M := le_trans hm_pos.le (le_max_left m q)
  have hm_le_M : m ≤ M := le_max_left m q
  have hq_le_M : q ≤ M := le_max_right m q
  have hmq_le : m * q ≤ M * M :=
    mul_le_mul hm_le_M hq_le_M hq_nonneg hM_nonneg
  have hrad_le : m ^ 2 + 16 * m * q ≤ 17 * M ^ 2 := by
    have hm_sq_le : m ^ 2 ≤ M ^ 2 := by
      nlinarith [hm_pos.le, hM_nonneg, hm_le_M]
    nlinarith [hm_sq_le, hmq_le]
  have hsqrt_le : B ≤ (13 / 3) * M := by
    dsimp [B]
    rw [Real.sqrt_le_left (by nlinarith [hM_nonneg])]
    nlinarith [hrad_le, sq_nonneg M]
  have hD_le : D ≤ (16 / 3) * M := by
    dsimp [D]
    nlinarith [hm_le_M, hsqrt_le]
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact Real.sqrt_nonneg _
  have hD_pos : 0 < D := by
    dsimp [D]
    linarith
  have hone_minus : 1 - S.theoremAlpha hμ_pos = D⁻¹ := by
    dsimp [D, B, q, m, theoremAlpha, SOptLib.sqrtDenominatorContractionAlpha]
    ring
  calc
    1 / (1 - S.theoremAlpha hμ_pos) = D := by
      rw [hone_minus]
      field_simp [ne_of_gt hD_pos]
    _ ≤ (16 / 3) * max (Fintype.card ι : ℝ) (S.Lhat / S.μ) := by
      simpa [M, m, q] using hD_le

/-- Source step-16 max bound for the smoothness prefactor in the objective
bracket.

Aligns with Lan Theorem 5.4 proof step 16. Candidate audit: searched the
target file, SOptLib, and Mathlib for `Lhat/mu max prefactor` and alpha max
bounds; no existing theorem states this paper-specific scalar comparison, while
`Lhat_nonneg`, `Fintype.card_pos`, and the lattice bound `x <= max m x` exactly
prove it. -/
private theorem theorem54_two_lhat_div_mu_le_sixteen_thirds_max
    (hμ_pos : 0 < S.μ) :
    2 * S.Lhat / S.μ ≤
      (16 / 3) * max (Fintype.card ι : ℝ) (S.Lhat / S.μ) := by
  classical
  let m : ℝ := (Fintype.card ι : ℝ)
  let q : ℝ := S.Lhat / S.μ
  let M : ℝ := max m q
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg S.Lhat_nonneg hμ_pos.le
  have hq_le_M : q ≤ M := le_max_right m q
  have hM_nonneg : 0 ≤ M := le_trans hq_nonneg hq_le_M
  have hmain : 2 * q ≤ (16 / 3) * M := by
    nlinarith [hq_nonneg, hq_le_M, hM_nonneg]
  calc
    2 * S.Lhat / S.μ = 2 * q := by
      dsimp [q]
      ring
    _ ≤ (16 / 3) * max (Fintype.card ι : ℝ) (S.Lhat / S.μ) := by
      simpa [M, m, q] using hmain

/-- Generic scalar alpha-chain from the last lines of Theorem 5.4.

Aligns with Lan Theorem 5.4 proof steps 17--20. Candidate audit: searched the
target file, SOptLib, and Mathlib for `alpha power one minus over one minus
power rpow half geometric sum`; the hits include the output-mass identity,
`geom_sum_range_le_inv_one_sub`, and generic rpow normalization lemmas, but no
existing helper states this standalone source chain. -/
private theorem theorem54_alpha_chain_le_three_rpow_half
    {a : ℝ} {k : ℕ} (hk : 1 ≤ k) (ha_pos : 0 < a) (ha_lt_one : a < 1) :
    ((k : ℝ) + 1) * (a ^ k * (1 - a) / (1 - a ^ k)) ≤
      3 * Real.rpow a ((k : ℝ) / 2) := by
  let b : ℝ := Real.sqrt a
  have hb_nonneg : 0 ≤ b := by
    dsimp [b]
    exact Real.sqrt_nonneg _
  have hb_pos : 0 < b := by
    dsimp [b]
    exact Real.sqrt_pos.2 ha_pos
  have hb_sq : b ^ 2 = a := by
    dsimp [b]
    rw [Real.sq_sqrt ha_pos.le]
  have hb_lt_one : b < 1 := by
    by_contra h
    have hge : 1 ≤ b := le_of_not_gt h
    have hsq_ge : 1 ≤ b ^ 2 := by
      nlinarith [sq_nonneg (b - 1)]
    nlinarith [hb_sq, ha_lt_one]
  have hb_le_one : b ≤ 1 := hb_lt_one.le
  have hk_pos : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hsum_lower :
      ((k : ℝ) + 1) * b ^ k ≤
        (Finset.range (k + 1)).sum (fun j => b ^ j) := by
    calc
      ((k : ℝ) + 1) * b ^ k =
          (Finset.range (k + 1)).sum (fun _j => b ^ k) := by
            rw [Finset.sum_const, Finset.card_range]
            simp [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_assoc,
              mul_left_comm, mul_comm]
      _ ≤ (Finset.range (k + 1)).sum (fun j => b ^ j) := by
            refine Finset.sum_le_sum ?_
            intro j hj
            have hjle : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
            exact pow_right_anti₀ hb_nonneg hb_le_one hjle
  have hsum_mul_le :
      (((k : ℝ) + 1) * b ^ k) * (1 - b) ≤ 1 - b ^ (k + 1) := by
    have hgeom :
        ((Finset.range (k + 1)).sum (fun j => b ^ j)) * (1 - b) =
          1 - b ^ (k + 1) := by
      simpa using (geom_sum_mul_neg b (k + 1))
    calc
      (((k : ℝ) + 1) * b ^ k) * (1 - b) ≤
          ((Finset.range (k + 1)).sum (fun j => b ^ j)) * (1 - b) := by
            exact mul_le_mul_of_nonneg_right hsum_lower (sub_nonneg.mpr hb_le_one)
      _ = 1 - b ^ (k + 1) := hgeom
  have hpow_succ_le_one : b ^ (k + 1) ≤ 1 :=
    pow_le_one₀ hb_nonneg hb_le_one
  have hbase_two :
      ((k : ℝ) + 1) * b ^ k * (1 - b ^ 2) ≤
        2 * (1 - b ^ (k + 1)) := by
    calc
      ((k : ℝ) + 1) * b ^ k * (1 - b ^ 2) =
          ((((k : ℝ) + 1) * b ^ k) * (1 - b)) * (1 + b) := by
            ring
      _ ≤ (1 - b ^ (k + 1)) * (1 + b) := by
            exact mul_le_mul_of_nonneg_right hsum_mul_le (by nlinarith [hb_nonneg])
      _ ≤ (1 - b ^ (k + 1)) * 2 := by
            exact mul_le_mul_of_nonneg_left (by nlinarith [hb_le_one])
              (sub_nonneg.mpr hpow_succ_le_one)
      _ = 2 * (1 - b ^ (k + 1)) := by ring
  have hk_succ_le_two : k + 1 ≤ 2 * k := by
    have h := Nat.add_le_add_left hk k
    simpa [two_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  have hpow_two_le_succ : b ^ (2 * k) ≤ b ^ (k + 1) :=
    pow_right_anti₀ hb_nonneg hb_le_one hk_succ_le_two
  have hpow_two_le_one : b ^ (2 * k) ≤ 1 := by
    exact le_trans hpow_two_le_succ hpow_succ_le_one
  have hbase_three :
      ((k : ℝ) + 1) * b ^ k * (1 - b ^ 2) ≤
        3 * (1 - b ^ (2 * k)) := by
    calc
      ((k : ℝ) + 1) * b ^ k * (1 - b ^ 2) ≤
          2 * (1 - b ^ (k + 1)) := hbase_two
      _ ≤ 2 * (1 - b ^ (2 * k)) := by
            exact mul_le_mul_of_nonneg_left (by nlinarith [hpow_two_le_succ]) (by norm_num)
      _ ≤ 3 * (1 - b ^ (2 * k)) := by
            exact mul_le_mul_of_nonneg_right (by norm_num)
              (sub_nonneg.mpr hpow_two_le_one)
  have htwok_pos : 0 < 2 * k := Nat.mul_pos (by decide) hk_pos
  have hden_pos : 0 < 1 - b ^ (2 * k) := by
    exact sub_pos.mpr (pow_lt_one₀ hb_nonneg hb_lt_one (ne_of_gt htwok_pos))
  have hbpow_nonneg : 0 ≤ b ^ k := pow_nonneg hb_nonneg k
  have hdiv_le :
      (((k : ℝ) + 1) * b ^ k * (1 - b ^ 2)) / (1 - b ^ (2 * k)) ≤ 3 := by
    rw [div_le_iff₀ hden_pos]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hbase_three
  have hleft_le :
      ((k : ℝ) + 1) *
          (b ^ (2 * k) * (1 - b ^ 2) / (1 - b ^ (2 * k))) ≤
        3 * b ^ k := by
    calc
      ((k : ℝ) + 1) *
          (b ^ (2 * k) * (1 - b ^ 2) / (1 - b ^ (2 * k))) =
          b ^ k * ((((k : ℝ) + 1) * b ^ k * (1 - b ^ 2)) /
            (1 - b ^ (2 * k))) := by
            field_simp [ne_of_gt hden_pos]
            ring
      _ ≤ b ^ k * 3 := mul_le_mul_of_nonneg_left hdiv_le hbpow_nonneg
      _ = 3 * b ^ k := by ring
  have hrpow_eq : Real.rpow a ((k : ℝ) / 2) = b ^ k := by
    calc
      Real.rpow a ((k : ℝ) / 2) = a ^ ((k : ℝ) / 2) := by
        rfl
      _ = (Real.sqrt a) ^ (k : ℝ) := by
        rw [Real.rpow_div_two_eq_sqrt (x := a) (r := (k : ℝ)) ha_pos.le]
      _ = b ^ (k : ℝ) := by rfl
      _ = b ^ k := by
        rw [Real.rpow_natCast]
  have ha_eq : a = b ^ 2 := hb_sq.symm
  calc
    ((k : ℝ) + 1) * (a ^ k * (1 - a) / (1 - a ^ k)) =
        ((k : ℝ) + 1) *
          (b ^ (2 * k) * (1 - b ^ 2) / (1 - b ^ (2 * k))) := by
          rw [ha_eq]
          rw [pow_mul]
    _ ≤ 3 * b ^ k := hleft_le
    _ = 3 * Real.rpow a ((k : ℝ) / 2) := by
      rw [hrpow_eq]

/-- Theorem 5.4 raw-policy infrastructure for the canonical public endpoint. -/
private theorem theorem_5_4
    {k : ℕ} {xStar : E} {sigma0 : ℝ}
    (hk : 1 ≤ k)
    (hμ_pos : 0 < S.μ)
    (hopt : S.IsOptimalSolution xStar)
    (hsigma : S.InitialGradientBound sigma0)
    (hτ_policy : ∀ t, 1 ≤ t → S.τ t = S.constantTau hμ_pos)
    (hη_policy : ∀ t, 1 ≤ t → S.η t = S.constantEta hμ_pos)
    (hα_policy : ∀ t, 1 ≤ t → S.α t = S.constantAlphaStep hμ_pos) :
    expectationLe S.P
        (fun ω =>
          S.V (S.positiveEtaXIterate (S.theoremPositiveEtaDomain hμ_pos hη_policy) k ω) xStar)
        (2 * S.Delta0Sigma0 hμ_pos xStar sigma0 * S.theoremAlpha hμ_pos ^ k / S.μ) ∧
      expectationLe S.P
        (fun ω =>
          S.psi (S.theoremWeightedOutput hμ_pos hη_policy k hk
            (S.theoremTheta_outputWeightsPositive hk hμ_pos) ω) -
            S.psi xStar)
        (16 * max (Fintype.card ι : ℝ) (S.Lhat / S.μ) *
          S.Delta0Sigma0 hμ_pos xStar sigma0 *
            Real.rpow (S.theoremAlpha hμ_pos) ((k : ℝ) / 2)) := by
  have hfresh : S.FreshConditionalBlockSampling := S.freshConditionalBlockSampling
  have hwd :
      SOptLib.expectationWellDefined S.P
          (fun ω =>
            S.V
              (S.positiveEtaXIterate (S.theoremPositiveEtaDomain hμ_pos hη_policy) k ω)
              xStar) ∧
        SOptLib.expectationWellDefined S.P
          (fun ω =>
            S.psi (S.theoremWeightedOutput hμ_pos hη_policy k hk
              (S.theoremTheta_outputWeightsPositive hk hμ_pos) ω) -
              S.psi xStar) :=
    by
      constructor
      · simpa [SOptLib.expectationWellDefined] using
          (S.positiveEta_strictPast_payload_integrable
            (S.theoremPositiveEtaDomain hμ_pos hη_policy) hk
            (G := fun x _prev => S.V x xStar))
      · simpa [SOptLib.expectationWellDefined] using
          (S.theorem54_weighted_output_payload_integrable hμ_pos hη_policy hk
            (S.theoremTheta_outputWeightsPositive hk hμ_pos)
            (fun x => S.psi x - S.psi xStar))
  let Sθ : Setup ι E := { S with θ := S.theoremTheta hμ_pos }
  have hμθ : 0 < Sθ.μ := by
    simpa [Sθ] using hμ_pos
  have hηθ : Sθ.PositiveEtaDomain := by
    simpa [Sθ, constantEta, theoremAlpha] using
      (S.theoremPositiveEtaDomain hμ_pos hη_policy)
  have hτθ_policy : ∀ t, 1 ≤ t → Sθ.τ t = Sθ.constantTau hμθ := by
    intro t ht
    simpa [Sθ, constantTau, theoremAlpha] using hτ_policy t ht
  have hηθ_policy : ∀ t, 1 ≤ t → Sθ.η t = Sθ.constantEta hμθ := by
    intro t ht
    simpa [Sθ, constantEta, theoremAlpha] using hη_policy t ht
  have hαθ_policy : ∀ t, 1 ≤ t → Sθ.α t = Sθ.constantAlphaStep hμθ := by
    intro t ht
    simpa [Sθ, constantAlphaStep, theoremAlpha] using hα_policy t ht
  have hoptθ : Sθ.IsOptimalSolution xStar := by
    simpa [Sθ, IsOptimalSolution, psi] using hopt
  have hsigmaθ : Sθ.InitialGradientBound sigma0 := by
    simpa [Sθ, InitialGradientBound] using hsigma
  have htheta_policyθ : Sθ.TheoremOutputWeightPolicy hμθ k := by
    intro t ht
    simp [Sθ, TheoremOutputWeightPolicy, theoremTheta, theoremAlpha, Lhat]
  have hθposθ : Sθ.OutputWeightsPositive k := by
    intro t ht
    simpa [Sθ, theoremTheta, theoremAlpha] using
      (S.theoremTheta_outputWeightsPositive hk hμ_pos t ht)
  have hθ_side :
      ({ S with θ := S.theoremTheta hμ_pos } : Setup ι E).WeightCondition5261 k ∧
        ({ S with θ := S.theoremTheta hμ_pos } : Setup ι E).PropositionSideConditions k :=
    S.theorem54_theta_policy_weight_and_side_conditions hk hμ_pos
      hτ_policy hη_policy hα_policy
  have hweightθ : Sθ.WeightCondition5261 k := by
    simpa [Sθ] using hθ_side.1
  have hsideθ : Sθ.PropositionSideConditions k := by
    simpa [Sθ] using hθ_side.2
  have hprop :=
    Sθ.proposition_5_6_positive_domain hk hηθ hoptθ hsigmaθ hθposθ hweightθ hsideθ
  have hQ_prop :
      expectationLe Sθ.P
        (fun ω => Sθ.Q (Sθ.positiveEtaWeightedOutput hηθ k hk hθposθ ω) xStar)
        ((Sθ.outputWeightSum k)⁻¹ * Sθ.DeltaTilde0Sigma0 hηθ k xStar sigma0) :=
    hprop.1
  have hV_prop :
      expectationLe Sθ.P
        (fun ω => Sθ.V (Sθ.positiveEtaXIterate hηθ k ω) xStar)
        (2 * Sθ.DeltaTilde0Sigma0 hηθ k xStar sigma0 /
          (Sθ.θ k * (Sθ.μ + Sθ.η k))) :=
    hprop.2
  constructor
  · have hVRhs :
        2 * Sθ.DeltaTilde0Sigma0 hηθ k xStar sigma0 /
            (Sθ.θ k * (Sθ.μ + Sθ.η k)) ≤
          2 * S.Delta0Sigma0 hμ_pos xStar sigma0 *
            S.theoremAlpha hμ_pos ^ k / S.μ := by
      change
        2 *
            ({ S with θ := S.theoremTheta hμ_pos } : Setup ι E).DeltaTilde0Sigma0
              hηθ k xStar sigma0 /
            ((({ S with θ := S.theoremTheta hμ_pos } : Setup ι E).θ k) *
              ((({ S with θ := S.theoremTheta hμ_pos } : Setup ι E).μ) +
                (({ S with θ := S.theoremTheta hμ_pos } : Setup ι E).η k))) ≤
          2 * S.Delta0Sigma0 hμ_pos xStar sigma0 *
            S.theoremAlpha hμ_pos ^ k / S.μ
      exact S.theorem54_v_rhs_bound_from_delta_tilde
        (k := k) (xStar := xStar) (sigma0 := sigma0)
        hk hμ_pos hηθ hτ_policy hη_policy hα_policy
    rcases hV_prop with ⟨_hV_wd, hV_le⟩
    have hV_le_S :
        SOptLib.expectation S.P
            (fun ω =>
              S.V
                (S.positiveEtaXIterate
                  (S.theoremPositiveEtaDomain hμ_pos hη_policy) k ω)
                xStar) ≤
          2 * Sθ.DeltaTilde0Sigma0 hηθ k xStar sigma0 /
            (Sθ.θ k * (Sθ.μ + Sθ.η k)) := by
      have hfun_eq :
          (fun ω => Sθ.V (Sθ.positiveEtaXIterate hηθ k ω) xStar) =
            (fun ω =>
              S.V
                (S.positiveEtaXIterate
                  (S.theoremPositiveEtaDomain hμ_pos hη_policy) k ω)
                xStar) := by
        funext ω
        have hx :=
          S.positiveEtaXIterate_theta_update_eq
            (S.theoremTheta hμ_pos) hηθ
            (S.theoremPositiveEtaDomain hμ_pos hη_policy) k ω
        exact congrArg (fun y => S.V y xStar) hx
      simpa [Sθ, hfun_eq] using hV_le
    exact ⟨hwd.1, le_trans hV_le_S hVRhs⟩
  ·
    have hOutEq :
        ∀ ω, Sθ.positiveEtaWeightedOutput hηθ k hk hθposθ ω =
          S.theoremWeightedOutput hμ_pos hη_policy k hk
            (S.theoremTheta_outputWeightsPositive hk hμ_pos) ω := by
      intro ω
      rw [Sθ.positiveEtaWeightedOutput_def, S.theoremWeightedOutput_def]
      have hden : Sθ.outputWeightSum k = S.theoremOutputWeightSum hμ_pos k := by
        change Finset.sum (outputWindow k) (S.theoremTheta hμ_pos) =
          Finset.sum (outputWindow k) (S.theoremTheta hμ_pos)
        rfl
      have hsum :
          Finset.sum (outputWindow k)
              (fun t => Sθ.θ t • Sθ.positiveEtaXIterate hηθ t ω) =
            Finset.sum (outputWindow k)
              (fun t => S.theoremTheta hμ_pos t •
                S.theoremXIterate hμ_pos hη_policy t ω) := by
        apply Finset.sum_congr rfl
        intro t _ht
        have hx :
            Sθ.positiveEtaXIterate hηθ t ω =
              S.positiveEtaXIterate
                (S.theoremPositiveEtaDomain hμ_pos hη_policy) t ω := by
          exact S.positiveEtaXIterate_theta_update_eq
            (S.theoremTheta hμ_pos) hηθ
            (S.theoremPositiveEtaDomain hμ_pos hη_policy) t ω
        change S.theoremTheta hμ_pos t • Sθ.positiveEtaXIterate hηθ t ω =
          S.theoremTheta hμ_pos t •
            S.positiveEtaXIterate
              (S.theoremPositiveEtaDomain hμ_pos hη_policy) t ω
        exact congrArg (fun z => S.theoremTheta hμ_pos t • z) hx
      rw [hden, hsum]
    have hQ_out :
        expectationLe S.P
          (fun ω =>
            S.Q (S.theoremWeightedOutput hμ_pos hη_policy k hk
              (S.theoremTheta_outputWeightsPositive hk hμ_pos) ω) xStar)
          ((Sθ.outputWeightSum k)⁻¹ * Sθ.DeltaTilde0Sigma0 hηθ k xStar sigma0) := by
      rcases hQ_prop with ⟨hQwd, hQle⟩
      refine ⟨?_, ?_⟩
      · simpa [Sθ, hOutEq] using hQwd
      · simpa [Sθ, hOutEq] using hQle
    let a : ℝ := S.theoremAlpha hμ_pos
    let Δ : ℝ := S.Delta0Sigma0 hμ_pos xStar sigma0
    have ha_pos : 0 < a := by
      simpa [a] using (S.theoremAlpha_pos_lt_one hμ_pos).1
    have ha_lt_one : a < 1 := by
      simpa [a] using (S.theoremAlpha_pos_lt_one hμ_pos).2
    have hDelta_tilde :
        Sθ.DeltaTilde0Sigma0 hηθ k xStar sigma0 ≤ (1 - a)⁻¹ * Δ := by
      change ({ S with θ := S.theoremTheta hμ_pos } : Setup ι E).DeltaTilde0Sigma0
          hηθ k xStar sigma0 ≤
        (1 - S.theoremAlpha hμ_pos)⁻¹ *
          S.Delta0Sigma0 hμ_pos xStar sigma0
      exact
        S.theorem54_delta_tilde_le_delta0_over_one_minus_alpha
          (k := k) (xStar := xStar) (sigma0 := sigma0)
          hμ_pos hηθ hτ_policy hη_policy hα_policy
    have hW_pos : 0 < Sθ.outputWeightSum k :=
      Sθ.outputWeightSum_pos hk hθposθ
    have hW_eq :
        Sθ.outputWeightSum k =
          Finset.sum (outputWindow k) (fun t => (a ^ t)⁻¹) := by
      change Finset.sum (outputWindow k) (S.theoremTheta hμ_pos) =
        Finset.sum (outputWindow k) (fun t => (a ^ t)⁻¹)
      apply Finset.sum_congr rfl
      intro t _ht
      simp [theoremTheta, a]
    have hmass_inv :
        (Sθ.outputWeightSum k)⁻¹ * (1 - a)⁻¹ =
          a ^ k / (1 - a ^ k) := by
      rw [hW_eq]
      exact theorem54_inverse_geometric_output_mass hk ha_pos ha_lt_one
    have hQ_rhs_le :
        (Sθ.outputWeightSum k)⁻¹ *
            Sθ.DeltaTilde0Sigma0 hηθ k xStar sigma0 ≤
          (a ^ k / (1 - a ^ k)) * Δ := by
      calc
        (Sθ.outputWeightSum k)⁻¹ *
            Sθ.DeltaTilde0Sigma0 hηθ k xStar sigma0
            ≤ (Sθ.outputWeightSum k)⁻¹ * ((1 - a)⁻¹ * Δ) := by
              exact mul_le_mul_of_nonneg_left hDelta_tilde
                (inv_nonneg.mpr hW_pos.le)
        _ = (a ^ k / (1 - a ^ k)) * Δ := by
              rw [← hmass_inv]
              ring
    have hQ_scalar :
        expectationLe S.P
          (fun ω =>
            S.Q (S.theoremWeightedOutput hμ_pos hη_policy k hk
              (S.theoremTheta_outputWeightsPositive hk hμ_pos) ω) xStar)
          ((a ^ k / (1 - a ^ k)) * Δ) := by
      rcases hQ_out with ⟨hQwd, hQle⟩
      exact ⟨hQwd, le_trans hQle hQ_rhs_le⟩
    have hPositiveOut_mem :
        ∀ ω, Sθ.positiveEtaWeightedOutput hηθ k hk hθposθ ω ∈ Sθ.X := by
      intro ω
      rw [Sθ.positiveEtaWeightedOutput_def]
      exact
        Convex.normalized_weighted_sum_mem Sθ.hX_convex (outputWindow k) Sθ.θ
          (fun t => Sθ.positiveEtaXIterate hηθ t ω)
          (Sθ.outputWeightSum_pos hk hθposθ)
          (fun t ht => (hθposθ t ht).le)
          (fun t _ht => Sθ.positiveEtaXIterate_mem hηθ t ω)
    have hOut_mem :
        ∀ ω,
          S.theoremWeightedOutput hμ_pos hη_policy k hk
            (S.theoremTheta_outputWeightsPositive hk hμ_pos) ω ∈ S.X := by
      intro ω
      have hmem := hPositiveOut_mem ω
      rw [hOutEq ω] at hmem
      simpa [Sθ] using hmem
    have hObj_point_lf :
        ∀ ω,
          S.psi (S.theoremWeightedOutput hμ_pos hη_policy k hk
              (S.theoremTheta_outputWeightsPositive hk hμ_pos) ω) -
              S.psi xStar ≤
            S.Q (S.theoremWeightedOutput hμ_pos hη_policy k hk
              (S.theoremTheta_outputWeightsPositive hk hμ_pos) ω) xStar +
              (S.Lf / 2) *
                S.primalNorm
                  (S.theoremWeightedOutput hμ_pos hη_policy k hk
                    (S.theoremTheta_outputWeightsPositive hk hμ_pos) ω - xStar) ^ 2 := by
      intro ω
      have hcomp :=
        S.QComparison_Eq_5_2_60 hopt (hOut_mem ω)
      nlinarith
    have hObj_point_lhat :
        ∀ ω,
          S.psi (S.theoremWeightedOutput hμ_pos hη_policy k hk
              (S.theoremTheta_outputWeightsPositive hk hμ_pos) ω) -
              S.psi xStar ≤
            S.Q (S.theoremWeightedOutput hμ_pos hη_policy k hk
              (S.theoremTheta_outputWeightsPositive hk hμ_pos) ω) xStar +
              (S.Lhat / 2) *
                S.primalNorm
                  (S.theoremWeightedOutput hμ_pos hη_policy k hk
                    (S.theoremTheta_outputWeightsPositive hk hμ_pos) ω - xStar) ^ 2 := by
      intro ω
      exact le_trans (hObj_point_lf ω)
        (add_le_add_right
          (S.theorem54_lf_remainder_le_lhat_remainder
            (hOut_mem ω) hopt.1)
          _)
    have hDist_pointwise_V :
        ∀ ω,
          (S.Lhat / 2) *
              S.primalNorm
                (S.theoremWeightedOutput hμ_pos hη_policy k hk
                  (S.theoremTheta_outputWeightsPositive hk hμ_pos) ω - xStar) ^ 2 ≤
            (S.Lhat / 2) *
              ((S.theoremOutputWeightSum hμ_pos k)⁻¹ *
                Finset.sum (outputWindow k) (fun t =>
                  S.theoremTheta hμ_pos t *
                    (2 * S.V (S.theoremXIterate hμ_pos hη_policy t ω) xStar))) := by
      intro ω
      exact mul_le_mul_of_nonneg_left
        (S.theorem54_weighted_output_sq_primalNorm_le_weighted_V_pointwise
          hk hμ_pos hη_policy
          (S.theoremTheta_outputWeightsPositive hk hμ_pos) hopt ω)
        (by nlinarith [S.Lhat_nonneg])
    have hVterm_raw :
        expectationLe S.P
          (fun ω =>
            (S.Lhat / 2) *
              ((S.theoremOutputWeightSum hμ_pos k)⁻¹ *
                Finset.sum (outputWindow k) (fun t =>
                  S.theoremTheta hμ_pos t *
                    (2 * S.V (S.theoremXIterate hμ_pos hη_policy t ω) xStar))))
          ((S.Lhat / 2) * (S.theoremOutputWeightSum hμ_pos k)⁻¹ *
            Finset.sum (outputWindow k)
              (fun _t => 4 * S.Delta0Sigma0 hμ_pos xStar sigma0 / S.μ)) :=
      S.theorem54_weighted_V_sum_expectation_bound_raw
        hk hμ_pos hopt hsigma hτ_policy hη_policy hα_policy
    have hmass_inv_theorem :
        (S.theoremOutputWeightSum hμ_pos k)⁻¹ * (1 - a)⁻¹ =
          a ^ k / (1 - a ^ k) := by
      have hden :
          Sθ.outputWeightSum k = S.theoremOutputWeightSum hμ_pos k := by
        change Finset.sum (outputWindow k) (S.theoremTheta hμ_pos) =
          Finset.sum (outputWindow k) (S.theoremTheta hμ_pos)
        rfl
      simpa [hden] using hmass_inv
    have hW_inv_eq :
        (S.theoremOutputWeightSum hμ_pos k)⁻¹ =
          a ^ k * (1 - a) / (1 - a ^ k) := by
      have h1ma_ne : 1 - a ≠ 0 := ne_of_gt (sub_pos.mpr ha_lt_one)
      calc
        (S.theoremOutputWeightSum hμ_pos k)⁻¹ =
            ((S.theoremOutputWeightSum hμ_pos k)⁻¹ * (1 - a)⁻¹) * (1 - a) := by
              field_simp [h1ma_ne]
        _ = (a ^ k / (1 - a ^ k)) * (1 - a) := by
              rw [hmass_inv_theorem]
        _ = a ^ k * (1 - a) / (1 - a ^ k) := by
              ring
    have hsum_const :
        Finset.sum (outputWindow k)
            (fun _t => 4 * S.Delta0Sigma0 hμ_pos xStar sigma0 / S.μ) =
          (k : ℝ) * (4 * Δ / S.μ) := by
      have hcard : (outputWindow k).card = k := by
        simp [outputWindow, Nat.sub_add_cancel hk]
      rw [Finset.sum_const, hcard]
      simp [nsmul_eq_mul, Δ]
    have hVterm :
        expectationLe S.P
          (fun ω =>
            (S.Lhat / 2) *
              ((S.theoremOutputWeightSum hμ_pos k)⁻¹ *
                Finset.sum (outputWindow k) (fun t =>
                  S.theoremTheta hμ_pos t *
                    (2 * S.V (S.theoremXIterate hμ_pos hη_policy t ω) xStar))))
          ((2 * S.Lhat / S.μ) * (k : ℝ) * Δ *
            (a ^ k * (1 - a) / (1 - a ^ k))) := by
      rcases hVterm_raw with ⟨hVwd, hVle⟩
      refine ⟨hVwd, le_trans hVle ?_⟩
      apply le_of_eq
      rw [hW_inv_eq, hsum_const]
      ring
    have hpoint :
        ∀ᵐ ω ∂S.P,
          S.psi (S.theoremWeightedOutput hμ_pos hη_policy k hk
              (S.theoremTheta_outputWeightsPositive hk hμ_pos) ω) -
              S.psi xStar ≤
            S.Q (S.theoremWeightedOutput hμ_pos hη_policy k hk
              (S.theoremTheta_outputWeightsPositive hk hμ_pos) ω) xStar +
              (S.Lhat / 2) *
                ((S.theoremOutputWeightSum hμ_pos k)⁻¹ *
                  Finset.sum (outputWindow k) (fun t =>
                    S.theoremTheta hμ_pos t *
                      (2 * S.V (S.theoremXIterate hμ_pos hη_policy t ω) xStar))) := by
      exact Filter.Eventually.of_forall (fun ω =>
        le_trans (hObj_point_lhat ω)
          (add_le_add_right (hDist_pointwise_V ω)
            (S.Q (S.theoremWeightedOutput hμ_pos hη_policy k hk
              (S.theoremTheta_outputWeightsPositive hk hμ_pos) ω) xStar)))
    have hObj_pre :
        expectationLe S.P
          (fun ω =>
            S.psi (S.theoremWeightedOutput hμ_pos hη_policy k hk
              (S.theoremTheta_outputWeightsPositive hk hμ_pos) ω) -
              S.psi xStar)
          ((a ^ k / (1 - a ^ k)) * Δ +
            (2 * S.Lhat / S.μ) * (k : ℝ) * Δ *
              (a ^ k * (1 - a) / (1 - a ^ k))) :=
      expectationLe_of_pointwise_le_add hwd.2 hQ_scalar hVterm hpoint
    rcases hObj_pre with ⟨hObj_wd, hObj_le⟩
    refine ⟨hObj_wd, le_trans hObj_le ?_⟩
    have h1ma_ne : 1 - a ≠ 0 := ne_of_gt (sub_pos.mpr ha_lt_one)
    have hpre_eq :
        a ^ k / (1 - a ^ k) * Δ +
            2 * S.Lhat / S.μ * (k : ℝ) * Δ *
              (a ^ k * (1 - a) / (1 - a ^ k)) =
          ((1 / (1 - a) + (2 * S.Lhat / S.μ) * (k : ℝ)) *
            Δ * (a ^ k * (1 - a) / (1 - a ^ k))) := by
      field_simp [h1ma_ne]
    rw [hpre_eq]
    let M : ℝ := max (Fintype.card ι : ℝ) (S.Lhat / S.μ)
    let R : ℝ := a ^ k * (1 - a) / (1 - a ^ k)
    have hm_pos : 0 < (Fintype.card ι : ℝ) := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
    have hM_nonneg : 0 ≤ M := by
      dsimp [M]
      exact le_trans hm_pos.le (le_max_left _ _)
    have hDelta_nonneg : 0 ≤ Δ := by
      simpa [Δ] using S.Delta0Sigma0_nonneg hμ_pos hopt sigma0
    have hpow_lt_one : a ^ k < 1 :=
      pow_lt_one₀ ha_pos.le ha_lt_one (ne_of_gt (lt_of_lt_of_le zero_lt_one hk))
    have hR_nonneg : 0 ≤ R := by
      have hnum_nonneg : 0 ≤ a ^ k * (1 - a) := by
        exact mul_nonneg (pow_nonneg ha_pos.le k) (sub_nonneg.mpr ha_lt_one.le)
      have hden_pos : 0 < 1 - a ^ k := sub_pos.mpr hpow_lt_one
      dsimp [R]
      exact div_nonneg hnum_nonneg hden_pos.le
    have hB1 : 1 / (1 - a) ≤ (16 / 3) * M := by
      simpa [a, M] using
        S.theorem54_one_div_one_minus_alpha_le_sixteen_thirds_max hμ_pos
    have hB2 : 2 * S.Lhat / S.μ ≤ (16 / 3) * M := by
      simpa [M] using
        S.theorem54_two_lhat_div_mu_le_sixteen_thirds_max hμ_pos
    have hk_nonneg : 0 ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
    have hbracket :
        1 / (1 - a) + 2 * S.Lhat / S.μ * (k : ℝ) ≤
          (16 / 3) * M * ((k : ℝ) + 1) := by
      have hB2k :
          2 * S.Lhat / S.μ * (k : ℝ) ≤
            ((16 / 3) * M) * (k : ℝ) :=
        mul_le_mul_of_nonneg_right hB2 hk_nonneg
      calc
        1 / (1 - a) + 2 * S.Lhat / S.μ * (k : ℝ) ≤
            (16 / 3) * M + ((16 / 3) * M) * (k : ℝ) :=
              add_le_add hB1 hB2k
        _ = (16 / 3) * M * ((k : ℝ) + 1) := by ring
    have hchain :
        ((k : ℝ) + 1) * R ≤
          3 * Real.rpow a ((k : ℝ) / 2) := by
      simpa [R] using
        theorem54_alpha_chain_le_three_rpow_half
          (a := a) (k := k) hk ha_pos ha_lt_one
    have hcoef_nonneg : 0 ≤ (16 / 3) * M * Δ := by
      exact mul_nonneg (mul_nonneg (by norm_num) hM_nonneg) hDelta_nonneg
    calc
      (1 / (1 - a) + 2 * S.Lhat / S.μ * (k : ℝ)) * Δ *
          (a ^ k * (1 - a) / (1 - a ^ k))
          ≤ ((16 / 3) * M * ((k : ℝ) + 1)) * Δ * R := by
            have hstep1 :
                (1 / (1 - a) + 2 * S.Lhat / S.μ * (k : ℝ)) * Δ ≤
                  ((16 / 3) * M * ((k : ℝ) + 1)) * Δ :=
              mul_le_mul_of_nonneg_right hbracket hDelta_nonneg
            simpa [R] using mul_le_mul_of_nonneg_right hstep1 hR_nonneg
      _ = (16 / 3) * M * Δ * (((k : ℝ) + 1) * R) := by ring
      _ ≤ (16 / 3) * M * Δ *
            (3 * Real.rpow a ((k : ℝ) / 2)) := by
            exact mul_le_mul_of_nonneg_left hchain hcoef_nonneg
      _ = 16 * M * Δ * Real.rpow a ((k : ℝ) / 2) := by ring
      _ = 16 * max (Fintype.card ι : ℝ) (S.Lhat / S.μ) *
            S.Delta0Sigma0 hμ_pos xStar sigma0 *
            Real.rpow (S.theoremAlpha hμ_pos) ((k : ℝ) / 2) := by
            simp [M, Δ, a, mul_assoc, mul_left_comm, mul_comm]

/-- Theorem 5.4 under the canonical source-named parameter policy object. -/
theorem theorem_5_4_canonical_policy
    {k : ℕ} {xStar : E} {sigma0 : ℝ}
    (hk : 1 ≤ k)
    (hμ_pos : 0 < S.μ)
    (hopt : S.IsOptimalSolution xStar)
    (hsigma : S.InitialGradientBound sigma0)
    (hpolicy : S.Theorem54ParameterPolicy hμ_pos) :
    expectationLe S.P
        (fun ω =>
          S.V (S.positiveEtaXIterate
            (S.theoremPositiveEtaDomain hμ_pos
              (S.theorem54ParameterPolicy_eta hpolicy)) k ω) xStar)
        (2 * S.Delta0Sigma0 hμ_pos xStar sigma0 *
          S.theoremAlpha hμ_pos ^ k / S.μ) ∧
      expectationLe S.P
        (fun ω =>
          S.psi (S.theoremWeightedOutput hμ_pos
            (S.theorem54ParameterPolicy_eta hpolicy) k hk
            (S.theoremTheta_outputWeightsPositive hk hμ_pos) ω) -
            S.psi xStar)
        (16 * max (Fintype.card ι : ℝ) (S.Lhat / S.μ) *
          S.Delta0Sigma0 hμ_pos xStar sigma0 *
            Real.rpow (S.theoremAlpha hμ_pos) ((k : ℝ) / 2)) := by
  exact S.theorem_5_4 hk hμ_pos hopt hsigma
    (S.theorem54ParameterPolicy_tau hpolicy)
    (S.theorem54ParameterPolicy_eta hpolicy)
    (S.theorem54ParameterPolicy_alpha hpolicy)

end Setup

end RandomGradientExtrapolation
